(*
  Micro_Mojo_Static.thy

  Static semantics of micro-Mojo: typing, a flow-sensitive ownership
  checker (Mojo's lifetime checker), and the ASAP elaboration that inserts
  explicit DROP statements.
*)

theory Micro_Mojo_Static
  imports Micro_Mojo_Semantics
begin

section \<open>Overview\<close>

text \<open>
  This theory provides the two static components that the dynamic semantics
  relies on.

  \<^bold>\<open>The ownership checker\<close> @{text "check_prog"} returns the list of errors in
  a program (empty means well-formed). Like Mojo's lifetime checker, it is
  a flow-sensitive abstract interpretation of each function body. The
  abstract state records
    \<^item> which owned variables are definitely initialized (moves and
      @{text "DROP"} remove variables, assignments add them);
    \<^item> which reference bindings may have been invalidated by a
      shape-changing mutation of a list they point into (interior origins);
    \<^item> inside @{text "__init__"}, which fields of @{text "out self"} are
      initialized.
  On top of this it checks types, implicit copies, argument exclusivity,
  mutation through immutable arguments, and that a returned reference comes
  from the declared origin.

  \<^bold>\<open>Origins are regions.\<close> Each reference binding carries a static
  \<^emph>\<open>origin\<close>: the set of variables it may point into, which is a region in
  the sense of @{text "Mojo_Region_Model"}. It also carries an \<^emph>\<open>interior\<close>
  set, the variables into whose list items it may point. A reference may
  be used only if it has not been invalidated and every owned variable in
  its origin is still initialized. This is exactly @{text "safe_to_deref"}
  from Part 2 of the region theory, applied to the origin. Argument
  exclusivity compares the origins of borrowed arguments, which is Rule 2
  (@{text "mem_disjoint"}) at the level of static paths.

  \<^bold>\<open>The ASAP elaboration\<close> @{text "elaborate"} inserts @{text "DROP x"} right
  after the last use of each owned variable @{text "x"}, where a use of a
  reference counts as a use of every variable in its origin. This is the
  lifetime extension of Mojo's origins. We prove that elaboration only
  inserts @{text "DROP"}s (@{text "elab_only_inserts_drops"}).

  \<^bold>\<open>Simplifications\<close>, each a deliberate restriction relative to Mojo, chosen
  to keep the checker small:
    \<^item> variable names must be distinct within a function (Mojo allows
      shadowing in inner blocks);
    \<^item> only owned local variables can be transferred with @{text "^"}
      (Mojo also allows moving out of a field if it is reinitialized, or
      in @{text "__deinit__"});
    \<^item> @{text "var"} arguments without @{text "^"} must be of trivial type
      (Mojo copies any @{text "Copyable"} value implicitly here);
    \<^item> static paths stop at the first index, so @{text "l[i]"} and
      @{text "l[j]"} are always considered to overlap;
    \<^item> the analysis and drop insertion work at statement granularity, while
      Mojo destroys temporaries inside expressions.

  \<^bold>\<open>Soundness\<close> is the target theorem for the next step: for a program
  accepted by @{text "check_prog"}, running the elaborated program never
  produces an ownership error (@{text "ErrUninit"}, @{text "ErrInvalidated"},
  @{text "ErrDangling"}, @{text "ErrNotCopyable"}, @{text "ErrFieldInit"}).
  For now we check it on all the examples.
\<close>

section \<open>A checking monad\<close>

datatype 'a ck = Good 'a | Bad string

fun bind_ck :: "'a ck \<Rightarrow> ('a \<Rightarrow> 'b ck) \<Rightarrow> 'b ck" where
  "bind_ck (Good a) f = f a"
| "bind_ck (Bad m) f = Bad m"

lemma bind_ck_cong [fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>a. m' = Good a \<Longrightarrow> f a = f' a) \<Longrightarrow> bind_ck m f = bind_ck m' f'"
  by (cases m) auto

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind_ck

definition check :: "bool \<Rightarrow> string \<Rightarrow> unit ck" where
  "check b msg = (if b then Good () else Bad msg)"

section \<open>Typing\<close>

fun trivial_ty :: "ty \<Rightarrow> bool" where
  "trivial_ty TInt = True"
| "trivial_ty TBool = True"
| "trivial_ty TStr = True"
| "trivial_ty TNone = True"
| "trivial_ty _ = False"

text \<open>
  Static kinds of variables: owned variables (@{text "var"} declarations and
  @{text "var"} parameters), borrowed parameters with their convention, and
  reference bindings with their origin and interior.
\<close>

datatype vkind =
    KOwned ty
  | KBorrow conv ty
  | KRef ty "vname set" "vname set"   \<comment> \<open>type, origin, interior\<close>

type_synonym senv = "(vname \<times> vkind) list"

fun kind_ty :: "vkind \<Rightarrow> ty" where
  "kind_ty (KOwned T) = T"
| "kind_ty (KBorrow _ T) = T"
| "kind_ty (KRef T _ _) = T"

fun ret_ty :: "ret \<Rightarrow> ty" where
  "ret_ty RNone = TNone"
| "ret_ty (RVal T) = T"
| "ret_ty (RRef _ T) = T"

definition field_ty :: "prog \<Rightarrow> name \<Rightarrow> fname \<Rightarrow> ty ck" where
  "field_ty P S f = (case find_struct P S of
     None \<Rightarrow> Bad (''unknown struct '' @ S)
   | Some sd \<Rightarrow> (case map_of (sd_fields sd) f of
       None \<Rightarrow> Bad (''no field '' @ f @ '' in '' @ S)
     | Some T \<Rightarrow> Good T))"

text \<open>
  The parameters of a call @{text "f(...)"}: those of the function, of the
  initializer without @{text "out self"}, or the fields of a
  @{text "@fieldwise_init"} struct, passed as @{text "var"}.
\<close>

definition call_params :: "prog \<Rightarrow> name \<Rightarrow> (conv \<times> vname \<times> ty) list ck" where
  "call_params P f = (case find_struct P f of
     Some sd \<Rightarrow> (case sd_init sd of
        Some fd \<Rightarrow> Good (tl (fd_params fd))
      | None \<Rightarrow> if sd_fieldwise sd then Good (map (\<lambda>(fl, T). (Var, fl, T)) (sd_fields sd))
               else Bad (''struct '' @ f @ '' has no initializer''))
   | None \<Rightarrow> (case find_fun P f of
        Some fd \<Rightarrow> Good (fd_params fd)
      | None \<Rightarrow> Bad (''unknown function '' @ f)))"

definition call_ret :: "prog \<Rightarrow> name \<Rightarrow> ty" where
  "call_ret P f = (case find_struct P f of
     Some _ \<Rightarrow> TStruct f
   | None \<Rightarrow> (case find_fun P f of Some fd \<Rightarrow> ret_ty (fd_ret fd) | None \<Rightarrow> TNone))"

definition meth_decl :: "prog \<Rightarrow> name \<Rightarrow> name \<Rightarrow> fundecl ck" where
  "meth_decl P S m = (case find_struct P S of
     None \<Rightarrow> Bad (''unknown struct '' @ S)
   | Some sd \<Rightarrow> (case find_method sd m of
       None \<Rightarrow> Bad (''no method '' @ m @ '' in '' @ S)
     | Some fd \<Rightarrow> Good fd))"

definition param_tys :: "(conv \<times> vname \<times> ty) list \<Rightarrow> ty list" where
  "param_tys ps = map (\<lambda>(_, _, T). T) ps"

fun ptype :: "prog \<Rightarrow> senv \<Rightarrow> place \<Rightarrow> ty ck"
and etype :: "prog \<Rightarrow> senv \<Rightarrow> expr \<Rightarrow> ty ck"
and etypes :: "prog \<Rightarrow> senv \<Rightarrow> expr list \<Rightarrow> ty list ck"
where
  "ptype P \<Gamma> (PVar x) = (case map_of \<Gamma> x of
     Some k \<Rightarrow> Good (kind_ty k)
   | None \<Rightarrow> Bad (''unbound variable '' @ x))"
| "ptype P \<Gamma> (PField p f) = do {
     T \<leftarrow> ptype P \<Gamma> p;
     (case T of TStruct S \<Rightarrow> field_ty P S f | _ \<Rightarrow> Bad ''field access on a non-struct'') }"
| "ptype P \<Gamma> (PIndex p e) = do {
     T \<leftarrow> ptype P \<Gamma> p;
     I \<leftarrow> etype P \<Gamma> e;
     check (I = TInt) ''list index must be an Int'';
     (case T of TList U \<Rightarrow> Good U | _ \<Rightarrow> Bad ''indexing a non-list'') }"
| "etype P \<Gamma> (EInt _) = Good TInt"
| "etype P \<Gamma> (EBool _) = Good TBool"
| "etype P \<Gamma> (EStr _) = Good TStr"
| "etype P \<Gamma> (EPlace p) = ptype P \<Gamma> p"
| "etype P \<Gamma> (ETake p) = ptype P \<Gamma> p"
| "etype P \<Gamma> (ECopy p) = ptype P \<Gamma> p"
| "etype P \<Gamma> (ECall f es) = do {
     ps \<leftarrow> call_params P f;
     Ts \<leftarrow> etypes P \<Gamma> es;
     check (Ts = param_tys ps) (''argument types do not match the parameters of '' @ f);
     Good (call_ret P f) }"
| "etype P \<Gamma> (EMeth p m es) = do {
     T \<leftarrow> ptype P \<Gamma> p;
     Ts \<leftarrow> etypes P \<Gamma> es;
     (case T of
        TList U \<Rightarrow>
          if m = ''append'' then do { check (Ts = [U]) ''bad argument to append''; Good TNone }
          else if m = ''pop'' then do { check (Ts = []) ''pop takes no arguments''; Good U }
          else Bad (''no list method '' @ m)
      | TStruct S \<Rightarrow> do {
          fd \<leftarrow> meth_decl P S m;
          check (Ts = param_tys (tl (fd_params fd)))
            (''argument types do not match the parameters of '' @ m);
          Good (ret_ty (fd_ret fd)) }
      | _ \<Rightarrow> Bad ''method call on a value that is neither a struct nor a list'') }"
| "etype P \<Gamma> (EBin op a b) = do {
     A \<leftarrow> etype P \<Gamma> a;
     B \<leftarrow> etype P \<Gamma> b;
     (case op of
        Add \<Rightarrow> do { check (A = TInt \<and> B = TInt) ''arithmetic needs Int operands''; Good TInt }
      | Sub \<Rightarrow> do { check (A = TInt \<and> B = TInt) ''arithmetic needs Int operands''; Good TInt }
      | Mul \<Rightarrow> do { check (A = TInt \<and> B = TInt) ''arithmetic needs Int operands''; Good TInt }
      | Lt \<Rightarrow> do { check (A = TInt \<and> B = TInt) ''comparison needs Int operands''; Good TBool }
      | Le \<Rightarrow> do { check (A = TInt \<and> B = TInt) ''comparison needs Int operands''; Good TBool }
      | Eq \<Rightarrow> do { check (A = B \<and> (A = TInt \<or> A = TBool)) ''equality needs two Ints or two Bools'';
                  Good TBool }
      | And \<Rightarrow> do { check (A = TBool \<and> B = TBool) ''logical operator needs Bool operands''; Good TBool }
      | Or \<Rightarrow> do { check (A = TBool \<and> B = TBool) ''logical operator needs Bool operands''; Good TBool }) }"
| "etype P \<Gamma> (ENot a) = do {
     A \<leftarrow> etype P \<Gamma> a;
     check (A = TBool) ''not needs a Bool'';
     Good TBool }"
| "etype P \<Gamma> (ELen p) = do {
     T \<leftarrow> ptype P \<Gamma> p;
     (case T of TList _ \<Rightarrow> Good TInt | _ \<Rightarrow> Bad ''len of a non-list'') }"
| "etype P \<Gamma> (EList es) = do {
     Ts \<leftarrow> etypes P \<Gamma> es;
     (case Ts of
        [] \<Rightarrow> Bad ''an empty list literal needs a declared type''
      | T # _ \<Rightarrow> do { check (list_all (\<lambda>U. U = T) Ts) ''list elements must have the same type'';
                     Good (TList T) }) }"
| "etypes P \<Gamma> [] = Good []"
| "etypes P \<Gamma> (e # es) = do { T \<leftarrow> etype P \<Gamma> e; Ts \<leftarrow> etypes P \<Gamma> es; Good (T # Ts) }"

text \<open>An initializing expression of declared type @{text "T"}; @{text "[]"} needs the declaration.\<close>

definition ty_init :: "prog \<Rightarrow> senv \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> unit ck" where
  "ty_init P \<Gamma> T e = (case e of
     EList [] \<Rightarrow> (case T of TList _ \<Rightarrow> Good () | _ \<Rightarrow> Bad ''type mismatch'')
   | _ \<Rightarrow> do { U \<leftarrow> etype P \<Gamma> e; check (U = T) ''type mismatch'' })"

section \<open>The ownership checker\<close>

subsection \<open>Static paths, origins and interiors\<close>

fun root_of :: "place \<Rightarrow> vname" where
  "root_of (PVar x) = x"
| "root_of (PField p _) = root_of p"
| "root_of (PIndex p _) = root_of p"

fun has_index :: "place \<Rightarrow> bool" where
  "has_index (PVar _) = False"
| "has_index (PField p _) = has_index p"
| "has_index (PIndex _ _) = True"

text \<open>
  The static path of a place: its field selections from the root, up to
  the first index. Everything below an index is unknown statically, so two
  places overlap if one static path is a prefix of the other.
\<close>

fun spath :: "place \<Rightarrow> fname list" where
  "spath (PVar _) = []"
| "spath (PField p f) = (if has_index p then spath p else spath p @ [f])"
| "spath (PIndex p _) = spath p"

definition is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_prefix xs ys \<longleftrightarrow> take (length xs) ys = xs"

text \<open>
  The origin of a place is the origin of its root: the root itself, unless
  the root is a reference binding, whose origin is recorded. Its interior
  is the set of variables into whose list items it may point.
\<close>

definition static_roots :: "senv \<Rightarrow> vname \<Rightarrow> vname set" where
  "static_roots \<Gamma> x = (case map_of \<Gamma> x of Some (KRef _ og _) \<Rightarrow> og | _ \<Rightarrow> {x})"

definition ref_interior :: "senv \<Rightarrow> vname \<Rightarrow> vname set" where
  "ref_interior \<Gamma> x = (case map_of \<Gamma> x of Some (KRef _ _ i) \<Rightarrow> i | _ \<Rightarrow> {})"

definition place_origin :: "senv \<Rightarrow> place \<Rightarrow> vname set" where
  "place_origin \<Gamma> p = static_roots \<Gamma> (root_of p)"

definition place_interior :: "senv \<Rightarrow> place \<Rightarrow> vname set" where
  "place_interior \<Gamma> p =
     (if has_index p then static_roots \<Gamma> (root_of p) else {}) \<union> ref_interior \<Gamma> (root_of p)"

definition overlap :: "senv \<Rightarrow> place \<Rightarrow> place \<Rightarrow> bool" where
  "overlap \<Gamma> p q =
     (if root_of p = root_of q then is_prefix (spath p) (spath q) \<or> is_prefix (spath q) (spath p)
      else place_origin \<Gamma> p \<inter> place_origin \<Gamma> q \<noteq> {})"

subsection \<open>Abstract states\<close>

record astate =
  a_init :: "vname set"     \<comment> \<open>owned variables that are definitely initialized\<close>
  a_inval :: "vname set"    \<comment> \<open>references that may have been invalidated\<close>
  a_fields :: "fname set"   \<comment> \<open>initialized fields of @{text "out self"}\<close>

definition join :: "astate \<Rightarrow> astate \<Rightarrow> astate" where
  "join \<sigma>1 \<sigma>2 = \<lparr>a_init = a_init \<sigma>1 \<inter> a_init \<sigma>2, a_inval = a_inval \<sigma>1 \<union> a_inval \<sigma>2,
                 a_fields = a_fields \<sigma>1 \<inter> a_fields \<sigma>2\<rparr>"

text \<open>@{text "None"} is the state after a @{text "return"}: no state reaches it.\<close>

fun join_opt :: "astate option \<Rightarrow> astate option \<Rightarrow> astate option" where
  "join_opt None s = s"
| "join_opt s None = s"
| "join_opt (Some a) (Some b) = Some (join a b)"

text \<open>
  The context of a body: the program, the return specification, and the
  fields that @{text "__init__"} must initialize (empty elsewhere).
\<close>

record ctx =
  c_prog :: prog
  c_ret :: ret
  c_fields :: "fname list"

subsection \<open>Elementary checks\<close>

text \<open>
  A place may be used if its root is usable: an owned root must be
  initialized; a reference must not be invalidated and its owned origin
  variables must be initialized; inside @{text "__init__"}, @{text "self"} may
  only be used once every field is initialized, and a field only once it
  is.
\<close>

definition root_ok :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> place \<Rightarrow> unit ck" where
  "root_ok C \<Gamma> \<sigma> p = (let x = root_of p in case map_of \<Gamma> x of
     None \<Rightarrow> Bad (''unbound variable '' @ x)
   | Some (KOwned _) \<Rightarrow> check (x \<in> a_init \<sigma>) (''use of moved or uninitialized value '' @ x)
   | Some (KBorrow c _) \<Rightarrow>
       if c = Out then (case spath p of
          [] \<Rightarrow> check (set (c_fields C) \<subseteq> a_fields \<sigma>)
                  ''use of self before all fields are initialized''
        | f # _ \<Rightarrow> check (f \<in> a_fields \<sigma>) (''use of uninitialized field '' @ f))
       else Good ()
   | Some (KRef _ og _) \<Rightarrow> do {
       check (x \<notin> a_inval \<sigma>) (''use of invalidated reference '' @ x);
       check (\<forall>y \<in> og. case map_of \<Gamma> y of Some (KOwned _) \<Rightarrow> y \<in> a_init \<sigma> | _ \<Rightarrow> True)
         (''reference '' @ x @ '' is used after a value it refers to was moved'') })"

text \<open>
  A place may be mutated unless its origin contains an immutable argument.
  For a reference this checks every variable it may point into, so a
  reference to an @{text "imm"} argument cannot be used to mutate it.
\<close>

fun imm_kind :: "vkind option \<Rightarrow> bool" where
  "imm_kind (Some (KBorrow c _)) = (c = Imm)"
| "imm_kind _ = False"

definition mut_ok :: "senv \<Rightarrow> place \<Rightarrow> unit ck" where
  "mut_ok \<Gamma> p = check
     (\<forall>y \<in> place_origin \<Gamma> p. \<not> imm_kind (map_of \<Gamma> y))
     ''cannot mutate through an immutable argument''"

definition refs_into :: "senv \<Rightarrow> vname set \<Rightarrow> vname set" where
  "refs_into \<Gamma> R = set [x. (x, k) \<leftarrow> \<Gamma>, case k of KRef _ _ i \<Rightarrow> i \<inter> R \<noteq> {} | _ \<Rightarrow> False]"

text \<open>
  Mutating a place of type @{text "T"} may change the shape of every list
  inside the value at the place. This invalidates the references into the
  items of those lists, so the checker marks as invalidated every reference
  whose interior meets the origin of the place. If @{text "T"} is trivial, the
  value contains no lists, and nothing is invalidated. This is the
  @{text "Shape"}/@{text "Item"} distinction of the region theory: assigning a
  trivial list item is an item mutation and preserves references to the
  other items.

  An earlier version also treated every assignment to a list item, such as
  @{text "l[i] = v"}, as an item mutation. That is unsound when the items
  themselves contain lists: in a @{text "List[List[Int]]"}, assigning
  @{text "l[0]"} replaces the inner list that a reference to @{text "l[0][1]"}
  points into. The soundness proof exposed this. The check is conservative
  because interiors do not record at which index a reference points into
  a list: assigning @{text "l[1]"} also invalidates a reference to
  @{text "l[0][0]"}.
\<close>

definition invalidate_place :: "senv \<Rightarrow> astate \<Rightarrow> place \<Rightarrow> ty \<Rightarrow> astate" where
  "invalidate_place \<Gamma> \<sigma> p T =
     (if trivial_ty T then \<sigma>
      else \<sigma>\<lparr>a_inval := a_inval \<sigma> \<union> refs_into \<Gamma> (place_origin \<Gamma> p)\<rparr>)"

text \<open>
  The conventions under which an argument is borrowed mutably: @{text "mut"},
  and also @{text "ref"} and @{text "out"}, through which the callee may
  write too.
\<close>

definition borrows_mut :: "conv \<Rightarrow> bool" where
  "borrows_mut c \<longleftrightarrow> c = conv.Mut \<or> c = Ref \<or> c = Out"

text \<open>
  Argument exclusivity: no mutably borrowed argument may overlap another
  borrowed argument. Trivial values passed @{text "imm"} are copies and are
  not borrowed. (An earlier version only checked @{text "mut"} arguments,
  which let a @{text "ref"} argument alias an @{text "imm"} one.)
\<close>

definition exclusive :: "senv \<Rightarrow> (place \<times> conv) list \<Rightarrow> unit ck" where
  "exclusive \<Gamma> bs = check
     (list_all id [\<not> (borrows_mut (snd (bs ! i)) \<or> borrows_mut (snd (bs ! j)))
                   \<or> \<not> overlap \<Gamma> (fst (bs ! i)) (fst (bs ! j)).
                   i \<leftarrow> [0..<length bs], j \<leftarrow> [0..<length bs], i < j])
     ''argument exclusivity: a mut argument aliases another argument''"

subsection \<open>Places in flight\<close>

text \<open>
  A borrowed argument, a method receiver and the list in @{text "l[e]"} are
  evaluated to a location before the remaining arguments (or the index)
  are evaluated, and the location is used afterwards. Mojo keeps such a
  borrow live while the other arguments are evaluated, so evaluating them
  may not move or mutate the borrowed value. An earlier version of the
  checker did not check this, and accepted programs such as
  @{text "g(l[0], f(l))"}, where @{text "f(mut l)"} appends to @{text "l"}, or
  @{text "g(l, l^)"}, which fail at run time. The soundness proof for calls
  exposed this.

  @{text "mroots P \<Gamma> e"} over-approximates the variables whose values
  evaluating @{text "e"} may move or mutate: the variables transferred with
  @{text "^"}, and the origins of the places passed to @{text "mut"},
  @{text "ref"} and @{text "out"} parameters and of mutated method receivers.
  For a call, @{text "eargs"} is the part due to evaluating the arguments
  (before the call itself), and @{text "bargs"} consists of the origins of
  the places the call borrows mutably.
\<close>

definition bargs :: "senv \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> vname set" where
  "bargs \<Gamma> ps es = \<Union> (set [place_origin \<Gamma> p. ((c, _, _), EPlace p) \<leftarrow> zip ps es, borrows_mut c])"

fun mroots_p :: "prog \<Rightarrow> senv \<Rightarrow> place \<Rightarrow> vname set"
and mroots :: "prog \<Rightarrow> senv \<Rightarrow> expr \<Rightarrow> vname set"
and mroots_l :: "prog \<Rightarrow> senv \<Rightarrow> expr list \<Rightarrow> vname set"
and eargs :: "prog \<Rightarrow> senv \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> vname set"
where
  "mroots_p P \<Gamma> (PVar x) = {}"
| "mroots_p P \<Gamma> (PField p f) = mroots_p P \<Gamma> p"
| "mroots_p P \<Gamma> (PIndex p e) = mroots_p P \<Gamma> p \<union> mroots P \<Gamma> e"
| "mroots P \<Gamma> (EPlace p) = mroots_p P \<Gamma> p"
| "mroots P \<Gamma> (ETake p) = insert (root_of p) (mroots_p P \<Gamma> p)"
| "mroots P \<Gamma> (ECopy p) = mroots_p P \<Gamma> p"
| "mroots P \<Gamma> (ECall f es) = (case call_params P f of
     Good ps \<Rightarrow> eargs P \<Gamma> ps es \<union> bargs \<Gamma> ps es
   | Bad _ \<Rightarrow> {})"
| "mroots P \<Gamma> (EMeth p m es) = mroots_p P \<Gamma> p \<union> (case ptype P \<Gamma> p of
     Good (TList _) \<Rightarrow> place_origin \<Gamma> p \<union> mroots_l P \<Gamma> es
   | Good (TStruct S) \<Rightarrow> (case meth_decl P S m of
       Good fd \<Rightarrow> (case fd_params fd of
         (c, _, _) # ps \<Rightarrow>
           (if borrows_mut c then place_origin \<Gamma> p else {}) \<union> eargs P \<Gamma> ps es \<union> bargs \<Gamma> ps es
       | [] \<Rightarrow> {})
     | Bad _ \<Rightarrow> {})
   | _ \<Rightarrow> {})"
| "mroots P \<Gamma> (EBin _ a b) = mroots P \<Gamma> a \<union> mroots P \<Gamma> b"
| "mroots P \<Gamma> (ENot a) = mroots P \<Gamma> a"
| "mroots P \<Gamma> (ELen p) = mroots_p P \<Gamma> p"
| "mroots P \<Gamma> (EList es) = mroots_l P \<Gamma> es"
| "mroots P \<Gamma> (EInt _) = {}"
| "mroots P \<Gamma> (EBool _) = {}"
| "mroots P \<Gamma> (EStr _) = {}"
| "mroots_l P \<Gamma> [] = {}"
| "mroots_l P \<Gamma> (e # es) = mroots P \<Gamma> e \<union> mroots_l P \<Gamma> es"
| "eargs P \<Gamma> ((c, x, T) # ps) (e # es) =
     (if c = Var \<or> c = Deinit then mroots P \<Gamma> e
      else (case e of EPlace p \<Rightarrow> mroots_p P \<Gamma> p | _ \<Rightarrow> mroots P \<Gamma> e)) \<union> eargs P \<Gamma> ps es"
| "eargs P \<Gamma> [] _ = {}"
| "eargs P \<Gamma> (_ # _) [] = {}"

text \<open>
  A call of a function returning a reference, used as a value, copies the
  value it refers to implicitly. An earlier version of the checker allowed
  this for any type, and the run-time copy then failed with
  @{text "ErrNotCopyable"}.
\<close>

definition val_call :: "prog \<Rightarrow> name \<Rightarrow> bool" where
  "val_call P f = (case find_struct P f of
     Some _ \<Rightarrow> True
   | None \<Rightarrow> (case find_fun P f of
       Some fd \<Rightarrow> (case fd_ret fd of RRef _ T \<Rightarrow> trivial_ty T | _ \<Rightarrow> True)
     | None \<Rightarrow> True))"

subsection \<open>Expressions\<close>

text \<open>
  @{text "chk_idx"} checks the index expressions of a place, @{text "chk_expr"}
  an expression evaluated to an owned value, and @{text "chk_args"} the
  arguments of a call, returning the borrowed places for the exclusivity
  check. Expressions evaluate left to right, and the abstract state is
  threaded accordingly.
\<close>

fun chk_idx :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> place \<Rightarrow> astate ck"
and chk_expr :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> expr \<Rightarrow> astate ck"
and chk_exprs :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> expr list \<Rightarrow> astate ck"
and chk_args :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow>
                 (astate \<times> (place \<times> conv) list) ck"
where
  "chk_idx C \<Gamma> \<sigma> (PVar x) = Good \<sigma>"
| "chk_idx C \<Gamma> \<sigma> (PField p f) = chk_idx C \<Gamma> \<sigma> p"
| "chk_idx C \<Gamma> \<sigma> (PIndex p e) = do {
     \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
     check (place_origin \<Gamma> p \<inter> mroots (c_prog C) \<Gamma> e = {})
       ''an index may not move or mutate the indexed value'';
     chk_expr C \<Gamma> \<sigma> e }"
| "chk_expr C \<Gamma> \<sigma> (EInt _) = Good \<sigma>"
| "chk_expr C \<Gamma> \<sigma> (EBool _) = Good \<sigma>"
| "chk_expr C \<Gamma> \<sigma> (EStr _) = Good \<sigma>"
| "chk_expr C \<Gamma> \<sigma> (EPlace p) = do {
     \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
     root_ok C \<Gamma> \<sigma> p;
     T \<leftarrow> ptype (c_prog C) \<Gamma> p;
     check (trivial_ty T) ''implicit copy of a non-trivial value: use ^ or copy()'';
     Good \<sigma> }"
| "chk_expr C \<Gamma> \<sigma> (ETake p) = (case p of
     PVar x \<Rightarrow> (case map_of \<Gamma> x of
        Some (KOwned _) \<Rightarrow> do {
          check (x \<in> a_init \<sigma>) (''transfer of moved or uninitialized value '' @ x);
          Good (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) }
      | _ \<Rightarrow> Bad (''only owned local variables can be transferred: '' @ x))
   | _ \<Rightarrow> Bad ''cannot transfer out of a field or list element'')"
| "chk_expr C \<Gamma> \<sigma> (ECopy p) = do {
     \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
     root_ok C \<Gamma> \<sigma> p;
     T \<leftarrow> ptype (c_prog C) \<Gamma> p;
     (case T of
        TStruct S \<Rightarrow> (case find_struct (c_prog C) S of
           Some sd \<Rightarrow> check (sd_copyable sd) (S @ '' is not Copyable'')
         | None \<Rightarrow> Bad (''unknown struct '' @ S))
      | _ \<Rightarrow> Good ());
     Good \<sigma> }"
| "chk_expr C \<Gamma> \<sigma> (ECall f es) = do {
     check (val_call (c_prog C) f)
       ''a reference returned by a call is used as a value, which needs a trivial type'';
     ps \<leftarrow> call_params (c_prog C) f;
     (\<sigma>, bs) \<leftarrow> chk_args C \<Gamma> \<sigma> ps es;
     exclusive \<Gamma> bs;
     Good \<sigma> }"
| "chk_expr C \<Gamma> \<sigma> (EMeth p m es) = do {
     \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
     root_ok C \<Gamma> \<sigma> p;
     T \<leftarrow> ptype (c_prog C) \<Gamma> p;
     (case T of
        TList _ \<Rightarrow> do {
          mut_ok \<Gamma> p;
          check (place_origin \<Gamma> p \<inter> mroots_l (c_prog C) \<Gamma> es = {})
            ''the arguments of a method call may not move or mutate its receiver'';
          \<sigma> \<leftarrow> chk_exprs C \<Gamma> \<sigma> es;
          Good (invalidate_place \<Gamma> \<sigma> p T) }
      | TStruct S \<Rightarrow> do {
          fd \<leftarrow> meth_decl (c_prog C) S m;
          (case fd_params fd of
             (c, _, _) # ps \<Rightarrow> do {
               (if borrows_mut c then mut_ok \<Gamma> p else Good ());
               check (place_origin \<Gamma> p \<inter> eargs (c_prog C) \<Gamma> ps es = {})
                 ''the arguments of a method call may not move or mutate its receiver'';
               check (case fd_ret fd of RRef _ U \<Rightarrow> trivial_ty U | _ \<Rightarrow> True)
                 ''a reference returned by a method is used as a value, which needs a trivial type'';
               (\<sigma>, bs) \<leftarrow> chk_args C \<Gamma> \<sigma> ps es;
               exclusive \<Gamma> ((p, c) # bs);
               Good (if borrows_mut c then invalidate_place \<Gamma> \<sigma> p T else \<sigma>) }
           | [] \<Rightarrow> Bad ''method without self'') }
      | _ \<Rightarrow> Bad ''method call on a value that is neither a struct nor a list'') }"
| "chk_expr C \<Gamma> \<sigma> (EBin _ a b) = do { \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> a; chk_expr C \<Gamma> \<sigma> b }"
| "chk_expr C \<Gamma> \<sigma> (ENot a) = chk_expr C \<Gamma> \<sigma> a"
| "chk_expr C \<Gamma> \<sigma> (ELen p) = do { \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p; root_ok C \<Gamma> \<sigma> p; Good \<sigma> }"
| "chk_expr C \<Gamma> \<sigma> (EList es) = chk_exprs C \<Gamma> \<sigma> es"
| "chk_exprs C \<Gamma> \<sigma> [] = Good \<sigma>"
| "chk_exprs C \<Gamma> \<sigma> (e # es) = do { \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e; chk_exprs C \<Gamma> \<sigma> es }"
| "chk_args C \<Gamma> \<sigma> [] [] = Good (\<sigma>, [])"
| "chk_args C \<Gamma> \<sigma> ((c, x, T) # ps) (e # es) = do {
     (\<sigma>, bs1) \<leftarrow>
       (if c = Var \<or> c = Deinit then do { \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e; Good (\<sigma>, []) }
        else (case e of
          EPlace p \<Rightarrow> do {
            \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
            root_ok C \<Gamma> \<sigma> p;
            U \<leftarrow> ptype (c_prog C) \<Gamma> p;
            if c = Imm \<and> trivial_ty U then Good (\<sigma>, [])
            else do {
              check (place_origin \<Gamma> p \<inter> eargs (c_prog C) \<Gamma> ps es = {})
                ''a later argument may not move or mutate a borrowed argument'';
              if borrows_mut c then do { mut_ok \<Gamma> p; Good (invalidate_place \<Gamma> \<sigma> p U, [(p, c)]) }
              else Good (\<sigma>, [(p, c)]) } }
        | _ \<Rightarrow>
            if c = Imm then do { \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e; Good (\<sigma>, []) }
            else Bad (''the argument for mut/ref parameter '' @ x @ '' must be a place'')));
     (\<sigma>, bs2) \<leftarrow> chk_args C \<Gamma> \<sigma> ps es;
     Good (\<sigma>, bs1 @ bs2) }"
| "chk_args C \<Gamma> \<sigma> _ _ = Bad ''wrong number of arguments''"

text \<open>
  The arguments of a call, checked as by @{text "chk_expr"} but without
  using the result as a value (for @{text "ref"} bindings).
\<close>

definition chk_call :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> name \<Rightarrow> expr list \<Rightarrow> astate ck" where
  "chk_call C \<Gamma> \<sigma> f es = do {
     ps \<leftarrow> call_params (c_prog C) f;
     (\<sigma>, bs) \<leftarrow> chk_args C \<Gamma> \<sigma> ps es;
     exclusive \<Gamma> bs;
     Good \<sigma> }"

lemma chk_expr_ECall:
  "chk_expr C \<Gamma> \<sigma> (ECall f es) = do {
     check (val_call (c_prog C) f)
       ''a reference returned by a call is used as a value, which needs a trivial type'';
     chk_call C \<Gamma> \<sigma> f es }"
  by (simp add: chk_call_def)

subsection \<open>Statements\<close>

text \<open>
  The arguments of a reference-returning call that end up in the origin of
  the result: those passed to the parameters named in @{text "ref[...]"}.
\<close>

text \<open>
  Assigning to a place of type @{text "T"}, after the right-hand side has been
  checked: assigning a whole owned variable (re)initializes it, assigning a
  field of @{text "out self"} initializes that field, and any other place
  must be usable and mutable. In all cases the references into the
  interior of the place are invalidated, unless @{text "T"} is trivial.
\<close>

definition chk_assign :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> place \<Rightarrow> ty \<Rightarrow> astate ck" where
  "chk_assign C \<Gamma> \<sigma> p T = (case (p, map_of \<Gamma> (root_of p)) of
     (PVar x, Some (KOwned _)) \<Rightarrow>
       Good (invalidate_place \<Gamma> (\<sigma>\<lparr>a_init := insert x (a_init \<sigma>)\<rparr>) p T)
   | (PField (PVar _) f, Some (KBorrow Out _)) \<Rightarrow>
       Good (invalidate_place \<Gamma> (\<sigma>\<lparr>a_fields := insert f (a_fields \<sigma>)\<rparr>) p T)
   | _ \<Rightarrow> do {
       \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
       root_ok C \<Gamma> \<sigma> p;
       mut_ok \<Gamma> p;
       Good (invalidate_place \<Gamma> \<sigma> p T) })"

definition ref_args :: "(conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> vname list \<Rightarrow> place list" where
  "ref_args ps es ns = [p. ((_, x, _), EPlace p) \<leftarrow> zip ps es, x \<in> set ns]"

text \<open>
  @{text "chk_stmt"} returns the extended static environment and the abstract
  state after the statement (@{text "None"} after a @{text "return"}). Blocks
  of @{text "if"} and @{text "while"} discard their declarations. The states of
  the two branches of an @{text "if"} are joined. A @{text "while"} loop is
  analysed by iterating the body from the join of the entry state and the
  state after the body until it is stable (@{text "chk_loop"}). This always
  converges because joining only shrinks the initialized and field sets and
  only grows the invalidated set; @{text "chk_loop"}'s bound covers every
  possible step.
\<close>

function (sequential) chk_stmt :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> stmt \<Rightarrow> (senv \<times> astate option) ck"
and chk_loop :: "nat \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> expr \<Rightarrow> stmt \<Rightarrow> astate option ck"
where
  "chk_stmt C \<Gamma> \<sigma> SPass = Good (\<Gamma>, Some \<sigma>)"
| "chk_stmt C \<Gamma> \<sigma> (SSeq a b) = do {
     (\<Gamma>, o\<sigma>) \<leftarrow> chk_stmt C \<Gamma> \<sigma> a;
     (case o\<sigma> of None \<Rightarrow> Good (\<Gamma>, None) | Some \<sigma> \<Rightarrow> chk_stmt C \<Gamma> \<sigma> b) }"
| "chk_stmt C \<Gamma> \<sigma> (SVar x T eo) = do {
     check (x \<notin> fst ` set \<Gamma>) (''variable declared twice: '' @ x);
     (case eo of
        None \<Rightarrow> Good ((x, KOwned T) # \<Gamma>, Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>))
      | Some e \<Rightarrow> do {
          ty_init (c_prog C) \<Gamma> T e;
          \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e;
          Good ((x, KOwned T) # \<Gamma>, Some (\<sigma>\<lparr>a_init := insert x (a_init \<sigma>)\<rparr>)) }) }"
| "chk_stmt C \<Gamma> \<sigma> (SRef x e) = do {
     check (x \<notin> fst ` set \<Gamma>) (''variable declared twice: '' @ x);
     (case e of
        EPlace p \<Rightarrow> do {
          \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
          root_ok C \<Gamma> \<sigma> p;
          T \<leftarrow> ptype (c_prog C) \<Gamma> p;
          Good ((x, KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)) # \<Gamma>, Some \<sigma>) }
      | ECall f es \<Rightarrow> (case find_fun (c_prog C) f of
          Some fd \<Rightarrow> (case fd_ret fd of
             RRef ns T \<Rightarrow> do {
               _ \<leftarrow> etype (c_prog C) \<Gamma> e;
               \<sigma> \<leftarrow> chk_call C \<Gamma> \<sigma> f es;
               Good ((x, KRef T (\<Union>p \<in> set (ref_args (fd_params fd) es ns). place_origin \<Gamma> p)
                                (\<Union>p \<in> set (ref_args (fd_params fd) es ns). place_origin \<Gamma> p))
                       # \<Gamma>, Some \<sigma>) }
           | _ \<Rightarrow> Bad (''a ref binding needs a reference, but '' @ f @ '' returns a value''))
        | None \<Rightarrow> Bad (''unknown function '' @ f))
      | _ \<Rightarrow> Bad ''a ref binding needs a place or a reference-returning call'') }"
| "chk_stmt C \<Gamma> \<sigma> (SAssign p e) = do {
     T \<leftarrow> ptype (c_prog C) \<Gamma> p;
     ty_init (c_prog C) \<Gamma> T e;
     \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e;
     \<sigma> \<leftarrow> chk_assign C \<Gamma> \<sigma> p T;
     Good (\<Gamma>, Some \<sigma>) }"
| "chk_stmt C \<Gamma> \<sigma> (SExpr e) = do {
     _ \<leftarrow> etype (c_prog C) \<Gamma> e;
     \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> e;
     Good (\<Gamma>, Some \<sigma>) }"
| "chk_stmt C \<Gamma> \<sigma> (SPrint es) = do {
     Ts \<leftarrow> etypes (c_prog C) \<Gamma> es;
     check (list_all trivial_ty Ts) ''print only takes Int, Bool and String values'';
     \<sigma> \<leftarrow> chk_exprs C \<Gamma> \<sigma> es;
     Good (\<Gamma>, Some \<sigma>) }"
| "chk_stmt C \<Gamma> \<sigma> (SIf c a b) = do {
     T \<leftarrow> etype (c_prog C) \<Gamma> c;
     check (T = TBool) ''an if condition must be a Bool'';
     \<sigma> \<leftarrow> chk_expr C \<Gamma> \<sigma> c;
     (_, o1) \<leftarrow> chk_stmt C \<Gamma> \<sigma> a;
     (_, o2) \<leftarrow> chk_stmt C \<Gamma> \<sigma> b;
     Good (\<Gamma>, join_opt o1 o2) }"
| "chk_stmt C \<Gamma> \<sigma> (SWhile c b) = do {
     T \<leftarrow> etype (c_prog C) \<Gamma> c;
     check (T = TBool) ''a while condition must be a Bool'';
     o\<sigma> \<leftarrow> chk_loop (Suc (Suc (length \<Gamma> + size b + length (c_fields C)))) C \<Gamma> \<sigma> c b;
     Good (\<Gamma>, o\<sigma>) }"
| "chk_stmt C \<Gamma> \<sigma> (SReturn None) = do {
     check (c_ret C = RNone) ''missing return value'';
     check (set (c_fields C) \<subseteq> a_fields \<sigma>) ''return before every field of self is initialized'';
     Good (\<Gamma>, None) }"
| "chk_stmt C \<Gamma> \<sigma> (SReturn (Some e)) = (case c_ret C of
     RNone \<Rightarrow> Bad ''return with a value from a function without a result''
   | RVal T \<Rightarrow> do {
       ty_init (c_prog C) \<Gamma> T e;
       _ \<leftarrow> chk_expr C \<Gamma> \<sigma> e;
       Good (\<Gamma>, None) }
   | RRef ns T \<Rightarrow> (case e of
       EPlace p \<Rightarrow> do {
         \<sigma> \<leftarrow> chk_idx C \<Gamma> \<sigma> p;
         root_ok C \<Gamma> \<sigma> p;
         U \<leftarrow> ptype (c_prog C) \<Gamma> p;
         check (U = T) ''type mismatch in returned reference'';
         check (place_origin \<Gamma> p \<subseteq> set ns)
           ''the returned reference may point outside its declared origin, e.g. to a local'';
         Good (\<Gamma>, None) }
     | _ \<Rightarrow> Bad ''a reference-returning function must return a place''))"
| "chk_stmt C \<Gamma> \<sigma> (SDrop p) = (case (p, map_of \<Gamma> (root_of p)) of
     (PVar x, Some (KOwned _)) \<Rightarrow> Good (\<Gamma>, Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>))
   | _ \<Rightarrow> Bad ''only owned local variables can be dropped'')"
| "chk_loop 0 C \<Gamma> \<sigma> c b = Bad ''loop analysis did not converge''"
| "chk_loop (Suc k) C \<Gamma> \<sigma> c b = do {
     \<sigma>c \<leftarrow> chk_expr C \<Gamma> \<sigma> c;
     (_, ob) \<leftarrow> chk_stmt C \<Gamma> \<sigma>c b;
     (case join_opt (Some \<sigma>) ob of
        Some \<sigma>' \<Rightarrow> if \<sigma>' = \<sigma> then Good (Some \<sigma>c) else chk_loop k C \<Gamma> \<sigma>' c b
      | None \<Rightarrow> Good None) }"
  by pat_completeness auto

text \<open>
  Termination: lexicographically by the size of the statement being
  checked, and then by the iteration bound of @{text "chk_loop"} (which
  checks its body, a statement of the same size, before iterating).
\<close>

termination
  by (relation "measures [case_sum (\<lambda>(C, \<Gamma>, \<sigma>, s). size s) (\<lambda>(k, C, \<Gamma>, \<sigma>, c, b). size b),
                          case_sum (\<lambda>_. 0) (\<lambda>(k, _). Suc k)]") auto

subsection \<open>Functions and programs\<close>

fun decl_names :: "stmt \<Rightarrow> vname list" where
  "decl_names (SVar x _ _) = [x]"
| "decl_names (SRef x _) = [x]"
| "decl_names (SSeq a b) = decl_names a @ decl_names b"
| "decl_names (SIf _ a b) = decl_names a @ decl_names b"
| "decl_names (SWhile _ b) = decl_names b"
| "decl_names _ = []"

definition param_kind :: "conv \<times> vname \<times> ty \<Rightarrow> vname \<times> vkind" where
  "param_kind = (\<lambda>(c, x, T). (x, if c = Var then KOwned T else KBorrow c T))"

text \<open>
  A body is checked with its parameters in scope: @{text "var"} parameters
  are owned and initialized, all others borrowed. A body may only fall off
  its end if it returns nothing, and @{text "__init__"} must initialize every
  field.
\<close>

definition chk_body :: "prog \<Rightarrow> ret \<Rightarrow> fname list \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> stmt \<Rightarrow> unit ck" where
  "chk_body P rt flds ps body = do {
     check (distinct (map (fst \<circ> snd) ps @ decl_names body))
       ''variable names must be distinct within a function'';
     check (length (filter (\<lambda>(c, _, _). c = Out) ps) \<le> 1) ''at most one out parameter'';
     check (case rt of
              RRef ns _ \<Rightarrow> list_all (\<lambda>x. list_ex (\<lambda>(c, y, _). y = x \<and> (c = conv.Mut \<or> c = Ref)) ps) ns
            | _ \<Rightarrow> True)
       ''the origin of a returned reference must consist of mut or ref parameters'';
     (_, o\<sigma>) \<leftarrow> chk_stmt \<lparr>c_prog = P, c_ret = rt, c_fields = flds\<rparr> (rev (map param_kind ps))
                 \<lparr>a_init = set [x. (c, x, _) \<leftarrow> ps, c = Var], a_inval = {}, a_fields = {}\<rparr> body;
     (case o\<sigma> of
        None \<Rightarrow> Good ()
      | Some \<sigma> \<Rightarrow> do {
          check (rt = RNone) ''missing return'';
          check (set flds \<subseteq> a_fields \<sigma>) ''__init__ does not initialize every field'' }) }"

definition report :: "string \<Rightarrow> unit ck \<Rightarrow> string list" where
  "report loc r = (case r of Good _ \<Rightarrow> [] | Bad msg \<Rightarrow> [loc @ '': '' @ msg])"

definition chk_fun :: "prog \<Rightarrow> string \<Rightarrow> fundecl \<Rightarrow> string list" where
  "chk_fun P prefix fd =
     report (prefix @ fd_name fd) (chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd))"

definition chk_struct :: "prog \<Rightarrow> structdecl \<Rightarrow> string list" where
  "chk_struct P sd =
     report (sd_name sd) (do {
       check (distinct (map fst (sd_fields sd))) ''duplicate field names'';
       check (case sd_init sd of
                None \<Rightarrow> True
              | Some fd \<Rightarrow> fd_ret fd = RNone \<and>
                  (case fd_params fd of (Out, _, T) # _ \<Rightarrow> T = TStruct (sd_name sd) | _ \<Rightarrow> False))
         ''__init__ must take out self first and return nothing'';
       check (list_all (\<lambda>fd. case fd_params fd of
                (c, _, T) # _ \<Rightarrow> (c = Imm \<or> c = conv.Mut \<or> c = Ref) \<and> T = TStruct (sd_name sd)
              | [] \<Rightarrow> False) (sd_methods sd))
         ''a method must take self first, as an imm, mut or ref parameter'' })
     @ (case sd_init sd of
        None \<Rightarrow> []
      | Some fd \<Rightarrow> report (sd_name sd @ ''.__init__'')
                    (chk_body P RNone (map fst (sd_fields sd)) (fd_params fd) (fd_body fd)))
     @ (case sd_deinit sd of
          None \<Rightarrow> []
        | Some body \<Rightarrow> report (sd_name sd @ ''.__deinit__'')
                        (chk_body P RNone [] [(Deinit, ''self'', TStruct (sd_name sd))] body))
     @ concat (map (chk_fun P (sd_name sd @ ''.'')) (sd_methods sd))"

definition check_prog :: "prog \<Rightarrow> string list" where
  "check_prog P =
     (if list_ex (\<lambda>fd. list_ex (\<lambda>sd. sd_name sd = fd_name fd) (p_structs P)) (p_funs P)
      then [''a function has the name of a struct''] else [])
     @ (case find_fun P ''main'' of
          None \<Rightarrow> [''no main function'']
        | Some fd \<Rightarrow> if fd_params fd = [] then [] else [''main takes no parameters''])
     @ concat (map (chk_struct P) (p_structs P)) @ concat (map (chk_fun P '''') (p_funs P))"

section \<open>ASAP elaboration\<close>

subsection \<open>Variables, moves and origins\<close>

fun pvars :: "place \<Rightarrow> vname set"
and evars :: "expr \<Rightarrow> vname set"
and evars_list :: "expr list \<Rightarrow> vname set"
where
  "pvars (PVar x) = {x}"
| "pvars (PField p _) = pvars p"
| "pvars (PIndex p e) = pvars p \<union> evars e"
| "evars (EInt _) = {}"
| "evars (EBool _) = {}"
| "evars (EStr _) = {}"
| "evars (EPlace p) = pvars p"
| "evars (ETake p) = pvars p"
| "evars (ECopy p) = pvars p"
| "evars (ECall _ es) = evars_list es"
| "evars (EMeth p _ es) = pvars p \<union> evars_list es"
| "evars (EBin _ a b) = evars a \<union> evars b"
| "evars (ENot a) = evars a"
| "evars (ELen p) = pvars p"
| "evars (EList es) = evars_list es"
| "evars_list [] = {}"
| "evars_list (e # es) = evars e \<union> evars_list es"

text \<open>The variables transferred out of by @{text "x^"}.\<close>

fun pmoves :: "place \<Rightarrow> vname set"
and emoves :: "expr \<Rightarrow> vname set"
and emoves_list :: "expr list \<Rightarrow> vname set"
where
  "pmoves (PVar _) = {}"
| "pmoves (PField p _) = pmoves p"
| "pmoves (PIndex p e) = pmoves p \<union> emoves e"
| "emoves (ETake (PVar x)) = {x}"
| "emoves (ETake p) = pmoves p"
| "emoves (EPlace p) = pmoves p"
| "emoves (ECopy p) = pmoves p"
| "emoves (ECall _ es) = emoves_list es"
| "emoves (EMeth p _ es) = pmoves p \<union> emoves_list es"
| "emoves (EBin _ a b) = emoves a \<union> emoves b"
| "emoves (ENot a) = emoves a"
| "emoves (ELen p) = pmoves p"
| "emoves (EList es) = emoves_list es"
| "emoves _ = {}"
| "emoves_list [] = {}"
| "emoves_list (e # es) = emoves e \<union> emoves_list es"

text \<open>
  The origins of reference bindings, computed by one forward pass over a
  body (names are distinct, so a single map suffices). A reference to a
  place has the origin of the place's root; a reference returned by a call
  has the origins of the arguments passed to the parameters named in its
  @{text "ref[...]"}.
\<close>

type_synonym omap = "(vname \<times> vname set) list"

definition root_closure :: "omap \<Rightarrow> vname \<Rightarrow> vname set" where
  "root_closure M x = (case map_of M x of Some og \<Rightarrow> og | None \<Rightarrow> {x})"

definition ref_origin :: "prog \<Rightarrow> omap \<Rightarrow> expr \<Rightarrow> vname set" where
  "ref_origin P M e = (case e of
     EPlace p \<Rightarrow> root_closure M (root_of p)
   | ECall f es \<Rightarrow> (case find_fun P f of
       Some fd \<Rightarrow> (case fd_ret fd of
          RRef ns _ \<Rightarrow> \<Union>p \<in> set (ref_args (fd_params fd) es ns). root_closure M (root_of p)
        | _ \<Rightarrow> {})
     | None \<Rightarrow> {})
   | _ \<Rightarrow> {})"

fun refs_of :: "prog \<Rightarrow> omap \<Rightarrow> stmt \<Rightarrow> omap" where
  "refs_of P M (SRef x e) = (x, ref_origin P M e) # M"
| "refs_of P M (SSeq a b) = refs_of P (refs_of P M a) b"
| "refs_of P M (SIf _ a b) = refs_of P (refs_of P M a) b"
| "refs_of P M (SWhile _ b) = refs_of P M b"
| "refs_of P M _ = M"

text \<open>
  Lifetime extension: using a reference uses every variable in its origin.
\<close>

definition expand :: "omap \<Rightarrow> vname set \<Rightarrow> vname set" where
  "expand M S = S \<union> \<Union> (set [og. (r, og) \<leftarrow> M, r \<in> S])"

subsection \<open>Liveness\<close>

text \<open>
  Uses, definitions and moves of the simple (non-compound) statements.
  Assigning a whole variable defines it; its old value is destroyed by the
  assignment itself, so no @{text "DROP"} is needed for it.
\<close>

fun leaf_uses :: "stmt \<Rightarrow> vname set" where
  "leaf_uses (SVar _ _ eo) = (case eo of None \<Rightarrow> {} | Some e \<Rightarrow> evars e)"
| "leaf_uses (SRef _ e) = evars e"
| "leaf_uses (SAssign p e) = evars e \<union> (case p of PVar _ \<Rightarrow> {} | _ \<Rightarrow> pvars p)"
| "leaf_uses (SExpr e) = evars e"
| "leaf_uses (SPrint es) = evars_list es"
| "leaf_uses (SReturn eo) = (case eo of None \<Rightarrow> {} | Some e \<Rightarrow> evars e)"
| "leaf_uses (SDrop p) = pvars p"
| "leaf_uses _ = {}"

fun leaf_defs :: "stmt \<Rightarrow> vname set" where
  "leaf_defs (SVar x _ _) = {x}"
| "leaf_defs (SRef x _) = {x}"
| "leaf_defs (SAssign (PVar x) _) = {x}"
| "leaf_defs _ = {}"

fun leaf_moves :: "stmt \<Rightarrow> vname set" where
  "leaf_moves (SVar _ _ eo) = (case eo of None \<Rightarrow> {} | Some e \<Rightarrow> emoves e)"
| "leaf_moves (SRef _ e) = emoves e"
| "leaf_moves (SAssign _ e) = emoves e"
| "leaf_moves (SExpr e) = emoves e"
| "leaf_moves (SPrint es) = emoves_list es"
| "leaf_moves (SReturn eo) = (case eo of None \<Rightarrow> {} | Some e \<Rightarrow> emoves e)"
| "leaf_moves _ = {}"

fun stmt_vars :: "stmt \<Rightarrow> vname set" where
  "stmt_vars (SSeq a b) = stmt_vars a \<union> stmt_vars b"
| "stmt_vars (SIf c a b) = evars c \<union> stmt_vars a \<union> stmt_vars b"
| "stmt_vars (SWhile c b) = evars c \<union> stmt_vars b"
| "stmt_vars s = leaf_uses s \<union> leaf_defs s"

text \<open>
  @{text "live M s L"}: the variables live before @{text "s"}, given those
  live after it. For a loop we compute the least fixpoint by iteration; the
  bound is the number of variables that can possibly become live.
\<close>

function (sequential) live :: "omap \<Rightarrow> stmt \<Rightarrow> vname set \<Rightarrow> vname set"
and loop_live :: "nat \<Rightarrow> omap \<Rightarrow> expr \<Rightarrow> stmt \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> vname set"
where
  "live M (SSeq a b) L = live M a (live M b L)"
| "live M (SIf c a b) L = expand M (evars c) \<union> live M a L \<union> live M b L"
| "live M (SWhile c b) L =
     loop_live (Suc (card (stmt_vars b \<union> evars c \<union> L \<union> \<Union> (set (map snd M))))) M c b L
       (expand M (evars c) \<union> L)"
| "live M (SReturn eo) L = expand M (leaf_uses (SReturn eo))"
| "live M s L = (L - leaf_defs s) \<union> expand M (leaf_uses s)"
| "loop_live 0 M c b L X = X"
| "loop_live (Suc k) M c b L X =
     (let X' = expand M (evars c) \<union> L \<union> live M b X in
      if X' \<subseteq> X then X else loop_live k M c b L (X \<union> X'))"
  by pat_completeness auto

termination
  by (relation "measures [case_sum (\<lambda>(M, s, L). size s) (\<lambda>(k, M, c, b, L, X). size b),
                          case_sum (\<lambda>_. 0) (\<lambda>(k, _). Suc k)]") auto

subsection \<open>Inserting drops\<close>

fun seq :: "stmt list \<Rightarrow> stmt" where
  "seq [] = SPass"
| "seq [s] = s"
| "seq (s # ss) = SSeq s (seq ss)"

text \<open>
  @{text "drops Os D"} drops the owned variables in @{text "D"}, in the order
  given by @{text "Os"} (reverse declaration order).
\<close>

definition drops :: "vname list \<Rightarrow> vname set \<Rightarrow> stmt list" where
  "drops Os D = map (\<lambda>x. SDrop (PVar x)) (filter (\<lambda>x. x \<in> D) Os)"

text \<open>
  @{text "elab M Os s L"} elaborates @{text "s"}, followed by a context in
  which @{text "L"} is live, into a flat list of statements:
    \<^item> after a simple statement, drop the owned variables it uses or
      defines that are not live afterwards (unless it moved them);
    \<^item> at the start of each branch of an @{text "if"}, drop the variables that
      are live before the @{text "if"} but not in that branch;
    \<^item> a loop body is elaborated with the loop's live set (variables used in
      later iterations stay alive), and the variables only needed by the
      loop are dropped after it;
    \<^item> nothing is dropped after a @{text "return"}: the frame's cleanup does it.
\<close>

fun elab :: "omap \<Rightarrow> vname list \<Rightarrow> stmt \<Rightarrow> vname set \<Rightarrow> stmt list" where
  "elab M Os (SSeq a b) L = elab M Os a (live M b L) @ elab M Os b L"
| "elab M Os (SIf c a b) L =
     (let Lb = expand M (evars c) \<union> live M a L \<union> live M b L in
      [SIf c (seq (drops Os (Lb - live M a L) @ elab M Os a L))
             (seq (drops Os (Lb - live M b L) @ elab M Os b L))])"
| "elab M Os (SWhile c b) L =
     (let X = live M (SWhile c b) L in
      SWhile c (seq (elab M Os b X)) # drops Os (X - L))"
| "elab M Os (SReturn eo) L = [SReturn eo]"
| "elab M Os SPass L = []"
| "elab M Os s L = s # drops Os ((expand M (leaf_uses s) \<union> leaf_defs s) - L - leaf_moves s)"

text \<open>
  A body is elaborated with nothing live at its end. Its owned variables
  are its @{text "var"} parameters and @{text "var"} declarations.
\<close>

fun var_decls :: "stmt \<Rightarrow> vname list" where
  "var_decls (SVar x _ _) = [x]"
| "var_decls (SSeq a b) = var_decls a @ var_decls b"
| "var_decls (SIf _ a b) = var_decls a @ var_decls b"
| "var_decls (SWhile _ b) = var_decls b"
| "var_decls _ = []"

text \<open>
  Mojo destroys a @{text "var"} parameter that the body never uses as soon as
  the callee is entered (found by differential testing, tests d09 and d14),
  so the body starts with drops of the owned parameters that are not live
  on entry.
\<close>

definition elab_body :: "prog \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> stmt \<Rightarrow> stmt" where
  "elab_body P ps body =
     (let M = refs_of P [] body;
          Ps = [x. (c, x, _) \<leftarrow> ps, c = Var];
          Os = rev (Ps @ var_decls body)
      in seq (drops Os (set Ps - live M body {}) @ elab M Os body {}))"

definition elab_fun :: "prog \<Rightarrow> fundecl \<Rightarrow> fundecl" where
  "elab_fun P fd = Fun (fd_name fd) (fd_params fd) (fd_ret fd) (elab_body P (fd_params fd) (fd_body fd))"

definition elab_struct :: "prog \<Rightarrow> structdecl \<Rightarrow> structdecl" where
  "elab_struct P sd = Struct (sd_name sd) (sd_fields sd) (sd_copyable sd) (sd_fieldwise sd)
     (map_option (elab_fun P) (sd_init sd))
     (map_option (elab_body P [(Deinit, ''self'', TStruct (sd_name sd))]) (sd_deinit sd))
     (map (elab_fun P) (sd_methods sd))"

definition elaborate :: "prog \<Rightarrow> prog" where
  "elaborate P = Prog (map (elab_struct P) (p_structs P)) (map (elab_fun P) (p_funs P))"

subsection \<open>Elaboration only inserts drops\<close>

text \<open>
  @{text "strip"} flattens sequences and removes @{text "DROP"} and
  @{text "PASS"}; elaboration is invisible after stripping.
\<close>

fun strip :: "stmt \<Rightarrow> stmt list" where
  "strip SPass = []"
| "strip (SDrop _) = []"
| "strip (SSeq a b) = strip a @ strip b"
| "strip (SIf c a b) = [SIf c (seq (strip a)) (seq (strip b))]"
| "strip (SWhile c b) = [SWhile c (seq (strip b))]"
| "strip s = [s]"

lemma strip_seq: "strip (seq ss) = concat (map strip ss)"
  by (induct ss rule: seq.induct) auto

lemma strip_drops: "concat (map strip (drops Os D)) = []"
  by (induct Os) (auto simp: drops_def)

theorem elab_only_inserts_drops: "concat (map strip (elab M Os s L)) = strip s"
  by (induct M Os s L rule: elab.induct) (simp_all add: strip_seq strip_drops Let_def)

section \<open>Checking and elaborating the examples\<close>

text \<open>
  One more invalid example, for the origin check on reference returns:
@{verbatim [display]
\<open>def dangle(ref a: Int) -> ref[a] Int:
    var local = 5
    return local          # error: reference to a local escapes

def main():
    var x = 1
    ref r = dangle(x)
    print(r)\<close>}
\<close>

definition ex8 :: prog where
  "ex8 = Prog [] [
     Fun ''dangle'' [REFP ''a'' \<Ztypecolon>\<Ztypecolon> TInt] (RRef [''a''] TInt)
       (VAR ''local'' \<Ztypecolon> TInt ::= N 5 ;; RETURN \<langle>\<section>''local''\<rangle>),
     Fun ''main'' [] RNone
       (VAR ''x'' \<Ztypecolon> TInt ::= N 1 ;; REF ''r'' ::= ''dangle''\<lbrace>[\<langle>\<section>''x''\<rangle>]\<rbrace> ;; PRINT [\<langle>\<section>''r''\<rangle>])]"

lemma ex8_dangles: "run 200 ex8 = Err ErrDangling"
  by eval

text \<open>
  The checker accepts exactly the valid examples, and rejects each invalid
  one with the error a Mojo compiler reports. Example 6 is rejected for
  argument exclusivity, even though it runs (with visibly aliased output),
  because the semantics does not check exclusivity.
\<close>

lemma check_examples:
  "map check_prog [ex1, ex1_asap, ex3_ok, ex4, ex5, ex7] = replicate 6 []"
  "map check_prog [ex2, ex3, ex4_bad, ex6, ex8] =
     [[''main: use of moved or uninitialized value a''],
      [''main: use of invalidated reference elem''],
      [''Point.__init__: __init__ does not initialize every field''],
      [''main: argument exclusivity: a mut argument aliases another argument''],
      [''dangle: the returned reference may point outside its declared origin, e.g. to a local'']]"
  by eval+

text \<open>
  Elaborating Example 1 reproduces exactly the hand-written ASAP version:
  @{text b} is dropped after the last use of the reference @{text r} whose
  origin contains it, @{text a} is not dropped because it was transferred,
  and @{text l} is dropped after its last use.
\<close>

lemma ex1_elaborated: "elab_body ex1 [] ex1_main = ex1_asap_main"
  by eval

text \<open>
  In Example 5, the loop-local @{text r} is dropped right after its
  declaration (it is never used), inside the loop body, and the loop
  variable @{text i} after the loop.
\<close>

lemma ex5_elaborated:
  "elab_body ex5 [] (fd_body (the (find_fun ex5 ''main''))) =
     (VAR ''i'' \<Ztypecolon> TInt ::= N 0 ;;
      WHILE \<langle>\<section>''i''\<rangle> \<prec> N 3 DO
        (VAR ''r'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[\<langle>\<section>''i''\<rangle>]\<rbrace> ;; DROP \<section>''r'' ;; \<section>''i'' += N 1) ;;
      DROP \<section>''i'' ;;
      PRINT [Txt ''done''])"
  by eval

text \<open>
  The soundness target, tested on the examples: every accepted program,
  once elaborated, runs without error and prints what Mojo prints (with
  ASAP destruction).
\<close>

lemma accepted_examples_run:
  "map (run 200 \<circ> elaborate) [ex1, ex3_ok, ex4, ex5, ex7] =
     [Ok [[VInt 11], [VStr ''drop'', VInt 2], [VStr ''got'', VInt 11],
          [VStr ''drop'', VInt 11], [VInt 1]],
      Ok [[VInt 7, VInt 7, VInt 12, VInt 3]],
      Ok [[VInt 6, VInt 12, VInt 18]],
      Ok [[VStr ''drop'', VInt 0], [VStr ''drop'', VInt 1], [VStr ''drop'', VInt 2],
          [VStr ''done'']],
      Ok [[VInt 2, VInt 1]]]"
  by eval

end