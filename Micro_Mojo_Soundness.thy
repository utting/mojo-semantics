(*
  Micro_Mojo_Soundness.thy

  Soundness of the micro-Mojo ownership checker with respect to the
  big-step semantics. This first part covers expressions without calls.
*)

theory Micro_Mojo_Soundness
  imports Micro_Mojo_Static
begin

section \<open>Overview\<close>

text \<open>
  The target theorem is that a program accepted by @{text "check_prog"} never
  produces an ownership error when it runs. This theory proves the first part:
  soundness for expressions that contain no calls. Calls of functions and methods are
  mutually recursive with statements, so they belong to the next part,
  where the expression lemmas below become cases of one induction over the fuel.

  \<^bold>\<open>The result is stronger than ownership safety.\<close> The checker also checks
  types, so a checked expression can go wrong only with
  @{text "ErrBounds"}, an out-of-range index, which Mojo also reports at run
  time. Every other error is excluded, including @{text "ErrType"}. Proving
  the stronger statement costs little extra, because excluding
  @{text "ErrUninit"} needs well-typed values anyway: a value of a known type
  is never @{text "VUndef"} and has the fields that a place selects.

  \<^bold>\<open>The invariant\<close> @{text "inv"} relates a static environment @{text "\<Gamma>"}
  and an abstract state @{text "\<sigma>"} to a run-time environment and state:
    \<^item> an owned variable is bound to its own root, which holds a
      well-typed value if the variable is in @{text "a_init \<sigma>"}, and
      a well-typed value or @{text "VUndef"} otherwise;
    \<^item> a borrowed parameter denotes a well-typed value, except for the
      @{text "out self"} of @{text "__init__"}, whose fields outside
      @{text "a_fields \<sigma>"} may still be uninitialized;
    \<^item> a reference binding denotes a path below the location of a
      \<^emph>\<open>base\<close> variable in its origin; the steps from the base determine
      its type, and pass through a list item only if the base is in its
      interior. It denotes a well-typed value unless it is invalidated or
      its owned base is uninitialized. This is @{text "safe_to_deref"} of
      the region theory, read as an invariant;
    \<^item> exclusivity (@{text "excl"}): the location of a writable variable
      (owned, or borrowed other than @{text "imm"}) overlaps no other
      non-reference variable's location. This is what makes a move or a
      write local: it changes only memory below one variable, and the
      references that can see it are either unaffected, unusable, or
      invalidated by the checker;
    \<^item> locations lie below @{text "nroot"}, above which the heap is empty,
      names are distinct, and at most one @{text "out"} parameter is in scope.

  \<^bold>\<open>Proof technique.\<close> Results of the interpreter are reasoned about with a
  small Hoare-style predicate @{text "spec r Q"}: @{text "r"} is not an error
  other than @{text "ErrBounds"}, and @{text "Q"} holds for its value if it
  succeeds. @{text "spec"} distributes over the monadic bind, so each case of
  the interpreter is verified by following its @{text "do"} block. The
  three mutually recursive functions @{text "eval"}, @{text "evals"} and
  @{text "eval_place"} are verified together by induction on the fuel,
  which every recursive call decreases. This is simpler than the
  function package's thirteen-way induction rule.

  \<^bold>\<open>Alternatives.\<close> A typed semantics, in which the store is indexed by
  types, would make value typing hold by construction. We keep the untyped
  interpreter, because it is the reference semantics and runs the examples,
  and state typing as part of the invariant instead. Instead of the fuel
  induction one could define the semantics as an inductive relation and
  induct on derivations; with a functional interpreter, fuel induction is
  the natural choice.
\<close>

section \<open>Results that do not go wrong\<close>

definition safe :: "'a res \<Rightarrow> bool" where
  "safe r \<longleftrightarrow> (\<forall>e. r = Err e \<longrightarrow> e = ErrBounds)"

definition spec :: "'a res \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "spec r Q \<longleftrightarrow> safe r \<and> (\<forall>a. r = Ok a \<longrightarrow> Q a)"

lemma spec_Ok [intro!]: "Q a \<Longrightarrow> spec (Ok a) Q"
  by (simp add: spec_def safe_def)

lemma spec_OutOfFuel [intro!]: "spec OutOfFuel Q"
  by (simp add: spec_def safe_def)

lemma spec_ErrBounds [intro!]: "spec (Err ErrBounds) Q"
  by (simp add: spec_def safe_def)

lemma spec_bind [intro]:
  "spec m (\<lambda>a. spec (f a) Q) \<Longrightarrow> spec (bind_res m f) Q"
  by (cases m) (auto simp: spec_def safe_def)

lemma spec_mono:
  "spec r Q \<Longrightarrow> (\<And>a. Q a \<Longrightarrow> Q' a) \<Longrightarrow> spec r Q'"
  by (auto simp: spec_def)

lemma spec_safe: "spec r Q \<Longrightarrow> safe r"
  by (simp add: spec_def)

lemma spec_Ok_D: "spec r Q \<Longrightarrow> r = Ok a \<Longrightarrow> Q a"
  by (simp add: spec_def)

lemma bind_res_Ok_iff: "bind_res m f = Ok b \<longleftrightarrow> (\<exists>a. m = Ok a \<and> f a = Ok b)"
  by (cases m) auto

section \<open>Well-typed values\<close>

text \<open>
  @{text "vt P T v"}: the value @{text "v"} is a fully initialized value of
  type @{text "T"}. A struct value carries the fields of its declaration, in
  order, each well typed. Field types are looked up with @{text "map_of"},
  like @{text "field_ty"} does, so duplicate field names need no special
  treatment.
\<close>

fun vt :: "prog \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> bool" where
  "vt P T VUndef = False"
| "vt P T VNone = (T = TNone)"
| "vt P T (VInt _) = (T = TInt)"
| "vt P T (VBool _) = (T = TBool)"
| "vt P T (VStr _) = (T = TStr)"
| "vt P T (VStruct S fs) = (T = TStruct S \<and>
     (\<exists>sd. find_struct P S = Some sd \<and> map fst fs = map fst (sd_fields sd) \<and>
       (\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u)))"
| "vt P T (VList g vs) = (\<exists>U. T = TList U \<and> (\<forall>u \<in> set vs. vt P U u))"

text \<open>A possibly uninitialized value, such as that of an owned variable after a move.\<close>

definition wt_opt :: "prog \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> bool" where
  "wt_opt P T v \<longleftrightarrow> v = VUndef \<or> vt P T v"

lemma vt_not_undef: "vt P T v \<Longrightarrow> v \<noteq> VUndef"
  by auto

lemma vt_trivial: "vt P T v \<Longrightarrow> trivial_ty T \<Longrightarrow> trivial v"
  by (cases v; cases T) auto

section \<open>Paths into the heap\<close>

lemma walk_append: "walk v (ss @ ts) = bind_res (walk v ss) (\<lambda>u. walk u ts)"
  by (induction v ss rule: walk.induct) (auto split: option.splits)

text \<open>
  The record @{text "ctx"} of the checker has its own @{text "ctx.extend"}, so
  the heap path operation needs its qualified name here.
\<close>

abbreviation ext :: "path \<Rightarrow> step \<Rightarrow> path" where
  "ext \<equiv> Micro_Mojo_Semantics.extend"

lemma get_extend: "get st (ext q s) = bind_res (get st q) (\<lambda>v. walk v [s])"
  by (cases q) (auto simp: get_def Micro_Mojo_Semantics.extend_def walk_append split: option.splits)

lemma vt_field:
  assumes "vt P (TStruct S) v" "field_ty P S f = Good U"
  shows "\<exists>u. walk v [Fld f] = Ok u \<and> vt P U u"
proof -
  from assms(1) obtain fs sd where v: "v = VStruct S fs" and sd: "find_struct P S = Some sd"
    and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u"
    by (cases v) auto
  from assms(2) sd have U: "map_of (sd_fields sd) f = Some U"
    by (auto simp: field_ty_def split: option.splits)
  then have "f \<in> fst ` set fs"
    using names by (metis map_of_eq_None_iff option.distinct(1) set_map)
  then obtain u where u: "map_of fs f = Some u"
    by (meson map_of_eq_None_iff not_Some_eq)
  then have "(f, u) \<in> set fs" by (rule map_of_SomeD)
  with fs U have "vt P U u" by auto
  with u v show ?thesis by simp
qed

section \<open>The invariant\<close>

text \<open>
  The location that a binding denotes: its root, or the borrowed path. A
  borrowed parameter may be bound to a root of its own, because trivial
  @{text "imm"} arguments and temporaries are passed by copy.
\<close>

definition bpath :: "binding \<Rightarrow> path" where
  "bpath b = (case b of Own r \<Rightarrow> (r, []) | Bor q \<Rightarrow> q)"

lemma bpath_simps [simp]: "bpath (Own r) = (r, [])" "bpath (Bor q) = q"
  by (simp_all add: bpath_def)

text \<open>
  The value of @{text "out self"} inside @{text "__init__"} (when
  @{text "c_fields C"} is not empty): a struct whose fields in
  @{text "a_fields \<sigma>"} are initialized and whose other fields may not be.
  In any other function an @{text "out"} parameter is borrowed from an
  initialized place, so its value is fully initialized.
\<close>

definition out_val :: "prog \<Rightarrow> ctx \<Rightarrow> astate \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> bool" where
  "out_val P C \<sigma> T v \<longleftrightarrow>
     (if c_fields C = [] then vt P T v
      else \<exists>S sd fs. T = TStruct S \<and> find_struct P S = Some sd \<and>
        c_fields C = map fst (sd_fields sd) \<and> v = VStruct S fs \<and>
        map fst fs = map fst (sd_fields sd) \<and>
        (\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                              (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)))"

text \<open>
  \<^bold>\<open>Locations of references.\<close> A reference binding denotes a path below the
  location of a \<^emph>\<open>base\<close> variable @{text "z"} in its origin, a variable that is
  not itself a reference. The steps @{text "ss"} from the base determine the
  reference's type statically (@{text "sty"}), and if they pass through a
  list item then @{text "z"} is in the reference's interior. These facts
  never change, because the path of a reference is fixed when it is
  created. They are what makes assignment sound: a reference into the
  assigned value either reaches it through fields only, which a new value
  of the same type also has, or it goes through a list item and is in the
  interior, so the checker invalidates it.
\<close>

fun sty :: "prog \<Rightarrow> ty \<Rightarrow> step list \<Rightarrow> ty option" where
  "sty P T [] = Some T"
| "sty P (TStruct S) (Fld f # ss) = (case field_ty P S f of Good U \<Rightarrow> sty P U ss | Bad _ \<Rightarrow> None)"
| "sty P (TList U) (Idx _ _ # ss) = sty P U ss"
| "sty P _ _ = None"

definition has_idx :: "step list \<Rightarrow> bool" where
  "has_idx ss \<longleftrightarrow> (\<exists>i g. Idx i g \<in> set ss)"

definition pext :: "path \<Rightarrow> step list \<Rightarrow> path" where
  "pext q ss = (fst q, snd q @ ss)"

fun is_ref :: "vkind \<Rightarrow> bool" where
  "is_ref (KRef _ _ _) = True"
| "is_ref _ = False"

text \<open>
  A reference may be used (its value is well typed) if it has not been
  invalidated and its base, if owned, is initialized. This is weaker than
  the checker's condition (every owned variable of the origin initialized),
  so that moving and reinitializing another variable of the origin does not
  affect it.
\<close>

fun binding_ok :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> env \<Rightarrow> state \<Rightarrow> vname \<Rightarrow> vkind \<Rightarrow>
                   binding \<Rightarrow> bool" where
  "binding_ok P C \<Gamma> \<sigma> env st x (KOwned T) b =
     (\<exists>r v. b = Own r \<and> heap st r = Some v \<and>
            (if x \<in> a_init \<sigma> then vt P T v else wt_opt P T v))"
| "binding_ok P C \<Gamma> \<sigma> env st x (KBorrow c T) b =
     (\<exists>v. get st (bpath b) = Ok v \<and> (if c = Out then out_val P C \<sigma> T v else vt P T v))"
| "binding_ok P C \<Gamma> \<sigma> env st x (KRef T og I) b =
     (\<exists>q z kz bz ss. b = Bor q \<and> z \<in> og \<and> map_of \<Gamma> z = Some kz \<and> \<not> is_ref kz \<and>
        map_of env z = Some bz \<and> q = pext (bpath bz) ss \<and> sty P (kind_ty kz) ss = Some T \<and>
        (has_idx ss \<longrightarrow> z \<in> I) \<and>
        (x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow>
           (\<exists>v. get st q = Ok v \<and> vt P T v)))"

text \<open>
  \<^bold>\<open>Exclusivity.\<close> The location of a writable variable (owned, or borrowed
  under a convention other than @{text "imm"}) overlaps the location of no
  other non-reference variable. Two paths overlap if they have the same root
  and one extends the other. At function entry this is what argument
  exclusivity guarantees. For an owned variable it says that no other
  variable reaches its root, which is what makes a move local.
\<close>

definition below :: "path \<Rightarrow> path \<Rightarrow> bool" where
  "below q' q \<longleftrightarrow> fst q' = fst q \<and> (\<exists>us. snd q' = snd q @ us)"

definition overlaps :: "path \<Rightarrow> path \<Rightarrow> bool" where
  "overlaps q q' \<longleftrightarrow> below q q' \<or> below q' q"

fun writable :: "vkind \<Rightarrow> bool" where
  "writable (KOwned _) = True"
| "writable (KBorrow c _) = (c \<noteq> Imm)"
| "writable (KRef _ _ _) = False"

definition excl :: "senv \<Rightarrow> env \<Rightarrow> bool" where
  "excl \<Gamma> env \<longleftrightarrow>
     (\<forall>x kx bx y ky by. map_of \<Gamma> x = Some kx \<and> writable kx \<and> map_of env x = Some bx \<and>
        map_of \<Gamma> y = Some ky \<and> \<not> is_ref ky \<and> map_of env y = Some by \<and> y \<noteq> x \<longrightarrow>
        \<not> overlaps (bpath bx) (bpath by))"

text \<open>
  Static well-formedness of a static environment: names are distinct, and
  the origin of a reference consists of variables declared before it.
\<close>

fun wf_senv :: "senv \<Rightarrow> bool" where
  "wf_senv [] = True"
| "wf_senv ((x, k) # \<Gamma>) = (x \<notin> fst ` set \<Gamma> \<and> wf_senv \<Gamma> \<and>
     (case k of KRef _ og _ \<Rightarrow> og \<subseteq> fst ` set \<Gamma> | _ \<Rightarrow> True))"

text \<open>
  At most one @{text "out"} parameter is in scope (checked by @{text "chk_body"}),
  so the initialized fields in @{text "a_fields"} belong to it.
\<close>

definition one_out :: "senv \<Rightarrow> bool" where
  "one_out \<Gamma> \<longleftrightarrow> (\<forall>x y T U. map_of \<Gamma> x = Some (KBorrow Out T) \<longrightarrow>
                              map_of \<Gamma> y = Some (KBorrow Out U) \<longrightarrow> x = y)"

text \<open>
  The invariant: the run-time environment binds the same names in the same
  order as the static one, every binding satisfies @{text "binding_ok"},
  exclusivity holds, and all bound locations lie below @{text "nroot"},
  above which the heap is empty (so allocation is fresh).
\<close>

definition inv :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool" where
  "inv P C \<Gamma> \<sigma> env st \<longleftrightarrow>
     wf_senv \<Gamma> \<and> one_out \<Gamma> \<and> map fst env = map fst \<Gamma> \<and>
     (\<forall>x k. map_of \<Gamma> x = Some k \<longrightarrow>
        (\<exists>b. map_of env x = Some b \<and> binding_ok P C \<Gamma> \<sigma> env st x k b)) \<and>
     excl \<Gamma> env \<and>
     (\<forall>x b. map_of env x = Some b \<longrightarrow> fst (bpath b) < nroot st) \<and>
     (\<forall>r. nroot st \<le> r \<longrightarrow> heap st r = None)"

text \<open>The invariant depends on the state only through the heap and @{text "nroot"}.\<close>

lemma get_heap_cong: "heap st' = heap st \<Longrightarrow> get st' q = get st q"
  by (simp add: get_def)

lemma binding_ok_heap_cong:
  "heap st' = heap st \<Longrightarrow>
   binding_ok P C \<Gamma> \<sigma> env st' x k b = binding_ok P C \<Gamma> \<sigma> env st x k b"
  by (cases k) (simp_all add: get_def)

lemma inv_heap_cong:
  "heap st' = heap st \<Longrightarrow> nroot st' = nroot st \<Longrightarrow>
   inv P C \<Gamma> \<sigma> env st' = inv P C \<Gamma> \<sigma> env st"
proof -
  assume h: "heap st' = heap st" and n: "nroot st' = nroot st"
  show ?thesis unfolding inv_def using binding_ok_heap_cong[OF h] h n by simp
qed

lemma inv_ngen [simp]: "inv P C \<Gamma> \<sigma> env (st\<lparr>ngen := k\<rparr>) = inv P C \<Gamma> \<sigma> env st"
  by (rule inv_heap_cong) simp_all

lemma inv_out_lines [simp]: "inv P C \<Gamma> \<sigma> env (st\<lparr>out_lines := k\<rparr>) = inv P C \<Gamma> \<sigma> env st"
  by (rule inv_heap_cong) simp_all

lemma inv_binding:
  "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> map_of \<Gamma> x = Some k \<Longrightarrow>
   \<exists>b. map_of env x = Some b \<and> binding_ok P C \<Gamma> \<sigma> env st x k b"
  by (simp add: inv_def)

lemma inv_excl: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> excl \<Gamma> env"
  by (simp add: inv_def)

lemma excl_D:
  "excl \<Gamma> env \<Longrightarrow> map_of \<Gamma> x = Some kx \<Longrightarrow> writable kx \<Longrightarrow> map_of env x = Some bx \<Longrightarrow>
   map_of \<Gamma> y = Some ky \<Longrightarrow> \<not> is_ref ky \<Longrightarrow> map_of env y = Some by \<Longrightarrow> y \<noteq> x \<Longrightarrow>
   \<not> overlaps (bpath bx) (bpath by)"
  unfolding excl_def by blast

lemma overlaps_same_root: "fst q = fst q' \<Longrightarrow> snd q = [] \<Longrightarrow> overlaps q q'"
  by (auto simp: overlaps_def below_def)

lemma below_pext [simp]: "below (pext q ss) q"
  by (simp add: below_def pext_def)

lemma fst_pext [simp]: "fst (pext q ss) = fst q"
  by (simp add: pext_def)

lemma pext_Nil [simp]: "pext q [] = q"
  by (simp add: pext_def)

lemma pext_pext [simp]: "pext (pext q ss) ts = pext q (ss @ ts)"
  by (simp add: pext_def)

lemma get_pext: "get st (pext q ss) = bind_res (get st q) (\<lambda>v. walk v ss)"
  by (cases q) (auto simp: get_def pext_def walk_append split: option.splits)

lemma has_idx_simps [simp]:
  "\<not> has_idx []" "has_idx (ss @ ts) \<longleftrightarrow> has_idx ss \<or> has_idx ts"
  "has_idx [Fld f] = False" "has_idx [Idx i g] = True"
  by (auto simp: has_idx_def)

lemma sty_append:
  "sty P T (ss @ ts) = (case sty P T ss of Some U \<Rightarrow> sty P U ts | None \<Rightarrow> None)"
  by (induction P T ss rule: sty.induct) (auto split: ck.splits option.splits)

section \<open>Abstract states along an expression\<close>

lemma bind_ck_Good_iff [simp]: "bind_ck m f = Good b \<longleftrightarrow> (\<exists>a. m = Good a \<and> f a = Good b)"
  by (cases m) auto

lemma check_Good_iff [simp]: "check b msg = Good u \<longleftrightarrow> b"
  by (simp add: check_def)

text \<open>
  Within an expression the abstract state only loses information: moves
  remove variables from @{text "a_init"} and list mutations add references to
  @{text "a_inval"}. @{text "ale \<sigma>' \<sigma>"} says @{text "\<sigma>'"} is a possible later state.
\<close>

definition ale :: "astate \<Rightarrow> astate \<Rightarrow> bool" where
  "ale \<sigma>' \<sigma> \<longleftrightarrow> a_init \<sigma>' \<subseteq> a_init \<sigma> \<and> a_inval \<sigma> \<subseteq> a_inval \<sigma>' \<and> a_fields \<sigma>' = a_fields \<sigma>"

lemma ale_refl [simp]: "ale \<sigma> \<sigma>"
  by (simp add: ale_def)

lemma ale_trans: "ale \<sigma>2 \<sigma>1 \<Longrightarrow> ale \<sigma>1 \<sigma> \<Longrightarrow> ale \<sigma>2 \<sigma>"
  by (auto simp: ale_def)

lemma case_owned_eq:
  "(case m of Some (KOwned _) \<Rightarrow> A | _ \<Rightarrow> True) = (\<forall>U. m = Some (KOwned U) \<longrightarrow> A)"
  by (auto split: option.splits vkind.splits)

lemma root_ok_ale:
  "root_ok C \<Gamma> \<sigma>' p = Good () \<Longrightarrow> ale \<sigma>' \<sigma> \<Longrightarrow> root_ok C \<Gamma> \<sigma> p = Good ()"
  unfolding root_ok_def Let_def
  apply (cases "map_of \<Gamma> (root_of p)")
   apply simp
  subgoal for k
    by (cases k) (auto simp: ale_def check_def case_owned_eq split: list.splits if_splits)
  done

text \<open>
  @{text "frame"}: the heap changed only at roots of owned variables that are
  no longer initialized, that is, variables moved from.
\<close>

definition frame :: "senv \<Rightarrow> env \<Rightarrow> astate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "frame \<Gamma> env \<sigma>' st st' \<longleftrightarrow>
     (\<forall>r. heap st' r \<noteq> heap st r \<longrightarrow>
        (\<exists>y U. map_of \<Gamma> y = Some (KOwned U) \<and> map_of env y = Some (Own r) \<and> y \<notin> a_init \<sigma>'))"

lemma frame_refl [simp]: "frame \<Gamma> env \<sigma> st st"
  by (simp add: frame_def)

lemma frame_heap_cong: "heap st' = heap st \<Longrightarrow> frame \<Gamma> env \<sigma> st st'"
  by (simp add: frame_def)

lemma frame_trans:
  "frame \<Gamma> env \<sigma>1 st st1 \<Longrightarrow> frame \<Gamma> env \<sigma>2 st1 st2 \<Longrightarrow> ale \<sigma>2 \<sigma>1 \<Longrightarrow> frame \<Gamma> env \<sigma>2 st st2"
  unfolding frame_def ale_def by (metis subsetD)

text \<open>
  The owned variables in the origin of a usable place are initialized.
\<close>

lemma origin_init:
  assumes "root_ok C \<Gamma> \<sigma> p = Good ()" "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some (KOwned U)"
  shows "z \<in> a_init \<sigma>"
proof (cases "map_of \<Gamma> (root_of p)")
  case None
  with assms(1) show ?thesis by (simp add: root_ok_def)
next
  case (Some k)
  with assms show ?thesis
    by (cases k) (auto simp: root_ok_def place_origin_def static_roots_def case_owned_eq Let_def
                       split: if_splits)
qed

text \<open>
  The root under the base of a usable place is not among the changed roots:
  if it were the root of a moved variable, exclusivity would make that
  variable the base, and it would not be initialized.
\<close>

lemma root_unchanged:
  assumes "excl \<Gamma> env" "root_ok C \<Gamma> \<sigma>' p = Good ()" "frame \<Gamma> env \<sigma>' st st'"
    and "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz" "map_of env z = Some bz"
  shows "heap st' (fst (bpath bz)) = heap st (fst (bpath bz))"
proof (rule ccontr)
  assume "heap st' (fst (bpath bz)) \<noteq> heap st (fst (bpath bz))"
  with assms(3) obtain y U where y: "map_of \<Gamma> y = Some (KOwned U)"
    "map_of env y = Some (Own (fst (bpath bz)))" "y \<notin> a_init \<sigma>'"
    by (auto simp: frame_def)
  show False
  proof (cases "z = y")
    case True
    with assms(2,4) y show ?thesis using origin_init by fastforce
  next
    case False
    have "\<not> overlaps (bpath (Own (fst (bpath bz)))) (bpath bz)"
      using excl_D[OF assms(1) y(1) _ y(2) assms(5,6,7)] False by simp
    then show False by (simp add: overlaps_same_root)
  qed
qed

section \<open>Expressions without calls\<close>

fun simple_place :: "place \<Rightarrow> bool"
and simple_expr :: "expr \<Rightarrow> bool"
and simple_exprs :: "expr list \<Rightarrow> bool"
where
  "simple_place (PVar _) = True"
| "simple_place (PField p _) = simple_place p"
| "simple_place (PIndex p e) = (simple_place p \<and> simple_expr e)"
| "simple_expr (EPlace p) = simple_place p"
| "simple_expr (ETake p) = simple_place p"
| "simple_expr (ECopy p) = simple_place p"
| "simple_expr (ECall _ _) = False"
| "simple_expr (EMeth _ _ _) = False"
| "simple_expr (EBin _ a b) = (simple_expr a \<and> simple_expr b)"
| "simple_expr (ENot a) = simple_expr a"
| "simple_expr (ELen p) = simple_place p"
| "simple_expr (EList es) = simple_exprs es"
| "simple_expr _ = True"
| "simple_exprs [] = True"
| "simple_exprs (e # es) = (simple_expr e \<and> simple_exprs es)"

subsection \<open>Static facts\<close>


lemma chk_simple_ale:
  "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<Longrightarrow> simple_place p \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<Longrightarrow> simple_expr e \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<Longrightarrow> simple_exprs es \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs) \<Longrightarrow> True"
proof (induction C \<Gamma> \<sigma> p and C \<Gamma> \<sigma> e and C \<Gamma> \<sigma> es and C \<Gamma> \<sigma> ps es arbitrary: \<sigma>' and \<sigma>' and \<sigma>' and \<sigma>' bs
       rule: chk_idx_chk_expr_chk_exprs_chk_args.induct)
qed (auto split: place.splits option.splits vkind.splits intro: ale_trans, auto simp: ale_def)

text \<open>
  Usability of a place is a property of its root, and of its first field
  when the root is @{text "out self"}. So a place is usable if an extension
  of it is, except that @{text "self.f"} may be usable when @{text "self"} is
  not yet.
\<close>

lemma root_ok_PIndex: "root_ok C \<Gamma> \<sigma> (PIndex p e) = root_ok C \<Gamma> \<sigma> p"
  unfolding root_ok_def Let_def spath.simps root_of.simps ..

lemma spath_nonempty: "\<not> has_index p \<Longrightarrow> (\<forall>x. p \<noteq> PVar x) \<Longrightarrow> spath p \<noteq> []"
  by (induction p) auto

lemma root_ok_PField:
  assumes "root_ok C \<Gamma> \<sigma> (PField p f) = Good ()"
    and "\<forall>x T. p = PVar x \<longrightarrow> map_of \<Gamma> x \<noteq> Some (KBorrow Out T)"
  shows "root_ok C \<Gamma> \<sigma> p = Good ()"
proof (cases "\<exists>T. map_of \<Gamma> (root_of p) = Some (KBorrow Out T)")
  case True
  then obtain T where T: "map_of \<Gamma> (root_of p) = Some (KBorrow Out T)" by blast
  with assms(2) have np: "\<forall>x. p \<noteq> PVar x" by auto
  show ?thesis
  proof (cases "has_index p")
    case True
    with assms(1) T show ?thesis unfolding root_ok_def Let_def spath.simps root_of.simps by simp
  next
    case False
    with np obtain g gs where "spath p = g # gs" using spath_nonempty by (cases "spath p") auto
    with assms(1) False T show ?thesis
      unfolding root_ok_def Let_def spath.simps root_of.simps by simp
  qed
next
  case False
  with assms(1) show ?thesis
    by (auto simp: root_ok_def Let_def split: option.splits vkind.splits)
qed

subsection \<open>Reading variables\<close>

lemma out_val_full:
  "out_val P C \<sigma> T v \<Longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma> \<Longrightarrow> vt P T v"
proof (cases "c_fields C = []")
  case True
  assume "out_val P C \<sigma> T v"
  with True show ?thesis by (simp add: out_val_def)
next
  case False
  assume ov: "out_val P C \<sigma> T v" and sub: "set (c_fields C) \<subseteq> a_fields \<sigma>"
  with False obtain S sd fs where T: "T = TStruct S" and sd: "find_struct P S = Some sd"
    and cf: "c_fields C = map fst (sd_fields sd)" and v: "v = VStruct S fs"
    and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                                   (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)"
    by (auto simp: out_val_def)
  have "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u"
  proof (intro ballI, clarify)
    fix f u assume fu: "(f, u) \<in> set fs"
    then have "f \<in> set (c_fields C)" using cf names
      by (metis fst_conv image_eqI list.set_map)
    with fu fs sub show "\<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u" by blast
  qed
  with T sd v names show ?thesis by simp
qed

lemma out_field:
  assumes "out_val P C \<sigma> (TStruct S) v" "f \<in> a_fields \<sigma>" "field_ty P S f = Good U"
  shows "\<exists>u. walk v [Fld f] = Ok u \<and> vt P U u"
proof (cases "c_fields C = []")
  case True
  with assms show ?thesis by (auto simp: out_val_def intro: vt_field)
next
  case False
  with assms(1) obtain sd fs where sd: "find_struct P S = Some sd" and v: "v = VStruct S fs"
    and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                                   (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)"
    by (auto simp: out_val_def)
  from assms(3) sd have U: "map_of (sd_fields sd) f = Some U"
    by (auto simp: field_ty_def split: option.splits)
  then have "f \<in> fst ` set fs"
    using names by (metis map_of_eq_None_iff option.distinct(1) set_map)
  then obtain u where u: "map_of fs f = Some u"
    by (meson map_of_eq_None_iff not_Some_eq)
  then have "(f, u) \<in> set fs" by (rule map_of_SomeD)
  with fs U assms(2) have "vt P U u" by auto
  with u v show ?thesis by simp
qed

text \<open>A usable variable denotes a well-typed value.\<close>

lemma var_usable:
  assumes "inv P C \<Gamma> \<sigma> env st" "root_ok C \<Gamma> \<sigma> (PVar x) = Good ()" "map_of \<Gamma> x = Some k"
  shows "\<exists>b v. map_of env x = Some b \<and> get st (bpath b) = Ok v \<and> vt P (kind_ty k) v"
proof -
  from assms(1,3) obtain b where b: "map_of env x = Some b" "binding_ok P C \<Gamma> \<sigma> env st x k b"
    by (blast dest: inv_binding)
  show ?thesis
  proof (cases k)
    case (KOwned T)
    with b assms(2,3) show ?thesis by (auto simp: root_ok_def get_def)
  next
    case (KBorrow c T)
    with b assms(2,3) show ?thesis
      by (cases "c = Out") (auto simp: root_ok_def intro: out_val_full)
  next
    case (KRef T og I)
    with b obtain q z kz bz ss where r: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    from assms(2,3) KRef r(2,3) have "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>)"
      by (auto simp: root_ok_def case_owned_eq)
    with r b KRef show ?thesis by auto
  qed
qed

lemma eval_place_PVar:
  "map_of env x = Some b \<Longrightarrow>
   eval_place P n env st (PVar x) = (if n = 0 then OutOfFuel else Ok (bpath b, st))"
  by (cases n; cases b) auto

subsection \<open>Moves preserve the invariant\<close>

lemma out_val_upd [simp]:
  "out_val P C (\<sigma>\<lparr>a_init := X\<rparr>) T v = out_val P C \<sigma> T v"
  "out_val P C (\<sigma>\<lparr>a_inval := X\<rparr>) T v = out_val P C \<sigma> T v"
  by (simp_all add: out_val_def)

lemma get_root_cong: "heap st' (fst q) = heap st (fst q) \<Longrightarrow> get st' q = get st q"
  by (simp add: get_def)

lemma inv_move:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "map_of \<Gamma> x = Some (KOwned U)"
    and r: "map_of env x = Some (Own r)" and h: "heap st' = (heap st)(r := Some VUndef)"
    and n: "nroot st' = nroot st"
  shows "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env st'"
proof -
  let ?\<sigma> = "\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>"
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have rlt: "r < nroot st" using inv r by (fastforce simp: inv_def)
  text \<open>Every non-reference variable other than @{text "x"} lives at another root.\<close>
  have other: "\<And>z kz bz. map_of \<Gamma> z = Some kz \<Longrightarrow> \<not> is_ref kz \<Longrightarrow> map_of env z = Some bz \<Longrightarrow>
                 z \<noteq> x \<Longrightarrow> fst (bpath bz) \<noteq> r"
  proof -
    fix z kz bz assume "map_of \<Gamma> z = Some kz" "\<not> is_ref kz" "map_of env z = Some bz" "z \<noteq> x"
    then have "\<not> overlaps (bpath (Own r)) (bpath bz)"
      using excl_D[OF excl x _ r] by simp
    then show "fst (bpath bz) \<noteq> r" by (auto simp: overlaps_same_root)
  qed
  have bind: "\<exists>b. map_of env y = Some b \<and> binding_ok P C \<Gamma> ?\<sigma> env st' y k b"
    if yk: "map_of \<Gamma> y = Some k" for y k
  proof -
    from inv yk obtain b where b: "map_of env y = Some b" "binding_ok P C \<Gamma> \<sigma> env st y k b"
      by (blast dest: inv_binding)
    show ?thesis
    proof (cases "y = x")
      case True
      with x yk r b h show ?thesis by (auto simp: wt_opt_def)
    next
      case False
      show ?thesis
      proof (cases k)
        case (KOwned T)
        from b(2) KOwned obtain r' v where bo: "b = Own r'" "heap st r' = Some v"
          "if y \<in> a_init \<sigma> then vt P T v else wt_opt P T v" by auto
        have "r' \<noteq> r" using other[OF yk _ b(1) False] KOwned bo by simp
        with bo h b(1) KOwned False show ?thesis by simp
      next
        case (KBorrow c T)
        have "fst (bpath b) \<noteq> r" using other[OF yk _ b(1) False] KBorrow by simp
        then have "get st' (bpath b) = get st (bpath b)"
          by (intro get_root_cong) (simp add: h)
        with b KBorrow show ?thesis by (auto split: if_splits)
      next
        case (KRef T og I)
        with b obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
          "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
          "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
          "y \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow>
             (\<exists>v. get st q = Ok v \<and> vt P T v)"
          by (simp only: binding_ok.simps) blast
        have live: "\<exists>v. get st' q = Ok v \<and> vt P T v"
          if l: "y \<notin> a_inval ?\<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init ?\<sigma>)"
        proof -
          have "z \<noteq> x" using l x rf(3) by auto
          then have "fst q \<noteq> r" using other[OF rf(3,4,5)] rf(6) by simp
          then have "get st' q = get st q" by (intro get_root_cong) (simp add: h)
          with rf(9) l show ?thesis by auto
        qed
        have "binding_ok P C \<Gamma> ?\<sigma> env st' y k b"
          unfolding KRef binding_ok.simps using rf(1-8) live by blast
        with b(1) show ?thesis by blast
      qed
    qed
  qed
  show ?thesis
    unfolding inv_def using inv bind rlt h n by (auto simp: inv_def)
qed

subsection \<open>Operators\<close>

lemma binop_sound:
  assumes "etype P \<Gamma> (EBin op a b) = Good T" "etype P \<Gamma> a = Good A" "etype P \<Gamma> b = Good B"
    and "vt P A v1" "vt P B v2"
  shows "\<exists>v. binop_val op v1 v2 = Ok v \<and> vt P T v"
  using assms
  by (cases op; cases v1; cases v2) (auto simp: binop_val_def)

lemma copy_ok_sound:
  "vt P T v \<Longrightarrow> (\<forall>S. T = TStruct S \<longrightarrow> (\<exists>sd. find_struct P S = Some sd \<and> sd_copyable sd)) \<Longrightarrow>
   copy_ok P v = Ok ()"
  by (cases v) (auto simp: copy_ok_def)

lemma list_all2_vt_same:
  "list_all2 (vt P) Ts vs \<Longrightarrow> list_all (\<lambda>U. U = T) Ts \<Longrightarrow> \<forall>u \<in> set vs. vt P T u"
  by (induction rule: list_all2_induct) auto

lemma fst_ext [simp]: "fst (ext q s) = fst q"
  by (simp add: Micro_Mojo_Semantics.extend_def)

lemma spec_mono_pair:
  "spec r (\<lambda>(a, b). Q a b) \<Longrightarrow> (\<And>a b. Q a b \<Longrightarrow> Q' (a, b)) \<Longrightarrow> spec r Q'"
  by (auto simp: spec_def)

subsection \<open>The soundness of call-free expressions\<close>

text \<open>
  The three statements, for a given fuel. A place is evaluated to a path
  that denotes a well-typed value and starts at the location of the
  place's root variable; an expression to a well-typed value. In both cases
  the invariant holds afterwards for the abstract state computed by the
  checker, and the heap changed only at the roots of moved variables.
\<close>

text \<open>
  @{text "ploc P \<Gamma> env p T q"}: the path @{text "q"} lies below the location of
  a base variable @{text "z"} in the origin of the place @{text "p"}, the steps
  have static type @{text "T"}, and they pass through a list item only if
  @{text "z"} is in the interior of @{text "p"}. This is what a reference to
  @{text "p"} records (@{text "binding_ok"}).
\<close>

definition ploc :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> place \<Rightarrow> ty \<Rightarrow> path \<Rightarrow> bool" where
  "ploc P \<Gamma> env p T q \<longleftrightarrow> (\<exists>z kz bz ss. z \<in> place_origin \<Gamma> p \<and> map_of \<Gamma> z = Some kz \<and>
     \<not> is_ref kz \<and> map_of env z = Some bz \<and> q = pext (bpath bz) ss \<and>
     sty P (kind_ty kz) ss = Some T \<and> (has_idx ss \<longrightarrow> z \<in> place_interior \<Gamma> p))"

lemma ext_pext: "ext q s = pext q [s]"
  by (simp add: Micro_Mojo_Semantics.extend_def pext_def)

lemma ploc_PVar:
  assumes "map_of \<Gamma> x = Some k" "map_of env x = Some b" "binding_ok P C \<Gamma> \<sigma> env st x k b"
  shows "ploc P \<Gamma> env (PVar x) (kind_ty k) (bpath b)"
proof (cases k)
  case (KRef T og I)
  with assms show ?thesis
    by (fastforce simp: ploc_def place_origin_def static_roots_def place_interior_def
                        ref_interior_def)
next
  case (KOwned T)
  with assms show ?thesis
    by (auto simp: ploc_def place_origin_def static_roots_def intro!: exI[of _ "[]"])
next
  case (KBorrow c T)
  with assms show ?thesis
    by (auto simp: ploc_def place_origin_def static_roots_def intro!: exI[of _ "[]"])
qed

lemma ploc_field:
  assumes "ploc P \<Gamma> env p (TStruct S) q" "field_ty P S f = Good T"
  shows "ploc P \<Gamma> env (PField p f) T (ext q (Fld f))"
  using assms
  by (fastforce simp: ploc_def ext_pext sty_append place_origin_def place_interior_def)

lemma ploc_index:
  assumes "ploc P \<Gamma> env p (TList T) q"
  shows "ploc P \<Gamma> env (PIndex p e) T (ext q (Idx i g))"
  using assms
  by (fastforce simp: ploc_def ext_pext sty_append place_origin_def place_interior_def)

definition sound_place :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_place P C \<Gamma> n \<longleftrightarrow> (\<forall>env st p \<sigma> \<sigma>' T.
     inv P C \<Gamma> \<sigma> env st \<longrightarrow> simple_place p \<longrightarrow> chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<longrightarrow>
     ptype P \<Gamma> p = Good T \<longrightarrow> root_ok C \<Gamma> \<sigma>' p = Good () \<longrightarrow>
     spec (eval_place P n env st p) (\<lambda>(q, st').
       inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       ploc P \<Gamma> env p T q))"

definition sound_expr :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_expr P C \<Gamma> n \<longleftrightarrow> (\<forall>env st e \<sigma> \<sigma>' T.
     inv P C \<Gamma> \<sigma> env st \<longrightarrow> simple_expr e \<longrightarrow> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<longrightarrow>
     etype P \<Gamma> e = Good T \<longrightarrow>
     spec (eval P n env st e) (\<lambda>(v, st').
       inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v))"

definition sound_exprs :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_exprs P C \<Gamma> n \<longleftrightarrow> (\<forall>env st es \<sigma> \<sigma>' Ts.
     inv P C \<Gamma> \<sigma> env st \<longrightarrow> simple_exprs es \<longrightarrow> chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<longrightarrow>
     etypes P \<Gamma> es = Good Ts \<longrightarrow>
     spec (evals P n env st es) (\<lambda>(vs, st').
       inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> list_all2 (vt P) Ts vs))"

lemma sound_place_Suc:
  assumes CP: "c_prog C = P" and IHp: "sound_place P C \<Gamma> n" and IHe: "sound_expr P C \<Gamma> n"
  shows "sound_place P C \<Gamma> (Suc n)"
  unfolding sound_place_def
proof (intro allI impI)
  fix env st p \<sigma> \<sigma>' T
  assume inv: "inv P C \<Gamma> \<sigma> env st" and sim: "simple_place p" and chk: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>'"
    and ty: "ptype P \<Gamma> p = Good T" and ro: "root_ok C \<Gamma> \<sigma>' p = Good ()"
  show "spec (eval_place P (Suc n) env st p) (\<lambda>(q, st').
       inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       ploc P \<Gamma> env p T q)"
  proof (cases p)
    case (PVar x)
    from ty PVar obtain k where k: "map_of \<Gamma> x = Some k" "T = kind_ty k"
      by (auto split: option.splits)
    from chk PVar have "\<sigma>' = \<sigma>" by simp
    from inv k obtain b where b: "map_of env x = Some b" "binding_ok P C \<Gamma> \<sigma> env st x k b"
      by (blast dest: inv_binding)
    from inv ro PVar k \<open>\<sigma>' = \<sigma>\<close> b(1) obtain v where "get st (bpath b) = Ok v" "vt P T v"
      using var_usable by fastforce
    moreover have "ploc P \<Gamma> env (PVar x) T (bpath b)" using ploc_PVar[OF k(1) b] k(2) by simp
    ultimately show ?thesis using inv PVar \<open>\<sigma>' = \<sigma>\<close> b(1)
      by (auto simp: eval_place_PVar split: binding.splits)
  next
    case (PField p0 f)
    from ty PField obtain S where t0: "ptype P \<Gamma> p0 = Good (TStruct S)" and ft: "field_ty P S f = Good T"
      by (auto split: ty.split_asm) (metis ty.exhaust)
    from chk PField have c0: "chk_idx C \<Gamma> \<sigma> p0 = Good \<sigma>'" by simp
    show ?thesis
    proof (cases "\<exists>x T0. p0 = PVar x \<and> map_of \<Gamma> x = Some (KBorrow Out T0)")
      case True
      then obtain x T0 where x: "p0 = PVar x" "map_of \<Gamma> x = Some (KBorrow Out T0)" by blast
      from c0 x have "\<sigma>' = \<sigma>" by simp
      from t0 x have T0: "T0 = TStruct S" by simp
      from inv x obtain b where b: "map_of env x = Some b" "binding_ok P C \<Gamma> \<sigma> env st x (KBorrow Out T0) b"
        by (blast dest: inv_binding)
      then obtain v where v: "get st (bpath b) = Ok v" "out_val P C \<sigma> T0 v" by auto
      from ro PField x \<open>\<sigma>' = \<sigma>\<close> have "f \<in> a_fields \<sigma>"
        by (simp add: root_ok_def)
      with v T0 ft obtain u where "walk v [Fld f] = Ok u" "vt P T u"
        using out_field by blast
      moreover have "ploc P \<Gamma> env (PVar x) (TStruct S) (bpath b)"
        using ploc_PVar[OF x(2) b] T0 by simp
      then have "ploc P \<Gamma> env (PField (PVar x) f) T (ext (bpath b) (Fld f))"
        using ploc_field ft by blast
      ultimately show ?thesis using inv PField x \<open>\<sigma>' = \<sigma>\<close> b(1) v
        by (cases n) (auto simp: get_extend split: binding.splits)
    next
      case False
      with ro PField have ro0: "root_ok C \<Gamma> \<sigma>' p0 = Good ()"
        using root_ok_PField by blast
      from sim PField have "simple_place p0" by simp
      with IHp inv c0 t0 ro0 have IH: "spec (eval_place P n env st p0) (\<lambda>(q, st').
         inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P (TStruct S) v) \<and>
         ploc P \<Gamma> env p0 (TStruct S) q)"
        unfolding sound_place_def by blast
      show ?thesis
        unfolding PField eval_place.simps place.case
        apply (rule spec_bind)
        apply (rule spec_mono_pair[OF IH])
        using ft by (auto simp: get_extend ploc_field dest: vt_field)
    qed
  next
    case (PIndex p0 e)
    from ty PIndex obtain T0 where t0: "ptype P \<Gamma> p0 = Good T0" and te: "etype P \<Gamma> e = Good TInt"
      and T0: "T0 = TList T"
      by (auto split: ty.split_asm) (metis ty.exhaust)
    from chk PIndex obtain \<sigma>1 where c0: "chk_idx C \<Gamma> \<sigma> p0 = Good \<sigma>1"
      and ce: "chk_expr C \<Gamma> \<sigma>1 e = Good \<sigma>'" by auto
    from sim PIndex have s0: "simple_place p0" and se: "simple_expr e" by simp_all
    from ce se have ale1: "ale \<sigma>' \<sigma>1" by (rule chk_simple_ale)
    from ro PIndex have ro0: "root_ok C \<Gamma> \<sigma>' p0 = Good ()" by (simp add: root_ok_PIndex)
    then have ro1: "root_ok C \<Gamma> \<sigma>1 p0 = Good ()" using ale1 by (rule root_ok_ale)
    from IHp inv s0 c0 t0 ro1 have IH: "spec (eval_place P n env st p0) (\<lambda>(q, st').
         inv P C \<Gamma> \<sigma>1 env st' \<and> frame \<Gamma> env \<sigma>1 st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T0 v) \<and>
         ploc P \<Gamma> env p0 T0 q)"
      unfolding sound_place_def by blast
    show ?thesis
      unfolding PIndex eval_place.simps place.case
      apply (rule spec_bind)
      apply (rule spec_mono_pair[OF IH])
      apply (elim conjE exE)
      subgoal for q st1 v
        apply (unfold prod.case)
        apply (rule spec_bind)
        apply (rule spec_mono_pair)
         apply (rule IHe[unfolded sound_expr_def, rule_format, OF _ se ce te])
         apply assumption
        apply (elim conjE)
        subgoal for iv st2
        proof -
          assume inv1: "inv P C \<Gamma> \<sigma>1 env st1" and fr1: "frame \<Gamma> env \<sigma>1 st st1"
            and g1: "get st1 q = Ok v" and vt1: "vt P T0 v"
            and pl: "ploc P \<Gamma> env p0 T0 q"
            and inv2: "inv P C \<Gamma> \<sigma>' env st2" and fr2: "frame \<Gamma> env \<sigma>' st1 st2"
            and vti: "vt P TInt iv"
          from pl obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p0" "map_of \<Gamma> z = Some kz"
            "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
            unfolding ploc_def by blast
          have "heap st2 (fst (bpath bz)) = heap st1 (fst (bpath bz))"
            using root_unchanged[OF inv_excl[OF inv1] ro0 fr2 z(1-4)] .
          with z(5) have "get st2 q = get st1 q" by (intro get_root_cong) simp
          with g1 have g2: "get st2 q = Ok v" by simp
          from vt1 T0 obtain g vs where v: "v = VList g vs" "\<forall>u \<in> set vs. vt P T u"
            by (cases v) auto
          from vti obtain i where i: "iv = VInt i" by (cases iv) auto
          have fr: "frame \<Gamma> env \<sigma>' st st2" using frame_trans[OF fr1 fr2 ale1] .
          show ?thesis
            using g2 v i inv2 fr ploc_index[OF pl[unfolded T0]]
            by (auto simp: get_extend)
        qed
        done
      done
  qed
qed

lemma sound_expr_Suc:
  assumes CP: "c_prog C = P" and IHp: "sound_place P C \<Gamma> n" and IHe: "sound_expr P C \<Gamma> n"
    and IHes: "sound_exprs P C \<Gamma> n"
  shows "sound_expr P C \<Gamma> (Suc n)"
  unfolding sound_expr_def
proof (intro allI impI)
  fix env st e \<sigma> \<sigma>' T
  assume inv: "inv P C \<Gamma> \<sigma> env st" and sim: "simple_expr e" and chk: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'"
    and ty: "etype P \<Gamma> e = Good T"
  have Pl: "\<And>env st p \<sigma> \<sigma>' T. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_place p \<Longrightarrow>
      chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<Longrightarrow> ptype P \<Gamma> p = Good T \<Longrightarrow> root_ok C \<Gamma> \<sigma>' p = Good () \<Longrightarrow>
      spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
        (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q)"
    using IHp unfolding sound_place_def by blast
  have Ex: "\<And>env st e \<sigma> \<sigma>' T. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_expr e \<Longrightarrow>
      chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<Longrightarrow> etype P \<Gamma> e = Good T \<Longrightarrow>
      spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
    using IHe unfolding sound_expr_def by blast
  have Exs: "\<And>env st es \<sigma> \<sigma>' Ts. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_exprs es \<Longrightarrow>
      chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<Longrightarrow> etypes P \<Gamma> es = Good Ts \<Longrightarrow>
      spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
        list_all2 (vt P) Ts vs)"
    using IHes unfolding sound_exprs_def by blast
  show "spec (eval P (Suc n) env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
  proof (cases e)
    case (EPlace p)
    from chk EPlace CP obtain \<sigma>1 T1 where c1: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and t1: "ptype P \<Gamma> p = Good T1"
      and tr: "trivial_ty T1" and \<sigma>': "\<sigma>' = \<sigma>1"
      by auto
    from sim EPlace have sp: "simple_place p" by simp
    from ty EPlace t1 have "T1 = T" by simp
    show ?thesis unfolding EPlace eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv sp c1 t1 ro]])
      using \<sigma>' tr \<open>T1 = T\<close> by (auto simp: read_val_def dest: vt_trivial)
  next
    case (ETake p)
    from chk ETake obtain x U where p: "p = PVar x" and xU: "map_of \<Gamma> x = Some (KOwned U)"
      and xi: "x \<in> a_init \<sigma>" and \<sigma>': "\<sigma>' = \<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>"
      by (auto split: place.splits option.splits vkind.splits)
    from ty ETake p xU have TU: "T = U" by simp
    from inv_binding[OF inv xU] xi obtain r v where r: "map_of env x = Some (Own r)"
      "heap st r = Some v" "vt P U v"
      by auto
    let ?st' = "st\<lparr>heap := (heap st)(r := Some VUndef)\<rparr>"
    have "inv P C \<Gamma> \<sigma>' env ?st'" using inv_move[OF inv xU r(1)] \<sigma>' by simp
    moreover have "frame \<Gamma> env \<sigma>' st ?st'" using xU r(1) \<sigma>' by (auto simp: frame_def)
    ultimately show ?thesis using r TU unfolding ETake p eval.simps expr.case
      by (cases n) (auto simp: get_def put_def)
  next
    case (ECopy p)
    from chk ECopy CP obtain \<sigma>1 T1 u where c1: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and t1: "ptype P \<Gamma> p = Good T1"
      and cp: "(case T1 of
                  TStruct S \<Rightarrow> (case find_struct P S of
                     Some sd \<Rightarrow> check (sd_copyable sd) (S @ '' is not Copyable'')
                   | None \<Rightarrow> Bad (''unknown struct '' @ S))
                | _ \<Rightarrow> Good ()) = Good u"
      and \<sigma>': "\<sigma>' = \<sigma>1"
      by (simp only: chk_expr.simps bind_ck_Good_iff ck.inject) (elim exE conjE, simp)
    from cp have cpy: "\<forall>S. T1 = TStruct S \<longrightarrow> (\<exists>sd. find_struct P S = Some sd \<and> sd_copyable sd)"
      by (cases T1) (auto split: option.splits)
    from sim ECopy have sp: "simple_place p" by simp
    from ty ECopy t1 have "T1 = T" by simp
    show ?thesis unfolding ECopy eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv sp c1 t1 ro]])
      using \<sigma>' cpy \<open>T1 = T\<close> by (auto simp: copy_ok_sound)
  next
    case (EBin op a b)
    from chk EBin obtain \<sigma>1 where ca: "chk_expr C \<Gamma> \<sigma> a = Good \<sigma>1" and cb: "chk_expr C \<Gamma> \<sigma>1 b = Good \<sigma>'"
      by auto
    from ty EBin obtain A B where ta: "etype P \<Gamma> a = Good A" and tb: "etype P \<Gamma> b = Good B"
      by auto
    from sim EBin have sa: "simple_expr a" and sb: "simple_expr b" by simp_all
    have ale1: "ale \<sigma>' \<sigma>1" using cb sb by (rule chk_simple_ale)
    have bs: "\<And>v1 v2. vt P A v1 \<Longrightarrow> vt P B v2 \<Longrightarrow> \<exists>v. binop_val op v1 v2 = Ok v \<and> vt P T v"
      using binop_sound ty ta tb EBin by blast
    show ?thesis unfolding EBin eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF inv sa ca ta]], unfold prod.case)
      apply (elim conjE)
      subgoal for v1 st1
        apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF _ sb cb tb]], assumption, unfold prod.case)
        subgoal for v2 st2
          using bs[of v1 v2] frame_trans[of \<Gamma> env \<sigma>1 st st1 \<sigma>' st2] ale1 by auto
        done
      done
  next
    case (ENot a)
    from chk ENot have ca: "chk_expr C \<Gamma> \<sigma> a = Good \<sigma>'" by simp
    from ty ENot have ta: "etype P \<Gamma> a = Good TBool" and T: "T = TBool" by auto
    from sim ENot have sa: "simple_expr a" by simp
    show ?thesis unfolding ENot eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF inv sa ca ta]], unfold prod.case)
      subgoal for v st1 using T by (cases v) auto
      done
  next
    case (ELen p)
    from chk ELen obtain \<sigma>1 where c1: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and \<sigma>': "\<sigma>' = \<sigma>1"
      by auto
    from ty ELen obtain T1 where t1: "ptype P \<Gamma> p = Good T1"
      and r: "(case T1 of TList _ \<Rightarrow> Good TInt | _ \<Rightarrow> Bad ''len of a non-list'') = Good T"
      by (simp only: etype.simps bind_ck_Good_iff) blast
    from r have l: "\<exists>U. T1 = TList U" and T: "T = TInt" by (cases T1; simp)+
    from sim ELen have sp: "simple_place p" by simp
    show ?thesis unfolding ELen eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv sp c1 t1 ro]])
      using \<sigma>' l T by (auto, case_tac v, auto)
  next
    case (EList es)
    from chk EList have ces: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>'" by simp
    from ty EList obtain Ts where ts: "etypes P \<Gamma> es = Good Ts"
      and r: "(case Ts of
                 [] \<Rightarrow> Bad ''an empty list literal needs a declared type''
               | T # _ \<Rightarrow> do { check (list_all (\<lambda>U. U = T) Ts) ''list elements must have the same type'';
                              Good (TList T) }) = Good T"
      by (simp only: etype.simps bind_ck_Good_iff) blast
    from r obtain T0 where same: "list_all (\<lambda>U. U = T0) Ts" and T: "T = TList T0"
      by (cases Ts) auto
    from sim EList have ss: "simple_exprs es" by simp
    show ?thesis unfolding EList eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Exs[OF inv ss ces ts]], unfold prod.case)
      using same T
      by (auto simp: fresh_gen_def frame_def dest: list_all2_vt_same)
  qed (use chk ty inv sim in auto)
qed

lemma sound_exprs_Suc:
  assumes IHe: "sound_expr P C \<Gamma> n" and IHes: "sound_exprs P C \<Gamma> n"
  shows "sound_exprs P C \<Gamma> (Suc n)"
  unfolding sound_exprs_def
proof (intro allI impI)
  fix env st es \<sigma> \<sigma>' Ts
  assume inv: "inv P C \<Gamma> \<sigma> env st" and sim: "simple_exprs es" and chk: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>'"
    and ty: "etypes P \<Gamma> es = Good Ts"
  have Ex: "\<And>env st e \<sigma> \<sigma>' T. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_expr e \<Longrightarrow>
      chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<Longrightarrow> etype P \<Gamma> e = Good T \<Longrightarrow>
      spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
    using IHe unfolding sound_expr_def by blast
  have Exs: "\<And>env st es \<sigma> \<sigma>' Ts. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_exprs es \<Longrightarrow>
      chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<Longrightarrow> etypes P \<Gamma> es = Good Ts \<Longrightarrow>
      spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
        list_all2 (vt P) Ts vs)"
    using IHes unfolding sound_exprs_def by blast
  show "spec (evals P (Suc n) env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
        list_all2 (vt P) Ts vs)"
  proof (cases es)
    case Nil
    with chk ty inv show ?thesis by auto
  next
    case (Cons e es')
    from chk Cons obtain \<sigma>1 where ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
      and ces: "chk_exprs C \<Gamma> \<sigma>1 es' = Good \<sigma>'" by auto
    from ty Cons obtain T1 Ts' where te: "etype P \<Gamma> e = Good T1" and ts: "etypes P \<Gamma> es' = Good Ts'"
      and Ts: "Ts = T1 # Ts'" by auto
    from sim Cons have se: "simple_expr e" and ss: "simple_exprs es'" by simp_all
    have ale1: "ale \<sigma>' \<sigma>1" using ces ss by (rule chk_simple_ale)
    show ?thesis unfolding Cons evals.simps list.case
      apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF inv se ce te]], unfold prod.case)
      apply (elim conjE)
      subgoal for v st1
        apply (rule spec_bind, rule spec_mono_pair[OF Exs[OF _ ss ces ts]], assumption, unfold prod.case)
        subgoal for vs st2
          using Ts frame_trans[of \<Gamma> env \<sigma>1 st st1 \<sigma>' st2] ale1 by auto
        done
      done
  qed
qed

lemma sound_all:
  assumes "c_prog C = P"
  shows "sound_place P C \<Gamma> n \<and> sound_expr P C \<Gamma> n \<and> sound_exprs P C \<Gamma> n"
proof (induction n)
  case 0
  show ?case by (simp add: sound_place_def sound_expr_def sound_exprs_def spec_def safe_def)
next
  case (Suc n)
  then show ?case
    using sound_place_Suc sound_expr_Suc sound_exprs_Suc assms by blast
qed

subsection \<open>The soundness theorem for expressions\<close>

text \<open>
  A call-free expression accepted by the checker, evaluated in a state
  satisfying the invariant, fails at most with @{text "ErrBounds"}. If it
  succeeds, its value is well typed and the invariant holds for the
  checker's abstract state afterwards. In particular it never fails with
  an ownership error.
\<close>

theorem expr_sound:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_expr e"
    and "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'" "etype P \<Gamma> e = Good T"
  shows "safe (eval P n env st e)"
    and "eval P n env st e = Ok (v, st') \<Longrightarrow> inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v"
proof -
  have "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
    using sound_all[OF assms(1), of \<Gamma> n] assms(2-) unfolding sound_expr_def by blast
  then show "safe (eval P n env st e)"
    and "eval P n env st e = Ok (v, st') \<Longrightarrow> inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v"
    by (auto simp: spec_def)
qed

definition ownership_err :: "err \<Rightarrow> bool" where
  "ownership_err e \<longleftrightarrow> e \<in> {ErrUninit, ErrDangling, ErrInvalidated, ErrNotCopyable, ErrFieldInit}"

corollary expr_no_ownership_error:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_expr e"
    and "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'" "etype P \<Gamma> e = Good T"
    and "eval P n env st e = Err err"
  shows "\<not> ownership_err err"
  using expr_sound(1)[OF assms(1-5), of n] assms(6) by (simp add: safe_def ownership_err_def)

section \<open>Next steps\<close>

text \<open>
  Statements within one frame are proved sound in
  @{text "Micro_Mojo_Soundness_Stmt"}, assuming a specification of
  destruction. What remains is calls (with list methods and
  @{text "__deinit__"}), which make expressions, statements and destruction
  mutually recursive and are to be proved by one induction on the fuel.
\<close>

end
