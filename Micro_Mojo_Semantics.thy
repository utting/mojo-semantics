(*
  Micro_Mojo_Semantics.thy

  Big-step semantics of micro-Mojo, given as a clocked definitional
  interpreter, plus the executed example programs and the connection of
  the memory model to the region theory.
*)

theory Micro_Mojo_Semantics
  imports Micro_Mojo_Syntax Mojo_Region_Model "HOL-Library.Monad_Syntax"
begin

section \<open>Design of the semantics\<close>

text \<open>
  \<^bold>\<open>Decision: functional big-step semantics.\<close> We define the big-step
  semantics as a total function with a fuel argument (a "clocked"
  definitional interpreter, in the style of Owens et al., "Functional
  Big-Step Semantics", ESOP 2016), rather than as an inductive relation.
  Reasons:
    \<^item> Errors must be explicit outcomes (as agreed). In an inductive
      big-step relation every premise that can fail needs an extra
      error-propagation rule, roughly doubling the number of rules. Here
      errors propagate through an error monad for free.
    \<^item> The examples can be \<^emph>\<open>run\<close> with @{command value} and their outputs
      checked by @{method eval}.
    \<^item> Determinism holds by construction.
  Divergence shows up as @{text "OutOfFuel"}. Each recursive call uses up
  one unit of fuel, which makes termination of the definition trivial.
  The alternative, an inductive relation, is still available: it could be
  derived later and proved equivalent ("for some fuel the interpreter
  returns @{text "r"}" iff "the relation relates the program to @{text "r"}").

  \<^bold>\<open>Decision: memory as trees, locations as paths.\<close> Every variable owns a
  \<^emph>\<open>root\<close> in the heap, holding a value \<^emph>\<open>tree\<close>: a struct value contains
  its field values and a list contains its items. A location is therefore
  a \<^emph>\<open>path\<close>, i.e.\ a root together with a sequence of steps (field
  selections and list indices). This makes Mojo's ownership tree
  literal: the owner of a location is the path with its last step
  removed. In the last section we instantiate the @{text "mojo_regions"}
  locale of the region theory with this owner function and show that the
  footprint of a location is exactly the set of its extensions.
  Moving a value just moves a subtree, copying it duplicates the subtree,
  and destroying it deinitializes the subtree.

  The alternative, a flat heap of cells with explicit child pointers, is
  closer to a real implementation, but it needs separate invariants to
  rule out sharing, which the tree representation gives for free.

  \<^bold>\<open>Initialization.\<close> An uninitialized location holds @{text "VUndef"} (the
  boolean "initialized" flag of the region theory's Part 2, folded into
  the value). A moved-out variable, a declared-but-unassigned variable,
  and a not-yet-assigned field inside @{text "__init__"} all hold
  @{text "VUndef"}. Reading or writing \<^emph>\<open>through\<close> @{text "VUndef"} is the
  error @{text "ErrUninit"}.

  \<^bold>\<open>Interior origins.\<close> Every list value carries a \<^emph>\<open>generation\<close> number,
  and every index step of a path records the generation the list had when
  the path was formed. Shape-changing operations (list creation,
  @{text "append"}, @{text "pop"}) give the list a fresh generation, while
  writes to items keep it. Following a path through a list whose
  generation has changed is the error @{text "ErrInvalidated"}. This is
  exactly the @{text "Shape"}/@{text "Item"} generation-counter model of the
  region theory's Part 3, applied per list.

  \<^bold>\<open>Dangling references.\<close> When a function returns, its owned locals are
  destroyed and their roots freed. A reference into a freed root is the
  error @{text "ErrDangling"}.

  \<^bold>\<open>What the dynamic semantics does not check.\<close> Argument exclusivity, the
  ban on implicitly copying non-trivial values into @{text "var"}
  parameters, and moving out of borrowed places are static rules. The
  semantics executes such programs anyway, which is what lets
  Example 6 \<^emph>\<open>show\<close> the aliasing hazard.
\<close>



section \<open>Run-time values and states\<close>

datatype step = Fld fname | Idx nat nat   \<comment> \<open>index, generation\<close>

type_synonym path = "nat \<times> step list"

text \<open>
  @{text "VNone"} is Mojo's @{text "None"}, used as the result of calls that
  return nothing.
\<close>

datatype val =
    VUndef
  | VNone
  | VInt int
  | VBool bool
  | VStr string
  | VStruct name "(fname \<times> val) list"
  | VList nat "val list"   \<comment> \<open>generation, items\<close>

text \<open>
  A variable either owns a root (@{text "var"} declarations, @{text "var"}
  parameters and temporaries) or borrows a location (@{text "mut"},
  @{text "ref"} and non-trivial @{text "imm"} parameters, and @{text "ref"}
  bindings).
\<close>

datatype binding = Own nat | Bor path

type_synonym env = "(vname \<times> binding) list"   \<comment> \<open>newest binding first\<close>

record state =
  heap :: "nat \<Rightarrow> val option"    \<comment> \<open>@{text "None"}: root not allocated or freed\<close>
  nroot :: nat                    \<comment> \<open>next fresh root\<close>
  ngen :: nat                     \<comment> \<open>next fresh list generation\<close>
  out_lines :: "val list list"       \<comment> \<open>one line per @{text "print"}\<close>

datatype err =
    ErrUninit
  | ErrDangling
  | ErrInvalidated
  | ErrBounds
  | ErrNotCopyable
  | ErrFieldInit
  | ErrUnbound vname
  | ErrUnknown name
  | ErrArity
  | ErrType string

datatype 'a res = Ok 'a | Err err | OutOfFuel

fun bind_res :: "'a res \<Rightarrow> ('a \<Rightarrow> 'b res) \<Rightarrow> 'b res" where
  "bind_res (Ok a) f = f a"
| "bind_res (Err e) f = Err e"
| "bind_res OutOfFuel f = OutOfFuel"

lemma bind_res_cong [fundef_cong]:
  "m = m' \<Longrightarrow> (\<And>a. m' = Ok a \<Longrightarrow> f a = f' a) \<Longrightarrow> bind_res m f = bind_res m' f'"
  by (cases m) auto

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind_res

datatype rval = RUnit | RV val | RP path    \<comment> \<open>results of calls\<close>
datatype outcome = Normal | Returned rval   \<comment> \<open>results of statements\<close>



section \<open>Heap operations\<close>

fun walk :: "val \<Rightarrow> step list \<Rightarrow> val res" where
  "walk v [] = Ok v"
| "walk (VStruct S fs) (Fld f # ss) =
     (case map_of fs f of Some v \<Rightarrow> walk v ss | None \<Rightarrow> Err (ErrType ''no such field''))"
| "walk (VList g vs) (Idx i g' # ss) =
     (if g \<noteq> g' then Err ErrInvalidated
      else if i < length vs then walk (vs ! i) ss else Err ErrBounds)"
| "walk VUndef (_ # _) = Err ErrUninit"
| "walk _ _ = Err (ErrType ''bad path'')"

fun update_at :: "val \<Rightarrow> step list \<Rightarrow> val \<Rightarrow> val res" where
  "update_at _ [] w = Ok w"
| "update_at (VStruct S fs) (Fld f # ss) w =
     (case map_of fs f of
        None \<Rightarrow> Err (ErrType ''no such field'')
      | Some v \<Rightarrow> do {
          v' \<leftarrow> update_at v ss w;
          Ok (VStruct S (map (\<lambda>(f', u). if f' = f then (f', v') else (f', u)) fs)) })"
| "update_at (VList g vs) (Idx i g' # ss) w =
     (if g \<noteq> g' then Err ErrInvalidated
      else if i < length vs then do { v' \<leftarrow> update_at (vs ! i) ss w; Ok (VList g (vs[i := v'])) }
      else Err ErrBounds)"
| "update_at VUndef (_ # _) w = Err ErrUninit"
| "update_at _ _ _ = Err (ErrType ''bad path'')"

definition get :: "state \<Rightarrow> path \<Rightarrow> val res" where
  "get st p = (case heap st (fst p) of None \<Rightarrow> Err ErrDangling | Some v \<Rightarrow> walk v (snd p))"

definition put :: "state \<Rightarrow> path \<Rightarrow> val \<Rightarrow> state res" where
  "put st p w = (case heap st (fst p) of
     None \<Rightarrow> Err ErrDangling
   | Some v \<Rightarrow> do { v' \<leftarrow> update_at v (snd p) w; Ok (st\<lparr>heap := (heap st)(fst p := Some v')\<rparr>) })"

definition alloc :: "state \<Rightarrow> val \<Rightarrow> nat \<times> state" where
  "alloc st v = (nroot st, st\<lparr>heap := (heap st)(nroot st := Some v), nroot := Suc (nroot st)\<rparr>)"

definition free :: "state \<Rightarrow> nat \<Rightarrow> state" where
  "free st r = st\<lparr>heap := (heap st)(r := None)\<rparr>"

definition fresh_gen :: "state \<Rightarrow> nat \<times> state" where
  "fresh_gen st = (ngen st, st\<lparr>ngen := Suc (ngen st)\<rparr>)"

definition extend :: "path \<Rightarrow> step \<Rightarrow> path" where
  "extend p s = (fst p, snd p @ [s])"

text \<open>Implicitly copyable values: Mojo's register-passable trivial types.\<close>

fun trivial :: "val \<Rightarrow> bool" where
  "trivial (VInt _) = True"
| "trivial (VBool _) = True"
| "trivial (VStr _) = True"
| "trivial VNone = True"
| "trivial _ = False"

text \<open>Reading a place as a value is an implicit copy.\<close>

definition read_val :: "val \<Rightarrow> val res" where
  "read_val v = (if v = VUndef then Err ErrUninit
                 else if trivial v then Ok v else Err ErrNotCopyable)"

fun int_op :: "(int \<Rightarrow> int \<Rightarrow> val) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val res" where
  "int_op f (VInt a) (VInt b) = Ok (f a b)"
| "int_op f _ _ = Err (ErrType ''expected Int operands'')"

fun bool_op :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val res" where
  "bool_op f (VBool a) (VBool b) = Ok (VBool (f a b))"
| "bool_op f _ _ = Err (ErrType ''expected Bool operands'')"

text \<open>
  Both operands are always evaluated: @{text "and"}/@{text "or"} are not
  short-circuiting in micro-Mojo, a simplification that makes no
  difference to programs without side effects in conditions.
\<close>

definition binop_val :: "binop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val res" where
  "binop_val op v1 v2 =
     (if v1 = VUndef \<or> v2 = VUndef then Err ErrUninit
      else case op of
        Add \<Rightarrow> int_op (\<lambda>a b. VInt (a + b)) v1 v2
      | Sub \<Rightarrow> int_op (\<lambda>a b. VInt (a - b)) v1 v2
      | Mul \<Rightarrow> int_op (\<lambda>a b. VInt (a * b)) v1 v2
      | Lt \<Rightarrow> int_op (\<lambda>a b. VBool (a < b)) v1 v2
      | Le \<Rightarrow> int_op (\<lambda>a b. VBool (a \<le> b)) v1 v2
      | Eq \<Rightarrow> (case (v1, v2) of
                (VBool a, VBool b) \<Rightarrow> Ok (VBool (a = b))
              | _ \<Rightarrow> int_op (\<lambda>a b. VBool (a = b)) v1 v2)
      | And \<Rightarrow> bool_op (\<and>) v1 v2
      | Or \<Rightarrow> bool_op (\<or>) v1 v2)"



section \<open>Program lookup\<close>

definition find_struct :: "prog \<Rightarrow> name \<Rightarrow> structdecl option" where
  "find_struct P S = find (\<lambda>sd. sd_name sd = S) (p_structs P)"

definition find_fun :: "prog \<Rightarrow> name \<Rightarrow> fundecl option" where
  "find_fun P f = find (\<lambda>fd. fd_name fd = f) (p_funs P)"

definition find_method :: "structdecl \<Rightarrow> name \<Rightarrow> fundecl option" where
  "find_method sd m = find (\<lambda>fd. fd_name fd = m) (sd_methods sd)"

text \<open>
  Expressions that denote a location rather than a value: places, and
  calls of functions returning a reference.
\<close>

fun is_ref_expr :: "prog \<Rightarrow> expr \<Rightarrow> bool" where
  "is_ref_expr P (EPlace _) = True"
| "is_ref_expr P (ECall f _) =
     (case find_fun P f of
        Some fd \<Rightarrow> (case fd_ret fd of RRef _ _ \<Rightarrow> True | _ \<Rightarrow> False)
      | None \<Rightarrow> False)"
| "is_ref_expr P _ = False"

definition copy_ok :: "prog \<Rightarrow> val \<Rightarrow> unit res" where
  "copy_ok P v = (case v of
     VUndef \<Rightarrow> Err ErrUninit
   | VStruct S _ \<Rightarrow> (case find_struct P S of
       Some sd \<Rightarrow> if sd_copyable sd then Ok () else Err ErrNotCopyable
     | None \<Rightarrow> Err (ErrUnknown S))
   | _ \<Rightarrow> Ok ())"

definition rval_to_val :: "state \<Rightarrow> rval \<Rightarrow> val res" where
  "rval_to_val st r = (case r of
     RUnit \<Rightarrow> Ok VNone
   | RV v \<Rightarrow> Ok v
   | RP p \<Rightarrow> do { v \<leftarrow> get st p; read_val v })"



section \<open>The interpreter\<close>

text \<open>
  The interpreter is one group of mutually recursive functions, each taking
  the fuel @{text "n"} as its first argument and the program @{text "P"} as a
  fixed parameter:

  ┌ @{text "eval n env st e"}: evaluate @{text "e"} to an \<^emph>\<open>owned\<close> value;
  ┌ @{text "evals"}: evaluate a list of expressions left to right;
  ┌ @{text "eval_place"}: evaluate a place to a path (an index is evaluated
    and bounds-checked here, and the path records the list's generation);
  ┌ @{text "eval_ref"}: evaluate a location-denoting expression to a path;
  ┌ @{text "pass_args"}: bind arguments to parameters according to their
    conventions, producing the callee's initial environment;
  ┌ @{text "call_fun"}, @{text "call_meth"}: calls of functions, constructors,
    methods and built-in list methods;
  ┌ @{text "invoke"}: run a body in a fresh frame and destroy the frame's
    owned locals on exit;
  ┌ @{text "exec"}, @{text "exec_block"}: statements, and statements in a new
    block scope;
  ┌ @{text "drop_path"}, @{text "drop_paths"}: destroy the value at a path,
    running @{text "__deinit__"} first and then destroying the remaining
    fields or items in order;
  ┌ @{text "cleanup"}: destroy and free the owned roots of an environment,
    newest first.

  \<^bold>\<open>Argument passing\<close> (@{text "pass_args"}), by convention:
  ┌ @{text "var"} (and @{text "deinit"}): the argument is evaluated to an owned
    value, which the callee owns in a fresh root. So @{text "x^"} transfers,
    and @{text "\<langle>x\<rangle>"} is an implicit copy, which is only allowed for
    trivial values;
  ┌ @{text "mut"}, @{text "ref"}: the argument must denote a location, which is
    borrowed;
  ┌ @{text "imm"}: a location holding a trivial value is \<^emph>\<open>copied\<close>, since
    Mojo passes register-passable values by value; other locations are
    borrowed; a non-location argument (such as a literal or a call result)
    becomes a temporary owned by the callee, destroyed when the callee
    returns.
\<close>

context
  fixes P :: prog
begin

function (sequential) eval :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> (val \<times> state) res"
and evals :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> (val list \<times> state) res"
and eval_place :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> place \<Rightarrow> (path \<times> state) res"
and eval_ref :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> (path \<times> state) res"
and pass_args :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> (env \<times> state) res"
and call_fun :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> name \<Rightarrow> expr list \<Rightarrow> (rval \<times> state) res"
and call_meth :: "nat \<Rightarrow> env \<Rightarrow> state \<Rightarrow> place \<Rightarrow> name \<Rightarrow> expr list \<Rightarrow> (rval \<times> state) res"
and invoke :: "nat \<Rightarrow> state \<Rightarrow> fundecl \<Rightarrow> env \<Rightarrow> (rval \<times> state) res"
and exec :: "nat \<Rightarrow> ret \<Rightarrow> env \<Rightarrow> state \<Rightarrow> stmt \<Rightarrow> (outcome \<times> env \<times> state) res"
and exec_block :: "nat \<Rightarrow> ret \<Rightarrow> env \<Rightarrow> state \<Rightarrow> stmt \<Rightarrow> (outcome \<times> env \<times> state) res"
and drop_path :: "nat \<Rightarrow> state \<Rightarrow> path \<Rightarrow> state res"
and drop_paths :: "nat \<Rightarrow> state \<Rightarrow> path list \<Rightarrow> state res"
and cleanup :: "nat \<Rightarrow> state \<Rightarrow> env \<Rightarrow> state res"
where
  "eval 0 _ _ _ = OutOfFuel"
| "eval (Suc n) env st e = (case e of
     EInt i \<Rightarrow> Ok (VInt i, st)
   | EBool b \<Rightarrow> Ok (VBool b, st)
   | EStr s \<Rightarrow> Ok (VStr s, st)
   | EPlace p \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       v \<leftarrow> get st q;
       w \<leftarrow> read_val v;
       Ok (w, st) }
   | ETake p \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       v \<leftarrow> get st q;
       if v = VUndef then Err ErrUninit
       else do { st \<leftarrow> put st q VUndef; Ok (v, st) } }
   | ECopy p \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       v \<leftarrow> get st q;
       copy_ok P v;
       Ok (v, st) }
   | ECall f es \<Rightarrow> do {
       (r, st) \<leftarrow> call_fun n env st f es;
       v \<leftarrow> rval_to_val st r;
       Ok (v, st) }
   | EMeth p m es \<Rightarrow> do {
       (r, st) \<leftarrow> call_meth n env st p m es;
       v \<leftarrow> rval_to_val st r;
       Ok (v, st) }
   | EBin op e1 e2 \<Rightarrow> do {
       (v1, st) \<leftarrow> eval n env st e1;
       (v2, st) \<leftarrow> eval n env st e2;
       v \<leftarrow> binop_val op v1 v2;
       Ok (v, st) }
   | ENot e \<Rightarrow> do {
       (v, st) \<leftarrow> eval n env st e;
       (case v of VBool b \<Rightarrow> Ok (VBool (\<not> b), st) | _ \<Rightarrow> Err (ErrType ''not'')) }
   | ELen p \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       v \<leftarrow> get st q;
       (case v of
          VList _ vs \<Rightarrow> Ok (VInt (int (length vs)), st)
        | VUndef \<Rightarrow> Err ErrUninit
        | _ \<Rightarrow> Err (ErrType ''len'')) }
   | EList es \<Rightarrow> do {
       (vs, st) \<leftarrow> evals n env st es;
       (case fresh_gen st of (g, st) \<Rightarrow> Ok (VList g vs, st)) })"

| "evals 0 _ _ _ = OutOfFuel"
| "evals (Suc n) env st es = (case es of
     [] \<Rightarrow> Ok ([], st)
   | e # es \<Rightarrow> do {
       (v, st) \<leftarrow> eval n env st e;
       (vs, st) \<leftarrow> evals n env st es;
       Ok (v # vs, st) })"

| "eval_place 0 _ _ _ = OutOfFuel"
| "eval_place (Suc n) env st p = (case p of
     PVar x \<Rightarrow> (case map_of env x of
        Some (Own r) \<Rightarrow> Ok ((r, []), st)
      | Some (Bor q) \<Rightarrow> Ok (q, st)
      | None \<Rightarrow> Err (ErrUnbound x))
   | PField p f \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       Ok (extend q (Fld f), st) }
   | PIndex p e \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       (iv, st) \<leftarrow> eval n env st e;
       v \<leftarrow> get st q;
       (case (v, iv) of
          (VList g vs, VInt i) \<Rightarrow>
            if 0 \<le> i \<and> nat i < length vs then Ok (extend q (Idx (nat i) g), st)
            else Err ErrBounds
        | (VUndef, _) \<Rightarrow> Err ErrUninit
        | _ \<Rightarrow> Err (ErrType ''index'')) })"

| "eval_ref 0 _ _ _ = OutOfFuel"
| "eval_ref (Suc n) env st e = (case e of
     EPlace p \<Rightarrow> eval_place n env st p
   | ECall f es \<Rightarrow> do {
       (r, st) \<leftarrow> call_fun n env st f es;
       (case r of RP q \<Rightarrow> Ok (q, st) | _ \<Rightarrow> Err (ErrType ''not a reference'')) }
   | _ \<Rightarrow> Err (ErrType ''not a place''))"

| "pass_args 0 _ _ _ _ = OutOfFuel"
| "pass_args (Suc n) env st ps es = (case (ps, es) of
     ([], []) \<Rightarrow> Ok ([], st)
   | ((c, x, T) # ps, e # es) \<Rightarrow> do {
       (b, st) \<leftarrow>
         (if c = Var \<or> c = Deinit then do {
            (v, st) \<leftarrow> eval n env st e;
            (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }
          else if is_ref_expr P e then do {
            (q, st) \<leftarrow> eval_ref n env st e;
            if c = Imm then do {
              v \<leftarrow> get st q;
              if trivial v then (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st))
              else Ok (Bor q, st) }
            else Ok (Bor q, st) }
          else if c = Imm then do {
            (v, st) \<leftarrow> eval n env st e;
            (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }
          else Err (ErrType ''mut or ref argument must be a place''));
       (bs, st) \<leftarrow> pass_args n env st ps es;
       Ok ((x, b) # bs, st) }
   | _ \<Rightarrow> Err ErrArity)"

| "call_fun 0 _ _ _ _ = OutOfFuel"
| "call_fun (Suc n) env st f es = (case find_struct P f of
     Some sd \<Rightarrow> (case sd_init sd of
        Some fd \<Rightarrow> (case fd_params fd of
           (Out, sx, _) # ps \<Rightarrow>
             (case alloc st (VStruct f (map (\<lambda>(fl, _). (fl, VUndef)) (sd_fields sd))) of
                (r, st) \<Rightarrow> do {
                  (benv, st) \<leftarrow> pass_args n env st ps es;
                  (_, st) \<leftarrow> invoke n st fd (rev benv @ [(sx, Bor (r, []))]);
                  v \<leftarrow> get st (r, []);
                  (case v of
                     VStruct _ fs \<Rightarrow>
                       if list_all (\<lambda>(_, u). u \<noteq> VUndef) fs then Ok (RV v, free st r)
                       else Err ErrFieldInit
                   | _ \<Rightarrow> Err ErrFieldInit) })
         | _ \<Rightarrow> Err (ErrType ''__init__ needs out self''))
      | None \<Rightarrow>
          if sd_fieldwise sd then do {
            (vs, st) \<leftarrow> evals n env st es;
            if length vs = length (sd_fields sd)
            then Ok (RV (VStruct f (zip (map fst (sd_fields sd)) vs)), st)
            else Err ErrArity }
          else Err (ErrType ''no initializer''))
   | None \<Rightarrow> (case find_fun P f of
        None \<Rightarrow> Err (ErrUnknown f)
      | Some fd \<Rightarrow> do {
          (benv, st) \<leftarrow> pass_args n env st (fd_params fd) es;
          invoke n st fd (rev benv) }))"

| "call_meth 0 _ _ _ _ _ = OutOfFuel"
| "call_meth (Suc n) env st p m es = do {
     (q, st) \<leftarrow> eval_place n env st p;
     v \<leftarrow> get st q;
     (case v of
        VList _ vs \<Rightarrow>
          if m = ''append'' then (case es of
             [e] \<Rightarrow> do {
               (x, st) \<leftarrow> eval n env st e;
               v \<leftarrow> get st q;
               (case v of
                  VList _ vs \<Rightarrow> (case fresh_gen st of (g, st) \<Rightarrow> do {
                     st \<leftarrow> put st q (VList g (vs @ [x]));
                     Ok (RUnit, st) })
                | _ \<Rightarrow> Err (ErrType ''append'')) }
           | _ \<Rightarrow> Err ErrArity)
          else if m = ''pop'' then
            (if es \<noteq> [] then Err ErrArity
             else if vs = [] then Err ErrBounds
             else (case fresh_gen st of (g, st) \<Rightarrow> do {
                st \<leftarrow> put st q (VList g (butlast vs));
                Ok (RV (last vs), st) }))
          else Err (ErrUnknown m)
      | VStruct S _ \<Rightarrow> (case find_struct P S of
          None \<Rightarrow> Err (ErrUnknown S)
        | Some sd \<Rightarrow> (case find_method sd m of
            None \<Rightarrow> Err (ErrUnknown m)
          | Some fd \<Rightarrow> (case fd_params fd of
              (_, sx, _) # ps \<Rightarrow> do {
                (benv, st) \<leftarrow> pass_args n env st ps es;
                invoke n st fd (rev benv @ [(sx, Bor q)]) }
            | [] \<Rightarrow> Err ErrArity)))
      | VUndef \<Rightarrow> Err ErrUninit
      | _ \<Rightarrow> Err (ErrType ''method receiver'')) }"

| "invoke 0 _ _ _ = OutOfFuel"
| "invoke (Suc n) st fd env = do {
     (oc, env, st) \<leftarrow> exec n (fd_ret fd) env st (fd_body fd);
     st \<leftarrow> cleanup n st env;
     Ok ((case oc of Normal \<Rightarrow> RUnit | Returned r \<Rightarrow> r), st) }"

| "exec 0 _ _ _ _ = OutOfFuel"
| "exec (Suc n) rt env st s = (case s of
     SPass \<Rightarrow> Ok (Normal, env, st)
   | SSeq s1 s2 \<Rightarrow> do {
       (oc, env, st) \<leftarrow> exec n rt env st s1;
       (case oc of Normal \<Rightarrow> exec n rt env st s2 | Returned r \<Rightarrow> Ok (Returned r, env, st)) }
   | SVar x T eo \<Rightarrow> do {
       (v, st) \<leftarrow> (case eo of None \<Rightarrow> Ok (VUndef, st) | Some e \<Rightarrow> eval n env st e);
       (case alloc st v of (r, st) \<Rightarrow> Ok (Normal, (x, Own r) # env, st)) }
   | SRef x e \<Rightarrow> do {
       (q, st) \<leftarrow> eval_ref n env st e;
       Ok (Normal, (x, Bor q) # env, st) }
   | SAssign p e \<Rightarrow> do {
       (v, st) \<leftarrow> eval n env st e;
       (q, st) \<leftarrow> eval_place n env st p;
       st \<leftarrow> drop_path n st q;
       st \<leftarrow> put st q v;
       Ok (Normal, env, st) }
   | SExpr e \<Rightarrow> do {
       (v, st) \<leftarrow> eval n env st e;
       (case alloc st v of (r, st) \<Rightarrow> do {
          st \<leftarrow> drop_path n st (r, []);
          Ok (Normal, env, free st r) }) }
   | SPrint es \<Rightarrow> do {
       (vs, st) \<leftarrow> evals n env st es;
       Ok (Normal, env, st\<lparr>out_lines := out_lines st @ [vs]\<rparr>) }
   | SIf e s1 s2 \<Rightarrow> do {
       (c, st) \<leftarrow> eval n env st e;
       (case c of
          VBool b \<Rightarrow> exec_block n rt env st (if b then s1 else s2)
        | _ \<Rightarrow> Err (ErrType ''if condition'')) }
   | SWhile e body \<Rightarrow> do {
       (c, st) \<leftarrow> eval n env st e;
       (case c of
          VBool True \<Rightarrow> do {
            (oc, env', st) \<leftarrow> exec_block n rt env st body;
            (case oc of
               Normal \<Rightarrow> exec n rt env st (SWhile e body)
             | Returned r \<Rightarrow> Ok (Returned r, env', st)) }
        | VBool False \<Rightarrow> Ok (Normal, env, st)
        | _ \<Rightarrow> Err (ErrType ''while condition'')) }
   | SReturn None \<Rightarrow> Ok (Returned RUnit, env, st)
   | SReturn (Some e) \<Rightarrow> (case rt of
        RRef _ _ \<Rightarrow> do { (q, st) \<leftarrow> eval_ref n env st e; Ok (Returned (RP q), env, st) }
      | _ \<Rightarrow> do { (v, st) \<leftarrow> eval n env st e; Ok (Returned (RV v), env, st) })
   | SDrop p \<Rightarrow> do {
       (q, st) \<leftarrow> eval_place n env st p;
       st \<leftarrow> drop_path n st q;
       Ok (Normal, env, st) })"

| "exec_block 0 _ _ _ _ = OutOfFuel"
| "exec_block (Suc n) rt env st s = do {
     (oc, env', st) \<leftarrow> exec n rt env st s;
     (case oc of
        Normal \<Rightarrow> do {
          st \<leftarrow> cleanup n st (take (length env' - length env) env');
          Ok (Normal, env, st) }
      | Returned r \<Rightarrow> Ok (Returned r, env', st)) }"

| "drop_path 0 _ _ = OutOfFuel"
| "drop_path (Suc n) st q = do {
     v \<leftarrow> get st q;
     (case v of
        VUndef \<Rightarrow> Ok st
      | VStruct S _ \<Rightarrow> (case find_struct P S of
          None \<Rightarrow> Err (ErrUnknown S)
        | Some sd \<Rightarrow> do {
            st \<leftarrow> (case sd_deinit sd of
                    None \<Rightarrow> Ok st
                  | Some body \<Rightarrow> do {
                      (_, env', st) \<leftarrow> exec n RNone [(''self'', Bor q)] st body;
                      cleanup n st env' });
            v \<leftarrow> get st q;
            (case v of
               VStruct _ fs \<Rightarrow> do {
                 st \<leftarrow> drop_paths n st (map (\<lambda>(f, _). extend q (Fld f)) fs);
                 put st q VUndef }
             | _ \<Rightarrow> put st q VUndef) })
      | VList g vs \<Rightarrow> do {
          st \<leftarrow> drop_paths n st (map (\<lambda>i. extend q (Idx i g)) [0..<length vs]);
          put st q VUndef }
      | _ \<Rightarrow> put st q VUndef) }"

| "drop_paths 0 _ _ = OutOfFuel"
| "drop_paths (Suc n) st qs = (case qs of
     [] \<Rightarrow> Ok st
   | q # qs \<Rightarrow> do { st \<leftarrow> drop_path n st q; drop_paths n st qs })"

| "cleanup 0 _ _ = OutOfFuel"
| "cleanup (Suc n) st env = (case env of
     [] \<Rightarrow> Ok st
   | (x, Own r) # env \<Rightarrow> do { st \<leftarrow> drop_path n st (r, []); cleanup n (free st r) env }
   | (x, Bor _) # env \<Rightarrow> cleanup n st env)"
  by pat_completeness auto

text \<open>
  Termination is by the fuel, which every recursive call decreases. The
  automatic search of @{command fun} (lexicographic orders over the sizes of
  all arguments of all thirteen functions) is far too slow here, so we give
  the measure explicitly: the function package encodes the arguments of the
  mutually recursive functions as a tree of sums of tuples, and the fuel is
  the first component of every tuple.
\<close>

termination
  by (relation "measure (case_sum
        (case_sum (case_sum fst (case_sum fst fst)) (case_sum fst (case_sum fst fst)))
        (case_sum (case_sum fst (case_sum fst fst))
                  (case_sum (case_sum fst fst) (case_sum fst fst))))") auto

end

definition init_state :: state where
  "init_state = \<lparr>heap = (\<lambda>_. None), nroot = 0, ngen = 0, out_lines = []\<rparr>"

text \<open>
  Running a program calls @{text "main"} with no arguments and returns the
  printed lines.
\<close>

definition run :: "nat \<Rightarrow> prog \<Rightarrow> val list list res" where
  "run fuel P = (case find_fun P ''main'' of
     None \<Rightarrow> Err (ErrUnknown ''main'')
   | Some fd \<Rightarrow> do { (_, st) \<leftarrow> invoke P fuel init_state fd []; Ok (out_lines st) })"



section \<open>Running the examples\<close>

text \<open>
  Each example of @{text "Micro_Mojo_Syntax"} is run with enough fuel, and
  its output is checked by evaluation. The invalid examples end in the
  run-time error corresponding to Mojo's static error. Output printed
  before an error is not part of the result, since the error monad does
  not carry the state; if that becomes important, @{text Err} can be
  extended with the state.
\<close>

text \<open>
  Example 1 without ASAP elaboration: remaining variables are destroyed
  when @{text main} returns, so @{text b} is destroyed last.
\<close>

lemma ex1_output: "run 200 ex1 =
  Ok [[VInt 11], [VStr ''got'', VInt 11], [VStr ''drop'', VInt 11], [VInt 1],
      [VStr ''drop'', VInt 2]]"
  by eval

text \<open>
  With the explicit @{text DROP}s that ASAP elaboration would insert,
  @{text b} is destroyed right after the last use of the reference
  @{text r} whose origin includes it, which is the order a Mojo program
  prints.
\<close>

lemma ex1_asap_output: "run 200 ex1_asap =
  Ok [[VInt 11], [VStr ''drop'', VInt 2], [VStr ''got'', VInt 11],
      [VStr ''drop'', VInt 11], [VInt 1]]"
  by eval

lemma ex2_use_after_transfer: "run 200 ex2 = Err ErrUninit"
  by eval

lemma ex3_invalidated: "run 200 ex3 = Err ErrInvalidated"
  by eval

text \<open>Writing through an element reference is an item mutation and keeps it valid.\<close>

lemma ex3_ok_output: "run 200 ex3_ok = Ok [[VInt 7, VInt 7, VInt 12, VInt 3]]"
  by eval

lemma ex4_output: "run 200 ex4 = Ok [[VInt 6, VInt 12, VInt 18]]"
  by eval

lemma ex4_bad_field_init: "run 200 ex4_bad = Err ErrFieldInit"
  by eval

lemma ex5_output: "run 200 ex5 =
  Ok [[VStr ''drop'', VInt 0], [VStr ''drop'', VInt 1], [VStr ''drop'', VInt 2],
      [VStr ''done'']]"
  by eval

text \<open>
  Example 6: the first call (non-aliased) appends @{text "1, 1"}; the second,
  aliased call appends @{text "3, 4"} instead of @{text "3, 3"}. The dynamic
  semantics cannot detect this; it is the static argument-exclusivity rule
  (Rule 2 of the region model) that must reject it.
\<close>

lemma ex6_output: "run 200 ex6 = Ok [[VInt 0, VInt 1, VInt 1], [VInt 3, VInt 4]]"
  by eval

lemma ex7_output: "run 200 ex7 = Ok [[VInt 2, VInt 1]]"
  by eval



section \<open>Connection to the region theory\<close>

text \<open>
  Paths are the locations of micro-Mojo. The direct owner of a path is the
  path without its last step, so a struct value owns its fields and a list
  owns its items. With this owner function, the assumption-free locale
  @{text mojo_regions} of @{text "Mojo_Region_Model"} applies directly. Its
  @{text footprint} of a location (everything that destroying or moving the
  location destroys or moves) is exactly the set of extensions of the
  path. This is the subtree that @{text drop_path} deinitializes and
  @{text ETake} moves. So the region theory's notions of footprint,
  @{text mem_disjoint} and well-formed regions can be used unchanged for
  the static well-formedness rules: an origin such as @{text "[a, b]"} in
  @{text "ref[a, b]"} denotes the region @{text "{root a, root b}"}.
\<close>

definition path_owner :: "path \<Rightarrow> path option" where
  "path_owner p = (if snd p = [] then None else Some (fst p, butlast (snd p)))"

interpretation paths: mojo_regions path_owner .

text \<open>
  We use @{text path_owner} only through this applied equation. Unfolding
  @{text path_owner_def} itself would rewrite the parameter of
  @{text "paths.ancestor_at"} into a @{text "\<lambda>"}-term, after which the interpreted
  equations of @{text ancestor_at} no longer match.
\<close>

lemma path_owner_Pair [simp]:
  "path_owner (r, ss) = (if ss = [] then None else Some (r, butlast ss))"
  by (simp add: path_owner_def)

lemma paths_ancestor_at:
  "paths.ancestor_at k (r, ss) =
     (if k \<le> length ss then Some (r, take (length ss - k) ss) else None)"
proof (induct k)
  case 0
  show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "Suc k \<le> length ss")
    case True
    with Suc have "paths.ancestor_at k (r, ss) = Some (r, take (length ss - k) ss)" by simp
    moreover from True have "take (length ss - k) ss \<noteq> []" by (cases ss) auto
    moreover from True have "butlast (take (length ss - k) ss) = take (length ss - Suc k) ss"
      by (simp add: butlast_take)
    ultimately show ?thesis using True by simp
  next
    case False
    show ?thesis
    proof (cases "k \<le> length ss")
      case True
      with False have "k = length ss" by simp
      with Suc show ?thesis by simp
    next
      case False
      with Suc show ?thesis by simp
    qed
  qed
qed

lemma paths_strictly_contains:
  "paths.strictly_contains (r, ss) (r', ts) \<longleftrightarrow> r' = r \<and> (\<exists>us. us \<noteq> [] \<and> ts = ss @ us)"
proof
  assume "paths.strictly_contains (r, ss) (r', ts)"
  then obtain k where "paths.ancestor_at (Suc k) (r', ts) = Some (r, ss)"
    unfolding paths.strictly_contains_def by blast
  then have k: "Suc k \<le> length ts" "r' = r" "ss = take (length ts - Suc k) ts"
    by (auto simp: paths_ancestor_at split: if_splits)
  let ?us = "drop (length ts - Suc k) ts"
  from k have "?us \<noteq> []" and "ts = ss @ ?us" by auto
  with k show "r' = r \<and> (\<exists>us. us \<noteq> [] \<and> ts = ss @ us)" by blast
next
  assume "r' = r \<and> (\<exists>us. us \<noteq> [] \<and> ts = ss @ us)"
  then obtain us where us: "r' = r" "us \<noteq> []" "ts = ss @ us" by blast
  then have "paths.ancestor_at (Suc (length us - 1)) (r', ts) = Some (r, ss)"
    by (simp add: paths_ancestor_at)
  then show "paths.strictly_contains (r, ss) (r', ts)"
    unfolding paths.strictly_contains_def by blast
qed

theorem paths_footprint: "paths.footprint (r, ss) = {(r, ss @ us) | us. True}"
proof -
  have "c \<in> paths.footprint (r, ss) \<longleftrightarrow> (\<exists>us. c = (r, ss @ us))" for c
  proof (cases c)
    case (Pair r' ts)
    have "ts = ss @ [] \<or> (\<exists>us. us \<noteq> [] \<and> ts = ss @ us) \<longleftrightarrow> (\<exists>us. ts = ss @ us)"
      by auto
    then show ?thesis
      using Pair by (auto simp: paths.footprint_def paths_strictly_contains)
  qed
  then show ?thesis by auto
qed

end
