(*
  Micro_Mojo_Syntax.thy

  Abstract syntax of micro-Mojo, a small subset of Mojo 1.0 chosen to make
  Mojo's ownership rules observable in small example programs, together with
  Mojo-like notation and a suite of encoded example programs.
*)

theory Micro_Mojo_Syntax
  imports Main
begin

section \<open>Overview\<close>

text \<open>
  Micro-Mojo is the subset of Mojo 1.0 proposed earlier in this project. It
  contains:

    \<^item> the types @{text "Int"}, @{text "Bool"}, user-defined structs and the
      built-in dynamic container @{text "List[T]"}; string literals only
      appear as arguments of @{text "print"};

    \<^item> functions declared with @{text "def"}, whose parameters carry Mojo's
      argument conventions (default/@{text "imm"}, @{text "mut"}, @{text "var"},
      @{text "ref"}), returning nothing, a value, or a reference whose origin
      is a union of parameters (@{text "-> ref[a, b] T"});

    \<^item> structs with fields, optionally @{text "@fieldwise_init"} and
      @{text "Copyable"}, an optional @{text "__init__(out self, ...)"}, an
      optional @{text "__deinit__(deinit self)"} and methods;

    \<^item> statements @{text "var"}, reference bindings @{text "ref r = ..."},
      assignment, @{text "if"}/@{text "else"}, @{text "while"}, @{text "return"},
      expression statements, @{text "print"}, and an explicit @{text "drop"}.

  \<^bold>\<open>Decision: an explicit @{text "drop"} statement.\<close> Mojo destroys values
  ASAP, i.e. right after their last use. We agreed to implement this as a
  later static elaboration pass that inserts explicit @{text "DROP p"}
  statements, so that the dynamic semantics never has to perform last-use
  analysis. @{text "DROP"} is therefore part of the abstract syntax even
  though Mojo programmers never write it. The semantics additionally
  destroys any variables still owning a value when their scope ends, in
  reverse declaration order, so that un-elaborated programs still have a
  sensible (C++-like) meaning; after elaboration this fallback never fires.

  \<^bold>\<open>Decision: one call form for functions and constructors.\<close> In Mojo
  @{text "Res(1)"} is simply a call of the type @{text "Res"}. We mirror this:
  @{text "ECall f args"} constructs a struct when @{text "f"} names a struct,
  and calls a function otherwise. This keeps the abstract syntax small.

  \<^bold>\<open>Decision: places are a separate syntactic category.\<close> Argument conventions
  distinguish passing a \<^emph>\<open>location\<close> (@{text "mut"}, @{text "ref"}, and
  @{text "imm"} for non-trivial values) from passing a \<^emph>\<open>value\<close>
  (@{text "var"}). Making places (@{text "x"}, @{text "p.f"}, @{text "p[i]"})
  an explicit category, and marking where a place is used as an expression
  (@{text "EPlace"}), lets the semantics decide by the callee's convention
  whether an argument @{text "\<langle>p\<rangle>"} is passed by reference or read.

  \<^bold>\<open>What is left out\<close>, as agreed: traits beyond the @{text "Copyable"} marker,
  generics and @{text "comptime"}, closures, @{text "raises"}/@{text "try"},
  @{text "match"}, @{text "for"}, SIMD, Python interop, overloading, implicit
  conversions, keyword/variadic arguments and @{text "Pointer"}. The obvious
  next extension is @{text "Pointer[T, origin]"}.
\<close>

section \<open>Abstract syntax\<close>

type_synonym vname = string   \<comment> \<open>variables and parameters\<close>
type_synonym fname = string   \<comment> \<open>struct fields\<close>
type_synonym name = string    \<comment> \<open>functions, methods and structs\<close>

text \<open>
  @{text TStr} is only the type of string literals (which may only be
  printed), and @{text TNone} is the type of calls that return nothing.
\<close>

datatype ty = TInt | TBool | TStr | TNone | TStruct name | TList ty

text \<open>
  Argument conventions. @{text "Out"} is only used for the @{text "self"}
  parameter of @{text "__init__"}, and @{text "Deinit"} for the @{text "self"}
  parameter of @{text "__deinit__"}; we keep them in the same datatype because
  Mojo treats them as ordinary conventions. @{text "Var"} is Mojo's owned
  @{text "var"} convention.
\<close>

datatype conv = Imm | Mut | Var | Ref | Out | Deinit

datatype binop = Add | Sub | Mul | Lt | Le | Eq | And | Or

text \<open>
  Places and expressions are mutually recursive because an index
  expression appears inside a place.

    \<^item> @{text "EPlace p"}: use place @{text "p"} as an expression. Read as a
      value it is an implicit copy (only allowed for trivial values); passed
      to a @{text "mut"}/@{text "ref"}/@{text "imm"} parameter it is a reference.
    \<^item> @{text "ETake p"}: Mojo's transfer @{text "p^"}.
    \<^item> @{text "ECopy p"}: Mojo's explicit @{text "p.copy()"}.
    \<^item> @{text "EMeth p m args"}: method call @{text "p.m(args)"}; the
      receiver is a place, which is all the examples need.
\<close>

datatype place =
    PVar vname
  | PField place fname
  | PIndex place expr
and expr =
    EInt int
  | EBool bool
  | EStr string
  | EPlace place
  | ETake place
  | ECopy place
  | ECall name "expr list"
  | EMeth place name "expr list"
  | EBin binop expr expr
  | ENot expr
  | ELen place
  | EList "expr list"

datatype stmt =
    SPass
  | SSeq stmt stmt
  | SVar vname ty "expr option"   \<comment> \<open>@{text "var x: T = e"} or @{text "var x: T"}\<close>
  | SRef vname expr               \<comment> \<open>@{text "ref r = e"}\<close>
  | SAssign place expr
  | SExpr expr
  | SPrint "expr list"
  | SIf expr stmt stmt
  | SWhile expr stmt
  | SReturn "expr option"
  | SDrop place                   \<comment> \<open>inserted by ASAP elaboration\<close>

text \<open>
  Return specifications: no result, a value, or a reference whose origin is
  the union of the listed parameters (@{text "-> ref[a, b] T"}).
\<close>

datatype ret = RNone | RVal ty | RRef "vname list" ty

datatype fundecl = Fun
  (fd_name: name)
  (fd_params: "(conv \<times> vname \<times> ty) list")
  (fd_ret: ret)
  (fd_body: stmt)

text \<open>
  A struct declaration: name, fields, whether it is @{text "Copyable"},
  whether it is @{text "@fieldwise_init"}, an optional @{text "__init__"}
  (whose first parameter is @{text "out self"}), an optional
  @{text "__deinit__"} body (with @{text "deinit self"} implicit), and methods
  (whose first parameter is @{text "self"} with some convention).
\<close>

datatype structdecl = Struct
  (sd_name: name)
  (sd_fields: "(fname \<times> ty) list")
  (sd_copyable: bool)
  (sd_fieldwise: bool)
  (sd_init: "fundecl option")
  (sd_deinit: "stmt option")
  (sd_methods: "fundecl list")

datatype prog = Prog (p_structs: "structdecl list") (p_funs: "fundecl list")

section \<open>Mojo-like notation\<close>

text \<open>
  The notation follows Mojo where Isabelle's syntax allows it, and IMP-style
  upper-case keywords otherwise (to avoid clashes with HOL syntax):

  ┌ @{text "\<section>x"} is variable @{text "x"} as a place, @{text "p\<bullet>f"} a field,
    @{text "p\<lbrakk>e\<rbrakk>"} an index;
  ┌ @{text "\<langle>p\<rangle>"} uses a place as an expression, @{text "p\<^sup>^"} is Mojo's
    @{text "p^"}, @{text "COPY p"} is @{text "p.copy()"};
  ┌ @{text "f\<lbrace>es\<rbrace>"} is a call (or construction), @{text "p\<bullet>m\<lbrace>es\<rbrace>"} a method
    call;
  ┌ statements use @{text ";;"} for sequencing and the keywords
    @{text "VAR"}, @{text "REF"}, @{text "::="}, @{text "+="}, @{text "IF"},
    @{text "WHILE"}, @{text "RETURN"}, @{text "PRINT"}, @{text "EVAL"} (expression
    statement) and @{text "DROP"}.

  The right argument of @{text "\<bullet>"} is atomic, so that @{text "p\<bullet>m\<lbrace>es\<rbrace>"}
  can only parse as a method call. Bodies of @{text "IF"}/@{text "WHILE"} that
  are sequences need parentheses.
\<close>

notation PVar ("\<section>_" [1000] 1000)
notation PField ("_\<bullet>_" [900, 1000] 900)
notation PIndex ("_\<lbrakk>_\<rbrakk>" [900, 0] 900)

notation EPlace ("\<langle>_\<rangle>")
notation ETake ("_\<^sup>^" [1000] 999)
notation ECopy ("COPY _" [1000] 999)
notation ECall ("_\<lbrace>_\<rbrace>" [1000, 0] 999)
notation EMeth ("_\<bullet>_\<lbrace>_\<rbrace>" [900, 1000, 0] 999)
notation ELen ("LEN _" [1000] 999)
notation EList ("LIST _" [1000] 999)
notation ENot ("NOT _" [999] 999)

abbreviation N :: "int \<Rightarrow> expr" where "N i \<equiv> EInt i"
abbreviation TT :: expr where "TT \<equiv> EBool True"
abbreviation FF :: expr where "FF \<equiv> EBool False"
abbreviation Txt :: "string \<Rightarrow> expr" where "Txt s \<equiv> EStr s"

abbreviation add_e (infixl "\<oplus>" 65) where "a \<oplus> b \<equiv> EBin Add a b"
abbreviation sub_e (infixl "\<ominus>" 65) where "a \<ominus> b \<equiv> EBin Sub a b"
abbreviation mul_e (infixl "\<otimes>" 70) where "a \<otimes> b \<equiv> EBin Mul a b"
abbreviation lt_e (infix "\<prec>" 50) where "a \<prec> b \<equiv> EBin Lt a b"
abbreviation le_e (infix "\<preceq>" 50) where "a \<preceq> b \<equiv> EBin Le a b"
abbreviation eq_e (infix "\<doteq>" 50) where "a \<doteq> b \<equiv> EBin Eq a b"
abbreviation and_e (infixr "AND" 35) where "a AND b \<equiv> EBin And a b"
abbreviation or_e (infixr "OR" 30) where "a OR b \<equiv> EBin Or a b"

notation SPass ("PASS")
notation SSeq (infixr ";;" 10)
syntax
  "_svar_init" :: "vname \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> stmt" ("(VAR _ \<Ztypecolon> _ ::= _)" [1000, 999, 21] 20)
  "_svar_none" :: "vname \<Rightarrow> ty \<Rightarrow> stmt" ("(VAR _ \<Ztypecolon> _)" [1000, 999] 20)
  "_sreturn" :: "expr \<Rightarrow> stmt" ("RETURN _" [21] 20)
translations
  "VAR x \<Ztypecolon> T ::= e" \<rightleftharpoons> "CONST SVar x T (CONST Some e)"
  "VAR x \<Ztypecolon> T" \<rightleftharpoons> "CONST SVar x T (CONST None)"
  "RETURN e" \<rightleftharpoons> "CONST SReturn (CONST Some e)"
notation SRef ("(REF _ ::= _)" [1000, 21] 20)
notation SAssign (infix "::=" 20)
notation SExpr ("EVAL _" [21] 20)
notation SPrint ("PRINT _" [1000] 20)
notation SIf ("(IF _ THEN/ _/ ELSE _)" [0, 0, 20] 20)
notation SWhile ("(WHILE _ DO/ _)" [0, 20] 20)
notation SDrop ("DROP _" [1000] 20)

abbreviation return_none :: stmt ("RETURN0") where "RETURN0 \<equiv> SReturn None"

text \<open>@{text "p += e"} is sugar for @{text "p = p + e"}, as for Mojo's @{text "Int"}.\<close>

abbreviation add_assign :: "place \<Rightarrow> expr \<Rightarrow> stmt" (infix "+=" 20) where
  "p += e \<equiv> SAssign p (\<langle>p\<rangle> \<oplus> e)"

text \<open>Parameters: @{text "x \<Ztypecolon> T"} is the default (@{text "imm"}) convention.\<close>

abbreviation p_imm :: "vname \<Rightarrow> ty \<Rightarrow> conv \<times> vname \<times> ty" ("_ \<Ztypecolon>\<Ztypecolon> _" [1000, 999] 999)
  where "x \<Ztypecolon>\<Ztypecolon> T \<equiv> (Imm, x, T)"
abbreviation p_mut ("MUT _ \<Ztypecolon>\<Ztypecolon> _" [1000, 999] 999) where "MUT x \<Ztypecolon>\<Ztypecolon> T \<equiv> (Mut, x, T)"
abbreviation p_var ("OWN _ \<Ztypecolon>\<Ztypecolon> _" [1000, 999] 999) where "OWN x \<Ztypecolon>\<Ztypecolon> T \<equiv> (Var, x, T)"
abbreviation p_ref ("REFP _ \<Ztypecolon>\<Ztypecolon> _" [1000, 999] 999) where "REFP x \<Ztypecolon>\<Ztypecolon> T \<equiv> (Ref, x, T)"

text \<open>
  @{text "SELF S"}, @{text "MUTSELF S"} and @{text "OUTSELF S"} are the
  @{text "self"} parameters of methods and initializers of struct @{text "S"}.
\<close>

abbreviation SELF :: "name \<Rightarrow> conv \<times> vname \<times> ty" where "SELF S \<equiv> (Imm, ''self'', TStruct S)"
abbreviation MUTSELF :: "name \<Rightarrow> conv \<times> vname \<times> ty" where "MUTSELF S \<equiv> (Mut, ''self'', TStruct S)"
abbreviation OUTSELF :: "name \<Rightarrow> conv \<times> vname \<times> ty" where "OUTSELF S \<equiv> (Out, ''self'', TStruct S)"

section \<open>Example programs\<close>

text \<open>
  Each example is given first in Mojo, then encoded. Most examples come in
  pairs: a valid program and a near-identical invalid one, which a Mojo
  compiler rejects statically. The dynamic semantics (next theory) runs the
  valid ones and reports a run-time error for the invalid ones; the later
  well-formedness judgement is meant to rule exactly these out.

  Shared declarations: a resource whose destructor prints, so destruction
  order becomes visible in the output.
@{verbatim [display]
\<open>@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)\<close>}
\<close>

abbreviation "Res \<equiv> TStruct ''Res''"

definition res_struct :: structdecl where
  "res_struct = Struct ''Res'' [(''id'', TInt)] False True None
     (Some (PRINT [Txt ''drop'', \<langle>\<section>''self''\<bullet>''id''\<rangle>])) []"

text \<open>
@{verbatim [display]
\<open>def consume(var r: Res):
    print("got", r.id)

def bump(mut r: Res, n: Int):
    r.id += n

def pick(c: Bool, ref a: Res, ref b: Res) -> ref[a, b] Res:
    if c:
        return a
    else:
        return b\<close>}
\<close>

definition consume_fun :: fundecl where
  "consume_fun = Fun ''consume'' [OWN ''r'' \<Ztypecolon>\<Ztypecolon> Res] RNone
     (PRINT [Txt ''got'', \<langle>\<section>''r''\<bullet>''id''\<rangle>])"

definition bump_fun :: fundecl where
  "bump_fun = Fun ''bump'' [MUT ''r'' \<Ztypecolon>\<Ztypecolon> Res, ''n'' \<Ztypecolon>\<Ztypecolon> TInt] RNone
     (\<section>''r''\<bullet>''id'' += \<langle>\<section>''n''\<rangle>)"

definition pick_fun :: fundecl where
  "pick_fun = Fun ''pick'' [''c'' \<Ztypecolon>\<Ztypecolon> TBool, REFP ''a'' \<Ztypecolon>\<Ztypecolon> Res, REFP ''b'' \<Ztypecolon>\<Ztypecolon> Res]
     (RRef [''a'', ''b''] Res)
     (IF \<langle>\<section>''c''\<rangle> THEN RETURN \<langle>\<section>''a''\<rangle> ELSE RETURN \<langle>\<section>''b''\<rangle>)"

subsection \<open>Example 1: conventions, reference returns, transfer, lists\<close>

text \<open>
@{verbatim [display]
\<open>def main():
    var a = Res(1)
    var b = Res(2)
    bump(a, 10)
    ref r = pick(True, a, b)
    print(r.id)                  # 11
    consume(a^)                  # got 11 / drop 11
    var l: List[Int] = [1, 2, 3]
    ref e = l[0]
    print(e)                     # 1
    l.append(4)
                                 # drop 2 (b's destructor)\<close>}
\<close>

definition ex1_main :: stmt where
  "ex1_main =
     (VAR ''a'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[N 1]\<rbrace> ;;
     VAR ''b'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[N 2]\<rbrace> ;;
     EVAL ''bump''\<lbrace>[\<langle>\<section>''a''\<rangle>, N 10]\<rbrace> ;;
     REF ''r'' ::= ''pick''\<lbrace>[TT, \<langle>\<section>''a''\<rangle>, \<langle>\<section>''b''\<rangle>]\<rbrace> ;;
     PRINT [\<langle>\<section>''r''\<bullet>''id''\<rangle>] ;;
     EVAL ''consume''\<lbrace>[\<section>''a''\<^sup>^]\<rbrace> ;;
     VAR ''l'' \<Ztypecolon> TList TInt ::= LIST [N 1, N 2, N 3] ;;
     REF ''e'' ::= \<langle>\<section>''l''\<lbrakk>N 0\<rbrakk>\<rangle> ;;
     PRINT [\<langle>\<section>''e''\<rangle>] ;;
     EVAL \<section>''l''\<bullet>''append''\<lbrace>[N 4]\<rbrace>)"

definition ex1 :: prog where
  "ex1 = Prog [res_struct]
     [consume_fun, bump_fun, pick_fun, Fun ''main'' [] RNone ex1_main]"

text \<open>
  The same program after ASAP elaboration (written by hand for now). Note
  that @{text b} is not dropped right after its last syntactic use in
  @{text pick}: the reference @{text r} has origin @{text "[a, b]"}, so
  @{text b}'s lifetime is extended to the last use of @{text r}. The
  variable @{text a} needs no @{text DROP} since it is transferred, and the
  @{text Int} list's drop prints nothing.
\<close>

definition ex1_asap_main :: stmt where
  "ex1_asap_main =
     (VAR ''a'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[N 1]\<rbrace> ;;
     VAR ''b'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[N 2]\<rbrace> ;;
     EVAL ''bump''\<lbrace>[\<langle>\<section>''a''\<rangle>, N 10]\<rbrace> ;;
     REF ''r'' ::= ''pick''\<lbrace>[TT, \<langle>\<section>''a''\<rangle>, \<langle>\<section>''b''\<rangle>]\<rbrace> ;;
     PRINT [\<langle>\<section>''r''\<bullet>''id''\<rangle>] ;;
     DROP \<section>''b'' ;;
     EVAL ''consume''\<lbrace>[\<section>''a''\<^sup>^]\<rbrace> ;;
     VAR ''l'' \<Ztypecolon> TList TInt ::= LIST [N 1, N 2, N 3] ;;
     REF ''e'' ::= \<langle>\<section>''l''\<lbrakk>N 0\<rbrakk>\<rangle> ;;
     PRINT [\<langle>\<section>''e''\<rangle>] ;;
     EVAL \<section>''l''\<bullet>''append''\<lbrace>[N 4]\<rbrace> ;;
     DROP \<section>''l'')"

definition ex1_asap :: prog where
  "ex1_asap = Prog [res_struct]
     [consume_fun, bump_fun, pick_fun, Fun ''main'' [] RNone ex1_asap_main]"

subsection \<open>Example 2: use after transfer (invalid)\<close>

text \<open>
@{verbatim [display]
\<open>def main():
    var a = Res(1)
    consume(a^)
    print(a.id)     # error: use of uninitialized value 'a'\<close>}
\<close>

definition ex2 :: prog where
  "ex2 = Prog [res_struct] [consume_fun, Fun ''main'' [] RNone (
     VAR ''a'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[N 1]\<rbrace> ;;
     EVAL ''consume''\<lbrace>[\<section>''a''\<^sup>^]\<rbrace> ;;
     PRINT [\<langle>\<section>''a''\<bullet>''id''\<rangle>])]"

subsection \<open>Example 3: interior-origin invalidation (invalid)\<close>

text \<open>
  The Mojo 1.0 release notes' own example of interior origins:
@{verbatim [display]
\<open>def main():
    var list: List[Int] = [1, 2, 3]
    ref elem = list[0]
    list.append(4)  # may reallocate, so `elem` is invalidated
    print(elem)     # error: use of invalidated interior reference\<close>}
  together with the valid variant that only writes through the element
  reference (an item mutation, which does not invalidate).
\<close>

definition ex3 :: prog where
  "ex3 = Prog [] [Fun ''main'' [] RNone (
     VAR ''list'' \<Ztypecolon> TList TInt ::= LIST [N 1, N 2, N 3] ;;
     REF ''elem'' ::= \<langle>\<section>''list''\<lbrakk>N 0\<rbrakk>\<rangle> ;;
     EVAL \<section>''list''\<bullet>''append''\<lbrace>[N 4]\<rbrace> ;;
     PRINT [\<langle>\<section>''elem''\<rangle>])]"

definition ex3_ok :: prog where
  "ex3_ok = Prog [] [Fun ''main'' [] RNone (
     VAR ''list'' \<Ztypecolon> TList TInt ::= LIST [N 1, N 2, N 3] ;;
     REF ''elem'' ::= \<langle>\<section>''list''\<lbrakk>N 0\<rbrakk>\<rangle> ;;
     \<section>''elem'' ::= N 7 ;;
     \<section>''list''\<lbrakk>N 1\<rbrakk> += N 10 ;;
     PRINT [\<langle>\<section>''elem''\<rangle>, \<langle>\<section>''list''\<lbrakk>N 0\<rbrakk>\<rangle>, \<langle>\<section>''list''\<lbrakk>N 1\<rbrakk>\<rangle>, LEN \<section>''list''])]"

subsection \<open>Example 4: initializers and returning owned values\<close>

text \<open>
@{verbatim [display]
\<open>struct Point:
    var x: Int
    var y: Int
    def __init__(out self, a: Int):
        self.x = a
        self.y = a * 2
    def sum(self) -> Int:
        return self.x + self.y
    def scale(mut self, k: Int):
        self.x = self.x * k
        self.y = self.y * k

def make(n: Int) -> Point:
    var p = Point(n)
    return p^

def main():
    var p = make(3)
    p.scale(2)
    print(p.x, p.y, p.sum())    # 6 12 18\<close>}
  The invalid variant omits @{text "self.y = a * 2"}
  (error: field 'y' not initialized in __init__).
\<close>

abbreviation "Point \<equiv> TStruct ''Point''"

definition point_struct :: "bool \<Rightarrow> structdecl" where
  "point_struct complete = Struct ''Point'' [(''x'', TInt), (''y'', TInt)] False False
     (Some (Fun ''__init__'' [OUTSELF ''Point'', ''a'' \<Ztypecolon>\<Ztypecolon> TInt] RNone
        (\<section>''self''\<bullet>''x'' ::= \<langle>\<section>''a''\<rangle> ;;
         (if complete then \<section>''self''\<bullet>''y'' ::= \<langle>\<section>''a''\<rangle> \<otimes> N 2 else PASS))))
     None
     [Fun ''sum'' [SELF ''Point''] (RVal TInt)
        (RETURN \<langle>\<section>''self''\<bullet>''x''\<rangle> \<oplus> \<langle>\<section>''self''\<bullet>''y''\<rangle>),
      Fun ''scale'' [MUTSELF ''Point'', ''k'' \<Ztypecolon>\<Ztypecolon> TInt] RNone
        (\<section>''self''\<bullet>''x'' ::= \<langle>\<section>''self''\<bullet>''x''\<rangle> \<otimes> \<langle>\<section>''k''\<rangle> ;;
         \<section>''self''\<bullet>''y'' ::= \<langle>\<section>''self''\<bullet>''y''\<rangle> \<otimes> \<langle>\<section>''k''\<rangle>)]"

definition ex4_prog :: "bool \<Rightarrow> prog" where
  "ex4_prog complete = Prog [point_struct complete]
     [Fun ''make'' [''n'' \<Ztypecolon>\<Ztypecolon> TInt] (RVal Point)
        (VAR ''p'' \<Ztypecolon> Point ::= ''Point''\<lbrace>[\<langle>\<section>''n''\<rangle>]\<rbrace> ;; RETURN \<section>''p''\<^sup>^),
      Fun ''main'' [] RNone
        (VAR ''p'' \<Ztypecolon> Point ::= ''make''\<lbrace>[N 3]\<rbrace> ;;
         EVAL \<section>''p''\<bullet>''scale''\<lbrace>[N 2]\<rbrace> ;;
         PRINT [\<langle>\<section>''p''\<bullet>''x''\<rangle>, \<langle>\<section>''p''\<bullet>''y''\<rangle>, \<section>''p''\<bullet>''sum''\<lbrace>[]\<rbrace>])]"

definition "ex4 = ex4_prog True"
definition "ex4_bad = ex4_prog False"

subsection \<open>Example 5: block scoping in loops\<close>

text \<open>
  A variable declared in a loop body is destroyed at the end of each
  iteration.
@{verbatim [display]
\<open>def main():
    var i = 0
    while i < 3:
        var r = Res(i)
        i += 1
    print("done")       # drop 0 / drop 1 / drop 2 / done\<close>}
\<close>

definition ex5 :: prog where
  "ex5 = Prog [res_struct] [Fun ''main'' [] RNone (
     VAR ''i'' \<Ztypecolon> TInt ::= N 0 ;;
     WHILE \<langle>\<section>''i''\<rangle> \<prec> N 3 DO (
       VAR ''r'' \<Ztypecolon> Res ::= ''Res''\<lbrace>[\<langle>\<section>''i''\<rangle>]\<rbrace> ;;
       \<section>''i'' += N 1) ;;
     PRINT [Txt ''done''])]"

subsection \<open>Example 6: why argument exclusivity matters\<close>

text \<open>
  Adapted from the Mojo manual's @{text append_twice}. Mojo rejects
  @{text "append_twice(l, l)"} because @{text l} is passed both as
  @{text mut} and as an immutable reference. The dynamic semantics happily
  runs it, and the aliasing is visible in the output: the second
  @{text "len(other)"} sees the first append. With an explicit copy the
  result is the expected one. This is the hazard that Rule 2 of the region
  model (@{text mem_disjoint} for mutated region parameters) excludes.
@{verbatim [display]
\<open>def append_twice(mut l: List[Int], other: List[Int]):
    l.append(len(other))
    l.append(len(other))

def main():
    var l: List[Int] = [0]
    var m = l.copy()
    append_twice(l, m)          # l == [0, 1, 1]
    append_twice(l, l)          # rejected by Mojo; aliased: [0,1,1,3,4]
    print(l[3], l[4])\<close>}
\<close>

definition append_twice_fun :: fundecl where
  "append_twice_fun = Fun ''append_twice'' [MUT ''l'' \<Ztypecolon>\<Ztypecolon> TList TInt, ''other'' \<Ztypecolon>\<Ztypecolon> TList TInt] RNone
     (EVAL \<section>''l''\<bullet>''append''\<lbrace>[LEN \<section>''other'']\<rbrace> ;;
      EVAL \<section>''l''\<bullet>''append''\<lbrace>[LEN \<section>''other'']\<rbrace>)"

definition ex6 :: prog where
  "ex6 = Prog [] [append_twice_fun, Fun ''main'' [] RNone (
     VAR ''l'' \<Ztypecolon> TList TInt ::= LIST [N 0] ;;
     VAR ''m'' \<Ztypecolon> TList TInt ::= COPY \<section>''l'' ;;
     EVAL ''append_twice''\<lbrace>[\<langle>\<section>''l''\<rangle>, \<langle>\<section>''m''\<rangle>]\<rbrace> ;;
     PRINT [\<langle>\<section>''l''\<lbrakk>N 0\<rbrakk>\<rangle>, \<langle>\<section>''l''\<lbrakk>N 1\<rbrakk>\<rangle>, \<langle>\<section>''l''\<lbrakk>N 2\<rbrakk>\<rangle>] ;;
     EVAL ''append_twice''\<lbrace>[\<langle>\<section>''l''\<rangle>, \<langle>\<section>''l''\<rangle>]\<rbrace> ;;
     PRINT [\<langle>\<section>''l''\<lbrakk>N 3\<rbrakk>\<rangle>, \<langle>\<section>''l''\<lbrakk>N 4\<rbrakk>\<rangle>])]"

subsection \<open>Example 7: @{text mut} parameters of trivial type\<close>

text \<open>
@{verbatim [display]
\<open>def swap(mut a: Int, mut b: Int):
    var t = a
    a = b
    b = t

def main():
    var x = 1
    var y = 2
    swap(x, y)
    print(x, y)                 # 2 1\<close>}
\<close>

definition ex7 :: prog where
  "ex7 = Prog [] [
     Fun ''swap'' [MUT ''a'' \<Ztypecolon>\<Ztypecolon> TInt, MUT ''b'' \<Ztypecolon>\<Ztypecolon> TInt] RNone
       (VAR ''t'' \<Ztypecolon> TInt ::= \<langle>\<section>''a''\<rangle> ;; \<section>''a'' ::= \<langle>\<section>''b''\<rangle> ;; \<section>''b'' ::= \<langle>\<section>''t''\<rangle>),
     Fun ''main'' [] RNone
       (VAR ''x'' \<Ztypecolon> TInt ::= N 1 ;; VAR ''y'' \<Ztypecolon> TInt ::= N 2 ;;
        EVAL ''swap''\<lbrace>[\<langle>\<section>''x''\<rangle>, \<langle>\<section>''y''\<rangle>]\<rbrace> ;;
        PRINT [\<langle>\<section>''x''\<rangle>, \<langle>\<section>''y''\<rangle>])]"

end
