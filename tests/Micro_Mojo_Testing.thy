(*
  Micro_Mojo_Testing.thy

  Support for differential testing of the micro-Mojo semantics against the
  Mojo compiler. The Python tools in mojo2isabelle/ translate *.mojo programs
  into terms of type `prog`, run them with Mojo to record the observed
  behaviour, and generate a theory (Micro_Mojo_Tests.thy) with one lemma per
  test, stated with the predicates defined here and proved by `eval`.
*)

theory Micro_Mojo_Testing
  imports Mojo_Semantics.Micro_Mojo_Static
begin

section \<open>Rendering output the way Mojo prints it\<close>

text \<open>
  Mojo's @{text print} writes its arguments separated by single spaces,
  followed by a newline. @{text Int}s are printed in decimal and @{text Bool}s
  as @{text True}/@{text False}. The semantics records each printed line as a
  list of values; we render these into strings and compare against the lines
  captured from the real compiler. Comparing rendered text (rather than
  parsing the compiler's output back into values) avoids any ambiguity between
  a printed string @{text "\"1\""} and a printed integer.
\<close>

fun nat_digits :: "nat \<Rightarrow> string" where
  "nat_digits n = (if n < 10 then [char_of (48 + n)]
                   else nat_digits (n div 10) @ [char_of (48 + n mod 10)])"

definition int_str :: "int \<Rightarrow> string" where
  "int_str i = (if i < 0 then ''-'' @ nat_digits (nat (- i)) else nat_digits (nat i))"

fun render_val :: "val \<Rightarrow> string" where
  "render_val (VInt i) = int_str i"
| "render_val (VBool True) = ''True''"
| "render_val (VBool False) = ''False''"
| "render_val (VStr s) = s"
| "render_val _ = ''<unprintable>''"

fun join_sp :: "string list \<Rightarrow> string" where
  "join_sp [] = []"
| "join_sp [s] = s"
| "join_sp (s # ss) = s @ '' '' @ join_sp ss"

definition render_line :: "val list \<Rightarrow> string" where
  "render_line vs = join_sp (map render_val vs)"

lemma render_examples:
  "render_line [VStr ''drop'', VInt 11] = ''drop 11''"
  "render_line [VInt (-5), VBool True, VInt 0, VInt 123456] = ''-5 True 0 123456''"
  "render_line [] = ''''"
  by eval+

section \<open>The three kinds of test\<close>

text \<open>
  Programs are tested after ASAP elaboration (@{text elaborate}), since that
  is what makes destructor output come out in Mojo's order.

    \<^item> @{text "test_output P fuel lines"}: the checker accepts @{text P} and
      running it prints exactly @{text lines}.
    \<^item> @{text "test_compile_error P"}: the checker rejects @{text P}. (Which
      message the compiler gives is not compared.)
    \<^item> @{text "test_runtime_error P fuel"}: the checker accepts @{text P},
      but running it ends in a run-time error. In the semantics only
      @{text ErrBounds} (index out of range, pop of an empty list) corresponds
      to a failure that Mojo can have at run time.

  Running out of fuel never counts as success: pick a larger @{text fuel}.
\<close>

definition test_output :: "prog \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> bool" where
  "test_output P fuel exp =
     (check_prog P = [] \<and>
      (case run fuel (elaborate P) of
         Ok ls \<Rightarrow> map render_line ls = exp
       | _ \<Rightarrow> False))"

definition test_compile_error :: "prog \<Rightarrow> bool" where
  "test_compile_error P = (check_prog P \<noteq> [])"

definition test_runtime_error :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "test_runtime_error P fuel =
     (check_prog P = [] \<and> run fuel (elaborate P) = Err ErrBounds)"

text \<open>
  Diagnostics for a failing test: @{text "actual_output P fuel"} shows what
  the semantics does (use with @{command value}).
\<close>

definition actual_output :: "prog \<Rightarrow> nat \<Rightarrow> string list + err + unit" where
  "actual_output P fuel =
     (if check_prog P \<noteq> [] then Inr (Inr ())
      else case run fuel (elaborate P) of
             Ok ls \<Rightarrow> Inl (map render_line ls)
           | Err e \<Rightarrow> Inr (Inl e)
           | OutOfFuel \<Rightarrow> Inr (Inr ()))"

end
