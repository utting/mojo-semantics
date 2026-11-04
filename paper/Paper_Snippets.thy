(*
  Paper_Snippets.thy -- fragments of the interpreter that are quoted in the
  paper, produced by antiquotations so that they follow the theory sources.
  See paper/make-snippets.sh.
*)

theory Paper_Snippets
  imports "Mojo_Semantics.Micro_Mojo_Semantics"
begin

text_raw \<open>\snip{invoke_eqn}{1}{2}{%\<close>
text \<open>@{thm [display, margin=72, show_question_marks=false] invoke.simps(2)}\<close>
text_raw \<open>}%endsnip\<close>

text_raw \<open>\snip{run_eqn}{1}{2}{%\<close>
text \<open>@{thm [display, margin=72, show_question_marks=false] run_def}\<close>
text_raw \<open>}%endsnip\<close>

end
