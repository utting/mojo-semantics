(*
  Micro_Mojo_Translation_Check.thy

  Regression test for the Python translator mojo2isabelle/mojo_translate.py:
  the programs it produces from the example *.mojo files are exactly the
  hand-written encodings of Micro_Mojo_Syntax / Micro_Mojo_Static. (The
  translator emits plain constructors, the hand-written ones use notation,
  but both denote the same terms.)
*)

theory Micro_Mojo_Translation_Check
  imports Micro_Mojo_Tests
begin

lemma "t_ex1_conventions = ex1"
  by (simp add: t_ex1_conventions_def ex1_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex2_use_after_move = ex2"
  by (simp add: t_ex2_use_after_move_def ex2_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex3_interior_invalidated = ex3"
  by (simp add: t_ex3_interior_invalidated_def ex3_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex3_interior_ok = ex3_ok"
  by (simp add: t_ex3_interior_ok_def ex3_ok_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex4_point = ex4"
  by (simp add: t_ex4_point_def ex4_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex5_loop_scope = ex5"
  by (simp add: t_ex5_loop_scope_def ex5_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex6_aliased_mut = ex6"
  by (simp add: t_ex6_aliased_mut_def ex6_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex7_swap = ex7"
  by (simp add: t_ex7_swap_def ex7_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

lemma "t_ex8_dangling_ref = ex8"
  by (simp add: t_ex8_dangling_ref_def ex8_def res_struct_def consume_fun_def bump_fun_def pick_fun_def ex1_main_def append_twice_fun_def point_struct_def ex4_prog_def)

text \<open>
  The hand-written @{text ex4_bad} ends its @{text "__init__"} with an
  explicit @{text PASS} (it is @{text "ex4_prog False"}); the translator does
  not emit @{text PASS} for an empty block, so the terms differ syntactically
  so instead of equality we check that the checker gives both the same result.
\<close>

lemma "check_prog t_ex4_point_bad_init = check_prog ex4_bad"
  by eval

end
