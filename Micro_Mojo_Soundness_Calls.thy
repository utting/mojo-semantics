(*
  Micro_Mojo_Soundness_Calls.thy

  Soundness of the micro-Mojo checker for whole programs, with calls.
*)

theory Micro_Mojo_Soundness_Calls
  imports Micro_Mojo_Soundness_Stmt
begin

section \<open>Overview\<close>

text \<open>
  This theory removes the two restrictions of the previous ones: it covers
  calls of functions, initializers and methods, and it proves the
  specification of destruction instead of assuming it.

  \<^bold>\<open>Frames.\<close> A callee can change the caller's memory only below the
  locations of its writable parameters. Inside the callee, a statement can
  change memory only below the locations of writable variables. We state
  this with @{text "hagree W st st'"}: at every root that existed before,
  any path that is not at or below one of the locations @{text "W"} leads to
  a value with the same outermost shape (same struct and field names, same
  list generation and length, same scalar). The invariant is then restored
  by @{text "inv_chg"}, which generalizes @{text "inv_write"} from one
  written path to any set of changed locations, each holding a well-typed
  value afterwards.

  \<^bold>\<open>The induction.\<close> All functions of the interpreter are treated together,
  by induction on the fuel, with each statement quantified over all
  contexts, so that the callee's body (checked in its own context) is
  covered.

  \<^bold>\<open>Result.\<close> @{text "run_safe"}: for a program accepted by the checker
  (@{text "check_prog P = []"}), @{text "run fuel P"} never ends in an error
  other than @{text "ErrBounds"}, for any fuel. In particular there is no
  ownership error (@{text "run_no_ownership_error"}). Destruction is now
  proved (@{text "SD"}), not assumed.

  \<^bold>\<open>Checker changes made for this proof.\<close> Proving calls sound exposed
  several holes in the checker, which were fixed in
  @{text "Micro_Mojo_Static"}: places still in use while a later argument
  or index is evaluated (@{text "mroots"}, @{text "eargs"}, @{text "bargs"});
  the origin of a reference returned by a call; @{text "ref[ns]"} origins
  that are not @{text "mut"}/@{text "ref"} parameters; reference-returning
  calls used as values of non-trivial type; early @{text "return"} in an
  initializer; the receiver parameters of initializers and methods;
  duplicate field names; name clashes between functions and structs; and a
  @{text "main"} with parameters.

  \<^bold>\<open>What remains.\<close> The theorem is about programs that the checker
  accepts as written, i.e.\ with explicit @{text "SDrop"}s. The next step is
  to show that the ASAP elaboration (@{text "elab_body"}) produces programs
  that the checker accepts whenever the source is acceptable, so that
  soundness carries over to Mojo-style programs without explicit drops.
  Also open: bounds errors (which Mojo checks at run time too) and
  termination (handled here by fuel).
\<close>



section \<open>Well-formed programs\<close>

definition wf_prog :: "prog \<Rightarrow> bool" where
  "wf_prog P \<longleftrightarrow> check_prog P = []"

definition wf_fields :: "prog \<Rightarrow> bool" where
  "wf_fields P \<longleftrightarrow> (\<forall>S sd. find_struct P S = Some sd \<longrightarrow> distinct (map fst (sd_fields sd)))"

lemma find_struct_Some: "find_struct P S = Some sd \<Longrightarrow> sd \<in> set (p_structs P) \<and> sd_name sd = S"
  by (auto simp: find_struct_def find_Some_iff)

lemma find_fun_Some: "find_fun P f = Some fd \<Longrightarrow> fd \<in> set (p_funs P) \<and> fd_name fd = f"
  by (auto simp: find_fun_def find_Some_iff)

lemma find_method_Some: "find_method sd m = Some fd \<Longrightarrow> fd \<in> set (sd_methods sd) \<and> fd_name fd = m"
  by (auto simp: find_method_def find_Some_iff)

lemma report_Nil: "report loc r = [] \<longleftrightarrow> (\<exists>u. r = Good u)"
  by (cases r) (auto simp: report_def)

lemma wf_struct:
  assumes "wf_prog P" "find_struct P S = Some sd"
  shows "chk_struct P sd = []"
  using assms find_struct_Some[OF assms(2)] by (auto simp: wf_prog_def check_prog_def)

lemma wf_fun:
  assumes "wf_prog P" "find_fun P f = Some fd"
  shows "chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()"
  using assms find_fun_Some[OF assms(2)]
  by (auto simp: wf_prog_def check_prog_def chk_fun_def report_Nil)

lemma wf_fun_not_struct:
  assumes "wf_prog P" "find_fun P f = Some fd"
  shows "find_struct P f = None"
proof (rule ccontr)
  assume "find_struct P f \<noteq> None"
  then obtain sd where sd: "find_struct P f = Some sd" by blast
  have "\<not> list_ex (\<lambda>fd. list_ex (\<lambda>sd. sd_name sd = fd_name fd) (p_structs P)) (p_funs P)"
    using assms(1) by (auto simp: wf_prog_def check_prog_def split: if_splits)
  with find_struct_Some[OF sd] find_fun_Some[OF assms(2)] show False
    unfolding list_ex_iff by (metis (mono_tags, lifting))
qed

lemma case_out_param:
  "(case ps of (Out, _, T) # _ \<Rightarrow> T = U | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>sx ps'. ps = (Out, sx, U) # ps')"
proof (cases ps)
  case (Cons a ps')
  obtain c x T where "a = (c, x, T)" by (cases a)
  with Cons show ?thesis by (cases c) auto
qed simp

lemma case_self_param:
  "(case ps of (c, _, T) # _ \<Rightarrow> Q c T | [] \<Rightarrow> False) \<longleftrightarrow> (\<exists>c sx T ps'. ps = (c, sx, T) # ps' \<and> Q c T)"
  by (cases ps) auto

lemma wf_struct_facts:
  assumes "wf_prog P" "find_struct P S = Some sd"
  shows "distinct (map fst (sd_fields sd))"
    and "sd_init sd = Some fd \<Longrightarrow> fd_ret fd = RNone \<and>
           (\<exists>sx ps. fd_params fd = (Out, sx, TStruct S) # ps) \<and>
           chk_body P RNone (map fst (sd_fields sd)) (fd_params fd) (fd_body fd) = Good ()"
    and "sd_deinit sd = Some body \<Longrightarrow>
           chk_body P RNone [] [(Deinit, ''self'', TStruct S)] body = Good ()"
    and "find_method sd m = Some fd \<Longrightarrow>
           (\<exists>c sx ps. fd_params fd = (c, sx, TStruct S) # ps \<and> (c = Imm \<or> c = conv.Mut \<or> c = Ref)) \<and>
           chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()"
proof -
  have ck: "chk_struct P sd = []" using wf_struct[OF assms] .
  have nm: "sd_name sd = S" using find_struct_Some[OF assms(2)] by simp
  from ck show "distinct (map fst (sd_fields sd))"
    by (auto simp: chk_struct_def report_Nil)
  show "sd_init sd = Some fd \<Longrightarrow> fd_ret fd = RNone \<and>
           (\<exists>sx ps. fd_params fd = (Out, sx, TStruct S) # ps) \<and>
           chk_body P RNone (map fst (sd_fields sd)) (fd_params fd) (fd_body fd) = Good ()"
    using ck nm by (auto simp: chk_struct_def report_Nil case_out_param)
  show "sd_deinit sd = Some body \<Longrightarrow> chk_body P RNone [] [(Deinit, ''self'', TStruct S)] body = Good ()"
    using ck nm by (auto simp: chk_struct_def report_Nil)
  assume m: "find_method sd m = Some fd"
  then have fd: "fd \<in> set (sd_methods sd)" by (simp add: find_method_Some)
  from ck fd nm show "(\<exists>c sx ps. fd_params fd = (c, sx, TStruct S) # ps \<and> (c = Imm \<or> c = conv.Mut \<or> c = Ref)) \<and>
           chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()"
    by (auto simp: chk_struct_def report_Nil chk_fun_def list_all_iff case_self_param)
qed

lemma wf_prog_fields: "wf_prog P \<Longrightarrow> wf_fields P"
  using wf_struct_facts(1) by (auto simp: wf_fields_def)



section \<open>Changes below a set of locations\<close>

subsection \<open>Values\<close>

text \<open>
  The outermost shape of a value: its constructor, struct name and field
  names, or list generation and length. Two values agree outside a set
  @{text "Ss"} of step lists if every path that does not extend one of them
  leads to the same shape in both (or fails in both, in the same way).

  \<^bold>\<open>Decision: shapes along paths.\<close> We compare values through @{text "walk"},
  which sees only the first of two fields with the same name. This makes
  the relation insensitive to such duplicates, which the heap operations
  treat inconsistently (@{text "update_at"} updates every field of a given
  name). Well-formed programs have no duplicate field names, which we use
  when we reconstruct the type of a changed value (@{text "vagree_vt"}).
  An alternative is an inductive relation on the structure of values,
  which would have to treat duplicate fields specially.
\<close>

fun skel :: "val \<Rightarrow> val" where
  "skel (VStruct S fs) = VStruct S (map (\<lambda>(f, _). (f, VUndef)) fs)"
| "skel (VList g vs) = VList g (map (\<lambda>_. VUndef) vs)"
| "skel v = v"

definition rskel :: "val res \<Rightarrow> val res" where
  "rskel r = (case r of Ok v \<Rightarrow> Ok (skel v) | _ \<Rightarrow> r)"

definition pfx :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "pfx xs ys \<longleftrightarrow> (\<exists>us. ys = xs @ us)"

definition vagree :: "step list set \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "vagree Ss w w' \<longleftrightarrow> (\<forall>ss. (\<forall>s \<in> Ss. \<not> pfx s ss) \<longrightarrow> rskel (walk w' ss) = rskel (walk w ss))"

lemma rskel_Ok_iff: "rskel r = Ok u \<longleftrightarrow> (\<exists>v. r = Ok v \<and> u = skel v)"
  by (cases r) (auto simp: rskel_def)

lemma map_skel_fields: "map (\<lambda>(f, _). (f, VUndef)) fs = map (\<lambda>f. (f, VUndef)) (map fst fs)"
  by (induction fs) auto

lemma skel_eq_cases:
  "skel w' = skel w \<Longrightarrow> (case w of
     VStruct S fs \<Rightarrow> \<exists>fs'. w' = VStruct S fs' \<and> map fst fs' = map fst fs
   | VList g vs \<Rightarrow> \<exists>vs'. w' = VList g vs' \<and> length vs' = length vs
   | _ \<Rightarrow> w' = w)"
proof (cases w)
  case (VStruct S fs)
  moreover assume "skel w' = skel w"
  ultimately show ?thesis
    by (cases w') (auto simp: map_skel_fields comp_def dest!: arg_cong[where f="map fst"])
next
  case (VList g vs)
  moreover assume "skel w' = skel w"
  ultimately show ?thesis by (cases w') (auto dest: map_eq_imp_length_eq)
qed (cases w'; auto)+

lemma walk_Fld_Cons: "map_of fs f = Some u \<Longrightarrow> walk (VStruct S fs) (Fld f # ss) = walk u ss"
  by simp

lemma pfx_Cons: "pfx (s # ss) (t # ts) \<longleftrightarrow> s = t \<and> pfx ss ts"
  by (auto simp: pfx_def)

lemma pfx_Nil [simp]: "pfx [] ss" "pfx s [] \<longleftrightarrow> s = []"
  by (auto simp: pfx_def)

lemma vagree_root: "vagree Ss w w' \<Longrightarrow> [] \<notin> Ss \<Longrightarrow> skel w' = skel w"
  by (auto simp: vagree_def rskel_def dest!: spec[of _ "[]"])

lemma vagree_top:
  "[] \<in> Ss \<Longrightarrow> (\<forall>s \<in> Ss. \<forall>U. sty P T s = Some U \<longrightarrow> (\<exists>u. walk w' s = Ok u \<and> vt P U u)) \<Longrightarrow>
   vt P T w'"
  by fastforce

lemma vagree_scalar:
  "vagree Ss w w' \<Longrightarrow> vt P T w \<Longrightarrow>
   (\<forall>s \<in> Ss. \<forall>U. sty P T s = Some U \<longrightarrow> (\<exists>u. walk w' s = Ok u \<and> vt P U u)) \<Longrightarrow>
   (\<forall>S fs. w \<noteq> VStruct S fs) \<Longrightarrow> (\<forall>g vs. w \<noteq> VList g vs) \<Longrightarrow> vt P T w'"
proof (cases "[] \<in> Ss")
  case False
  assume "vagree Ss w w'" "vt P T w" "\<forall>S fs. w \<noteq> VStruct S fs" "\<forall>g vs. w \<noteq> VList g vs"
  with vagree_root[OF _ False] have "skel w' = skel w" by metis
  with \<open>vt P T w\<close> \<open>\<forall>S fs. w \<noteq> VStruct S fs\<close> \<open>\<forall>g vs. w \<noteq> VList g vs\<close> show ?thesis
    by (cases w'; cases w) auto
qed (blast intro: vagree_top)

lemma vagree_child:
  assumes "vagree Ss w w'" "[] \<notin> Ss"
    "\<And>ss. walk w (st # ss) = walk u ss" "\<And>ss. walk w' (st # ss) = walk u' ss"
  shows "vagree {s. st # s \<in> Ss} u u'"
  unfolding vagree_def
proof (intro allI impI)
  fix ss assume h: "\<forall>s \<in> {s. st # s \<in> Ss}. \<not> pfx s ss"
  have "\<forall>s \<in> Ss. \<not> pfx s (st # ss)"
  proof
    fix s assume s: "s \<in> Ss"
    show "\<not> pfx s (st # ss)"
    proof (cases s)
      case Nil with s assms(2) show ?thesis by simp
    next
      case (Cons t s') with s h show ?thesis by (auto simp: pfx_Cons)
    qed
  qed
  with assms(1) have "rskel (walk w' (st # ss)) = rskel (walk w (st # ss))"
    by (simp add: vagree_def)
  with assms(3,4) show "rskel (walk u' ss) = rskel (walk u ss)" by simp
qed

lemma vagree_vt:
  assumes wf: "wf_fields P"
  shows "vagree Ss w w' \<Longrightarrow> vt P T w \<Longrightarrow>
    (\<forall>s \<in> Ss. \<forall>U. sty P T s = Some U \<longrightarrow> (\<exists>u. walk w' s = Ok u \<and> vt P U u)) \<Longrightarrow> vt P T w'"
proof (induction w arbitrary: T Ss w')
  case (VStruct S fs)
  show ?case
  proof (cases "[] \<in> Ss")
    case True
    with VStruct.prems(3) show ?thesis by fastforce
  next
    case False
    with VStruct.prems(1) have "skel w' = skel (VStruct S fs)" by (rule vagree_root)
    from skel_eq_cases[OF this] obtain fs' where w': "w' = VStruct S fs'" and nm: "map fst fs' = map fst fs"
      by auto
    from VStruct.prems(2) obtain sd where T: "T = TStruct S" and sd: "find_struct P S = Some sd"
      and names: "map fst fs = map fst (sd_fields sd)"
      and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u"
      by auto
    have dist: "distinct (map fst fs')" using wf sd nm names by (simp add: wf_fields_def)
    have "\<forall>(f, u') \<in> set fs'. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u'"
    proof (intro ballI, clarify)
      fix f u' assume fu': "(f, u') \<in> set fs'"
      have mu': "map_of fs' f = Some u'" using map_of_distinct_mem[OF dist fu'] .
      have "f \<in> fst ` set fs" using fu' nm by (metis fst_conv image_eqI list.set_map)
      then obtain u where mu: "map_of fs f = Some u"
        by (meson map_of_eq_None_iff not_Some_eq)
      then have fu: "(f, u) \<in> set fs" by (rule map_of_SomeD)
      with fs obtain U where U: "map_of (sd_fields sd) f = Some U" "vt P U u" by blast
      have ft: "field_ty P S f = Good U" using sd U(1) by (simp add: field_ty_def)
      have ag: "vagree {s. Fld f # s \<in> Ss} u u'"
        by (rule vagree_child[OF VStruct.prems(1) False]) (simp_all add: mu mu' w')
      have "vt P U u'"
      proof (rule VStruct.IH[OF fu _ ag U(2)])
        show "u \<in> Basic_BNFs.snds (f, u)" by simp
        show "\<forall>s \<in> {s. Fld f # s \<in> Ss}. \<forall>U'. sty P U s = Some U' \<longrightarrow> (\<exists>x. walk u' s = Ok x \<and> vt P U' x)"
          using VStruct.prems(3) T ft mu' w' by fastforce
      qed
      with U(1) show "\<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u'" by blast
    qed
    with T sd nm names w' show ?thesis by simp
  qed
next
  case (VList g vs)
  show ?case
  proof (cases "[] \<in> Ss")
    case True
    with VList.prems(3) show ?thesis by fastforce
  next
    case False
    with VList.prems(1) have "skel w' = skel (VList g vs)" by (rule vagree_root)
    from skel_eq_cases[OF this] obtain vs' where w': "w' = VList g vs'" and len: "length vs' = length vs"
      by auto
    from VList.prems(2) obtain U where T: "T = TList U" and vs: "\<forall>u \<in> set vs. vt P U u" by auto
    have "\<forall>u' \<in> set vs'. vt P U u'"
    proof
      fix u' assume "u' \<in> set vs'"
      then obtain i where i: "i < length vs'" "u' = vs' ! i" by (auto simp: in_set_conv_nth)
      have mem: "vs ! i \<in> set vs" using i len by simp
      have ag: "vagree {s. Idx i g # s \<in> Ss} (vs ! i) (vs' ! i)"
        by (rule vagree_child[OF VList.prems(1) False]) (use i len w' in simp_all)
      show "vt P U u'"
        unfolding i(2)
      proof (rule VList.IH[OF mem ag])
        show "vt P U (vs ! i)" using vs mem by blast
        show "\<forall>s \<in> {s. Idx i g # s \<in> Ss}. \<forall>U'. sty P U s = Some U' \<longrightarrow>
                (\<exists>x. walk (vs' ! i) s = Ok x \<and> vt P U' x)"
          using VList.prems(3) T i w' by fastforce
      qed
    qed
    with T w' show ?thesis by simp
  qed
qed (rule vagree_scalar, assumption+, simp, simp)+

subsection \<open>Heaps\<close>

text \<open>
  @{text "hagree W st st'"}: the roots below @{text "nroot st"} that contain
  no location of @{text "W"} are unchanged, and in the others every path that
  is not at or below a location of @{text "W"} leads to the same shape.
\<close>

definition hagree :: "path set \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "hagree W st st' \<longleftrightarrow> (\<forall>r < nroot st. r \<notin> fst ` W \<longrightarrow> heap st' r = heap st r) \<and>
     (\<forall>p. fst p < nroot st \<longrightarrow> (\<forall>q \<in> W. \<not> below p q) \<longrightarrow> rskel (get st' p) = rskel (get st p))"

lemma hagree_refl [simp]: "hagree W st st"
  by (simp add: hagree_def)

lemma hagreeD1: "hagree W st st' \<Longrightarrow> r < nroot st \<Longrightarrow> r \<notin> fst ` W \<Longrightarrow> heap st' r = heap st r"
  unfolding hagree_def by blast

lemma hagreeD2:
  "hagree W st st' \<Longrightarrow> fst p < nroot st \<Longrightarrow> \<forall>q \<in> W. \<not> below p q \<Longrightarrow> rskel (get st' p) = rskel (get st p)"
  unfolding hagree_def by blast

lemma hagree_trans:
  assumes "hagree W1 st st1" "hagree W2 st1 st2" "nroot st \<le> nroot st1"
  shows "hagree (W1 \<union> W2) st st2"
  unfolding hagree_def
proof (intro conjI allI impI)
  fix r assume "r < nroot st" "r \<notin> fst ` (W1 \<union> W2)"
  with assms show "heap st2 r = heap st r" using hagreeD1 by (metis Un_iff image_Un less_le_trans)
next
  fix p assume "fst p < nroot st" "\<forall>q \<in> W1 \<union> W2. \<not> below p q"
  with assms show "rskel (get st2 p) = rskel (get st p)" using hagreeD2 by (metis Un_iff less_le_trans)
qed

lemma hagree_mono:
  assumes "hagree W st st'" "\<forall>q \<in> W. \<exists>q' \<in> W'. below q q'"
  shows "hagree W' st st'"
  unfolding hagree_def
proof (intro conjI allI impI)
  fix r assume r: "r < nroot st" "r \<notin> fst ` W'"
  have "r \<notin> fst ` W"
  proof
    assume "r \<in> fst ` W"
    then obtain q where "q \<in> W" "fst q = r" by blast
    with assms(2) obtain q' where "q' \<in> W'" "below q q'" by blast
    with \<open>fst q = r\<close> r(2) show False by (auto simp: below_def)
  qed
  with assms(1) r(1) show "heap st' r = heap st r" by (simp add: hagree_def)
next
  fix p assume p: "fst p < nroot st" "\<forall>q \<in> W'. \<not> below p q"
  have "\<forall>q \<in> W. \<not> below p q" using p(2) assms(2) below_trans by blast
  with assms(1) p(1) show "rskel (get st' p) = rskel (get st p)" by (rule hagreeD2)
qed

lemma hagree_heap:
  "(\<forall>r < nroot st. heap st' r = heap st r) \<Longrightarrow> hagree W st st'"
  unfolding hagree_def by (metis get_root_cong)

lemma map_replicate_undef: "map (\<lambda>_. VUndef) xs = replicate (length xs) VUndef"
  by (induction xs) auto

lemma skel_update: "update_at u (s # rs) v = Ok u' \<Longrightarrow> skel u' = skel u"
  by (cases u; cases s)
     (auto simp: bind_res_Ok_iff map_skel_fields map_replicate_undef split: option.splits if_splits)

lemma hagree_put:
  assumes "put st q v = Ok st'"
  shows "hagree {q} st st'"
proof -
  from assms obtain w w' where w: "heap st (fst q) = Some w" "update_at w (snd q) v = Ok w'"
    and st': "st' = st\<lparr>heap := (heap st)(fst q := Some w')\<rparr>"
    by (auto simp: put_def bind_res_Ok_iff split: option.splits)
  show ?thesis
    unfolding hagree_def
  proof (intro conjI allI impI)
    fix r assume "r < nroot st" "r \<notin> fst ` {q}"
    with st' show "heap st' r = heap st r" by auto
  next
    fix p assume "fst p < nroot st" "\<forall>q' \<in> {q}. \<not> below p q'"
    then have nb: "\<not> below p q" by simp
    show "rskel (get st' p) = rskel (get st p)"
    proof (cases "fst p = fst q")
      case False
      with st' show ?thesis by (simp add: get_def)
    next
      case True
      with nb have np: "\<not> (\<exists>us. snd p = snd q @ us)" by (auto simp: below_def)
      have gp: "get st' p = walk w' (snd p)" "get st p = walk w (snd p)"
        using True st' w(1) by (simp_all add: get_def)
      show ?thesis
      proof (cases "\<exists>rs. snd q = snd p @ rs")
        case True
        then obtain rs where rs: "snd q = snd p @ rs" by blast
        with np obtain s rs' where rs': "rs = s # rs'" by (cases rs) auto
        from update_walk_ok[OF w(2)] obtain u0 where "walk w (snd q) = Ok u0" by blast
        with rs obtain u where u: "walk w (snd p) = Ok u"
          by (auto simp: walk_append bind_res_Ok_iff)
        from walk_update_prefix[OF w(2)[unfolded rs] u] obtain u' where
          u': "walk w' (snd p) = Ok u'" "update_at u rs v = Ok u'" by blast
        have "skel u' = skel u" using skel_update u'(2) rs' by simp
        with u u' gp show ?thesis by (simp add: rskel_def)
      next
        case False
        with np have "walk w' (snd p) = walk w (snd p)"
          by (intro walk_update_disjoint[OF w(2)]) auto
        with gp show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  A location with no changed location at or above it holds a value that
  agrees with the old one outside the changed locations below it, and so
  keeps its type if those hold values of the right types.
\<close>

lemma hagree_vagree:
  assumes ag: "hagree W st st'" and p: "fst p < nroot st" "\<forall>q \<in> W. \<not> below p q"
    and g: "get st p = Ok v"
  shows "\<exists>v'. get st' p = Ok v' \<and> vagree {s. pext p s \<in> W} v v'"
proof -
  have r: "rskel (get st' p) = rskel (get st p)" using ag p by (rule hagreeD2)
  with g obtain v' where g': "get st' p = Ok v'" by (auto simp: rskel_def split: res.splits)
  have "vagree {s. pext p s \<in> W} v v'"
    unfolding vagree_def
  proof (intro allI impI)
    fix ss assume ss: "\<forall>s \<in> {s. pext p s \<in> W}. \<not> pfx s ss"
    have "\<forall>q \<in> W. \<not> below (pext p ss) q"
    proof (intro ballI notI)
      fix q assume q: "q \<in> W" "below (pext p ss) q"
      then obtain us where fq: "fst q = fst p" and e: "snd p @ ss = snd q @ us"
        by (auto simp: below_def pext_def)
      from append_prefix_cases[OF e] show False
      proof
        assume "\<exists>t. snd q = snd p @ t"
        then obtain t where t: "snd q = snd p @ t" by blast
        then have "q = pext p t" using fq by (cases q) (simp add: pext_def)
        with q(1) ss have "\<not> pfx t ss" by blast
        with e t show False by (auto simp: pfx_def)
      next
        assume "\<exists>t. snd p = snd q @ t"
        with fq p(2) q(1) show False by (auto simp: below_def)
      qed
    qed
    with ag p(1) have "rskel (get st' (pext p ss)) = rskel (get st (pext p ss))"
      by (intro hagreeD2) simp_all
    with g g' show "rskel (walk v' ss) = rskel (walk v ss)" by (simp add: get_pext)
  qed
  with g' show ?thesis by blast
qed

lemma hagree_typed:
  assumes wf: "wf_fields P" and ag: "hagree W st st'" and p: "fst p < nroot st" "\<forall>q \<in> W. \<not> below p q"
    and g: "get st p = Ok v" "vt P T v"
    and Wty: "\<And>s U. pext p s \<in> W \<Longrightarrow> sty P T s = Some U \<Longrightarrow> \<exists>u. get st' (pext p s) = Ok u \<and> vt P U u"
  shows "\<exists>v'. get st' p = Ok v' \<and> vt P T v'"
proof -
  from hagree_vagree[OF ag p g(1)] obtain v' where v': "get st' p = Ok v'"
    and va: "vagree {s. pext p s \<in> W} v v'" by blast
  have "vt P T v'"
  proof (rule vagree_vt[OF wf va g(2)], intro ballI allI impI)
    fix s U assume "s \<in> {s. pext p s \<in> W}" "sty P T s = Some U"
    with Wty obtain u where "get st' (pext p s) = Ok u" "vt P U u" by blast
    with v' show "\<exists>u. walk v' s = Ok u \<and> vt P U u" by (simp add: get_pext)
  qed
  with v' show ?thesis by blast
qed

text \<open>
  The same, restricted to the roots in a set @{text "R"}. A callee also
  changes its own roots, which the caller does not see.
\<close>

definition hagree_on :: "nat set \<Rightarrow> path set \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "hagree_on R W st st' \<longleftrightarrow> (\<forall>p. fst p \<in> R \<longrightarrow> fst p < nroot st \<longrightarrow> (\<forall>q \<in> W. \<not> below p q) \<longrightarrow>
     rskel (get st' p) = rskel (get st p))"

lemma hagree_onD:
  "hagree_on R W st st' \<Longrightarrow> fst p \<in> R \<Longrightarrow> fst p < nroot st \<Longrightarrow> \<forall>q \<in> W. \<not> below p q \<Longrightarrow>
   rskel (get st' p) = rskel (get st p)"
  unfolding hagree_on_def by blast

lemma hagree_on_hagree: "hagree W st st' \<Longrightarrow> hagree_on R W st st'"
  by (simp add: hagree_on_def hagreeD2)

lemma hagree_on_union:
  assumes "hagree (W \<union> Wf) st st'" "\<forall>q \<in> Wf. fst q \<notin> R"
  shows "hagree_on R W st st'"
  unfolding hagree_on_def
proof (intro allI impI)
  fix p assume p: "fst p \<in> R" "fst p < nroot st" "\<forall>q \<in> W. \<not> below p q"
  have "\<forall>q \<in> W \<union> Wf. \<not> below p q" using p assms(2) by (auto simp: below_def)
  with assms(1) p(2) show "rskel (get st' p) = rskel (get st p)" by (rule hagreeD2)
qed

lemma hagree_vagree_on:
  assumes ag: "hagree_on R W st st'" and p: "fst p \<in> R" "fst p < nroot st" "\<forall>q \<in> W. \<not> below p q"
    and g: "get st p = Ok v"
  shows "\<exists>v'. get st' p = Ok v' \<and> vagree {s. pext p s \<in> W} v v'"
proof -
  have r: "rskel (get st' p) = rskel (get st p)" using hagree_onD[OF ag p] .
  with g obtain v' where g': "get st' p = Ok v'" by (auto simp: rskel_def split: res.splits)
  have "vagree {s. pext p s \<in> W} v v'"
    unfolding vagree_def
  proof (intro allI impI)
    fix ss assume ss: "\<forall>s \<in> {s. pext p s \<in> W}. \<not> pfx s ss"
    have "\<forall>q \<in> W. \<not> below (pext p ss) q"
    proof (intro ballI notI)
      fix q assume q: "q \<in> W" "below (pext p ss) q"
      then obtain us where fq: "fst q = fst p" and e: "snd p @ ss = snd q @ us"
        by (auto simp: below_def pext_def)
      from append_prefix_cases[OF e] show False
      proof
        assume "\<exists>t. snd q = snd p @ t"
        then obtain t where t: "snd q = snd p @ t" by blast
        then have "q = pext p t" using fq by (cases q) (simp add: pext_def)
        with q(1) ss have "\<not> pfx t ss" by blast
        with e t show False by (auto simp: pfx_def)
      next
        assume "\<exists>t. snd p = snd q @ t"
        with fq p(3) q(1) show False by (auto simp: below_def)
      qed
    qed
    with ag p(1,2) have "rskel (get st' (pext p ss)) = rskel (get st (pext p ss))"
      by (intro hagree_onD) simp_all
    with g g' show "rskel (walk v' ss) = rskel (walk v ss)" by (simp add: get_pext)
  qed
  with g' show ?thesis by blast
qed

lemma hagree_typed_on:
  assumes wf: "wf_fields P" and ag: "hagree_on R W st st'" and p: "fst p \<in> R" "fst p < nroot st"
    "\<forall>q \<in> W. \<not> below p q"
    and g: "get st p = Ok v" "vt P T v"
    and Wty: "\<And>s U. pext p s \<in> W \<Longrightarrow> sty P T s = Some U \<Longrightarrow> \<exists>u. get st' (pext p s) = Ok u \<and> vt P U u"
  shows "\<exists>v'. get st' p = Ok v' \<and> vt P T v'"
proof -
  from hagree_vagree_on[OF ag p g(1)] obtain v' where v': "get st' p = Ok v'"
    and va: "vagree {s. pext p s \<in> W} v v'" by blast
  have "vt P T v'"
  proof (rule vagree_vt[OF wf va g(2)], intro ballI allI impI)
    fix s U assume "s \<in> {s. pext p s \<in> W}" "sty P T s = Some U"
    with Wty obtain u where "get st' (pext p s) = Ok u" "vt P U u" by blast
    with v' show "\<exists>u. walk v' s = Ok u \<and> vt P U u" by (simp add: get_pext)
  qed
  with v' show ?thesis by blast
qed

definition envroots :: "env \<Rightarrow> nat set" where
  "envroots env = {fst (bpath b) | x b. map_of env x = Some b}"

lemma envroots_I: "map_of env x = Some b \<Longrightarrow> fst (bpath b) \<in> envroots env"
  by (auto simp: envroots_def)



section \<open>Changes preserve the invariant\<close>

text \<open>
  A changed location must lie below a writable variable, have a well-typed
  value afterwards, and, if its type is not trivial, the references into
  the interior of its variable must be invalidated.
\<close>

definition wtarget :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> astate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> path \<Rightarrow> bool" where
  "wtarget P \<Gamma> env \<sigma> st st' q \<longleftrightarrow> (\<exists>z kz bz ss T. map_of \<Gamma> z = Some kz \<and> writable kz \<and>
     map_of env z = Some bz \<and> q = pext (bpath bz) ss \<and> sty P (kind_ty kz) ss = Some T \<and>
     (\<exists>u. get st q = Ok u) \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
     (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> {z} \<subseteq> a_inval \<sigma>))"

lemma below_common: "below a c \<Longrightarrow> below a d \<Longrightarrow> overlaps c d"
  unfolding below_def overlaps_def by (metis append_prefix_cases)

lemma excl_same_base:
  assumes "excl \<Gamma> env" "map_of \<Gamma> z = Some kz" "writable kz" "map_of env z = Some bz"
    "map_of \<Gamma> y = Some ky" "\<not> is_ref ky" "map_of env y = Some by"
    "below a (bpath bz)" "below a (bpath by)"
  shows "z = y"
  using excl_D[OF assms(1-7)] below_common[OF assms(8,9)] by blast

lemma pext_eq_pext: "pext q ss = pext q ts \<Longrightarrow> ss = ts"
  by (simp add: pext_def)

lemma below_pext_iff: "below a q \<longleftrightarrow> (\<exists>s. a = pext q s)"
  by (cases a; cases q) (auto simp: below_def pext_def)

text \<open>The changed locations that meet the location of a non-reference variable lie below it.\<close>

lemma wtarget_meets:
  assumes excl: "excl \<Gamma> env" and W: "wtarget P \<Gamma> env \<sigma> st st' q"
    and y: "map_of \<Gamma> y = Some ky" "\<not> is_ref ky" "map_of env y = Some by"
    and m: "below q (bpath by) \<or> below (bpath by) q"
  shows "\<exists>ss T. q = pext (bpath by) ss \<and> sty P (kind_ty ky) ss = Some T \<and>
           (\<exists>u. get st q = Ok u) \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
           (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> {y} \<subseteq> a_inval \<sigma>)"
proof -
  from W obtain z kz bz ss T where z: "map_of \<Gamma> z = Some kz" "writable kz" "map_of env z = Some bz"
    and q: "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T" "\<exists>u. get st q = Ok u"
      "\<exists>v. get st' q = Ok v \<and> vt P T v" "\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> {z} \<subseteq> a_inval \<sigma>"
    unfolding wtarget_def by blast
  have "below q (bpath bz)" using q(1) by simp
  have "z = y"
  proof (cases "below q (bpath by)")
    case True
    show ?thesis by (rule excl_same_base[OF excl z y \<open>below q (bpath bz)\<close> True])
  next
    case False
    with m have b: "below (bpath by) q" by simp
    show ?thesis
      by (rule excl_same_base[OF excl z y below_trans[OF b \<open>below q (bpath bz)\<close>] below_refl])
  qed
  with z y q show ?thesis by auto
qed

lemma wtarget_above:
  assumes excl: "excl \<Gamma> env" and W: "wtarget P \<Gamma> env \<sigma> st st' q"
    and y: "map_of \<Gamma> y = Some ky" "\<not> is_ref ky" "map_of env y = Some by"
    and m: "below (bpath by) q"
  shows "q = bpath by \<and> (\<exists>v. get st' q = Ok v \<and> vt P (kind_ty ky) v)"
proof -
  from wtarget_meets[OF excl W y] m obtain ss T where q: "q = pext (bpath by) ss"
    "sty P (kind_ty ky) ss = Some T" "\<exists>v. get st' q = Ok v \<and> vt P T v" by blast
  from m q(1) have "ss = []" by (cases "bpath by") (auto simp: below_def pext_def)
  with q show ?thesis by simp
qed

text \<open>
  The value of @{text "out self"} keeps its form when its fields change
  below locations that hold well-typed values afterwards.
\<close>

lemma out_val_vagree:
  assumes wf: "wf_fields P" and ov: "out_val P C \<sigma> T v" and cf: "c_fields C \<noteq> []"
    and va: "vagree Ss v v'" and nil: "[] \<notin> Ss"
    and new: "\<forall>s \<in> Ss. \<forall>U. sty P T s = Some U \<longrightarrow> (\<exists>u. walk v' s = Ok u \<and> vt P U u)"
    and old: "\<forall>s \<in> Ss. \<exists>u. walk v s = Ok u"
    and fl: "\<forall>f. f \<in> a_fields \<sigma>' \<longrightarrow> f \<notin> a_fields \<sigma> \<longrightarrow> [Fld f] \<in> Ss"
  shows "out_val P C \<sigma>' T v'"
proof -
  from ov cf obtain S sd fs where T: "T = TStruct S" and sd: "find_struct P S = Some sd"
    and c: "c_fields C = map fst (sd_fields sd)" and v: "v = VStruct S fs"
    and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                                   (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)"
    by (auto simp: out_val_def)
  from vagree_root[OF va nil] v obtain fs' where v': "v' = VStruct S fs'" and nm: "map fst fs' = map fst fs"
    using skel_eq_cases by fastforce
  have dist: "distinct (map fst fs')" using wf sd nm names by (simp add: wf_fields_def)
  have "\<forall>(f, u') \<in> set fs'. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u' \<and>
                                (f \<in> a_fields \<sigma>' \<longrightarrow> vt P U u')"
  proof (intro ballI, clarify)
    fix f u' assume fu': "(f, u') \<in> set fs'"
    have mu': "map_of fs' f = Some u'" using map_of_distinct_mem[OF dist fu'] .
    have "f \<in> fst ` set fs" using fu' nm by (metis fst_conv image_eqI list.set_map)
    then obtain u where mu: "map_of fs f = Some u" by (meson map_of_eq_None_iff not_Some_eq)
    then have fu: "(f, u) \<in> set fs" by (rule map_of_SomeD)
    with fs obtain U where U: "map_of (sd_fields sd) f = Some U" "wt_opt P U u"
      "f \<in> a_fields \<sigma> \<longrightarrow> vt P U u" by blast
    have ft: "field_ty P S f = Good U" using sd U(1) by (simp add: field_ty_def)
    have ag: "vagree {s. Fld f # s \<in> Ss} u u'"
      by (rule vagree_child[OF va nil]) (simp_all add: mu mu' v v')
    have newf: "\<forall>s \<in> {s. Fld f # s \<in> Ss}. \<forall>U'. sty P U s = Some U' \<longrightarrow> (\<exists>x. walk u' s = Ok x \<and> vt P U' x)"
      using new T ft mu' v' by fastforce
    have "wt_opt P U u' \<and> (f \<in> a_fields \<sigma>' \<longrightarrow> vt P U u')"
    proof (cases "[Fld f] \<in> Ss")
      case True
      with newf have "vt P U u'" by fastforce
      then show ?thesis by (simp add: wt_opt_def)
    next
      case False
      then have nil': "[] \<notin> {s. Fld f # s \<in> Ss}" by simp
      show ?thesis
      proof (cases "u = VUndef")
        case True
        have "{s. Fld f # s \<in> Ss} = {}"
        proof (rule ccontr)
          assume "{s. Fld f # s \<in> Ss} \<noteq> {}"
          then obtain s where s: "Fld f # s \<in> Ss" by blast
          with nil' have "s \<noteq> []" by auto
          with old s mu v True show False by (cases s) auto
        qed
        with ag True have "u' = VUndef" using vagree_root[OF ag] by (cases u') auto
        moreover have "f \<notin> a_fields \<sigma>'" using fl False U(3) True by auto
        ultimately show ?thesis by (simp add: wt_opt_def)
      next
        case False
        with U(2) have "vt P U u" by (simp add: wt_opt_def)
        from vagree_vt[OF wf ag this newf] show ?thesis by (simp add: wt_opt_def)
      qed
    qed
    with U(1) show "\<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u' \<and> (f \<in> a_fields \<sigma>' \<longrightarrow> vt P U u')"
      by blast
  qed
  moreover have "sd_fields sd \<noteq> []" using cf c by auto
  ultimately show ?thesis using T sd c v' nm names by (simp add: out_val_def cf)
qed

lemma skel_undef [simp]: "skel v = VUndef \<longleftrightarrow> v = VUndef"
  by (cases v) auto

lemma vt_out_val:
  "vt P T v' \<Longrightarrow> out_val P C \<sigma> T v \<Longrightarrow> out_val P C \<sigma>' T v'"
  by (cases "c_fields C = []"; cases v') (auto simp: out_val_def wt_opt_def; fastforce)+

text \<open>
  \<^bold>\<open>The change lemma.\<close> If the heap changed only below locations that
  satisfy @{text "wtarget"} (and in fresh roots), the invariant holds again
  for an abstract state @{text "\<sigma>'"} that invalidates at least as much and
  initializes only variables and fields of @{text "out self"} whose
  locations were among the changed ones. This covers assignment (one
  location), calls (the locations of the mutably borrowed arguments) and
  list mutations.

  For a non-reference variable, exclusivity makes every changed location
  that meets its location lie below it, so its new value is either one of
  the changed values or is reconstructed by @{text "vagree_vt"}. For a
  reference, the changed locations that meet its path have the same base
  variable; one above the path is reached through fields only (or the
  reference is invalidated), and the others lie below it.
\<close>

lemma inv_chg:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and wf: "wf_fields P"
    and ag: "hagree_on (envroots env) W st st'" and nr: "nroot st \<le> nroot st'" "heap_fresh st'"
    and W: "\<forall>q \<in> W. wtarget P \<Gamma> env \<sigma>' st st' q"
    and inval: "a_inval \<sigma> \<subseteq> a_inval \<sigma>'"
    and init: "\<forall>y. y \<in> a_init \<sigma>' \<longrightarrow> y \<notin> a_init \<sigma> \<longrightarrow> (\<exists>r. map_of env y = Some (Own r) \<and> (r, []) \<in> W)"
    and flds: "\<forall>f. f \<in> a_fields \<sigma>' \<longrightarrow> f \<notin> a_fields \<sigma> \<longrightarrow>
                 (\<forall>s T b. map_of \<Gamma> s = Some (KBorrow Out T) \<longrightarrow> map_of env s = Some b \<longrightarrow>
                    ext (bpath b) (Fld f) \<in> W)"
  shows "inv P C \<Gamma> \<sigma>' env st'"
proof -
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have bounds: "\<And>x b. map_of env x = Some b \<Longrightarrow> fst (bpath b) < nroot st"
    using inv by (simp add: inv_def)
  text \<open>The value at the location of a non-reference variable.\<close>
  have nonref: "\<exists>v'. get st' (bpath b) = Ok v' \<and> vt P (kind_ty k) v'"
    if y: "map_of \<Gamma> y = Some k" "\<not> is_ref k" "map_of env y = Some b"
      and g: "get st (bpath b) = Ok v" "vt P (kind_ty k) v" for y k b v
  proof (cases "bpath b \<in> W")
    case True
    from wtarget_above[OF excl W[rule_format, OF True] y] show ?thesis by simp
  next
    case False
    have na: "\<forall>q \<in> W. \<not> below (bpath b) q"
      using wtarget_above[OF excl W[rule_format] y] False by blast
    show ?thesis
    proof (rule hagree_typed_on[OF wf ag envroots_I[OF y(3)] bounds[OF y(3)] na g])
      fix s U assume s: "pext (bpath b) s \<in> W" "sty P (kind_ty k) s = Some U"
      from wtarget_meets[OF excl W[rule_format, OF s(1)] y] s(2)
      show "\<exists>u. get st' (pext (bpath b) s) = Ok u \<and> vt P U u"
        by (auto dest: pext_eq_pext)
    qed
  qed
  text \<open>A location with a changed location strictly below it held a proper value.\<close>
  have notundef: "v \<noteq> VUndef"
    if y: "map_of \<Gamma> y = Some k" "\<not> is_ref k" "map_of env y = Some b"
      and g: "get st (bpath b) = Ok v" and q: "q \<in> W" "below q (bpath b)" "q \<noteq> bpath b" for y k b v q
  proof
    assume u: "v = VUndef"
    from wtarget_meets[OF excl W[rule_format, OF q(1)] y] q(2) obtain ss where
      ss: "q = pext (bpath b) ss" "\<exists>u. get st q = Ok u" by blast
    with q(3) obtain s ss' where "ss = s # ss'" by (cases ss) auto
    with ss g u show False by (auto simp: get_pext)
  qed
  text \<open>No changed location at or below the location: the shape is kept.\<close>
  have same: "rskel (get st' (bpath b)) = rskel (get st (bpath b))"
    if y: "map_of \<Gamma> y = Some k" "\<not> is_ref k" "map_of env y = Some b"
      and nW: "bpath b \<notin> W" for y k b
  proof (rule hagree_onD[OF ag envroots_I[OF y(3)] bounds[OF y(3)]])
    show "\<forall>q \<in> W. \<not> below (bpath b) q"
      using wtarget_above[OF excl W[rule_format] y] nW by blast
  qed
  have bind: "binding_ok P C \<Gamma> \<sigma>' env st' x k b"
    if xk: "map_of \<Gamma> x = Some k" and xb: "map_of env x = Some b"
      and old: "binding_ok P C \<Gamma> \<sigma> env st x k b" for x k b
  proof (cases k)
    case (KOwned T)
    with old obtain r v where b: "b = Own r" and hv: "heap st r = Some v"
      and vv: "if x \<in> a_init \<sigma> then vt P T v else wt_opt P T v" by auto
    have nr0: "\<not> is_ref k" using KOwned by simp
    have g: "get st (bpath b) = Ok v" using b hv by (simp add: get_def)
    have "\<exists>v'. heap st' r = Some v' \<and> (if x \<in> a_init \<sigma>' then vt P T v' else wt_opt P T v')"
    proof (cases "v = VUndef")
      case False
      with vv have "vt P T v" by (auto simp: wt_opt_def split: if_splits)
      from nonref[OF xk nr0 xb g] this KOwned obtain v' where "get st' (bpath b) = Ok v'" "vt P T v'"
        by auto
      with b show ?thesis by (auto simp: get_def wt_opt_def split: option.splits)
    next
      case True
      show ?thesis
      proof (cases "bpath b \<in> W")
        case inW: True
        from wtarget_above[OF excl W[rule_format, OF inW] xk nr0 xb] KOwned b obtain v' where
          "get st' (r, []) = Ok v'" "vt P T v'" by auto
        then show ?thesis by (auto simp: get_def wt_opt_def split: option.splits)
      next
        case nW: False
        from same[OF xk nr0 xb nW] g True have "rskel (get st' (bpath b)) = Ok VUndef"
          by (simp add: rskel_def)
        then have "get st' (bpath b) = Ok VUndef" by (auto simp: rskel_Ok_iff eq_commute[of VUndef])
        moreover have "x \<notin> a_init \<sigma>'"
        proof
          assume xi: "x \<in> a_init \<sigma>'"
          have "x \<notin> a_init \<sigma>" using vv True by auto
          with init xi xb b nW show False by auto
        qed
        ultimately show ?thesis using b by (auto simp: get_def wt_opt_def split: option.splits)
      qed
    qed
    with b KOwned show ?thesis by simp
  next
    case (KBorrow c T)
    have nr0: "\<not> is_ref k" using KBorrow by simp
    from old KBorrow obtain v where g: "get st (bpath b) = Ok v"
      and vv: "if c = Out then out_val P C \<sigma> T v else vt P T v" by auto
    show ?thesis
    proof (cases "c = Out \<and> c_fields C \<noteq> []")
      case False
      then have "vt P T v" using vv by (auto simp: out_val_def split: if_splits)
      from nonref[OF xk nr0 xb g] this KBorrow obtain v' where "get st' (bpath b) = Ok v'" "vt P T v'"
        by auto
      with False KBorrow show ?thesis by (auto simp: out_val_def)
    next
      case True
      then have c: "c = Out" and cf: "c_fields C \<noteq> []" by auto
      with vv have ov: "out_val P C \<sigma> T v" by simp
      show ?thesis
      proof (cases "bpath b \<in> W")
        case inW: True
        from wtarget_above[OF excl W[rule_format, OF inW] xk nr0 xb] KBorrow obtain v' where
          "get st' (bpath b) = Ok v'" "vt P T v'" by auto
        with vt_out_val ov c KBorrow show ?thesis by auto
      next
        case nW: False
        have na: "\<forall>q \<in> W. \<not> below (bpath b) q"
          using wtarget_above[OF excl W[rule_format] xk nr0 xb] nW by blast
        from hagree_vagree_on[OF ag envroots_I[OF xb] bounds[OF xb] na g] obtain v' where
          g': "get st' (bpath b) = Ok v'" and va: "vagree {s. pext (bpath b) s \<in> W} v v'" by blast
        have "out_val P C \<sigma>' T v'"
        proof (rule out_val_vagree[OF wf ov cf va])
          show "[] \<notin> {s. pext (bpath b) s \<in> W}" using nW by simp
          show "\<forall>s \<in> {s. pext (bpath b) s \<in> W}. \<forall>U. sty P T s = Some U \<longrightarrow> (\<exists>u. walk v' s = Ok u \<and> vt P U u)"
          proof (intro ballI allI impI)
            fix s U assume s: "s \<in> {s. pext (bpath b) s \<in> W}" "sty P T s = Some U"
            from wtarget_meets[OF excl W[rule_format] xk nr0 xb, of "pext (bpath b) s"] s KBorrow g'
            show "\<exists>u. walk v' s = Ok u \<and> vt P U u" by (auto simp: get_pext dest: pext_eq_pext)
          qed
          show "\<forall>s \<in> {s. pext (bpath b) s \<in> W}. \<exists>u. walk v s = Ok u"
          proof
            fix s assume s: "s \<in> {s. pext (bpath b) s \<in> W}"
            from wtarget_meets[OF excl W[rule_format] xk nr0 xb, of "pext (bpath b) s"] s g
            show "\<exists>u. walk v s = Ok u" by (auto simp: get_pext)
          qed
          show "\<forall>f. f \<in> a_fields \<sigma>' \<longrightarrow> f \<notin> a_fields \<sigma> \<longrightarrow> [Fld f] \<in> {s. pext (bpath b) s \<in> W}"
            using flds xk xb KBorrow c by (auto simp: ext_pext)
        qed
        with g' c KBorrow show ?thesis by auto
      qed
    qed
  next
    case (KRef T og I)
    from old KRef obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
      "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    have live: "\<exists>v. get st' q = Ok v \<and> vt P T v"
      if l: "x \<notin> a_inval \<sigma>' \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>')"
    proof (cases "\<exists>qw \<in> W. below q qw")
      case True
      then obtain qw where qw: "qw \<in> W" "below q qw" by blast
      have "below qw (bpath bz) \<or> below (bpath bz) qw"
        using below_common[OF qw(2), of "bpath bz"] rf(6) by (simp add: overlaps_def)
      with wtarget_meets[OF excl W[rule_format, OF qw(1)] rf(3,4,5)]
      obtain ss' T' where s': "qw = pext (bpath bz) ss'" "sty P (kind_ty kz) ss' = Some T'"
        "\<exists>v. get st' qw = Ok v \<and> vt P T' v" "\<not> trivial_ty T' \<longrightarrow> refs_into \<Gamma> {z} \<subseteq> a_inval \<sigma>'"
        by blast
      from qw(2) obtain rs where rs: "q = pext qw rs" by (auto simp: below_pext_iff)
      with rf(6) s'(1) have ss: "ss = ss' @ rs" by (simp add: pext_def)
      with rf(7) s'(2) have st: "sty P T' rs = Some T" by (simp add: sty_append)
      have nh: "\<not> has_idx rs"
      proof
        assume h: "has_idx rs"
        show False
        proof (cases "trivial_ty T'")
          case True
          with st h show False by (auto dest: sty_trivial)
        next
          case False
          with s'(4) have "refs_into \<Gamma> {z} \<subseteq> a_inval \<sigma>'" by simp
          moreover have "x \<in> refs_into \<Gamma> {z}"
            using refs_into_I[of \<Gamma> x T og I z "{z}"] xk KRef rf(8) ss h by simp
          ultimately show False using l by auto
        qed
      qed
      from s'(3) obtain w where w: "get st' qw = Ok w" "vt P T' w" by blast
      from walk_fields_typed[OF w(2) st nh] obtain u where "walk w rs = Ok u" "vt P T u" by blast
      with w rs show ?thesis by (simp add: get_pext)
    next
      case False
      have oldl: "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>)"
      proof
        show "x \<notin> a_inval \<sigma>" using l inval by auto
        show "\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>"
        proof (intro allI impI)
          fix U assume kU: "kz = KOwned U"
          show "z \<in> a_init \<sigma>"
          proof (rule ccontr)
            assume "z \<notin> a_init \<sigma>"
            with l kU init rf(5) obtain r where "bz = Own r" "(r, []) \<in> W" by fastforce
            with False rf(6) show False by auto
          qed
        qed
      qed
      with rf(9) obtain v where g: "get st q = Ok v" "vt P T v" by blast
      have qb: "fst q < nroot st" using bounds[OF rf(5)] rf(6) by simp
      have qr: "fst q \<in> envroots env" using envroots_I[OF rf(5)] rf(6) by simp
      show ?thesis
      proof (rule hagree_typed_on[OF wf ag qr qb _ g])
        show "\<forall>qw \<in> W. \<not> below q qw" using False by blast
        fix s U assume s: "pext q s \<in> W" "sty P T s = Some U"
        from wtarget_meets[OF excl W[rule_format, OF s(1)] rf(3,4,5)] rf(6)
        obtain ss' T' where s': "pext q s = pext (bpath bz) ss'" "sty P (kind_ty kz) ss' = Some T'"
          "\<exists>v. get st' (pext q s) = Ok v \<and> vt P T' v"
          by (metis below_pext below_trans)
        from s'(1) rf(6) have "ss' = ss @ s" by (simp add: pext_def)
        with s'(2) rf(7) s(2) have "T' = U" by (simp add: sty_append)
        with s'(3) show "\<exists>u. get st' (pext q s) = Ok u \<and> vt P U u" by simp
      qed
    qed
    show ?thesis
      unfolding KRef binding_ok.simps using rf(1-8) live by blast
  qed
  show ?thesis
    unfolding inv_def
  proof (intro conjI allI impI)
    show "wf_senv \<Gamma>" "one_out \<Gamma>" "map fst env = map fst \<Gamma>" "excl \<Gamma> env"
      using inv by (simp_all add: inv_def)
    fix x k assume "map_of \<Gamma> x = Some k"
    with inv obtain b where "map_of env x = Some b" "binding_ok P C \<Gamma> \<sigma> env st x k b"
      by (blast dest: inv_binding)
    with bind \<open>map_of \<Gamma> x = Some k\<close> show "\<exists>b. map_of env x = Some b \<and> binding_ok P C \<Gamma> \<sigma>' env st' x k b"
      by blast
  next
    fix x b assume "map_of env x = Some b"
    with bounds nr(1) show "fst (bpath b) < nroot st'" by (meson less_le_trans)
  next
    fix r assume "nroot st' \<le> r"
    with nr(2) show "heap st' r = None" by (simp add: heap_fresh_def)
  qed
qed



section \<open>Frames of evaluation\<close>

text \<open>
  @{text "chg \<Gamma> env V st st'"}: the heap changed only below the locations of
  the writable variables in @{text "V"} (and in fresh roots). Expressions
  change the variables in @{text "mroots"}, statements any writable variable.
\<close>

definition wpaths :: "senv \<Rightarrow> env \<Rightarrow> vname set \<Rightarrow> path set" where
  "wpaths \<Gamma> env V = {bpath b | z k b. z \<in> V \<and> map_of \<Gamma> z = Some k \<and> writable k \<and> map_of env z = Some b}"

definition chg :: "senv \<Rightarrow> env \<Rightarrow> vname set \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "chg \<Gamma> env V st st' \<longleftrightarrow> nroot st \<le> nroot st' \<and> heap_fresh st' \<and> hagree (wpaths \<Gamma> env V) st st'"

lemma wpaths_mono: "V \<subseteq> V' \<Longrightarrow> wpaths \<Gamma> env V \<subseteq> wpaths \<Gamma> env V'"
  by (auto simp: wpaths_def)

lemma wpaths_Un: "wpaths \<Gamma> env (V1 \<union> V2) = wpaths \<Gamma> env V1 \<union> wpaths \<Gamma> env V2"
  by (auto simp: wpaths_def)

lemma chg_refl: "heap_fresh st \<Longrightarrow> chg \<Gamma> env V st st"
  by (simp add: chg_def)

lemma chg_mono: "chg \<Gamma> env V st st' \<Longrightarrow> V \<subseteq> V' \<Longrightarrow> chg \<Gamma> env V' st st'"
  unfolding chg_def using hagree_mono wpaths_mono by (metis below_refl subsetD)

lemma chg_trans:
  "chg \<Gamma> env V1 st st1 \<Longrightarrow> chg \<Gamma> env V2 st1 st2 \<Longrightarrow> chg \<Gamma> env (V1 \<union> V2) st st2"
  unfolding chg_def wpaths_Un
  using hagree_trans[of "wpaths \<Gamma> env V1" st st1 "wpaths \<Gamma> env V2" st2] by auto

lemma chg_trans_sub:
  "chg \<Gamma> env V1 st st1 \<Longrightarrow> chg \<Gamma> env V2 st1 st2 \<Longrightarrow> V1 \<subseteq> V \<Longrightarrow> V2 \<subseteq> V \<Longrightarrow> chg \<Gamma> env V st st2"
  by (metis chg_mono chg_trans le_sup_iff)

lemma chg_heap:
  "nroot st \<le> nroot st' \<Longrightarrow> heap_fresh st' \<Longrightarrow> (\<forall>r < nroot st. heap st' r = heap st r) \<Longrightarrow>
   chg \<Gamma> env V st st'"
  by (simp add: chg_def hagree_heap)

lemma overlaps_sym: "overlaps a b \<longleftrightarrow> overlaps b a"
  by (auto simp: overlaps_def)

text \<open>
  A location below a non-reference variable outside @{text "V"} is not
  affected: by exclusivity, it is disjoint from every writable variable of
  @{text "V"}. This is how places stay valid while other arguments, an
  index, or the arguments of a method are evaluated.
\<close>

lemma chg_untouched:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and wf: "wf_fields P" and ch: "chg \<Gamma> env V st st'"
    and z: "map_of \<Gamma> z = Some kz" "\<not> is_ref kz" "map_of env z = Some bz" "z \<notin> V"
    and q: "below q (bpath bz)" and g: "get st q = Ok v" "vt P T v"
  shows "\<exists>v'. get st' q = Ok v' \<and> vt P T v'"
proof -
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have dis: "\<not> overlaps q w" if w: "w \<in> wpaths \<Gamma> env V" for w
  proof -
    from w obtain zw kw bw where zw: "zw \<in> V" "map_of \<Gamma> zw = Some kw" "writable kw"
      "map_of env zw = Some bw" "w = bpath bw" by (auto simp: wpaths_def)
    have "zw \<noteq> z" using zw(1) z(4) by blast
    from excl_D[OF excl zw(2,3,4) z(1,2,3) this[symmetric]] have "\<not> overlaps (bpath bz) (bpath bw)"
      by (simp add: overlaps_sym)
    from below_disjoint[OF q _ this, of w] zw(5) show ?thesis by simp
  qed
  have qb: "fst q < nroot st"
    using inv z(3) q by (auto simp: inv_def below_def)
  have ag: "hagree (wpaths \<Gamma> env V) st st'" using ch by (simp add: chg_def)
  show ?thesis
  proof (rule hagree_typed[OF wf ag qb _ g])
    show "\<forall>w \<in> wpaths \<Gamma> env V. \<not> below q w" using dis by (auto simp: overlaps_def)
    fix s U assume "pext q s \<in> wpaths \<Gamma> env V"
    with dis have "\<not> overlaps q (pext q s)" by blast
    then show "\<exists>u. get st' (pext q s) = Ok u \<and> vt P U u" by (simp add: overlaps_def)
  qed
qed

definition oloc :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> ty \<Rightarrow> path \<Rightarrow> bool" where
  "oloc P \<Gamma> env R I T q \<longleftrightarrow> (\<exists>z kz bz ss. z \<in> R \<and> map_of \<Gamma> z = Some kz \<and> \<not> is_ref kz \<and>
     map_of env z = Some bz \<and> q = pext (bpath bz) ss \<and> sty P (kind_ty kz) ss = Some T \<and>
     (has_idx ss \<longrightarrow> z \<in> I))"

lemma ploc_oloc: "ploc P \<Gamma> env p T q = oloc P \<Gamma> env (place_origin \<Gamma> p) (place_interior \<Gamma> p) T q"
  by (simp add: ploc_def oloc_def)

lemma chg_oloc:
  assumes "inv P C \<Gamma> \<sigma> env st" "wf_fields P" "chg \<Gamma> env V st st'" "oloc P \<Gamma> env R I T q"
    "R \<inter> V = {}" "get st q = Ok v" "vt P T v"
  shows "\<exists>v'. get st' q = Ok v' \<and> vt P T v'"
proof -
  from assms(4) obtain z kz bz ss where "z \<in> R" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
    "map_of env z = Some bz" "q = pext (bpath bz) ss" by (auto simp: oloc_def)
  with assms show ?thesis by (intro chg_untouched[OF assms(1-3)]) auto
qed

subsection \<open>Locations relative to the root variable\<close>

text \<open>
  The static path of a place determines the field steps of its location
  up to the first index, relative to the location of its root variable.
  This is what makes the static overlap check of argument exclusivity
  sound for two places with the same root.
\<close>

fun fpath :: "step list \<Rightarrow> fname list" where
  "fpath [] = []"
| "fpath (Fld f # ss) = f # fpath ss"
| "fpath (Idx _ _ # ss) = []"

definition rloc :: "env \<Rightarrow> place \<Rightarrow> path \<Rightarrow> bool" where
  "rloc env p q \<longleftrightarrow> (\<exists>b ss. map_of env (root_of p) = Some b \<and> q = pext (bpath b) ss \<and>
     fpath ss = spath p \<and> (has_idx ss \<longleftrightarrow> has_index p))"

lemma fpath_append: "fpath (ss @ ts) = fpath ss @ (if has_idx ss then [] else fpath ts)"
proof (induction ss)
  case (Cons s ss)
  then show ?case by (cases s) (auto simp: has_idx_def)
qed simp

lemma rloc_PVar: "map_of env x = Some b \<Longrightarrow> rloc env (PVar x) (bpath b)"
  by (auto simp: rloc_def intro!: exI[of _ "[]"])

lemma rloc_field: "rloc env p q \<Longrightarrow> rloc env (PField p f) (ext q (Fld f))"
  unfolding rloc_def by (fastforce simp: ext_pext fpath_append)

lemma rloc_index: "rloc env p q \<Longrightarrow> rloc env (PIndex p e) (ext q (Idx i g))"
  unfolding rloc_def by (fastforce simp: ext_pext fpath_append)

lemma pfx_fpath: "pfx a b \<Longrightarrow> is_prefix (fpath a) (fpath b)"
  by (auto simp: pfx_def fpath_append is_prefix_def)

lemma rloc_disjoint:
  assumes "rloc env p q" "rloc env p' q'" "root_of p = root_of p'"
    "\<not> is_prefix (spath p) (spath p')" "\<not> is_prefix (spath p') (spath p)"
  shows "\<not> overlaps q q'"
proof
  assume o: "overlaps q q'"
  from assms(1,2,3) obtain b ss ss' where q: "q = pext (bpath b) ss" "fpath ss = spath p"
    and q': "q' = pext (bpath b) ss'" "fpath ss' = spath p'"
    by (auto simp: rloc_def)
  from o q q' have "pfx ss ss' \<or> pfx ss' ss" by (auto simp: overlaps_def below_def pext_def pfx_def)
  with pfx_fpath q q' assms(4,5) show False by metis
qed

lemma mut_ok_writable:
  "mut_ok \<Gamma> p = Good () \<Longrightarrow> z \<in> place_origin \<Gamma> p \<Longrightarrow> map_of \<Gamma> z = Some kz \<Longrightarrow> \<not> is_ref kz \<Longrightarrow>
   writable kz"
  by (cases kz) (auto simp: mut_ok_def check_def split: if_splits)

text \<open>Argument exclusivity at run time.\<close>

lemma excl_args:
  assumes inv: "inv P C \<Gamma> \<sigma> env st"
    and p: "ploc P \<Gamma> env p T q" "rloc env p q" and p': "ploc P \<Gamma> env p' T' q'" "rloc env p' q'"
    and no: "\<not> overlap \<Gamma> p p'" and mo: "mut_ok \<Gamma> p = Good ()"
  shows "\<not> overlaps q q'"
proof (cases "root_of p = root_of p'")
  case True
  with no show ?thesis using rloc_disjoint[OF p(2) p'(2)] by (auto simp: overlap_def)
next
  case False
  with no have dj: "place_origin \<Gamma> p \<inter> place_origin \<Gamma> p' = {}" by (simp add: overlap_def)
  from p(1) obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
    "map_of env z = Some bz" "q = pext (bpath bz) ss" by (auto simp: ploc_def)
  from p'(1) obtain z' kz' bz' ss' where z': "z' \<in> place_origin \<Gamma> p'" "map_of \<Gamma> z' = Some kz'"
    "\<not> is_ref kz'" "map_of env z' = Some bz'" "q' = pext (bpath bz') ss'" by (auto simp: ploc_def)
  have "z' \<noteq> z" using dj z(1) z'(1) by blast
  have w: "writable kz" using mut_ok_writable[OF mo z(1-3)] .
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  from excl_D[OF excl z(2) w z(4) z'(2,3,4) \<open>z' \<noteq> z\<close>] have "\<not> overlaps (bpath bz) (bpath bz')" .
  from below_disjoint[OF _ _ this, of q q'] z(5) z'(5) show ?thesis by simp
qed



section \<open>Static facts about expressions with calls\<close>

lemma ale_invalidate: "ale (invalidate_place \<Gamma> \<sigma> p T) \<sigma>"
  by (simp add: invalidate_place_def ale_def)

lemma chk_ale:
  "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<Longrightarrow> ale \<sigma>' \<sigma>"
  "chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs) \<Longrightarrow> ale \<sigma>' \<sigma>"
  apply (induction C \<Gamma> \<sigma> p and C \<Gamma> \<sigma> e and C \<Gamma> \<sigma> es and C \<Gamma> \<sigma> ps es arbitrary: \<sigma>' and \<sigma>' and \<sigma>' and \<sigma>' bs
      rule: chk_idx_chk_expr_chk_exprs_chk_args.induct)
  apply (auto split: place.splits option.splits vkind.splits intro: ale_trans ale_invalidate)
  subgoal by (simp add: ale_def)
  subgoal for C \<Gamma> \<sigma> p m es \<sigma>' a aa
    apply (cases aa; simp)
     apply (elim exE conjE)
     apply (rename_tac S fd)
     apply (case_tac "fd_params fd"; simp)
     apply (rename_tac h ps, case_tac h)
     apply (auto split: if_splits)
    subgoal premises pr for S fd ps ab ba c ac bb
    proof -
      have "ale ac a" by (rule pr(1)) (use pr in auto)
      then show ?thesis using pr(8) ale_invalidate ale_trans by blast
    qed
    subgoal premises pr for S fd ps ab ba c bb
    proof -
      have "ale \<sigma>' a" by (rule pr(1)) (use pr in auto)
      then show ?thesis using pr(8) ale_trans by blast
    qed
    subgoal premises pr for x6 ab
    proof -
      have "ale ab a" by (rule pr(2)) (use pr in auto)
      then show ?thesis using pr(1) ale_invalidate ale_trans by blast
    qed
    done
  subgoal premises pr for C \<Gamma> \<sigma> c x ps e es \<sigma>' a b ba
  proof -
    have t: "ale \<sigma>' a" using pr(11)[OF refl refl pr(13)] .
    have h: "ale a \<sigma>"
    proof (cases "c = Var \<or> c = Deinit")
      case True
      with pr(12) pr(1) show ?thesis by (auto split: if_splits)
    next
      case False
      show ?thesis
      proof (cases e)
        case (EPlace p)
        with False pr(12) pr(2) show ?thesis
          by (auto split: if_splits intro: ale_trans ale_invalidate)
      qed (use False pr(12) pr(3-10) in \<open>auto split: if_splits\<close>)
    qed
    from t h show ?thesis by (rule ale_trans)
  qed
  done

definition excl_ok :: "senv \<Rightarrow> place \<times> conv \<Rightarrow> place \<times> conv \<Rightarrow> bool" where
  "excl_ok \<Gamma> x y \<longleftrightarrow> (borrows_mut (snd x) \<or> borrows_mut (snd y) \<longrightarrow> \<not> overlap \<Gamma> (fst x) (fst y))"

lemma set_pairs: "set [f i j. i \<leftarrow> [0..<n], j \<leftarrow> [0..<n], i < j] = {f i j | i j. i < j \<and> j < n}"
  apply (auto simp: set_concat)
   apply blast
  subgoal for i j by (rule bexI[of _ i], rule bexI[of _ j]) auto
  done

lemma ball_pairs: "(\<forall>x \<in> {f i j | i j. Q i j}. x) \<longleftrightarrow> (\<forall>i j. Q i j \<longrightarrow> f i j)"
  by blast

lemma exclusive_iff:
  "exclusive \<Gamma> bs = Good () \<longleftrightarrow> (\<forall>i j. i < j \<longrightarrow> j < length bs \<longrightarrow> excl_ok \<Gamma> (bs ! i) (bs ! j))"
  unfolding exclusive_def check_def list_all_iff set_pairs ball_pairs
  by (auto simp: excl_ok_def)

lemma exclusive_appendD:
  assumes "exclusive \<Gamma> (xs @ ys) = Good ()"
  shows "exclusive \<Gamma> ys = Good ()" "\<forall>x \<in> set xs. \<forall>y \<in> set ys. excl_ok \<Gamma> x y"
proof -
  from assms have a: "\<And>i j. i < j \<Longrightarrow> j < length (xs @ ys) \<Longrightarrow> excl_ok \<Gamma> ((xs @ ys) ! i) ((xs @ ys) ! j)"
    by (simp add: exclusive_iff)
  show "exclusive \<Gamma> ys = Good ()"
    unfolding exclusive_iff
  proof (intro allI impI)
    fix i j assume "i < j" "j < length ys"
    from a[of "length xs + i" "length xs + j"] this show "excl_ok \<Gamma> (ys ! i) (ys ! j)"
      by (simp add: nth_append)
  qed
  show "\<forall>x \<in> set xs. \<forall>y \<in> set ys. excl_ok \<Gamma> x y"
  proof (intro ballI)
    fix x y assume "x \<in> set xs" "y \<in> set ys"
    then obtain i j where "i < length xs" "x = xs ! i" "j < length ys" "y = ys ! j"
      by (auto simp: in_set_conv_nth)
    with a[of i "length xs + j"] show "excl_ok \<Gamma> x y" by (simp add: nth_append)
  qed
qed

lemma overlap_sym: "overlap \<Gamma> p p' = overlap \<Gamma> p' p"
  by (auto simp: overlap_def)



section \<open>The statements of the induction\<close>

text \<open>
  One statement per function of the interpreter, for a given fuel, each
  quantified over all contexts. They are proved together by induction on
  the fuel, each at fuel @{text "Suc n"} from all of them at @{text "n"}.

  \<^bold>\<open>Arguments.\<close> @{text "aok"} describes the binding produced for one argument:
  a fresh root holding a well-typed value (for @{text "var"} parameters,
  copies of trivial values and temporaries), or the location of a place
  argument. For mutably borrowed places it also records what the checker
  established: the place can be mutated, and the references into its
  interior are invalidated. @{text "args_ok"} adds that fresh roots are
  distinct and that mutably borrowed locations overlap no other borrowed
  location, which is argument exclusivity at run time.
\<close>

definition aok :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> astate \<Rightarrow> (place \<times> conv) list \<Rightarrow> state \<Rightarrow> state \<Rightarrow>
                   conv \<times> vname \<times> ty \<Rightarrow> expr \<Rightarrow> binding \<Rightarrow> bool" where
  "aok P \<Gamma> env \<sigma>' bs st st' prm e b = (case prm of (c, x, T) \<Rightarrow> (case b of
     Own r \<Rightarrow> nroot st \<le> r \<and> r < nroot st' \<and> (\<exists>v. heap st' r = Some v \<and> vt P T v) \<and> \<not> borrows_mut c
   | Bor q \<Rightarrow> (\<exists>p. e = EPlace p \<and> c \<noteq> Var \<and> c \<noteq> Deinit \<and> (p, c) \<in> set bs \<and>
        ploc P \<Gamma> env p T q \<and> rloc env p q \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
        (borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and>
           (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>')))))"

definition args_ok :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> astate \<Rightarrow> (place \<times> conv) list \<Rightarrow> state \<Rightarrow> state \<Rightarrow>
                       (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> env \<Rightarrow> bool" where
  "args_ok P \<Gamma> env \<sigma>' bs st st' ps es benv \<longleftrightarrow>
     map fst benv = map (fst \<circ> snd) ps \<and> length es = length ps \<and>
     (\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs st st' (ps ! i) (es ! i) (snd (benv ! i))) \<and>
     distinct [r. (x, Own r) \<leftarrow> benv] \<and>
     (\<forall>i j q q'. i < length ps \<longrightarrow> j < length ps \<longrightarrow> i \<noteq> j \<longrightarrow> snd (benv ! i) = Bor q \<longrightarrow>
        snd (benv ! j) = Bor q' \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow> \<not> overlaps q q')"

text \<open>Results of functions, and of calls as seen by the caller.\<close>

definition ret_res :: "prog \<Rightarrow> ret \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> state \<Rightarrow> rval \<Rightarrow> bool" where
  "ret_res P rt \<Gamma> env st r \<longleftrightarrow> (case rt of
     RNone \<Rightarrow> r = RUnit
   | RVal T \<Rightarrow> (\<exists>v. r = RV v \<and> vt P T v)
   | RRef ns T \<Rightarrow> (\<exists>q. r = RP q \<and> (\<exists>v. get st q = Ok v \<and> vt P T v) \<and> oloc P \<Gamma> env (set ns) UNIV T q))"

definition ref_origin_of :: "senv \<Rightarrow> fundecl \<Rightarrow> expr list \<Rightarrow> vname list \<Rightarrow> vname set" where
  "ref_origin_of \<Gamma> fd es ns = (\<Union>p \<in> set (ref_args (fd_params fd) es ns). place_origin \<Gamma> p)"

definition cres :: "prog \<Rightarrow> senv \<Rightarrow> env \<Rightarrow> name \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> rval \<Rightarrow> bool" where
  "cres P \<Gamma> env f es st r \<longleftrightarrow> (case find_struct P f of
     Some _ \<Rightarrow> (\<exists>v. r = RV v \<and> vt P (TStruct f) v)
   | None \<Rightarrow> (case find_fun P f of
       None \<Rightarrow> False
     | Some fd \<Rightarrow> (case fd_ret fd of
         RNone \<Rightarrow> r = RUnit
       | RVal T \<Rightarrow> (\<exists>v. r = RV v \<and> vt P T v)
       | RRef ns T \<Rightarrow> (\<exists>q. r = RP q \<and> (\<exists>v. get st q = Ok v \<and> vt P T v) \<and>
           oloc P \<Gamma> env (ref_origin_of \<Gamma> fd es ns) (ref_origin_of \<Gamma> fd es ns) T q))))"

text \<open>The entry of a callee, and what its execution guarantees to the caller.\<close>

definition astate0 :: "(conv \<times> vname \<times> ty) list \<Rightarrow> astate" where
  "astate0 ps = \<lparr>a_init = set [x. (c, x, _) \<leftarrow> ps, c = Var], a_inval = {}, a_fields = {}\<rparr>"

definition callee_ok :: "prog \<Rightarrow> ctx \<Rightarrow> fundecl \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool" where
  "callee_ok P C fd env st \<longleftrightarrow> c_prog C = P \<and> c_ret C = fd_ret fd \<and> (c_fields C = [] \<or> fd_ret fd = RNone) \<and>
     chk_body P (fd_ret fd) (c_fields C) (fd_params fd) (fd_body fd) = Good () \<and>
     inv P C (rev (map param_kind (fd_params fd))) (astate0 (fd_params fd)) env st \<and>
     (\<forall>x y r. (x, Own r) \<in> set env \<longrightarrow> (y, Own r) \<in> set env \<longrightarrow> x = y) \<and>
     (\<forall>x T r. map_of (rev (map param_kind (fd_params fd))) x = Some (KBorrow Out T) \<longrightarrow>
        map_of env x \<noteq> Some (Own r)) \<and>
     (case fd_ret fd of RRef ns _ \<Rightarrow> \<forall>z \<in> set ns. \<exists>q. map_of env z = Some (Bor q) | _ \<Rightarrow> True)"

definition invoke_post :: "prog \<Rightarrow> fundecl \<Rightarrow> env \<Rightarrow> state \<Rightarrow> rval \<times> state \<Rightarrow> bool" where
  "invoke_post P fd env st res \<longleftrightarrow> (case res of (r, st') \<Rightarrow>
     nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
     hagree (wpaths (rev (map param_kind (fd_params fd))) env UNIV \<union> {(r, []) | x r. (x, Own r) \<in> set env})
       st st' \<and>
     (\<forall>x c T q. map_of (rev (map param_kind (fd_params fd))) x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
        map_of env x = Some (Bor q) \<longrightarrow> (\<exists>v. get st' q = Ok v \<and> vt P T v)) \<and>
     ret_res P (fd_ret fd) (rev (map param_kind (fd_params fd))) env st' r)"

text \<open>
  After a statement, the environment has grown by fresh declarations, the
  heap changed only below writable variables of the frame (and in fresh
  roots), and the invariant holds: for the checker's result if the
  statement completes, or for the environment at the @{text "return"}, with
  all fields of @{text "out self"} initialized and a result of the declared
  type.
\<close>

definition spost :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> senv \<Rightarrow> astate option \<Rightarrow> env \<Rightarrow> state \<Rightarrow>
                     outcome \<times> env \<times> state \<Rightarrow> bool" where
  "spost P C \<Gamma> \<Gamma>' o\<sigma> env st res \<longleftrightarrow> (case res of (oc, env', st') \<Rightarrow>
     (\<exists>\<Delta>e. env' = \<Delta>e @ env \<and> (\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r)) \<and>
     chg \<Gamma> env UNIV st st' \<and>
     (case oc of
        Normal \<Rightarrow> \<exists>\<sigma>'. o\<sigma> = Some \<sigma>' \<and> inv P C \<Gamma>' \<sigma>' env' st'
      | Returned rv \<Rightarrow> \<exists>\<Delta> \<sigma>r. inv P C (\<Delta> @ \<Gamma>) \<sigma>r env' st' \<and>
                         (c_ret C = RNone \<longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma>r) \<and>
                         (\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T) \<and>
                         ret_res P (c_ret C) (\<Delta> @ \<Gamma>) env' st' rv))"

definition bpost :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate option \<Rightarrow> env \<Rightarrow> state \<Rightarrow>
                     outcome \<times> env \<times> state \<Rightarrow> bool" where
  "bpost P C \<Gamma> o\<sigma> env st res \<longleftrightarrow> (case res of (oc, env', st') \<Rightarrow>
     chg \<Gamma> env UNIV st st' \<and>
     (case oc of
        Normal \<Rightarrow> env' = env \<and> (\<exists>\<sigma>'. o\<sigma> = Some \<sigma>' \<and> inv P C \<Gamma> \<sigma>' env st')
      | Returned rv \<Rightarrow> (\<exists>\<Delta>e. env' = \<Delta>e @ env \<and> (\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r)) \<and>
          (\<exists>\<Delta> \<sigma>r. inv P C (\<Delta> @ \<Gamma>) \<sigma>r env' st' \<and> (c_ret C = RNone \<longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma>r) \<and>
                   (\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T) \<and>
                   ret_res P (c_ret C) (\<Delta> @ \<Gamma>) env' st' rv)))"

text \<open>Destroying the value at a path leaves @{text "VUndef"} there and changes nothing else.\<close>

definition dpost :: "state \<Rightarrow> path \<Rightarrow> state \<Rightarrow> bool" where
  "dpost st q st' \<longleftrightarrow> nroot st \<le> nroot st' \<and> heap_fresh st' \<and> hagree {q} st st' \<and> get st' q = Ok VUndef"

text \<open>An expression evaluated to a location: a place, or a call returning a reference.\<close>

definition ref_chk :: "ctx \<Rightarrow> senv \<Rightarrow> astate \<Rightarrow> expr \<Rightarrow> astate \<Rightarrow> ty \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> bool" where
  "ref_chk C \<Gamma> \<sigma> e \<sigma>' T R I \<longleftrightarrow>
     (\<exists>p. e = EPlace p \<and> chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<and> root_ok C \<Gamma> \<sigma>' p = Good () \<and>
        ptype (c_prog C) \<Gamma> p = Good T \<and> R = place_origin \<Gamma> p \<and> I = place_interior \<Gamma> p) \<or>
     (\<exists>f es fd ns. e = ECall f es \<and> find_fun (c_prog C) f = Some fd \<and> fd_ret fd = RRef ns T \<and>
        chk_call C \<Gamma> \<sigma> f es = Good \<sigma>' \<and> etype (c_prog C) \<Gamma> e = Good T \<and>
        R = ref_origin_of \<Gamma> fd es ns \<and> I = R)"

definition SP :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SP P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st p \<sigma>' T. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<longrightarrow> ptype P \<Gamma> p = Good T \<longrightarrow> root_ok C \<Gamma> \<sigma>' p = Good () \<longrightarrow>
     spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots_p P \<Gamma> p) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       ploc P \<Gamma> env p T q \<and> rloc env p q))"

definition SE :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SE P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st e \<sigma>' T. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<longrightarrow> etype P \<Gamma> e = Good T \<longrightarrow>
     spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v))"

definition SES :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SES P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st es \<sigma>' Ts. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<longrightarrow> etypes P \<Gamma> es = Good Ts \<longrightarrow>
     spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots_l P \<Gamma> es) st st' \<and> list_all2 (vt P) Ts vs))"

definition SR :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SR P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st e \<sigma>' T R I. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     ref_chk C \<Gamma> \<sigma> e \<sigma>' T R I \<longrightarrow>
     spec (eval_ref P n env st e) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       oloc P \<Gamma> env R I T q \<and> (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q)))"

definition SA :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SA P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st ps es \<sigma>' bs. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs) \<longrightarrow> etypes P \<Gamma> es = Good (param_tys ps) \<longrightarrow>
     exclusive \<Gamma> bs = Good () \<longrightarrow>
     spec (pass_args P n env st ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (eargs P \<Gamma> ps es) st st' \<and> args_ok P \<Gamma> env \<sigma>' bs st st' ps es benv))"

definition SCF :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SCF P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st f es \<sigma>' T. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_call C \<Gamma> \<sigma> f es = Good \<sigma>' \<longrightarrow> etype P \<Gamma> (ECall f es) = Good T \<longrightarrow>
     spec (call_fun P n env st f es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and> cres P \<Gamma> env f es st' r))"

definition SCM :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SCM P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st p m es \<sigma>' T. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_expr C \<Gamma> \<sigma> (EMeth p m es) = Good \<sigma>' \<longrightarrow> etype P \<Gamma> (EMeth p m es) = Good T \<longrightarrow>
     spec (call_meth P n env st p m es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and> (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v)))"

definition SI :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SI P n \<longleftrightarrow> (\<forall>C fd env st. callee_ok P C fd env st \<longrightarrow>
     spec (invoke P n st fd env) (invoke_post P fd env st))"

definition SS :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SS P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<longrightarrow>
     spec (exec P n (c_ret C) env st s) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st))"

definition SB :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SB P n \<longleftrightarrow> (\<forall>C \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. c_prog C = P \<longrightarrow> inv P C \<Gamma> \<sigma> env st \<longrightarrow>
     chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<longrightarrow>
     spec (exec_block P n (c_ret C) env st s) (bpost P C \<Gamma> o\<sigma> env st))"

definition SD :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SD P n \<longleftrightarrow> (\<forall>st q v T. get st q = Ok v \<longrightarrow> wt_opt P T v \<longrightarrow> heap_fresh st \<longrightarrow>
     spec (drop_path P n st q) (dpost st q))"

definition SDS :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SDS P n \<longleftrightarrow> (\<forall>st qs. heap_fresh st \<longrightarrow> (\<forall>q \<in> set qs. \<exists>v T. get st q = Ok v \<and> wt_opt P T v) \<longrightarrow>
     (\<forall>i j. i < length qs \<longrightarrow> j < length qs \<longrightarrow> i \<noteq> j \<longrightarrow> \<not> overlaps (qs ! i) (qs ! j)) \<longrightarrow>
     spec (drop_paths P n st qs) (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
       hagree (set qs) st st' \<and> (\<forall>q \<in> set qs. get st' q = Ok VUndef)))"

definition SC :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "SC P n \<longleftrightarrow> (\<forall>st env. cleanup_ok P env st \<longrightarrow> heap_fresh st \<longrightarrow>
     spec (cleanup P n st env) (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
       (\<forall>r. r < nroot st \<longrightarrow> r \<notin> owned_roots env \<longrightarrow> heap st' r = heap st r)))"

definition sound_all_at :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_all_at P n \<longleftrightarrow> SP P n \<and> SE P n \<and> SES P n \<and> SR P n \<and> SA P n \<and> SCF P n \<and> SCM P n \<and> SI P n \<and>
     SS P n \<and> SB P n \<and> SD P n \<and> SDS P n \<and> SC P n"

lemma sound_all_at_0: "sound_all_at P 0"
  by (simp add: sound_all_at_def SP_def SE_def SES_def SR_def SA_def SCF_def SCM_def SI_def SS_def SB_def
                SD_def SDS_def SC_def)



section \<open>Heap facts for destruction\<close>

lemma get_bound: "heap_fresh st \<Longrightarrow> get st p = Ok v \<Longrightarrow> fst p < nroot st"
  by (cases "heap st (fst p)") (auto simp: get_def heap_fresh_def not_less[symmetric])

lemma walk_update_ok: "walk w ss = Ok u \<Longrightarrow> \<exists>w'. update_at w ss x = Ok w'"
  by (induction w ss rule: walk.induct) (auto simp: bind_res_Ok_iff split: option.splits if_splits)

lemma put_ok:
  assumes "heap_fresh st" "get st q = Ok v"
  shows "\<exists>st'. put st q x = Ok st' \<and> nroot st' = nroot st \<and> heap_fresh st' \<and> hagree {q} st st' \<and>
           get st' q = Ok x"
proof -
  from assms(2) obtain w where w: "heap st (fst q) = Some w" "walk w (snd q) = Ok v"
    by (auto simp: get_def split: option.splits)
  from walk_update_ok[OF w(2)] obtain w' where w': "update_at w (snd q) x = Ok w'" by blast
  let ?st' = "st\<lparr>heap := (heap st)(fst q := Some w')\<rparr>"
  have p: "put st q x = Ok ?st'" using w(1) w' by (simp add: put_def)
  have "fst q < nroot st" using get_bound[OF assms] .
  with assms(1) have "heap_fresh ?st'" by (auto simp: heap_fresh_def)
  moreover have "get ?st' q = Ok x" using walk_update_same[OF w'] by (simp add: get_def)
  ultimately show ?thesis using p hagree_put[OF p] by auto
qed

lemma hagree_wt_opt:
  assumes wf: "wf_fields P" and ag: "hagree W st st'" and p: "fst p < nroot st"
    and dis: "\<forall>q \<in> W. \<not> overlaps p q" and g: "get st p = Ok v" "wt_opt P T v"
  shows "\<exists>v'. get st' p = Ok v' \<and> wt_opt P T v'"
proof (cases "v = VUndef")
  case True
  have "rskel (get st' p) = rskel (get st p)"
    using hagreeD2[OF ag p] dis by (auto simp: overlaps_def)
  with g True show ?thesis by (auto simp: rskel_def wt_opt_def split: res.splits)
next
  case False
  with g have vt: "vt P T v" by (simp add: wt_opt_def)
  have "\<exists>v'. get st' p = Ok v' \<and> vt P T v'"
  proof (rule hagree_typed[OF wf ag p _ g(1) vt])
    show "\<forall>q \<in> W. \<not> below p q" using dis by (auto simp: overlaps_def)
    fix s U assume "pext p s \<in> W"
    with dis show "\<exists>u. get st' (pext p s) = Ok u \<and> vt P U u" by (auto simp: overlaps_def)
  qed
  then show ?thesis by (auto simp: wt_opt_def)
qed

lemma hagree_heap_after:
  "hagree W st st1 \<Longrightarrow> (\<forall>r < nroot st. heap st2 r = heap st1 r) \<Longrightarrow> hagree W st st2"
  unfolding hagree_def by (metis get_root_cong)

lemma owned_roots_set: "r \<in> owned_roots env \<longleftrightarrow> (\<exists>x. (x, Own r) \<in> set env)"
  by (simp add: owned_roots_def)

context
  fixes P :: prog
  assumes wf: "wf_prog P"
begin

lemma wff: "wf_fields P"
  using wf by (rule wf_prog_fields)

lemma SC_Suc:
  assumes SD: "SD P n" and IH: "SC P n"
  shows "SC P (Suc n)"
  unfolding SC_def
proof (intro allI impI)
  fix st env assume ok: "cleanup_ok P env st" and fr: "heap_fresh st"
  show "spec (cleanup P (Suc n) st env) (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
       (\<forall>r. r < nroot st \<longrightarrow> r \<notin> owned_roots env \<longrightarrow> heap st' r = heap st r))"
  proof (cases env)
    case Nil
    with fr show ?thesis by simp
  next
    case (Cons xb env')
    obtain x b where xb: "xb = (x, b)" by (cases xb)
    show ?thesis
    proof (cases b)
      case (Bor q)
      with ok Cons xb have "cleanup_ok P env' st" by (auto simp: cleanup_ok_def)
      from IH[unfolded SC_def, rule_format, OF this fr] Cons xb Bor show ?thesis by simp
    next
      case (Own r)
      with Cons xb have "(x, Own r) \<in> set env" by simp
      with ok obtain v T where rv: "heap st r = Some v" "wt_opt P T v"
        unfolding cleanup_ok_def by blast
      have dp: "spec (drop_path P n st (r, [])) (dpost st (r, []))"
        using SD[unfolded SD_def, rule_format, of st "(r, [])" v T] rv fr by (simp add: get_def)
      have r_lt: "r < nroot st" using rv fr by (auto simp: heap_fresh_def not_less[symmetric])
      show ?thesis
        unfolding Cons xb Own cleanup.simps list.case prod.case binding.case
      proof (rule spec_bind, rule spec_mono[OF dp])
        fix st1 assume d: "dpost st (r, []) st1"
        let ?st2 = "free st1 r"
        have same: "\<forall>r'. r' < nroot st \<longrightarrow> r' \<noteq> r \<longrightarrow> heap st1 r' = heap st r'"
          using d hagreeD1 by (fastforce simp: dpost_def)
        have ok2: "cleanup_ok P env' ?st2"
          unfolding cleanup_ok_def
        proof (intro conjI allI impI)
          show "distinct [r. (x, Own r) \<leftarrow> env']"
            using ok Cons xb Own by (simp add: cleanup_ok_def)
          fix x' r' assume xr: "(x', Own r') \<in> set env'"
          then have "r' \<noteq> r"
            using ok Cons xb Own by (auto simp: cleanup_ok_def own_roots_mem)
          from xr ok Cons obtain v' T' where v': "heap st r' = Some v'" "wt_opt P T' v'"
            unfolding cleanup_ok_def by fastforce
          then have "r' < nroot st" using fr by (auto simp: heap_fresh_def not_less[symmetric])
          with \<open>r' \<noteq> r\<close> same v' show "\<exists>v T. heap ?st2 r' = Some v \<and> wt_opt P T v"
            by (auto simp: free_def)
        qed
        have fr2: "heap_fresh ?st2"
          using d by (auto simp: dpost_def heap_fresh_def free_def)
        show "spec (cleanup P n ?st2 env') (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
            (\<forall>r'. r' < nroot st \<longrightarrow> r' \<notin> owned_roots ((x, Own r) # env') \<longrightarrow> heap st' r' = heap st r'))"
          by (rule spec_mono[OF IH[unfolded SC_def, rule_format, OF ok2 fr2]])
             (use d same r_lt in \<open>auto simp: dpost_def free_def\<close>)
      qed
    qed
  qed
qed

lemma SDS_Suc:
  assumes SD: "SD P n" and IH: "SDS P n"
  shows "SDS P (Suc n)"
  unfolding SDS_def
proof (intro allI impI)
  fix st qs
  assume fr: "heap_fresh st" and ty: "\<forall>q \<in> set qs. \<exists>v T. get st q = Ok v \<and> wt_opt P T v"
    and dis: "\<forall>i j. i < length qs \<longrightarrow> j < length qs \<longrightarrow> i \<noteq> j \<longrightarrow> \<not> overlaps (qs ! i) (qs ! j)"
  show "spec (drop_paths P (Suc n) st qs) (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
       hagree (set qs) st st' \<and> (\<forall>q \<in> set qs. get st' q = Ok VUndef))"
  proof (cases qs)
    case Nil
    with fr show ?thesis by simp
  next
    case (Cons q qs')
    from ty Cons obtain v T where g: "get st q = Ok v" "wt_opt P T v" by auto
    have dq: "\<forall>q' \<in> set qs'. \<not> overlaps q' q"
    proof
      fix q' assume "q' \<in> set qs'"
      then obtain j where "j < length qs'" "q' = qs' ! j" by (auto simp: in_set_conv_nth)
      with dis[rule_format, of "Suc j" 0] Cons show "\<not> overlaps q' q" by simp
    qed
    show ?thesis
      unfolding Cons drop_paths.simps list.case
    proof (rule spec_bind, rule spec_mono[OF SD[unfolded SD_def, rule_format, OF g fr]])
      fix st1 assume d: "dpost st q st1"
      have fr1: "heap_fresh st1" and ag1: "hagree {q} st st1" and n1: "nroot st \<le> nroot st1"
        and u1: "get st1 q = Ok VUndef"
        using d by (auto simp: dpost_def)
      have ty1: "\<forall>q' \<in> set qs'. \<exists>v T. get st1 q' = Ok v \<and> wt_opt P T v"
      proof
        fix q' assume q': "q' \<in> set qs'"
        with ty Cons obtain v' T' where "get st q' = Ok v'" "wt_opt P T' v'" by auto
        moreover have "fst q' < nroot st" using get_bound[OF fr \<open>get st q' = Ok v'\<close>] .
        ultimately show "\<exists>v T. get st1 q' = Ok v \<and> wt_opt P T v"
          using hagree_wt_opt[OF wff ag1] dq q' by blast
      qed
      have dis1: "\<forall>i j. i < length qs' \<longrightarrow> j < length qs' \<longrightarrow> i \<noteq> j \<longrightarrow> \<not> overlaps (qs' ! i) (qs' ! j)"
        using dis Cons by (metis Suc_less_eq length_Cons nat.inject nth_Cons_Suc)
      have ih: "spec (drop_paths P n st1 qs') (\<lambda>st'. nroot st1 \<le> nroot st' \<and> heap_fresh st' \<and>
          hagree (set qs') st1 st' \<and> (\<forall>q \<in> set qs'. get st' q = Ok VUndef))"
        using IH fr1 ty1 dis1 unfolding SDS_def by blast
      show "spec (drop_paths P n st1 qs') (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
          hagree (set (q # qs')) st st' \<and> (\<forall>q \<in> set (q # qs'). get st' q = Ok VUndef))"
      proof (rule spec_mono[OF ih], clarify)
        fix st2 assume n2: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2"
          and ag2: "hagree (set qs') st1 st2" and u2: "\<forall>q \<in> set qs'. get st2 q = Ok VUndef"
        have "hagree ({q} \<union> set qs') st st2" by (rule hagree_trans[OF ag1 ag2 n1])
        moreover have "get st2 q = Ok VUndef"
        proof -
          have "fst q < nroot st1" using get_bound[OF fr1 u1] .
          moreover have "\<forall>q' \<in> set qs'. \<not> below q q'" using dq by (auto simp: overlaps_def)
          ultimately have "rskel (get st2 q) = rskel (get st1 q)" using hagreeD2[OF ag2] by blast
          with u1 show ?thesis by (auto simp: rskel_def split: res.splits)
        qed
        ultimately show "nroot st \<le> nroot st2 \<and> heap_fresh st2 \<and> hagree (set (q # qs')) st st2 \<and>
            (\<forall>q \<in> set (q # qs'). get st2 q = Ok VUndef)"
          using n1 n2 fr2 u2 by auto
      qed
    qed
  qed
qed

lemma chk_body_facts:
  assumes "chk_body P rt flds ps body = Good ()"
  shows "\<exists>\<Gamma>' o\<sigma>. chk_stmt \<lparr>c_prog = P, c_ret = rt, c_fields = flds\<rparr> (rev (map param_kind ps))
             (astate0 ps) body = Good (\<Gamma>', o\<sigma>) \<and>
           (case o\<sigma> of None \<Rightarrow> True | Some \<sigma> \<Rightarrow> rt = RNone \<and> set flds \<subseteq> a_fields \<sigma>)"
    and "distinct (map (fst \<circ> snd) ps @ decl_names body)"
    and "length (filter (\<lambda>(c, _, _). c = Out) ps) \<le> 1"
    and "case rt of RRef ns _ \<Rightarrow> list_all (\<lambda>x. list_ex (\<lambda>(c, y, _). y = x \<and> (c = conv.Mut \<or> c = Ref)) ps) ns
           | _ \<Rightarrow> True"
proof -
  let ?C = "\<lparr>c_prog = P, c_ret = rt, c_fields = flds\<rparr>"
  show "\<exists>\<Gamma>' o\<sigma>. chk_stmt ?C (rev (map param_kind ps)) (astate0 ps) body = Good (\<Gamma>', o\<sigma>) \<and>
           (case o\<sigma> of None \<Rightarrow> True | Some \<sigma> \<Rightarrow> rt = RNone \<and> set flds \<subseteq> a_fields \<sigma>)"
  proof (cases "chk_stmt ?C (rev (map param_kind ps)) (astate0 ps) body")
    case (Good a)
    obtain \<Gamma>' o\<sigma> where "a = (\<Gamma>', o\<sigma>)" by (cases a)
    with Good assms show ?thesis
      by (cases o\<sigma>) (auto simp: chk_body_def astate0_def)
  next
    case (Bad m)
    with assms show ?thesis by (simp add: chk_body_def astate0_def)
  qed
qed (use assms in \<open>auto simp: chk_body_def split: ck.splits\<close>)

lemma own_roots_set: "set [r. (x, Own r) \<leftarrow> E] = owned_roots E"
proof (induction E)
  case (Cons xb E)
  then show ?case by (cases xb; cases "snd xb") (auto simp: owned_roots_def)
qed (simp add: owned_roots_def)

lemma cleanup_ok_append:
  assumes "cleanup_ok P A st" "cleanup_ok P B st" "owned_roots A \<inter> owned_roots B = {}"
  shows "cleanup_ok P (A @ B) st"
proof -
  have e: "[r. (x, Own r) \<leftarrow> A @ B] = [r. (x, Own r) \<leftarrow> A] @ [r. (x, Own r) \<leftarrow> B]" by simp
  have "distinct ([r. (x, Own r) \<leftarrow> A] @ [r. (x, Own r) \<leftarrow> B])"
    unfolding distinct_append using assms by (simp add: cleanup_ok_def) (auto simp: owned_roots_def)
  with assms show ?thesis unfolding cleanup_ok_def e by auto
qed

lemma cleanup_ok_no_own:
  "\<forall>x r. (x, Own r) \<notin> set E \<Longrightarrow> cleanup_ok P E st"
proof -
  assume "\<forall>x r. (x, Own r) \<notin> set E"
  then have "set [r. (x, Own r) \<leftarrow> E] = {}" unfolding own_roots_set by (simp add: owned_roots_def)
  then have "[r. (x, Own r) \<leftarrow> E] = []" by (simp only: set_empty)
  then show ?thesis using \<open>\<forall>x r. (x, Own r) \<notin> set E\<close> unfolding cleanup_ok_def by (metis distinct.simps(1))
qed

lemma ext_disjoint: "s \<noteq> s' \<Longrightarrow> \<not> overlaps (ext q s) (ext q s')"
  by (auto simp: overlaps_def below_def ext_pext pext_def)

lemma below_ext: "below (ext q s) q" "\<not> below q (ext q s)"
  by (auto simp: below_def ext_pext pext_def)

text \<open>
  The state at the end of a body: the declarations of the body are on top
  of the environment, and the invariant holds for some extension of the
  static environment.
\<close>

lemma spost_end:
  assumes "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (oc, env', st')" "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  shows "\<exists>\<Delta> \<Delta>e \<sigma>'. env' = \<Delta>e @ env \<and> (\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r) \<and>
           inv P C (\<Delta> @ \<Gamma>) \<sigma>' env' st' \<and> (\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T) \<and>
           chg \<Gamma> env UNIV st st'"
proof (cases oc)
  case Normal
  from chk_stmt_extends(1)[OF assms(2)] obtain \<Delta> where "\<Gamma>' = \<Delta> @ \<Gamma>"
    "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T" by blast
  with assms(1) Normal show ?thesis by (auto simp: spost_def)
next
  case (Returned r)
  with assms(1) show ?thesis by (auto simp: spost_def)
qed

lemma len_ext: "inv P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st \<Longrightarrow> map fst env = map fst \<Gamma> \<Longrightarrow> length \<Delta>e = length \<Delta>"
  by (auto simp: inv_def dest!: arg_cong[where f = length])

lemma vt_struct_fields:
  assumes "vt P T (VStruct S fs)"
  shows "distinct (map fst fs)" "\<And>f u. (f, u) \<in> set fs \<Longrightarrow> map_of fs f = Some u \<and> (\<exists>U. vt P U u)"
proof -
  from assms obtain sd where sd: "find_struct P S = Some sd" and nm: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u" by auto
  show d: "distinct (map fst fs)" using wff sd nm by (simp add: wf_fields_def)
  fix f u assume fu: "(f, u) \<in> set fs"
  with fs map_of_distinct_mem[OF d fu] show "map_of fs f = Some u \<and> (\<exists>U. vt P U u)" by blast
qed

text \<open>The tail of a destruction: destroy the parts below @{text "q"}, then mark @{text "q"} destroyed.\<close>

lemma drop_tail:
  assumes SDS: "SDS P n" and ag: "hagree {q} st st2" and n2: "nroot st \<le> nroot st2" and fr2: "heap_fresh st2"
    and g2: "get st2 q = Ok w"
    and ss: "\<forall>i < length ss. \<exists>v T. get st2 (ext q (ss ! i)) = Ok v \<and> wt_opt P T v"
    and dss: "distinct ss"
  shows "spec (do { st \<leftarrow> drop_paths P n st2 (map (ext q) ss); put st q VUndef }) (dpost st q)"
proof -
  let ?qs = "map (ext q) ss"
  have ty: "\<forall>q' \<in> set ?qs. \<exists>v T. get st2 q' = Ok v \<and> wt_opt P T v"
    using ss by (auto simp: in_set_conv_nth)
  have dis: "\<forall>i j. i < length ?qs \<longrightarrow> j < length ?qs \<longrightarrow> i \<noteq> j \<longrightarrow> \<not> overlaps (?qs ! i) (?qs ! j)"
    using dss by (auto simp: ext_disjoint nth_eq_iff_index_eq)
  have ih: "spec (drop_paths P n st2 ?qs) (\<lambda>st'. nroot st2 \<le> nroot st' \<and> heap_fresh st' \<and>
      hagree (set ?qs) st2 st' \<and> (\<forall>q \<in> set ?qs. get st' q = Ok VUndef))"
    using SDS fr2 ty dis unfolding SDS_def by blast
  show ?thesis
  proof (rule spec_bind, rule spec_mono[OF ih], clarify)
    fix st3 assume n3: "nroot st2 \<le> nroot st3" and fr3: "heap_fresh st3" and ag3: "hagree (set ?qs) st2 st3"
    have "rskel (get st3 q) = rskel (get st2 q)"
    proof (rule hagreeD2[OF ag3])
      show "fst q < nroot st2" using get_bound[OF fr2 g2] .
      show "\<forall>q' \<in> set ?qs. \<not> below q q'" using below_ext(2) by auto
    qed
    with g2 obtain w3 where g3: "get st3 q = Ok w3" by (auto simp: rskel_def split: res.splits)
    from put_ok[OF fr3 g3, of VUndef] obtain st4 where p: "put st3 q VUndef = Ok st4"
      "nroot st4 = nroot st3" "heap_fresh st4" "hagree {q} st3 st4" "get st4 q = Ok VUndef" by blast
    have ag3': "hagree {q} st2 st3"
      by (rule hagree_mono[OF ag3]) (auto intro: below_ext(1))
    have "hagree ({q} \<union> {q}) st st3" by (rule hagree_trans[OF ag ag3' n2])
    then have "hagree ({q} \<union> {q}) st st4" using hagree_trans[OF _ p(4)] n2 n3 by fastforce
    then show "spec (put st3 q VUndef) (dpost st q)"
      using p n2 n3 by (simp add: dpost_def)
  qed
qed

lemma inv_deinit_entry:
  assumes "get st q = Ok v" "vt P (TStruct S) v" "heap_fresh st"
  shows "inv P C [(''self'', KBorrow Deinit (TStruct S))] (astate0 [(Deinit, ''self'', TStruct S)])
           [(''self'', Bor q)] st"
  using assms get_bound[OF assms(3,1)]
  by (auto simp: inv_def one_out_def excl_def heap_fresh_def)

lemma wpaths_self: "wpaths [(x, KBorrow Deinit T)] [(x, Bor q)] UNIV = {q}"
  by (auto simp: wpaths_def)

lemma SD_Suc:
  assumes SS: "SS P n" and SC: "SC P n" and SDS: "SDS P n"
  shows "SD P (Suc n)"
  unfolding SD_def
proof (intro allI impI)
  fix st q v T assume g: "get st q = Ok v" and wo: "wt_opt P T v" and fr: "heap_fresh st"
  have qb: "fst q < nroot st" using get_bound[OF fr g] .
  show "spec (drop_path P (Suc n) st q) (dpost st q)"
  proof (cases "v = VUndef")
    case True
    with g fr show ?thesis by (simp add: dpost_def)
  next
    case False
    note nu = this
    with wo have vt: "vt P T v" by (simp add: wt_opt_def)
    have plain: "spec (put st q VUndef) (dpost st q)"
    proof -
      from put_ok[OF fr g, of VUndef] obtain st' where "put st q VUndef = Ok st'"
        "nroot st' = nroot st" "heap_fresh st'" "hagree {q} st st'" "get st' q = Ok VUndef" by blast
      then show ?thesis by (simp add: dpost_def)
    qed
    show ?thesis
    proof (cases v)
      case (VStruct S fs)
      with vt have T: "T = TStruct S" by simp
      from vt T VStruct obtain sd where sd: "find_struct P S = Some sd" by auto
      text \<open>The destructor runs on the value, which keeps its type.\<close>
      have D: "spec (case sd_deinit sd of None \<Rightarrow> Ok st
                    | Some body \<Rightarrow> do { (_, env', st) \<leftarrow> exec P n RNone [(''self'', Bor q)] st body;
                                      cleanup P n st env' })
                 (\<lambda>st2. hagree {q} st st2 \<and> nroot st \<le> nroot st2 \<and> heap_fresh st2 \<and>
                        (\<exists>v2. get st2 q = Ok v2 \<and> vt P (TStruct S) v2))"
      proof (cases "sd_deinit sd")
        case None
        with g vt T fr show ?thesis by auto
      next
        case (Some body)
        let ?C = "\<lparr>c_prog = P, c_ret = RNone, c_fields = []\<rparr>"
        let ?\<Gamma> = "[(''self'', KBorrow Deinit (TStruct S))]"
        let ?env = "[(''self'', Bor q)]"
        have cb: "chk_body P RNone [] [(Deinit, ''self'', TStruct S)] body = Good ()"
          using wf_struct_facts(3)[OF wf sd Some] .
        from chk_body_facts(1)[OF cb] obtain \<Gamma>' o\<sigma> where
          cs: "chk_stmt ?C ?\<Gamma> (astate0 [(Deinit, ''self'', TStruct S)]) body = Good (\<Gamma>', o\<sigma>)"
          by (auto simp: param_kind_def)
        have i0: "inv P ?C ?\<Gamma> (astate0 [(Deinit, ''self'', TStruct S)]) ?env st"
          using inv_deinit_entry g vt T fr by blast
        have "spec (exec P n (c_ret ?C) ?env st body) (spost P ?C ?\<Gamma> \<Gamma>' o\<sigma> ?env st)"
          by (rule SS[unfolded SS_def, rule_format, OF _ i0 cs]) simp
        then have ex: "spec (exec P n RNone ?env st body) (spost P ?C ?\<Gamma> \<Gamma>' o\<sigma> ?env st)" by simp
        show ?thesis
          unfolding Some option.case
        proof (rule spec_bind, rule spec_mono[OF ex], clarify)
          fix oc env' st1 assume sp: "spost P ?C ?\<Gamma> \<Gamma>' o\<sigma> ?env st (oc, env', st1)"
          from spost_end[OF sp cs] obtain \<Delta> \<Delta>e \<sigma>' where e: "env' = \<Delta>e @ ?env"
            and fresh: "\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r"
            and i1: "inv P ?C (\<Delta> @ ?\<Gamma>) \<sigma>' env' st1" and nb: "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
            and ch: "chg ?\<Gamma> ?env UNIV st st1" by blast
          have len: "length \<Delta>e = length \<Delta>" using len_ext[OF i1[unfolded e]] by simp
          note F = inv_restrict_facts[OF i1[unfolded e] len nb]
          have cok: "cleanup_ok P env' st1"
            unfolding e by (rule cleanup_ok_append[OF F(7) cleanup_ok_no_own]) auto
          have fr1: "heap_fresh st1" and n1: "nroot st \<le> nroot st1" and ag1: "hagree {q} st st1"
            using ch wpaths_self by (auto simp: chg_def)
          have "\<exists>v1. get st1 q = Ok v1 \<and> vt P (TStruct S) v1"
          proof -
            have "map_of (\<Delta> @ ?\<Gamma>) ''self'' = Some (KBorrow Deinit (TStruct S))"
              "map_of (\<Delta>e @ ?env) ''self'' = Some (Bor q)"
              using F(5)[of "''self''"] by simp_all
            from inv_binding[OF i1 this(1)] this(2) e show ?thesis by auto
          qed
          then obtain v1 where g1: "get st1 q = Ok v1" "vt P (TStruct S) v1" by blast
          have cl: "spec (cleanup P n st1 env') (\<lambda>st'. nroot st1 \<le> nroot st' \<and> heap_fresh st' \<and>
              (\<forall>r. r < nroot st1 \<longrightarrow> r \<notin> owned_roots env' \<longrightarrow> heap st' r = heap st1 r))"
            using SC cok fr1 unfolding SC_def by blast
          show "spec (cleanup P n st1 env') (\<lambda>st2. hagree {q} st st2 \<and> nroot st \<le> nroot st2 \<and>
              heap_fresh st2 \<and> (\<exists>v2. get st2 q = Ok v2 \<and> vt P (TStruct S) v2))"
          proof (rule spec_mono[OF cl], clarify)
            fix st2 assume n2: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2"
              and h2: "\<forall>r. r < nroot st1 \<longrightarrow> r \<notin> owned_roots env' \<longrightarrow> heap st2 r = heap st1 r"
            have own: "\<forall>r. r \<in> owned_roots env' \<longrightarrow> nroot st \<le> r"
              using fresh e by (auto simp: owned_roots_set)
            have same: "\<forall>r < nroot st. heap st2 r = heap st1 r"
              using h2 own n1 by (meson leD less_le_trans)
            have "get st2 q = get st1 q" using same qb by (intro get_root_cong) simp
            with g1 hagree_heap_after[OF ag1 same] n1 n2 fr2
            show "hagree {q} st st2 \<and> nroot st \<le> nroot st2 \<and> heap_fresh st2 \<and>
                (\<exists>v2. get st2 q = Ok v2 \<and> vt P (TStruct S) v2)" by auto
          qed
        qed
      qed
      show ?thesis
        unfolding drop_path.simps g bind_res.simps VStruct val.case sd option.case
      proof (rule spec_bind, rule spec_mono[OF D], clarify)
        fix st2 v2 assume ag2: "hagree {q} st st2" and n2: "nroot st \<le> nroot st2" and fr2: "heap_fresh st2"
          and g2: "get st2 q = Ok v2" and vt2: "vt P (TStruct S) v2"
        from vt2 obtain fs2 where v2: "v2 = VStruct S fs2" by (cases v2) auto
        have d2: "distinct (map fst fs2)" and f2: "\<And>f u. (f, u) \<in> set fs2 \<Longrightarrow> map_of fs2 f = Some u \<and> (\<exists>U. vt P U u)"
          using vt_struct_fields[OF vt2[unfolded v2]] by blast+
        have m: "map (\<lambda>(f, _). ext q (Fld f)) fs2 = map (ext q) (map (\<lambda>f. Fld f) (map fst fs2))"
          by (induction fs2) auto
        have tl: "spec (do { st \<leftarrow> drop_paths P n st2 (map (ext q) (map (\<lambda>f. Fld f) (map fst fs2)));
                             put st q VUndef }) (dpost st q)"
        proof (rule drop_tail[OF SDS ag2 n2 fr2 g2])
          show "distinct (map (\<lambda>f. Fld f) (map fst fs2))" using d2 by (simp add: distinct_map inj_on_def)
          show "\<forall>i < length (map (\<lambda>f. Fld f) (map fst fs2)).
                  \<exists>v T. get st2 (ext q (map (\<lambda>f. Fld f) (map fst fs2) ! i)) = Ok v \<and> wt_opt P T v"
          proof (intro allI impI)
            fix i assume "i < length (map (\<lambda>f. Fld f) (map fst fs2))"
            then have i: "i < length fs2" by simp
            then have mem: "(fst (fs2 ! i), snd (fs2 ! i)) \<in> set fs2" by simp
            from f2[OF mem] obtain U where "map_of fs2 (fst (fs2 ! i)) = Some (snd (fs2 ! i))"
              "vt P U (snd (fs2 ! i))" by blast
            with g2 v2 i show "\<exists>v T. get st2 (ext q (map (\<lambda>f. Fld f) (map fst fs2) ! i)) = Ok v \<and> wt_opt P T v"
              by (auto simp: get_extend wt_opt_def)
          qed
        qed
        show "spec (get st2 q \<bind> (\<lambda>v. case v of
                      VStruct _ fs \<Rightarrow> do { st \<leftarrow> drop_paths P n st2 (map (\<lambda>(f, _). ext q (Fld f)) fs);
                                         put st q VUndef }
                    | _ \<Rightarrow> put st2 q VUndef)) (dpost st q)"
          using tl m v2 g2 by (simp del: map_map)
      qed
    next
      case (VList g vs)
      with vt obtain U where T: "T = TList U" and vs: "\<forall>u \<in> set vs. vt P U u" by auto
      have tl: "spec (do { st \<leftarrow> drop_paths P n st (map (ext q) (map (\<lambda>i. Idx i g) [0..<length vs]));
                           put st q VUndef }) (dpost st q)"
      proof (rule drop_tail[OF SDS hagree_refl order_refl fr g])
        show "distinct (map (\<lambda>i. Idx i g) [0..<length vs])" by (simp add: distinct_map inj_on_def)
        show "\<forall>i < length (map (\<lambda>i. Idx i g) [0..<length vs]).
                \<exists>v T. get st (ext q (map (\<lambda>i. Idx i g) [0..<length vs] ! i)) = Ok v \<and> wt_opt P T v"
          using g VList vs by (auto simp: get_extend wt_opt_def)
      qed
      have m: "map (\<lambda>i. ext q (Idx i g)) [0..<length vs] = map (ext q) (map (\<lambda>i. Idx i g) [0..<length vs])"
        by simp
      show ?thesis
        unfolding drop_path.simps g bind_res.simps VList val.case using tl m by (simp del: map_map)
    qed (use nu plain g in \<open>simp_all\<close>)
  qed
qed



section \<open>Places and expressions\<close>

lemma spec_bind_pair:
  "spec m (\<lambda>(a, b). Q a b) \<Longrightarrow> (\<And>a b. Q a b \<Longrightarrow> spec (f a b) R) \<Longrightarrow>
   spec (bind_res m (\<lambda>(a, b). f a b)) R"
  by (rule spec_bind, erule spec_mono) auto

lemma spec_bind_mono: "spec m Q \<Longrightarrow> (\<And>a. Q a \<Longrightarrow> spec (f a) R) \<Longrightarrow> spec (bind_res m f) R"
  by (rule spec_bind, erule spec_mono) auto

lemma spec_bind_pairQ:
  "spec m Q \<Longrightarrow> (\<And>a b. Q (a, b) \<Longrightarrow> spec (f a b) R) \<Longrightarrow> spec (bind_res m (\<lambda>(a, b). f a b)) R"
  by (rule spec_bind, erule spec_mono) auto

lemma chg_init: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> chg \<Gamma> env V st st"
  by (rule chg_refl[OF inv_heap_fresh])

lemma SP_Suc:
  assumes IHp: "SP P n" and IHe: "SE P n"
  shows "SP P (Suc n)"
  unfolding SP_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st p \<sigma>' T
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>'"
    and ty: "ptype P \<Gamma> p = Good T" and ro: "root_ok C \<Gamma> \<sigma>' p = Good ()"
  show "spec (eval_place P (Suc n) env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots_p P \<Gamma> p) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       ploc P \<Gamma> env p T q \<and> rloc env p q)"
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
    ultimately show ?thesis using inv PVar \<open>\<sigma>' = \<sigma>\<close> b(1) chg_init[OF inv] rloc_PVar[OF b(1)]
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
      moreover have "rloc env (PField (PVar x) f) (ext (bpath b) (Fld f))"
        using rloc_field[OF rloc_PVar[OF b(1)]] .
      ultimately show ?thesis using inv PField x \<open>\<sigma>' = \<sigma>\<close> b(1) v chg_init[OF inv]
        by (cases n) (auto simp: get_extend split: binding.splits)
    next
      case False
      with ro PField have ro0: "root_ok C \<Gamma> \<sigma>' p0 = Good ()"
        using root_ok_PField by blast
      have IH: "spec (eval_place P n env st p0) (\<lambda>(q, st').
         inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_p P \<Gamma> p0) st st' \<and>
         (\<exists>v. get st' q = Ok v \<and> vt P (TStruct S) v) \<and> ploc P \<Gamma> env p0 (TStruct S) q \<and> rloc env p0 q)"
        using IHp CP inv c0 t0 ro0 unfolding SP_def by blast
      show ?thesis
        unfolding PField eval_place.simps place.case
        apply (rule spec_bind)
        apply (rule spec_mono_pair[OF IH])
        using ft by (auto simp: get_extend ploc_field rloc_field dest: vt_field)
    qed
  next
    case (PIndex p0 e)
    from ty PIndex obtain T0 where t0: "ptype P \<Gamma> p0 = Good T0" and te: "etype P \<Gamma> e = Good TInt"
      and T0: "T0 = TList T"
      by (auto split: ty.split_asm) (metis ty.exhaust)
    from chk PIndex obtain \<sigma>1 where c0: "chk_idx C \<Gamma> \<sigma> p0 = Good \<sigma>1"
      and fl: "place_origin \<Gamma> p0 \<inter> mroots P \<Gamma> e = {}"
      and ce: "chk_expr C \<Gamma> \<sigma>1 e = Good \<sigma>'" using CP by auto
    have ale1: "ale \<sigma>' \<sigma>1" using chk_ale(2)[OF ce] .
    from ro PIndex have ro0: "root_ok C \<Gamma> \<sigma>' p0 = Good ()" by (simp add: root_ok_PIndex)
    then have ro1: "root_ok C \<Gamma> \<sigma>1 p0 = Good ()" using ale1 by (rule root_ok_ale)
    have IH: "spec (eval_place P n env st p0) (\<lambda>(q, st').
         inv P C \<Gamma> \<sigma>1 env st' \<and> chg \<Gamma> env (mroots_p P \<Gamma> p0) st st' \<and>
         (\<exists>v. get st' q = Ok v \<and> vt P T0 v) \<and> ploc P \<Gamma> env p0 T0 q \<and> rloc env p0 q)"
      using IHp CP inv c0 t0 ro1 unfolding SP_def by blast
    show ?thesis
      unfolding PIndex eval_place.simps place.case
    proof (rule spec_bind_pair[OF IH])
      fix q st1 assume h1: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots_p P \<Gamma> p0) st st1 \<and>
          (\<exists>v. get st1 q = Ok v \<and> vt P T0 v) \<and> ploc P \<Gamma> env p0 T0 q \<and> rloc env p0 q"
      then obtain v where inv1: "inv P C \<Gamma> \<sigma>1 env st1" and ch1: "chg \<Gamma> env (mroots_p P \<Gamma> p0) st st1"
        and g1: "get st1 q = Ok v" and vt1: "vt P T0 v" and pl: "ploc P \<Gamma> env p0 T0 q"
        and rl: "rloc env p0 q" by blast
      have IHe': "spec (eval P n env st1 e) (\<lambda>(iv, st2). inv P C \<Gamma> \<sigma>' env st2 \<and>
          chg \<Gamma> env (mroots P \<Gamma> e) st1 st2 \<and> vt P TInt iv)"
        using IHe CP inv1 ce te unfolding SE_def by blast
      show "spec (do { (iv, st) \<leftarrow> eval P n env st1 e; v \<leftarrow> get st q;
                 case (v, iv) of
                   (VList g vs, VInt i) \<Rightarrow>
                     if 0 \<le> i \<and> nat i < length vs then Ok (ext q (Idx (nat i) g), st) else Err ErrBounds
                 | (VUndef, _) \<Rightarrow> Err ErrUninit | _ \<Rightarrow> Err (ErrType ''index'') })
               (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_p P \<Gamma> (PIndex p0 e)) st st' \<and>
                  (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env (PIndex p0 e) T q \<and>
                  rloc env (PIndex p0 e) q)"
      proof (rule spec_bind_pair[OF IHe'], elim conjE)
        fix iv st2 assume inv2: "inv P C \<Gamma> \<sigma>' env st2" and ch2: "chg \<Gamma> env (mroots P \<Gamma> e) st1 st2"
          and vti: "vt P TInt iv"
        from chg_oloc[OF inv1 wff ch2 pl[unfolded ploc_oloc] fl g1 vt1] obtain v2 where
          g2: "get st2 q = Ok v2" "vt P T0 v2" by blast
        from g2(2) T0 obtain g vs where v: "v2 = VList g vs" "\<forall>u \<in> set vs. vt P T u"
          by (cases v2) auto
        from vti obtain i where i: "iv = VInt i" by (cases iv) auto
        have ch: "chg \<Gamma> env (mroots_p P \<Gamma> (PIndex p0 e)) st st2" using chg_trans[OF ch1 ch2] by simp
        show "spec (do { v \<leftarrow> get st2 q;
                 case (v, iv) of
                   (VList g vs, VInt i) \<Rightarrow>
                     if 0 \<le> i \<and> nat i < length vs then Ok (ext q (Idx (nat i) g), st2) else Err ErrBounds
                 | (VUndef, _) \<Rightarrow> Err ErrUninit | _ \<Rightarrow> Err (ErrType ''index'') })
               (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_p P \<Gamma> (PIndex p0 e)) st st' \<and>
                  (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env (PIndex p0 e) T q \<and>
                  rloc env (PIndex p0 e) q)"
          using g2 v i inv2 ch ploc_index[OF pl[unfolded T0]] rloc_index[OF rl]
          by (auto simp: get_extend)
      qed
    qed
  qed
qed

lemma chg_ngen: "chg \<Gamma> env V st st' \<Longrightarrow> chg \<Gamma> env V st (st'\<lparr>ngen := k\<rparr>)"
  by (auto simp: chg_def heap_fresh_def hagree_def get_def)

lemma wpaths_owned:
  "map_of \<Gamma> x = Some (KOwned U) \<Longrightarrow> map_of env x = Some (Own r) \<Longrightarrow> x \<in> V \<Longrightarrow>
   (r, []) \<in> wpaths \<Gamma> env V"
  by (force simp: wpaths_def)

lemma cres_val:
  assumes "cres P \<Gamma> env f es st r" "etype P \<Gamma> (ECall f es) = Good T" "val_call P f"
  shows "\<exists>v. rval_to_val st r = Ok v \<and> vt P T v"
proof (cases "find_struct P f")
  case (Some sd)
  with assms show ?thesis
    by (auto simp: cres_def rval_to_val_def call_ret_def call_params_def split: if_splits)
next
  case None
  then obtain fd where fd: "find_fun P f = Some fd" using assms(1) by (auto simp: cres_def split: option.splits)
  with None assms have T: "T = ret_ty (fd_ret fd)"
    by (auto simp: call_ret_def call_params_def split: if_splits)
  show ?thesis
  proof (cases "fd_ret fd")
    case (RRef ns U)
    with assms None fd T show ?thesis
      by (auto simp: cres_def rval_to_val_def val_call_def read_val_def dest: vt_trivial)
  qed (use assms None fd T in \<open>auto simp: cres_def rval_to_val_def\<close>)
qed

lemma SE_Suc:
  assumes IHp: "SP P n" and IHe: "SE P n" and IHes: "SES P n" and IHf: "SCF P n" and IHm: "SCM P n"
  shows "SE P (Suc n)"
  unfolding SE_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st e \<sigma>' T
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'"
    and ty: "etype P \<Gamma> e = Good T"
  have Pl: "\<And>st \<sigma> p \<sigma>' T. inv P C \<Gamma> \<sigma> env st \<Longrightarrow>
      chk_idx C \<Gamma> \<sigma> p = Good \<sigma>' \<Longrightarrow> ptype P \<Gamma> p = Good T \<Longrightarrow> root_ok C \<Gamma> \<sigma>' p = Good () \<Longrightarrow>
      spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_p P \<Gamma> p) st st' \<and>
        (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q \<and> rloc env p q)"
    using IHp CP unfolding SP_def by blast
  have Ex: "\<And>st e \<sigma> \<sigma>' T. inv P C \<Gamma> \<sigma> env st \<Longrightarrow>
      chk_expr C \<Gamma> \<sigma> e = Good \<sigma>' \<Longrightarrow> etype P \<Gamma> e = Good T \<Longrightarrow>
      spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
    using IHe CP unfolding SE_def by blast
  have Exs: "\<And>st es \<sigma> \<sigma>' Ts. inv P C \<Gamma> \<sigma> env st \<Longrightarrow>
      chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<Longrightarrow> etypes P \<Gamma> es = Good Ts \<Longrightarrow>
      spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_l P \<Gamma> es) st st' \<and>
        list_all2 (vt P) Ts vs)"
    using IHes CP unfolding SES_def by blast
  have ch0: "chg \<Gamma> env {} st st" by (rule chg_init[OF inv])
  show "spec (eval P (Suc n) env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
  proof (cases e)
    case (EPlace p)
    from chk EPlace CP obtain \<sigma>1 T1 where c1: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and t1: "ptype P \<Gamma> p = Good T1"
      and tr: "trivial_ty T1" and \<sigma>': "\<sigma>' = \<sigma>1"
      by auto
    from ty EPlace t1 have "T1 = T" by simp
    show ?thesis unfolding EPlace eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv c1 t1 ro]])
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
    have i': "inv P C \<Gamma> \<sigma>' env ?st'" using inv_move[OF inv xU r(1)] \<sigma>' by simp
    have rb: "r < nroot st" using inv_bounds[OF inv r(1)] by simp
    have "hagree {(r, [])} st ?st'"
      using hagree_put[of st "(r, [])" VUndef ?st'] r(2) by (simp add: put_def)
    then have "chg \<Gamma> env {x} st ?st'"
      unfolding chg_def using inv_heap_fresh[OF inv] rb wpaths_owned[OF xU r(1), of "{x}"]
      by (auto simp: heap_fresh_def elim!: hagree_mono) (metis below_refl)
    with i' r TU show ?thesis unfolding ETake p eval.simps expr.case
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
    from ty ECopy t1 have "T1 = T" by simp
    show ?thesis unfolding ECopy eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv c1 t1 ro]])
      using \<sigma>' cpy \<open>T1 = T\<close> by (auto simp: copy_ok_sound)
  next
    case (ECall f es)
    from chk ECall CP have vc: "val_call P f" and cc: "chk_call C \<Gamma> \<sigma> f es = Good \<sigma>'"
      by (simp_all only: chk_expr_ECall bind_ck_Good_iff check_Good_iff) auto
    have IH: "spec (call_fun P n env st f es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
        chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and> cres P \<Gamma> env f es st' r)"
      using IHf CP inv cc ty ECall unfolding SCF_def by blast
    show ?thesis unfolding ECall eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF IH])
      using cres_val[OF _ ty[unfolded ECall] vc] by fastforce
  next
    case (EMeth p m es)
    have IH: "spec (call_meth P n env st p m es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
        chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and> (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
      using IHm CP inv chk ty EMeth unfolding SCM_def by blast
    show ?thesis unfolding EMeth eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF IH])
      by fastforce
  next
    case (EBin op a b)
    from chk EBin obtain \<sigma>1 where ca: "chk_expr C \<Gamma> \<sigma> a = Good \<sigma>1" and cb: "chk_expr C \<Gamma> \<sigma>1 b = Good \<sigma>'"
      by auto
    from ty EBin obtain A B where ta: "etype P \<Gamma> a = Good A" and tb: "etype P \<Gamma> b = Good B"
      by auto
    have bs: "\<And>v1 v2. vt P A v1 \<Longrightarrow> vt P B v2 \<Longrightarrow> \<exists>v. binop_val op v1 v2 = Ok v \<and> vt P T v"
      using binop_sound ty ta tb EBin by blast
    show ?thesis unfolding EBin eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF inv ca ta]], unfold prod.case)
      apply (elim conjE)
      subgoal for v1 st1
        apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF _ cb tb]], assumption, unfold prod.case)
        subgoal for v2 st2
          using bs[of v1 v2] chg_trans[of \<Gamma> env "mroots P \<Gamma> a" st st1 "mroots P \<Gamma> b" st2] by auto
        done
      done
  next
    case (ENot a)
    from chk ENot have ca: "chk_expr C \<Gamma> \<sigma> a = Good \<sigma>'" by simp
    from ty ENot have ta: "etype P \<Gamma> a = Good TBool" and T: "T = TBool" by auto
    show ?thesis unfolding ENot eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Ex[OF inv ca ta]], unfold prod.case)
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
    show ?thesis unfolding ELen eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Pl[OF inv c1 t1 ro]])
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
    show ?thesis unfolding EList eval.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF Exs[OF inv ces ts]], unfold prod.case)
      using same T
      by (auto simp: fresh_gen_def chg_ngen dest: list_all2_vt_same)
  qed (use chk ty inv ch0 in auto)
qed

lemma SES_Suc:
  assumes IHe: "SE P n" and IHes: "SES P n"
  shows "SES P (Suc n)"
  unfolding SES_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st es \<sigma>' Ts
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>'"
    and ty: "etypes P \<Gamma> es = Good Ts"
  show "spec (evals P (Suc n) env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots_l P \<Gamma> es) st st' \<and> list_all2 (vt P) Ts vs)"
  proof (cases es)
    case Nil
    with chk ty inv chg_init[OF inv] show ?thesis by auto
  next
    case (Cons e es')
    from chk Cons obtain \<sigma>1 where ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
      and ces: "chk_exprs C \<Gamma> \<sigma>1 es' = Good \<sigma>'" by auto
    from ty Cons obtain T1 Ts' where te: "etype P \<Gamma> e = Good T1" and ts: "etypes P \<Gamma> es' = Good Ts'"
      and Ts: "Ts = T1 # Ts'" by auto
    have Ex: "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>1 env st' \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and>
        vt P T1 v)" using IHe CP inv ce te unfolding SE_def by blast
    show ?thesis unfolding Cons evals.simps list.case
    proof (rule spec_bind_pair[OF Ex], elim conjE)
      fix v st1 assume inv1: "inv P C \<Gamma> \<sigma>1 env st1" and ch1: "chg \<Gamma> env (mroots P \<Gamma> e) st st1"
        and vt1: "vt P T1 v"
      have Exs: "spec (evals P n env st1 es') (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots_l P \<Gamma> es') st1 st' \<and> list_all2 (vt P) Ts' vs)"
        using IHes CP inv1 ces ts unfolding SES_def by blast
      show "spec (do { (vs, st) \<leftarrow> evals P n env st1 es'; Ok (v # vs, st) })
          (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots_l P \<Gamma> (e # es')) st st' \<and>
             list_all2 (vt P) Ts vs)"
        by (rule spec_bind_pair[OF Exs]) (use Ts vt1 chg_trans[OF ch1] in auto)
    qed
  qed
qed

lemma SR_Suc:
  assumes IHp: "SP P n" and IHf: "SCF P n"
  shows "SR P (Suc n)"
  unfolding SR_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st e \<sigma>' T R I
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and rc: "ref_chk C \<Gamma> \<sigma> e \<sigma>' T R I"
  show "spec (eval_ref P (Suc n) env st e) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       oloc P \<Gamma> env R I T q \<and> (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q))"
  proof (cases "\<exists>p. e = EPlace p")
    case True
    with rc obtain p where p: "e = EPlace p" "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>'" "root_ok C \<Gamma> \<sigma>' p = Good ()"
      "ptype P \<Gamma> p = Good T" "R = place_origin \<Gamma> p" "I = place_interior \<Gamma> p"
      using CP by (auto simp: ref_chk_def)
    have IH: "spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots_p P \<Gamma> p) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       ploc P \<Gamma> env p T q \<and> rloc env p q)"
      using IHp CP inv p unfolding SP_def by blast
    show ?thesis unfolding p(1) eval_ref.simps expr.case
      by (rule spec_mono_pair[OF IH]) (use p in \<open>auto simp: ploc_oloc\<close>)
  next
    case False
    with rc obtain f es fd ns where c: "e = ECall f es" "find_fun P f = Some fd" "fd_ret fd = RRef ns T"
      "chk_call C \<Gamma> \<sigma> f es = Good \<sigma>'" "etype P \<Gamma> e = Good T" "R = ref_origin_of \<Gamma> fd es ns" "I = R"
      using CP by (auto simp: ref_chk_def)
    have ns: "find_struct P f = None" using wf_fun_not_struct[OF wf c(2)] .
    have IH: "spec (call_fun P n env st f es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
        chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and> cres P \<Gamma> env f es st' r)"
      using IHf CP inv c(4) c(5) c(1) unfolding SCF_def by blast
    show ?thesis unfolding c(1) eval_ref.simps expr.case
      apply (rule spec_bind, rule spec_mono_pair[OF IH])
      using ns c by (auto simp: cres_def)
  qed
qed



section \<open>Arguments\<close>

lemma vt_trivial_iff: "vt P T v \<Longrightarrow> trivial v = trivial_ty T"
  by (cases v; cases T) auto

lemma alloc_facts:
  assumes "alloc st v = (r, st')"
  shows "r = nroot st" "heap st' = (heap st)(r := Some v)" "nroot st' = Suc (nroot st)"
    "heap_fresh st \<Longrightarrow> heap_fresh st'" "ngen st' = ngen st"
  using assms by (auto simp: alloc_def heap_fresh_def)

lemma inv_alloc:
  "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> alloc st v = (r, st') \<Longrightarrow> inv P C \<Gamma> \<sigma> env st'"
  by (rule inv_heap_frame) (auto simp: alloc_def heap_fresh_def dest: inv_heap_fresh)

lemma chg_extend:
  "chg \<Gamma> env V st0 st \<Longrightarrow> nroot st \<le> nroot st' \<Longrightarrow> heap_fresh st' \<Longrightarrow>
   (\<forall>r < nroot st. heap st' r = heap st r) \<Longrightarrow> chg \<Gamma> env V st0 st'"
  unfolding chg_def using hagree_heap_after by (metis less_le_trans order_trans)

lemma chg_alloc: "chg \<Gamma> env V st0 st \<Longrightarrow> alloc st v = (r, st') \<Longrightarrow> chg \<Gamma> env V st0 st'"
  by (rule chg_extend) (auto simp: alloc_def chg_def heap_fresh_def)

lemma inv_invalidate: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> inv P C \<Gamma> (invalidate_place \<Gamma> \<sigma> p T) env st"
  by (rule inv_weaken) (auto simp: weaker_def invalidate_place_def)

lemma wpaths_bound: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> w \<in> wpaths \<Gamma> env V \<Longrightarrow> fst w < nroot st"
  by (auto simp: wpaths_def dest: inv_bounds)

text \<open>The facts about one argument, once it is passed.\<close>

definition hok :: "senv \<Rightarrow> env \<Rightarrow> astate \<Rightarrow> state \<Rightarrow> state \<Rightarrow> conv \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow>
                   (conv \<times> vname \<times> ty) list \<Rightarrow> expr list \<Rightarrow> (place \<times> conv) list \<Rightarrow> binding \<Rightarrow> bool" where
  "hok \<Gamma> env \<sigma>1 st st1 c T e ps es bs1 b \<longleftrightarrow> (case b of
     Own r \<Rightarrow> nroot st \<le> r \<and> r < nroot st1 \<and> (\<exists>v. heap st1 r = Some v \<and> vt P T v) \<and>
              \<not> borrows_mut c \<and> bs1 = []
   | Bor q \<Rightarrow> \<exists>p. e = EPlace p \<and> c \<noteq> Var \<and> c \<noteq> Deinit \<and> bs1 = [(p, c)] \<and> ploc P \<Gamma> env p T q \<and>
              rloc env p q \<and> (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and> place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps es = {} \<and>
              (borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and>
                 (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>1)))"

lemma aok_mono:
  "aok P \<Gamma> env \<sigma>' bs st1 st2 prm e b \<Longrightarrow> set bs \<subseteq> set bs' \<Longrightarrow> nroot st \<le> nroot st1 \<Longrightarrow>
   aok P \<Gamma> env \<sigma>' bs' st st2 prm e b"
  by (cases prm; cases b) (auto simp: aok_def)

lemma chk_args_cons:
  assumes "chk_args C \<Gamma> \<sigma> ((c, x, T) # ps) (e # es) = Good (\<sigma>', bs)"
  shows "\<exists>\<sigma>1 bs1 bs2. chk_args C \<Gamma> \<sigma>1 ps es = Good (\<sigma>', bs2) \<and> bs = bs1 @ bs2 \<and>
     (((c = Var \<or> c = Deinit) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = []) \<or>
      (c \<noteq> Var \<and> c \<noteq> Deinit \<and> (\<exists>p \<sigma>a U. e = EPlace p \<and> chk_idx C \<Gamma> \<sigma> p = Good \<sigma>a \<and>
         root_ok C \<Gamma> \<sigma>a p = Good () \<and> ptype (c_prog C) \<Gamma> p = Good U \<and>
         ((c = Imm \<and> trivial_ty U \<and> \<sigma>1 = \<sigma>a \<and> bs1 = []) \<or>
          (\<not> (c = Imm \<and> trivial_ty U) \<and> place_origin \<Gamma> p \<inter> eargs (c_prog C) \<Gamma> ps es = {} \<and>
           bs1 = [(p, c)] \<and>
           (if borrows_mut c then mut_ok \<Gamma> p = Good () \<and> \<sigma>1 = invalidate_place \<Gamma> \<sigma>a p U
            else \<sigma>1 = \<sigma>a))))) \<or>
      (c = Imm \<and> (\<forall>p. e \<noteq> EPlace p) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = []))"
  using assms
  by (cases "c = Var \<or> c = Deinit"; cases e) (auto split: if_splits)

lemma eargs_cons:
  "eargs P \<Gamma> ((c, x, T) # ps) (e # es) =
     (if c = Var \<or> c = Deinit then mroots P \<Gamma> e
      else (case e of EPlace p \<Rightarrow> mroots_p P \<Gamma> p | _ \<Rightarrow> mroots P \<Gamma> e)) \<union> eargs P \<Gamma> ps es"
  by simp

lemma own_root_in: "(y, Own r) \<in> set benv \<Longrightarrow> \<exists>j < length benv. snd (benv ! j) = Own r"
  by (auto simp: in_set_conv_nth)

lemma arg_tail:
  assumes IHa: "SA P n" and CP: "c_prog C = P" and inv0: "inv P C \<Gamma> \<sigma> env st"
    and inv1: "inv P C \<Gamma> \<sigma>1 env st1" and h: "hok \<Gamma> env \<sigma>1 st st1 c T e ps es bs1 b"
    and ch1: "chg \<Gamma> env Vh st st1"
    and ct: "chk_args C \<Gamma> \<sigma>1 ps es = Good (\<sigma>', bs2)" and ty: "etypes P \<Gamma> es = Good (param_tys ps)"
    and ex: "exclusive \<Gamma> (bs1 @ bs2) = Good ()"
  shows "spec (do { (bs', st) \<leftarrow> pass_args P n env st1 ps es; Ok ((x, b) # bs', st) })
           (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (Vh \<union> eargs P \<Gamma> ps es) st st' \<and>
              args_ok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st' ((c, x, T) # ps) (e # es) benv)"
proof (rule spec_bind_pair)
  show "spec (pass_args P n env st1 ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
      chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st' \<and> args_ok P \<Gamma> env \<sigma>' bs2 st1 st' ps es benv)"
    using IHa CP inv1 ct ty exclusive_appendD(1)[OF ex] unfolding SA_def by blast
next
  fix benv st2
  assume "inv P C \<Gamma> \<sigma>' env st2 \<and> chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st2 \<and>
      args_ok P \<Gamma> env \<sigma>' bs2 st1 st2 ps es benv"
  then have inv2: "inv P C \<Gamma> \<sigma>' env st2" and ch2: "chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st2"
    and ao: "args_ok P \<Gamma> env \<sigma>' bs2 st1 st2 ps es benv" by blast+
  from ao have mf: "map fst benv = map (fst \<circ> snd) ps" and le: "length es = length ps"
    and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs2 st1 st2 (ps ! i) (es ! i) (snd (benv ! i))"
    and di: "distinct [r. (x, Own r) \<leftarrow> benv]"
    and pw: "\<forall>i j q q'. i < length ps \<longrightarrow> j < length ps \<longrightarrow> i \<noteq> j \<longrightarrow> snd (benv ! i) = Bor q \<longrightarrow>
        snd (benv ! j) = Bor q' \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow> \<not> overlaps q q'"
    by (simp_all add: args_ok_def)
  have lb: "length benv = length ps" using mf by (metis length_map)
  have n01: "nroot st \<le> nroot st1" and n12: "nroot st1 \<le> nroot st2" using ch1 ch2 by (simp_all add: chg_def)
  have ale2: "ale \<sigma>' \<sigma>1" using chk_ale(4)[OF ct] .
  have excl: "excl \<Gamma> env" using inv0 by (simp add: inv_def)
  have exh: "\<forall>y \<in> set bs2. excl_ok \<Gamma> (hd bs1) y" if "bs1 \<noteq> []"
    using exclusive_appendD(2)[OF ex] that by simp
  text \<open>The head argument is unaffected by the evaluation of the others.\<close>
  have head: "aok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st2 (c, x, T) e b"
  proof (cases b)
    case (Own r)
    with h have r: "nroot st \<le> r" "r < nroot st1" "\<exists>v. heap st1 r = Some v \<and> vt P T v" "\<not> borrows_mut c"
      by (auto simp: hok_def)
    have nW: "r \<notin> fst ` wpaths \<Gamma> env (eargs P \<Gamma> ps es)"
      using wpaths_bound[OF inv0] r(1) by fastforce
    from ch2 have "hagree (wpaths \<Gamma> env (eargs P \<Gamma> ps es)) st1 st2" by (simp add: chg_def)
    from hagreeD1[OF this r(2) nW] have "heap st2 r = heap st1 r" .
    with r Own n12 show ?thesis by (auto simp: aok_def)
  next
    case (Bor q)
    with h obtain p where p: "e = EPlace p" "c \<noteq> Var" "c \<noteq> Deinit" "bs1 = [(p, c)]"
      "ploc P \<Gamma> env p T q" "rloc env p q" "\<exists>v. get st1 q = Ok v \<and> vt P T v"
      "place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps es = {}"
      "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and> (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>1)"
      by (auto simp: hok_def)
    from p(7) obtain v where g: "get st1 q = Ok v" "vt P T v" by blast
    from chg_oloc[OF inv1 wff ch2 p(5)[unfolded ploc_oloc] p(8) g] have "\<exists>v. get st2 q = Ok v \<and> vt P T v" .
    with p Bor ale2 show ?thesis by (auto simp: aok_def ale_def)
  qed
  have tail: "aok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st2 (ps ! j) (es ! j) (snd (benv ! j))" if "j < length ps" for j
    using aok_mono[OF ak[rule_format, OF that] _ n01] by auto
  have tail_own: "nroot st1 \<le> r" if "(y, Own r) \<in> set benv" for y r
  proof -
    from own_root_in[OF that] obtain j where "j < length benv" "snd (benv ! j) = Own r" by blast
    with ak lb show ?thesis by (cases "ps ! j") (auto simp: aok_def)
  qed
  have dist: "distinct [r. (x, Own r) \<leftarrow> (x, b) # benv]"
  proof (cases b)
    case (Own r)
    with h have "r < nroot st1" by (simp add: hok_def)
    then have "r \<notin> set [r. (x, Own r) \<leftarrow> benv]" using tail_own by (force simp: own_roots_set owned_roots_set)
    with di Own show ?thesis by simp
  qed (use di in simp)
  have pair: "\<not> overlaps q q'"
    if ij: "i < Suc (length ps)" "j < Suc (length ps)" "i \<noteq> j"
      and bi: "snd (((x, b) # benv) ! i) = Bor q" and bj: "snd (((x, b) # benv) ! j) = Bor q'"
      and bm: "borrows_mut (fst (((c, x, T) # ps) ! i))" for i j q q'
  proof (cases i)
    case 0
    then obtain j' where j': "j = Suc j'" "j' < length ps" using ij by (cases j) auto
    from 0 bi have b: "b = Bor q" by simp
    with h obtain p where p: "e = EPlace p" "bs1 = [(p, c)]" "ploc P \<Gamma> env p T q" "rloc env p q"
      "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good ()" by (auto simp: hok_def)
    obtain c' x' T' where pj: "ps ! j' = (c', x', T')" by (cases "ps ! j'")
    from ak[rule_format, OF j'(2)] pj bj j' obtain p' where p':
      "(p', c') \<in> set bs2" "ploc P \<Gamma> env p' T' q'" "rloc env p' q'" by (auto simp: aok_def)
    from bm 0 have "borrows_mut c" by simp
    with exh p(2) p'(1) have "\<not> overlap \<Gamma> p p'" by (auto simp: excl_ok_def)
    from excl_args[OF inv0 p(3,4) p'(2,3) this] p(5) \<open>borrows_mut c\<close> show ?thesis by simp
  next
    case (Suc i')
    then have i': "i' < length ps" using ij by simp
    obtain c' x' T' where pi: "ps ! i' = (c', x', T')" by (cases "ps ! i'")
    from bm Suc pi have bmc: "borrows_mut c'" by simp
    from ak[rule_format, OF i'] pi bi Suc obtain p' where p':
      "(p', c') \<in> set bs2" "ploc P \<Gamma> env p' T' q" "rloc env p' q" "mut_ok \<Gamma> p' = Good ()"
      using bmc by (auto simp: aok_def)
    show ?thesis
    proof (cases j)
      case 0
      from 0 bj have b: "b = Bor q'" by simp
      with h obtain p where p: "bs1 = [(p, c)]" "ploc P \<Gamma> env p T q'" "rloc env p q'"
        by (auto simp: hok_def)
      with exh p'(1) bmc have "\<not> overlap \<Gamma> p p'" by (auto simp: excl_ok_def)
      then have "\<not> overlap \<Gamma> p' p" by (simp add: overlap_sym)
      from excl_args[OF inv0 p'(2,3) p(2,3) this p'(4)] show ?thesis .
    next
      case (Suc j')
      with ij \<open>i = Suc i'\<close> have "j' < length ps" "i' \<noteq> j'" by auto
      with pw[rule_format, of i' j' q q'] i' bi bj Suc \<open>i = Suc i'\<close> bmc pi show ?thesis by simp
    qed
  qed
  show "spec (Ok ((x, b) # benv, st2)) (\<lambda>(benv', st'). inv P C \<Gamma> \<sigma>' env st' \<and>
      chg \<Gamma> env (Vh \<union> eargs P \<Gamma> ps es) st st' \<and>
      args_ok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st' ((c, x, T) # ps) (e # es) benv')"
    unfolding spec_Ok_iff prod.case
  proof (intro conjI)
    show "inv P C \<Gamma> \<sigma>' env st2" by (rule inv2)
    show "chg \<Gamma> env (Vh \<union> eargs P \<Gamma> ps es) st st2" by (rule chg_trans[OF ch1 ch2])
    show "args_ok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st2 ((c, x, T) # ps) (e # es) ((x, b) # benv)"
      unfolding args_ok_def
    proof (intro conjI allI impI)
      show "map fst ((x, b) # benv) = map (fst \<circ> snd) ((c, x, T) # ps)" using mf by simp
      show "length (e # es) = length ((c, x, T) # ps)" using le by simp
      show "distinct [r. (x, Own r) \<leftarrow> (x, b) # benv]" by (rule dist)
    next
      fix i assume "i < length ((c, x, T) # ps)"
      then show "aok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st2 (((c, x, T) # ps) ! i) ((e # es) ! i)
                   (snd (((x, b) # benv) ! i))"
        using head tail by (cases i) auto
    next
      fix i j q q'
      assume "i < length ((c, x, T) # ps)" "j < length ((c, x, T) # ps)" "i \<noteq> j"
        "snd (((x, b) # benv) ! i) = Bor q" "snd (((x, b) # benv) ! j) = Bor q'"
        "borrows_mut (fst (((c, x, T) # ps) ! i))"
      with pair show "\<not> overlaps q q'" by simp
    qed
  qed
qed

lemma borrows_mut_simps [simp]:
  "\<not> borrows_mut Var" "\<not> borrows_mut Deinit" "\<not> borrows_mut Imm"
  by (simp_all add: borrows_mut_def)

lemma hok_own:
  assumes "inv P C \<Gamma> \<sigma>1 env st1" "chg \<Gamma> env V st st1" "vt P T v" "alloc st1 v = (r, st1')"
    "\<not> borrows_mut c"
  shows "inv P C \<Gamma> \<sigma>1 env st1' \<and> chg \<Gamma> env V st st1' \<and> hok \<Gamma> env \<sigma>1 st st1' c T e ps es [] (Own r)"
  using assms inv_alloc[OF assms(1,4)] chg_alloc[OF assms(2,4)] alloc_facts[OF assms(4)]
  by (auto simp: hok_def chg_def)

lemma SA_Suc:
  assumes IHe: "SE P n" and IHr: "SR P n" and IHa: "SA P n"
  shows "SA P (Suc n)"
  unfolding SA_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st ps es \<sigma>' bs
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs)"
    and ty: "etypes P \<Gamma> es = Good (param_tys ps)" and ex: "exclusive \<Gamma> bs = Good ()"
  show "spec (pass_args P (Suc n) env st ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (eargs P \<Gamma> ps es) st st' \<and> args_ok P \<Gamma> env \<sigma>' bs st st' ps es benv)"
  proof (cases "ps = [] \<or> es = []")
    case True
    with chk have "ps = []" "es = []" "\<sigma>' = \<sigma>" "bs = []"
      by (cases ps; cases es; auto)+
    with inv chg_init[OF inv] show ?thesis by (simp add: args_ok_def)
  next
    case False
    then obtain c x T ps' e es' where pe: "ps = (c, x, T) # ps'" "es = e # es'"
      by (metis list.exhaust prod_cases3)
    from ty pe have te: "etype P \<Gamma> e = Good T" and ts: "etypes P \<Gamma> es' = Good (param_tys ps')"
      by (auto simp: param_tys_def)
    from chk_args_cons[OF chk[unfolded pe]] obtain \<sigma>1 bs1 bs2 where
      ct: "chk_args C \<Gamma> \<sigma>1 ps' es' = Good (\<sigma>', bs2)" and bs: "bs = bs1 @ bs2"
      and hd: "((c = Var \<or> c = Deinit) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = []) \<or>
      (c \<noteq> Var \<and> c \<noteq> Deinit \<and> (\<exists>p \<sigma>a U. e = EPlace p \<and> chk_idx C \<Gamma> \<sigma> p = Good \<sigma>a \<and>
         root_ok C \<Gamma> \<sigma>a p = Good () \<and> ptype (c_prog C) \<Gamma> p = Good U \<and>
         ((c = Imm \<and> trivial_ty U \<and> \<sigma>1 = \<sigma>a \<and> bs1 = []) \<or>
          (\<not> (c = Imm \<and> trivial_ty U) \<and> place_origin \<Gamma> p \<inter> eargs (c_prog C) \<Gamma> ps' es' = {} \<and>
           bs1 = [(p, c)] \<and>
           (if borrows_mut c then mut_ok \<Gamma> p = Good () \<and> \<sigma>1 = invalidate_place \<Gamma> \<sigma>a p U
            else \<sigma>1 = \<sigma>a))))) \<or>
      (c = Imm \<and> (\<forall>p. e \<noteq> EPlace p) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = [])"
      by blast
    define Vh where "Vh = (if c = Var \<or> c = Deinit then mroots P \<Gamma> e
      else (case e of EPlace p \<Rightarrow> mroots_p P \<Gamma> p | _ \<Rightarrow> mroots P \<Gamma> e))"
    have eq: "eargs P \<Gamma> ps es = Vh \<union> eargs P \<Gamma> ps' es'" by (simp add: pe Vh_def)
    define HEAD where "HEAD = (if c = Var \<or> c = Deinit then do {
            (v, st) \<leftarrow> eval P n env st e;
            (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }
          else if is_ref_expr P e then do {
            (q, st) \<leftarrow> eval_ref P n env st e;
            if c = Imm then do {
              v \<leftarrow> get st q;
              if trivial v then (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st))
              else Ok (Bor q, st) }
            else Ok (Bor q, st) }
          else if c = Imm then do {
            (v, st) \<leftarrow> eval P n env st e;
            (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }
          else Err (ErrType ''mut or ref argument must be a place''))"
    have unf: "pass_args P (Suc n) env st ps es =
        do { (b, st) \<leftarrow> HEAD; (bs, st) \<leftarrow> pass_args P n env st ps' es'; Ok ((x, b) # bs, st) }"
      by (simp add: pe HEAD_def)
    text \<open>Evaluating an argument to a value in a fresh root.\<close>
    have byval: "spec (do { (v, st) \<leftarrow> eval P n env st e; (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) })
        (\<lambda>(b, st1). inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
                    hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' [] b)"
      if ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" and nb: "\<not> borrows_mut c"
    proof (rule spec_bind_pair)
      show "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
          chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
        using IHe CP inv ce te unfolding SE_def by blast
    next
      fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and> vt P T v"
      obtain r st1' where al: "alloc st1 v = (r, st1')" by (cases "alloc st1 v")
      from hok_own[OF _ _ _ al nb, of C \<Gamma> \<sigma>1 env "mroots P \<Gamma> e" st T e ps' es'] h al
      show "spec (case alloc st1 v of (r, st) \<Rightarrow> Ok (Own r, st))
          (\<lambda>(b, st1). inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
                      hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' [] b)" by simp
    qed
    have H: "spec HEAD (\<lambda>(b, st1). inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env Vh st st1 \<and>
                hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' bs1 b)"
    proof -
      consider (V) "(c = Var \<or> c = Deinit) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = []"
        | (Pl) p \<sigma>a U where "c \<noteq> Var" "c \<noteq> Deinit" "e = EPlace p" "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>a"
            "root_ok C \<Gamma> \<sigma>a p = Good ()" "ptype (c_prog C) \<Gamma> p = Good U"
            "(c = Imm \<and> trivial_ty U \<and> \<sigma>1 = \<sigma>a \<and> bs1 = []) \<or>
             (\<not> (c = Imm \<and> trivial_ty U) \<and> place_origin \<Gamma> p \<inter> eargs (c_prog C) \<Gamma> ps' es' = {} \<and>
              bs1 = [(p, c)] \<and>
              (if borrows_mut c then mut_ok \<Gamma> p = Good () \<and> \<sigma>1 = invalidate_place \<Gamma> \<sigma>a p U
               else \<sigma>1 = \<sigma>a))"
        | (I) "c = Imm" "\<forall>p. e \<noteq> EPlace p" "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" "bs1 = []"
        using hd by blast
      then show ?thesis
      proof cases
        case V
        then have "HEAD = do { (v, st) \<leftarrow> eval P n env st e; (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }"
          "Vh = mroots P \<Gamma> e" by (simp_all add: HEAD_def Vh_def)
        with byval V show ?thesis by (auto simp: borrows_mut_def)
      next
        case Pl
        have U: "U = T" using Pl te CP by simp
        have rc: "ref_chk C \<Gamma> \<sigma> (EPlace p) \<sigma>a T (place_origin \<Gamma> p) (place_interior \<Gamma> p)"
          using Pl U by (simp add: ref_chk_def)
        have IHr': "spec (eval_ref P n env st (EPlace p)) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>a env st' \<and>
            chg \<Gamma> env (mroots P \<Gamma> (EPlace p)) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
            oloc P \<Gamma> env (place_origin \<Gamma> p) (place_interior \<Gamma> p) T q \<and> (\<forall>p'. EPlace p = EPlace p' \<longrightarrow> rloc env p' q))"
          using IHr CP inv rc unfolding SR_def by blast
        have hd': "HEAD = do { (q, st) \<leftarrow> eval_ref P n env st (EPlace p);
            if c = Imm then do { v \<leftarrow> get st q;
              if trivial v then (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) else Ok (Bor q, st) }
            else Ok (Bor q, st) }" and vh: "Vh = mroots_p P \<Gamma> p"
          using Pl by (simp_all add: HEAD_def Vh_def)
        show ?thesis
          unfolding hd' vh
        proof (rule spec_bind_pair[OF IHr'])
          fix q st1
          assume h: "inv P C \<Gamma> \<sigma>a env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> (EPlace p)) st st1 \<and>
            (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and> oloc P \<Gamma> env (place_origin \<Gamma> p) (place_interior \<Gamma> p) T q \<and>
            (\<forall>p'. EPlace p = EPlace p' \<longrightarrow> rloc env p' q)"
          then obtain v where inv1: "inv P C \<Gamma> \<sigma>a env st1" and ch1: "chg \<Gamma> env (mroots_p P \<Gamma> p) st st1"
            and g1: "get st1 q = Ok v" and vt1: "vt P T v" and pl: "ploc P \<Gamma> env p T q"
            and rl: "rloc env p q" by (auto simp: ploc_oloc)
          show "spec (if c = Imm then do { v \<leftarrow> get st1 q;
              if trivial v then (case alloc st1 v of (r, st) \<Rightarrow> Ok (Own r, st)) else Ok (Bor q, st1) }
            else Ok (Bor q, st1))
            (\<lambda>(b, st1'). inv P C \<Gamma> \<sigma>1 env st1' \<and> chg \<Gamma> env (mroots_p P \<Gamma> p) st st1' \<and>
              hok \<Gamma> env \<sigma>1 st st1' c T e ps' es' bs1 b)"
          proof (cases "c = Imm \<and> trivial_ty U")
            case True
            with Pl U have s1: "\<sigma>1 = \<sigma>a" "bs1 = []" "c = Imm" by auto
            obtain r st1' where al: "alloc st1 v = (r, st1')" by (cases "alloc st1 v")
            have "trivial v" using vt_trivial_iff[OF vt1] True U by simp
            with hok_own[OF inv1 ch1 vt1 al, of Imm e ps' es'] s1 g1 al show ?thesis by simp
          next
            case False
            with Pl U have s1: "bs1 = [(p, c)]" "place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps' es' = {}"
              "if borrows_mut c then mut_ok \<Gamma> p = Good () \<and> \<sigma>1 = invalidate_place \<Gamma> \<sigma>a p T else \<sigma>1 = \<sigma>a"
              using CP by auto
            have inv1': "inv P C \<Gamma> \<sigma>1 env st1"
              using s1(3) inv1 inv_invalidate by (auto split: if_splits)
            have ri: "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and>
                (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>1)"
              using s1(3) by (auto simp: invalidate_place_def)
            have hb: "hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' bs1 (Bor q)"
              using Pl s1 pl rl g1 vt1 ri by (auto simp: hok_def)
            have nt: "c = Imm \<longrightarrow> \<not> trivial v" using vt_trivial_iff[OF vt1] False U by auto
            show ?thesis using inv1' ch1 hb g1 nt by auto
          qed
        qed
      next
        case I
        then have vh: "Vh = mroots P \<Gamma> e" by (cases e) (auto simp: Vh_def)
        show ?thesis
        proof (cases "is_ref_expr P e")
          case False
          with I have "HEAD = do { (v, st) \<leftarrow> eval P n env st e; (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) }"
            by (simp add: HEAD_def)
          with byval[OF I(3)] I vh show ?thesis by simp
        next
          case True
          with I obtain f es0 fd ns T' where c: "e = ECall f es0" "find_fun P f = Some fd" "fd_ret fd = RRef ns T'"
            by (cases e) (auto split: option.splits ret.splits)
          have nsf: "find_struct P f = None" using wf_fun_not_struct[OF wf c(2)] .
          from I(3) c CP have vc: "val_call P f" and cc: "chk_call C \<Gamma> \<sigma> f es0 = Good \<sigma>1"
            by (simp_all only: chk_expr_ECall bind_ck_Good_iff check_Good_iff) auto
          have TT: "T' = T" using te c nsf by (simp add: call_ret_def call_params_def split: if_splits)
          have triv: "trivial_ty T" using vc nsf c TT by (simp add: val_call_def)
          have rc: "ref_chk C \<Gamma> \<sigma> e \<sigma>1 T (ref_origin_of \<Gamma> fd es0 ns) (ref_origin_of \<Gamma> fd es0 ns)"
            using c cc te CP TT by (simp add: ref_chk_def)
          have IHr': "spec (eval_ref P n env st e) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
              chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
              oloc P \<Gamma> env (ref_origin_of \<Gamma> fd es0 ns) (ref_origin_of \<Gamma> fd es0 ns) T q \<and>
              (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q))"
            using IHr CP inv rc unfolding SR_def by blast
          have hd': "HEAD = do { (q, st) \<leftarrow> eval_ref P n env st e; v \<leftarrow> get st q;
              if trivial v then (case alloc st v of (r, st) \<Rightarrow> Ok (Own r, st)) else Ok (Bor q, st) }"
            using I True by (simp add: HEAD_def)
          show ?thesis
            unfolding hd' vh
          proof (rule spec_bind_pair[OF IHr'])
            fix q st1
            assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
              (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and>
              oloc P \<Gamma> env (ref_origin_of \<Gamma> fd es0 ns) (ref_origin_of \<Gamma> fd es0 ns) T q \<and>
              (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q)"
            then obtain v where inv1: "inv P C \<Gamma> \<sigma>1 env st1" and ch1: "chg \<Gamma> env (mroots P \<Gamma> e) st st1"
              and g1: "get st1 q = Ok v" and vt1: "vt P T v" by blast
            obtain r st1' where al: "alloc st1 v = (r, st1')" by (cases "alloc st1 v")
            have "trivial v" using vt_trivial[OF vt1 triv] .
            with hok_own[OF inv1 ch1 vt1 al, of Imm e ps' es'] I g1 al
            show "spec (do { v \<leftarrow> get st1 q;
                if trivial v then (case alloc st1 v of (r, st) \<Rightarrow> Ok (Own r, st)) else Ok (Bor q, st1) })
                (\<lambda>(b, st1). inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
                   hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' bs1 b)" by simp
          qed
        qed
      qed
    qed
    have ex': "exclusive \<Gamma> (bs1 @ bs2) = Good ()" using ex bs by simp
    show ?thesis
      unfolding unf eq pe[symmetric] bs
    proof (rule spec_bind_pair[OF H])
      fix b st1 assume "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env Vh st st1 \<and> hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' bs1 b"
      then have inv1: "inv P C \<Gamma> \<sigma>1 env st1" and ch1: "chg \<Gamma> env Vh st st1"
        and h: "hok \<Gamma> env \<sigma>1 st st1 c T e ps' es' bs1 b" by blast+
      show "spec (do { (bs, st) \<leftarrow> pass_args P n env st1 ps' es'; Ok ((x, b) # bs, st) })
          (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (Vh \<union> eargs P \<Gamma> ps' es') st st' \<and>
             args_ok P \<Gamma> env \<sigma>' (bs1 @ bs2) st st' ps es benv)"
        using arg_tail[OF IHa CP inv inv1 h ch1 ct ts ex'] pe by simp
    qed
  qed
qed



section \<open>Entering and leaving a callee\<close>

lemma map_of_rev_distinct: "distinct (map fst xs) \<Longrightarrow> map_of (rev xs) = map_of xs"
proof (rule ext)
  fix x assume d: "distinct (map fst xs)"
  show "map_of (rev xs) x = map_of xs x"
  proof (cases "map_of xs x")
    case None
    then show ?thesis by (metis map_of_eq_None_iff set_rev)
  next
    case (Some v)
    then have "(x, v) \<in> set (rev xs)" by (simp add: map_of_SomeD)
    moreover have "distinct (map fst (rev xs))" using d by (simp add: rev_map[symmetric])
    ultimately show ?thesis using Some map_of_distinct_mem by metis
  qed
qed

lemma fst_param_kind [simp]: "fst (param_kind p) = fst (snd p)"
  by (cases p) (simp add: param_kind_def)

lemma comp_fst_param_kind [simp]: "fst \<circ> param_kind = fst \<circ> snd"
  by (rule ext) simp

lemma is_ref_param_kind [simp]: "\<not> is_ref (snd (param_kind p))"
  by (cases p) (simp add: param_kind_def)

lemma map_fst_param_kind: "map fst (map param_kind ps) = map (fst \<circ> snd) ps"
  by simp

lemma param_kind_nth:
  "i < length ps \<Longrightarrow> param_kind (ps ! i) =
     (fst (snd (ps ! i)), if fst (ps ! i) = Var then KOwned (snd (snd (ps ! i)))
                          else KBorrow (fst (ps ! i)) (snd (snd (ps ! i))))"
  by (cases "ps ! i") (simp add: param_kind_def)

lemma map_of_nth_distinct:
  "distinct (map fst xs) \<Longrightarrow> i < length xs \<Longrightarrow> map_of xs (fst (xs ! i)) = Some (snd (xs ! i))"
  using map_of_distinct_mem nth_mem by (metis prod.collapse)

lemma map_of_index:
  "map_of xs x = Some v \<Longrightarrow> \<exists>i < length xs. x = fst (xs ! i) \<and> v = snd (xs ! i)"
  by (drule map_of_SomeD) (metis fst_conv in_set_conv_nth snd_conv)

lemma wf_senv_noref: "distinct (map fst G) \<Longrightarrow> \<forall>(x, k) \<in> set G. \<not> is_ref k \<Longrightarrow> wf_senv G"
proof (induction G)
  case (Cons xk G)
  then show ?case by (cases xk; cases "snd xk") auto
qed simp

lemma param_kind_noref: "\<forall>(x, k) \<in> set (map param_kind ps). \<not> is_ref k"
  by (auto simp: param_kind_def split: if_splits)

lemma aok_root:
  assumes "aok P \<Gamma> env \<sigma>' bs st1 st2 prm e b" "inv P C \<Gamma> \<sigma> env st0"
  shows "(\<forall>r. b = Own r \<longrightarrow> nroot st1 \<le> r \<and> r < nroot st2) \<and> (\<forall>q. b = Bor q \<longrightarrow> fst q < nroot st0)"
  using assms by (cases prm; cases b) (auto simp: aok_def ploc_def dest: inv_bounds)

lemma own_root_unique:
  "distinct [r. (x, Own r) \<leftarrow> E] \<Longrightarrow> (x, Own r) \<in> set E \<Longrightarrow> (y, Own r) \<in> set E \<Longrightarrow> x = y"
proof (induction E)
  case (Cons xb E)
  obtain z b where xb: "xb = (z, b)" by (cases xb)
  show ?case
  proof (cases b)
    case (Own r')
    with Cons xb show ?thesis by (auto simp: own_roots_set owned_roots_set)
  next
    case (Bor q)
    with Cons xb show ?thesis by auto
  qed
qed simp

lemma diff_root: "fst a \<noteq> fst b \<Longrightarrow> \<not> overlaps a b"
  by (auto simp: overlaps_def below_def)

text \<open>
  The invariant of a callee at entry, for the bindings produced by passing
  the arguments, possibly followed by @{text "out self"} (in @{text "\<Gamma>0"}
  and @{text "E0"}), which lies in a root allocated before the arguments
  were evaluated.
\<close>

lemma callee_inv:
  assumes inv0: "inv P C \<Gamma> \<sigma> env st0" and ao: "args_ok P \<Gamma> env \<sigma>' bs st1 st2 ps es benv"
    and n01: "nroot st0 \<le> nroot st1" and n12: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2"
    and dist: "distinct (map (fst \<circ> snd) ps @ map fst \<Gamma>0)"
    and oo: "one_out (rev (map param_kind ps) @ \<Gamma>0)"
    and len0: "length \<Gamma>0 \<le> 1" and E0: "map fst E0 = map fst \<Gamma>0"
    and nref0: "\<forall>(x, k) \<in> set \<Gamma>0. \<not> is_ref k"
    and E0ok: "\<forall>x k b. map_of \<Gamma>0 x = Some k \<longrightarrow> map_of E0 x = Some b \<longrightarrow>
       binding_ok P C' (rev (map param_kind ps) @ \<Gamma>0) \<sigma>c (rev benv @ E0) st2 x k b \<and>
       nroot st0 \<le> fst (bpath b) \<and> fst (bpath b) < nroot st1"
    and outs: "\<forall>i < length ps. fst (ps ! i) = Out \<longrightarrow> c_fields C' = []"
  shows "inv P C' (rev (map param_kind ps) @ \<Gamma>0) \<sigma>c (rev benv @ E0) st2"
proof -
  let ?Gp = "map param_kind ps" and ?\<Gamma> = "rev (map param_kind ps) @ \<Gamma>0" and ?E = "rev benv @ E0"
  let ?pn = "\<lambda>i. fst (snd (ps ! i))"
  from ao have mf: "map fst benv = map (fst \<circ> snd) ps"
    and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs st1 st2 (ps ! i) (es ! i) (snd (benv ! i))"
    and di: "distinct [r. (x, Own r) \<leftarrow> benv]"
    and pw: "\<forall>i j q q'. i < length ps \<longrightarrow> j < length ps \<longrightarrow> i \<noteq> j \<longrightarrow> snd (benv ! i) = Bor q \<longrightarrow>
        snd (benv ! j) = Bor q' \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow> \<not> overlaps q q'"
    by (simp_all add: args_ok_def)
  have lb: "length benv = length ps" using mf by (metis length_map)
  have dps: "distinct (map (fst \<circ> snd) ps)" using dist by simp
  have dGp: "distinct (map fst ?Gp)" using dps by (simp add: map_fst_param_kind)
  have dbenv: "distinct (map fst benv)" using dps mf by simp
  have dG: "distinct (map fst ?\<Gamma>)"
    using dist by (simp add: rev_map[symmetric] map_fst_param_kind)
  have mfE: "map fst ?E = map fst ?\<Gamma>"
    using mf E0 by (simp add: rev_map[symmetric] map_fst_param_kind)
  have dE: "distinct (map fst ?E)" using dG mfE by simp
  text \<open>Variables of the callee: a parameter with index @{text "i"}, or the extra one.\<close>
  have par: "map_of ?\<Gamma> (?pn i) = Some (snd (param_kind (ps ! i))) \<and> map_of ?E (?pn i) = Some (snd (benv ! i))"
    if i: "i < length ps" for i
  proof -
    have "map_of ?Gp (?pn i) = Some (snd (param_kind (ps ! i)))"
      using map_of_nth_distinct[OF dGp, of i] i param_kind_nth[OF i] by simp
    moreover have "map_of benv (?pn i) = Some (snd (benv ! i))"
      using map_of_nth_distinct[OF dbenv, of i] i lb mf by (metis comp_apply nth_map)
    ultimately show ?thesis
      using map_of_rev_distinct[OF dGp] map_of_rev_distinct[OF dbenv] by (simp add: map_add_def)
  qed
  have cls: "(\<exists>i < length ps. x = ?pn i \<and> k = snd (param_kind (ps ! i)) \<and> b = snd (benv ! i)) \<or>
      (map_of \<Gamma>0 x = Some k \<and> map_of E0 x = Some b)"
    if xk: "map_of ?\<Gamma> x = Some k" and xb: "map_of ?E x = Some b" for x k b
  proof (cases "map_of (rev ?Gp) x")
    case (Some k')
    then have "map_of ?Gp x = Some k'" using map_of_rev_distinct[OF dGp] by simp
    from map_of_index[OF this] obtain i where i: "i < length ps" "x = fst (?Gp ! i)" "k' = snd (?Gp ! i)"
      by auto
    then have "x = ?pn i" using param_kind_nth[OF i(1)] by simp
    with par[OF i(1)] xk xb show ?thesis using i(1) by auto
  next
    case None
    then have "map_of ?\<Gamma> x = map_of \<Gamma>0 x" by (simp add: map_add_def)
    moreover have "map_of (rev benv) x = None"
    proof -
      have "x \<notin> fst ` set ?Gp" using None by (metis map_of_eq_None_iff set_rev)
      then have "x \<notin> fst ` set benv" using mf by (metis map_fst_param_kind set_map)
      then show ?thesis by (simp add: map_of_eq_None_iff)
    qed
    ultimately show ?thesis using xk xb by (simp add: map_add_def)
  qed
  have root_par: "(\<forall>r. snd (benv ! i) = Own r \<longrightarrow> nroot st1 \<le> r \<and> r < nroot st2) \<and>
      (\<forall>q. snd (benv ! i) = Bor q \<longrightarrow> fst q < nroot st0)" if "i < length ps" for i
    using aok_root[OF ak[rule_format, OF that] inv0] .
  text \<open>Bindings of parameters.\<close>
  have bpar: "binding_ok P C' ?\<Gamma> \<sigma>c ?E st2 (?pn i) (snd (param_kind (ps ! i))) (snd (benv ! i))"
    if i: "i < length ps" for i
  proof -
    obtain c x T where pi: "ps ! i = (c, x, T)" by (cases "ps ! i")
    have a: "aok P \<Gamma> env \<sigma>' bs st1 st2 (c, x, T) (es ! i) (snd (benv ! i))" using ak i pi by auto
    show ?thesis
    proof (cases "snd (benv ! i)")
      case (Own r)
      with a have "\<exists>v. heap st2 r = Some v \<and> vt P T v" by (auto simp: aok_def)
      with Own pi outs i show ?thesis by (auto simp: param_kind_def get_def wt_opt_def out_val_def)
    next
      case (Bor q)
      with a have "c \<noteq> Var" "\<exists>v. get st2 q = Ok v \<and> vt P T v" by (auto simp: aok_def)
      with Bor pi outs i show ?thesis by (auto simp: param_kind_def out_val_def)
    qed
  qed
  have bind: "\<exists>b. map_of ?E x = Some b \<and> binding_ok P C' ?\<Gamma> \<sigma>c ?E st2 x k b"
    if xk: "map_of ?\<Gamma> x = Some k" for x k
  proof -
    have "x \<in> fst ` set ?E" using xk mfE by (metis map_of_eq_None_iff option.distinct(1) set_map)
    then obtain b where xb: "map_of ?E x = Some b" by (meson map_of_eq_None_iff not_Some_eq)
    from cls[OF xk xb] show ?thesis
    proof
      assume "\<exists>i < length ps. x = ?pn i \<and> k = snd (param_kind (ps ! i)) \<and> b = snd (benv ! i)"
      with bpar xb show ?thesis by blast
    next
      assume "map_of \<Gamma>0 x = Some k \<and> map_of E0 x = Some b"
      with E0ok xb show ?thesis by blast
    qed
  qed
  text \<open>Exclusivity: distinct roots, except for borrowed arguments, where it is argument exclusivity.\<close>
  have excl: "excl ?\<Gamma> ?E"
    unfolding excl_def
  proof (intro allI impI, elim conjE)
    fix x kx bx y ky b2
    assume xk: "map_of ?\<Gamma> x = Some kx" and wx: "writable kx" and xb: "map_of ?E x = Some bx"
      and yk: "map_of ?\<Gamma> y = Some ky" and ny: "\<not> is_ref ky" and yb: "map_of ?E y = Some b2"
      and xy: "y \<noteq> x"
    from cls[OF xk xb] cls[OF yk yb] show "\<not> overlaps (bpath bx) (bpath b2)"
    proof (elim disjE exE conjE)
      fix i j assume i: "i < length ps" "x = ?pn i" "kx = snd (param_kind (ps ! i))" "bx = snd (benv ! i)"
        and j: "j < length ps" "y = ?pn j" "ky = snd (param_kind (ps ! j))" "b2 = snd (benv ! j)"
      have ij: "i \<noteq> j" using xy i j by auto
      note ri = root_par[OF i(1)] and rj = root_par[OF j(1)]
      show ?thesis
      proof (cases bx)
        case (Own r)
        then have e1: "snd (benv ! i) = Own r" using i(4) by simp
        with ri have r1: "nroot st1 \<le> r" by blast
        show ?thesis
        proof (cases b2)
          case (Own r')
          then have e2: "snd (benv ! j) = Own r'" using j(4) by simp
          have "r \<noteq> r'"
          proof
            assume "r = r'"
            have m1: "(?pn i, Own r) \<in> set benv" using e1 i(1) lb mf
              by (metis comp_apply nth_map nth_mem prod.collapse)
            have m2: "(?pn j, Own r) \<in> set benv" using e2 \<open>r = r'\<close> j(1) lb mf
              by (metis comp_apply nth_map nth_mem prod.collapse)
            have "?pn i \<noteq> ?pn j" using xy i j by simp
            moreover have "distinct [r. (x, Own r) \<leftarrow> benv]" by (rule di)
            ultimately show False using m1 m2 own_root_unique by metis
          qed
          with \<open>bx = Own r\<close> Own show ?thesis by (simp add: diff_root)
        next
          case (Bor q')
          then have "snd (benv ! j) = Bor q'" using j(4) by simp
          with rj have "fst q' < nroot st0" by blast
          with r1 n01 \<open>bx = Own r\<close> Bor show ?thesis by (intro diff_root) auto
        qed
      next
        case (Bor q)
        then have e1: "snd (benv ! i) = Bor q" using i(4) by simp
        with ri have q1: "fst q < nroot st0" by blast
        show ?thesis
        proof (cases b2)
          case (Own r')
          then have "snd (benv ! j) = Own r'" using j(4) by simp
          with rj have "nroot st1 \<le> r'" by blast
          with q1 n01 \<open>bx = Bor q\<close> Own show ?thesis by (intro diff_root) auto
        next
          case (Bor q')
          then have e2: "snd (benv ! j) = Bor q'" using j(4) by simp
          obtain c x' T where pi: "ps ! i = (c, x', T)" by (cases "ps ! i")
          from ak i(1) pi e1 have "c \<noteq> Var" "c \<noteq> Deinit" by (auto simp: aok_def)
          with wx i(3) pi have "borrows_mut c" by (cases c) (auto simp: param_kind_def borrows_mut_def)
          with pw[rule_format, OF i(1) j(1) ij e1 e2] pi \<open>bx = Bor q\<close> Bor show ?thesis by simp
        qed
      qed
    next
      fix i assume i: "i < length ps" "x = ?pn i" "kx = snd (param_kind (ps ! i))" "bx = snd (benv ! i)"
        and y0: "map_of \<Gamma>0 y = Some ky" "map_of E0 y = Some b2"
      have h: "nroot st0 \<le> fst (bpath b2) \<and> fst (bpath b2) < nroot st1" using E0ok y0 by blast
      show ?thesis
      proof (rule diff_root, cases bx)
        case (Own r)
        then have "snd (benv ! i) = Own r" using i(4) by simp
        with root_par[OF i(1)] have "nroot st1 \<le> r" by blast
        with Own h show "fst (bpath bx) \<noteq> fst (bpath b2)" by auto
      next
        case (Bor q)
        then have "snd (benv ! i) = Bor q" using i(4) by simp
        with root_par[OF i(1)] have "fst q < nroot st0" by blast
        with Bor h show "fst (bpath bx) \<noteq> fst (bpath b2)" by auto
      qed
    next
      fix j assume x0: "map_of \<Gamma>0 x = Some kx" "map_of E0 x = Some bx"
        and j: "j < length ps" "y = ?pn j" "ky = snd (param_kind (ps ! j))" "b2 = snd (benv ! j)"
      have h: "nroot st0 \<le> fst (bpath bx) \<and> fst (bpath bx) < nroot st1" using E0ok x0 by blast
      show ?thesis
      proof (rule diff_root, cases b2)
        case (Own r)
        then have "snd (benv ! j) = Own r" using j(4) by simp
        with root_par[OF j(1)] have "nroot st1 \<le> r" by blast
        with Own h show "fst (bpath bx) \<noteq> fst (bpath b2)" by auto
      next
        case (Bor q)
        then have "snd (benv ! j) = Bor q" using j(4) by simp
        with root_par[OF j(1)] have "fst q < nroot st0" by blast
        with Bor h show "fst (bpath bx) \<noteq> fst (bpath b2)" by auto
      qed
    next
      assume "map_of \<Gamma>0 x = Some kx" "map_of E0 x = Some bx" "map_of \<Gamma>0 y = Some ky" "map_of E0 y = Some b2"
      then have "x \<in> fst ` set \<Gamma>0" "y \<in> fst ` set \<Gamma>0" by (force dest: map_of_SomeD)+
      with len0 xy show ?thesis by (cases \<Gamma>0) auto
    qed
  qed
  have bounds: "fst (bpath b) < nroot st2" if xb: "map_of ?E x = Some b" for x b
  proof -
    have "x \<in> fst ` set ?\<Gamma>" using xb mfE by (metis map_of_eq_None_iff option.distinct(1) set_map)
    then obtain k where xk: "map_of ?\<Gamma> x = Some k" by (meson map_of_eq_None_iff not_Some_eq)
    from cls[OF xk xb] show ?thesis
    proof
      assume "\<exists>i < length ps. x = ?pn i \<and> k = snd (param_kind (ps ! i)) \<and> b = snd (benv ! i)"
      then obtain i where i: "i < length ps" "b = snd (benv ! i)" by blast
      note rp = root_par[OF i(1)]
      show ?thesis
      proof (cases b)
        case (Own r)
        then have "snd (benv ! i) = Own r" using i(2) by simp
        with rp have "r < nroot st2" by blast
        with Own show ?thesis by simp
      next
        case (Bor q)
        then have "snd (benv ! i) = Bor q" using i(2) by simp
        with rp have "fst q < nroot st0" by blast
        with Bor n01 n12 show ?thesis by simp
      qed
    next
      assume "map_of \<Gamma>0 x = Some k \<and> map_of E0 x = Some b"
      with E0ok n12 show ?thesis by fastforce
    qed
  qed
  have wf: "wf_senv ?\<Gamma>"
    by (rule wf_senv_noref[OF dG]) (use nref0 in \<open>auto simp: param_kind_def split: if_splits\<close>)
  show ?thesis
    unfolding inv_def
    using wf oo mfE bind excl bounds fr2 by (auto simp: heap_fresh_def)
qed

lemma callee_var_cases:
  assumes dps: "distinct (map (fst \<circ> snd) ps)" and mf: "map fst benv = map (fst \<circ> snd) ps"
    and xk: "map_of (rev (map param_kind ps) @ \<Gamma>0) x = Some k" and xb: "map_of (rev benv @ E0) x = Some b"
  shows "(\<exists>i < length ps. x = fst (snd (ps ! i)) \<and> k = snd (param_kind (ps ! i)) \<and> b = snd (benv ! i)) \<or>
         (map_of \<Gamma>0 x = Some k \<and> map_of E0 x = Some b)"
proof -
  have lb: "length benv = length ps" using mf by (metis length_map)
  have dGp: "distinct (map fst (map param_kind ps))" using dps by simp
  have dbenv: "distinct (map fst benv)" using dps mf by simp
  show ?thesis
  proof (cases "map_of (rev (map param_kind ps)) x")
    case (Some k')
    then have "map_of (map param_kind ps) x = Some k'" using map_of_rev_distinct[OF dGp] by simp
    from map_of_index[OF this] obtain i where i: "i < length ps" "x = fst (map param_kind ps ! i)"
      "k' = snd (map param_kind ps ! i)" by auto
    then have xi: "x = fst (snd (ps ! i))" by simp
    have "map_of benv x = Some (snd (benv ! i))"
      using map_of_nth_distinct[OF dbenv, of i] i lb mf xi by (metis comp_apply nth_map)
    then have "map_of (rev benv) x = Some (snd (benv ! i))" using map_of_rev_distinct[OF dbenv] by simp
    with Some i xi xk xb show ?thesis by (auto simp: map_add_def)
  next
    case None
    then have "map_of (rev (map param_kind ps) @ \<Gamma>0) x = map_of \<Gamma>0 x" by (simp add: map_add_def)
    moreover have "map_of (rev benv) x = None"
    proof -
      have "x \<notin> fst ` set (map param_kind ps)" using None by (metis map_of_eq_None_iff set_rev)
      then have "x \<notin> fst ` set benv" using mf by (metis map_fst_param_kind set_map)
      then show ?thesis by (simp add: map_of_eq_None_iff)
    qed
    ultimately show ?thesis using xk xb by (simp add: map_add_def)
  qed
qed

lemma refs_into_iff:
  "x \<in> refs_into \<Gamma> R \<longleftrightarrow> (\<exists>k. (x, k) \<in> set \<Gamma> \<and> (case k of KRef _ _ i \<Rightarrow> i \<inter> R \<noteq> {} | _ \<Rightarrow> False))"
  by (auto simp: refs_into_def)

lemma refs_into_mono: "A \<subseteq> B \<Longrightarrow> refs_into \<Gamma> A \<subseteq> refs_into \<Gamma> B"
proof
  fix x assume AB: "A \<subseteq> B" and "x \<in> refs_into \<Gamma> A"
  then obtain k where k: "(x, k) \<in> set \<Gamma>" "case k of KRef _ _ i \<Rightarrow> i \<inter> A \<noteq> {} | _ \<Rightarrow> False"
    by (auto simp: refs_into_iff)
  then obtain T og I where "k = KRef T og I" "I \<inter> A \<noteq> {}" by (cases k) auto
  with k(1) AB show "x \<in> refs_into \<Gamma> B" unfolding refs_into_iff by (intro exI[of _ k]) auto
qed

lemma bargs_I:
  assumes "i < length ps" "i < length es" "es ! i = EPlace p" "borrows_mut (fst (ps ! i))"
  shows "place_origin \<Gamma> p \<subseteq> bargs \<Gamma> ps es"
proof -
  have "(ps ! i, es ! i) \<in> set (zip ps es)" using assms(1,2) by (metis in_set_zip fst_conv snd_conv)
  with assms(3,4) show ?thesis
    unfolding bargs_def by (cases "ps ! i") force
qed

text \<open>
  After the callee returns, the caller's invariant holds again: the callee
  changed the caller's memory only at the locations of mutably borrowed
  arguments, where it left well-typed values, and the checker invalidated
  the references into them.
\<close>

lemma caller_restore:
  assumes inv0: "inv P C \<Gamma> \<sigma> env st0" and inv2: "inv P C \<Gamma> \<sigma>' env st2"
    and ao: "args_ok P \<Gamma> env \<sigma>' bs st1 st2 ps es benv" and n01: "nroot st0 \<le> nroot st1"
    and ag: "hagree (wpaths (rev (map param_kind ps) @ \<Gamma>0) (rev benv @ E0) UNIV \<union>
               {(r, []) | x r. (x, Own r) \<in> set (rev benv @ E0)}) st2 st3"
    and nr: "nroot st2 \<le> nroot st3" "heap_fresh st3"
    and new: "\<forall>i < length ps. \<forall>q. snd (benv ! i) = Bor q \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow>
                (\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (ps ! i))) v)"
    and E0f: "\<forall>x b. (x, b) \<in> set E0 \<longrightarrow> nroot st0 \<le> fst (bpath b)"
    and dps: "distinct (map (fst \<circ> snd) ps)"
  shows "inv P C \<Gamma> \<sigma>' env st3 \<and> hagree (wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> {q. nroot st0 \<le> fst q}) st2 st3"
proof -
  from ao have mf: "map fst benv = map (fst \<circ> snd) ps" and le: "length es = length ps"
    and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs st1 st2 (ps ! i) (es ! i) (snd (benv ! i))"
    by (simp_all add: args_ok_def)
  define W where "W = {q. \<exists>i < length ps. snd (benv ! i) = Bor q \<and> borrows_mut (fst (ps ! i))}"
  define Wf where "Wf = {q :: path. nroot st0 \<le> fst q}"
  have sub: "wpaths (rev (map param_kind ps) @ \<Gamma>0) (rev benv @ E0) UNIV \<subseteq> W \<union> Wf"
  proof
    fix q assume "q \<in> wpaths (rev (map param_kind ps) @ \<Gamma>0) (rev benv @ E0) UNIV"
    then obtain x k b where xk: "map_of (rev (map param_kind ps) @ \<Gamma>0) x = Some k" and w: "writable k"
      and xb: "map_of (rev benv @ E0) x = Some b" and q: "q = bpath b" unfolding wpaths_def by blast
    from callee_var_cases[OF dps mf xk xb] show "q \<in> W \<union> Wf"
    proof
      assume "\<exists>i < length ps. x = fst (snd (ps ! i)) \<and> k = snd (param_kind (ps ! i)) \<and> b = snd (benv ! i)"
      then obtain i where i: "i < length ps" "k = snd (param_kind (ps ! i))" "b = snd (benv ! i)" by blast
      obtain c y T where pi: "ps ! i = (c, y, T)" by (cases "ps ! i")
      have a: "aok P \<Gamma> env \<sigma>' bs st1 st2 (c, y, T) (es ! i) b"
        using ak[rule_format, OF i(1)] pi i(3) by simp
      show ?thesis
      proof (cases b)
        case (Own r)
        from a[unfolded Own] have "nroot st1 \<le> r" by (simp add: aok_def)
        with Own q n01 show ?thesis by (simp add: Wf_def)
      next
        case (Bor q')
        from a[unfolded Bor] have "c \<noteq> Var" "c \<noteq> Deinit" by (auto simp: aok_def)
        with w i(2) pi have "borrows_mut c" by (cases c) (auto simp: param_kind_def borrows_mut_def)
        with Bor q i pi show ?thesis by (auto simp: W_def)
      qed
    next
      assume "map_of \<Gamma>0 x = Some k \<and> map_of E0 x = Some b"
      then show ?thesis using E0f q map_of_SomeD unfolding Wf_def by fastforce
    qed
  qed
  have sub2: "{(r, []) | x r. (x, Own r) \<in> set (rev benv @ E0)} \<subseteq> Wf"
  proof
    fix q :: path assume "q \<in> {(r, []) | x r. (x, Own r) \<in> set (rev benv @ E0)}"
    then obtain x r where q: "q = (r, [])" and xr: "(x, Own r) \<in> set benv \<or> (x, Own r) \<in> set E0" by auto
    then show "q \<in> Wf"
    proof (elim disjE)
      assume "(x, Own r) \<in> set benv"
      from own_root_in[OF this] obtain j where j: "j < length benv" "snd (benv ! j) = Own r" by blast
      have lb: "length benv = length ps" using mf by (metis length_map)
      from ak j lb have "nroot st1 \<le> r" by (cases "ps ! j") (auto simp: aok_def)
      with q n01 show ?thesis by (simp add: Wf_def)
    next
      assume "(x, Own r) \<in> set E0"
      with E0f q show ?thesis by (fastforce simp: Wf_def)
    qed
  qed
  have agW: "hagree (W \<union> Wf) st2 st3"
    by (rule hagree_mono[OF ag]) (use sub sub2 below_refl in blast)
  have ron: "\<forall>q \<in> Wf. fst q \<notin> envroots env"
    using inv0 by (auto simp: Wf_def envroots_def dest: inv_bounds)
  have agon: "hagree_on (envroots env) W st2 st3" by (rule hagree_on_union[OF agW ron])
  have wt: "wtarget P \<Gamma> env \<sigma>' st2 st3 q" if q: "q \<in> W" for q
  proof -
    from q obtain i where i: "i < length ps" "snd (benv ! i) = Bor q" "borrows_mut (fst (ps ! i))"
      by (auto simp: W_def)
    obtain c y T where pi: "ps ! i = (c, y, T)" by (cases "ps ! i")
    have a: "aok P \<Gamma> env \<sigma>' bs st1 st2 (c, y, T) (es ! i) (Bor q)"
      using ak[rule_format, OF i(1)] pi i(2) by simp
    have bmc: "borrows_mut c" using i(3) pi by simp
    from a bmc obtain p where p: "ploc P \<Gamma> env p T q" "\<exists>v. get st2 q = Ok v \<and> vt P T v"
      "mut_ok \<Gamma> p = Good ()" "\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>'"
      by (auto simp: aok_def)
    from p(1) obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
      "map_of env z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T"
      by (auto simp: ploc_def)
    have "writable kz" using mut_ok_writable[OF p(3) z(1-3)] .
    moreover have "\<exists>v. get st3 q = Ok v \<and> vt P T v" using new[rule_format, OF i(1) i(2)] i(3) pi by simp
    moreover have "\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> {z} \<subseteq> a_inval \<sigma>'"
      using p(4) refs_into_mono[of "{z}" "place_origin \<Gamma> p"] z(1) by blast
    ultimately show ?thesis using z p(2) unfolding wtarget_def by blast
  qed
  have i3: "inv P C \<Gamma> \<sigma>' env st3"
    by (rule inv_chg[OF inv2 wff agon nr]) (use wt in auto)
  have "\<forall>q \<in> W \<union> Wf. \<exists>q' \<in> wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> Wf. below q q'"
  proof
    fix q assume "q \<in> W \<union> Wf"
    then show "\<exists>q' \<in> wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> Wf. below q q'"
    proof
      assume "q \<in> W"
      then obtain i where i: "i < length ps" "snd (benv ! i) = Bor q" "borrows_mut (fst (ps ! i))"
        by (auto simp: W_def)
      obtain c y T where pi: "ps ! i = (c, y, T)" by (cases "ps ! i")
      have a: "aok P \<Gamma> env \<sigma>' bs st1 st2 (c, y, T) (es ! i) (Bor q)"
        using ak[rule_format, OF i(1)] pi i(2) by simp
      have bmc: "borrows_mut c" using i(3) pi by simp
      from a bmc obtain p where p: "es ! i = EPlace p" "ploc P \<Gamma> env p T q" "mut_ok \<Gamma> p = Good ()"
        by (auto simp: aok_def)
      from p(2) obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
        "map_of env z = Some bz" "q = pext (bpath bz) ss" by (auto simp: ploc_def)
      have "z \<in> bargs \<Gamma> ps es" using bargs_I[OF i(1) _ p(1) i(3)] le i(1) z(1) by auto
      moreover have "writable kz" using mut_ok_writable[OF p(3) z(1-3)] .
      ultimately have "bpath bz \<in> wpaths \<Gamma> env (bargs \<Gamma> ps es)" using z by (auto simp: wpaths_def)
      with z(5) show ?thesis by (metis UnI1 below_pext)
    next
      assume "q \<in> Wf"
      then show ?thesis using below_refl by blast
    qed
  qed
  then have "hagree (wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> Wf) st2 st3" by (rule hagree_mono[OF agW])
  with i3 show ?thesis by (simp add: Wf_def)
qed

lemma hagree_drop_fresh:
  "hagree (W \<union> {q. M \<le> fst q}) st st' \<Longrightarrow> nroot st \<le> M \<Longrightarrow> hagree W st st'"
proof -
  assume ag: "hagree (W \<union> {q. M \<le> fst q}) st st'" and M: "nroot st \<le> M"
  show ?thesis
    unfolding hagree_def
  proof (intro conjI allI impI)
    fix r assume r: "r < nroot st" "r \<notin> fst ` W"
    then have "r \<notin> fst ` (W \<union> {q. M \<le> fst q})" using M by auto
    with ag r(1) show "heap st' r = heap st r" by (rule hagreeD1)
  next
    fix p assume p: "fst p < nroot st" "\<forall>q \<in> W. \<not> below p q"
    then have "\<forall>q \<in> W \<union> {q. M \<le> fst q}. \<not> below p q" using M by (auto simp: below_def)
    with ag p(1) show "rskel (get st' p) = rskel (get st p)" by (rule hagreeD2)
  qed
qed



section \<open>Calls\<close>

lemma own_unique_args:
  assumes "args_ok P \<Gamma> env \<sigma>' bs st1 st2 ps es benv" "\<forall>x r. (x, Own r) \<notin> set E0"
  shows "\<forall>x y r. (x, Own r) \<in> set (rev benv @ E0) \<longrightarrow> (y, Own r) \<in> set (rev benv @ E0) \<longrightarrow> x = y"
  using assms own_root_unique[of benv] by (auto simp: args_ok_def)

lemma callee_param_lookup:
  assumes dist: "distinct (map (fst \<circ> snd) ps @ map fst \<Gamma>0)" and mf: "map fst benv = map (fst \<circ> snd) ps"
    and i: "i < length ps"
  shows "map_of (rev (map param_kind ps) @ \<Gamma>0) (fst (snd (ps ! i))) = Some (snd (param_kind (ps ! i)))"
    "map_of (rev benv @ E0) (fst (snd (ps ! i))) = Some (snd (benv ! i))"
proof -
  have lb: "length benv = length ps" using mf by (metis length_map)
  have dps: "distinct (map (fst \<circ> snd) ps)" using dist by simp
  have dGp: "distinct (map fst (map param_kind ps))" using dps by simp
  have dbenv: "distinct (map fst benv)" using dps mf by simp
  have "map_of (map param_kind ps) (fst (snd (ps ! i))) = Some (snd (param_kind (ps ! i)))"
    using map_of_nth_distinct[OF dGp, of i] i by simp
  then show "map_of (rev (map param_kind ps) @ \<Gamma>0) (fst (snd (ps ! i))) = Some (snd (param_kind (ps ! i)))"
    using map_of_rev_distinct[OF dGp] by (simp add: map_add_def)
  have "map_of benv (fst (snd (ps ! i))) = Some (snd (benv ! i))"
    using map_of_nth_distinct[OF dbenv, of i] i lb mf by (metis comp_apply nth_map)
  then show "map_of (rev benv @ E0) (fst (snd (ps ! i))) = Some (snd (benv ! i))"
    using map_of_rev_distinct[OF dbenv] by (simp add: map_add_def)
qed

lemma one_out_params:
  assumes "length (filter (\<lambda>(c, _, _). c = Out) ps) \<le> 1" "distinct (map (fst \<circ> snd) ps)"
  shows "one_out (rev (map param_kind ps))"
  unfolding one_out_def
proof (intro allI impI)
  fix x y T U
  assume x: "map_of (rev (map param_kind ps)) x = Some (KBorrow Out T)"
    and y: "map_of (rev (map param_kind ps)) y = Some (KBorrow Out U)"
  have dGp: "distinct (map fst (map param_kind ps))" using assms(2) by simp
  from x y have "map_of (map param_kind ps) x = Some (KBorrow Out T)" "map_of (map param_kind ps) y = Some (KBorrow Out U)"
    using map_of_rev_distinct[OF dGp] by simp_all
  from this[THEN map_of_index] obtain i j where i: "i < length ps" "x = fst (snd (ps ! i))"
    "KBorrow Out T = snd (param_kind (ps ! i))" and j: "j < length ps" "y = fst (snd (ps ! j))"
    "KBorrow Out U = snd (param_kind (ps ! j))" by auto
  have ci: "fst (ps ! i) = Out" and cj: "fst (ps ! j) = Out"
    using i(3) j(3) param_kind_nth[OF i(1)] param_kind_nth[OF j(1)] by (auto split: if_splits)
  show "x = y"
  proof (rule ccontr)
    assume "x \<noteq> y"
    with i(2) j(2) have ij: "i \<noteq> j" by auto
    have "card {k. k < length ps \<and> fst (ps ! k) = Out} \<ge> 2"
    proof -
      have "{i, j} \<subseteq> {k. k < length ps \<and> fst (ps ! k) = Out}" using i(1) j(1) ci cj by auto
      from card_mono[OF _ this] ij show ?thesis by auto
    qed
    moreover have "length (filter (\<lambda>(c, _, _). c = Out) ps) = card {k. k < length ps \<and> fst (ps ! k) = Out}"
      by (simp add: length_filter_conv_card case_prod_unfold)
    ultimately show False using assms(1) by simp
  qed
qed

lemma inv_heap_envroots:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and h: "\<forall>r \<in> envroots env. heap st' r = heap st r"
    and n: "nroot st \<le> nroot st'" and fr: "heap_fresh st'"
  shows "inv P C \<Gamma> \<sigma> env st'"
proof -
  have get: "get st' p0 = get st p0" if "fst p0 \<in> envroots env" for p0
    using that h by (intro get_root_cong) simp
  have "binding_ok P C \<Gamma> \<sigma> env st' x k b" if "map_of \<Gamma> x = Some k" "map_of env x = Some b"
    "binding_ok P C \<Gamma> \<sigma> env st x k b" for x k b
  proof (cases k)
    case (KOwned T)
    with that h envroots_I[OF that(2)] show ?thesis by (auto split: if_splits)
  next
    case (KBorrow c T)
    with that get[of "bpath b"] envroots_I[OF that(2)] show ?thesis by simp
  next
    case (KRef T og I)
    with that(3) obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
      "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    have "get st' q = get st q" using get envroots_I[OF rf(5)] rf(6) by simp
    with rf have "binding_ok P C \<Gamma> \<sigma> env st' x (KRef T og I) b"
      unfolding binding_ok.simps by (metis (no_types, lifting))
    with KRef show ?thesis by simp
  qed
  with inv n fr show ?thesis
    by (fastforce simp: inv_def heap_fresh_def dest: less_le_trans)
qed

lemma envroots_bound: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> r \<in> envroots env \<Longrightarrow> r < nroot st"
  by (auto simp: envroots_def dest: inv_bounds)

lemma chg_call:
  assumes "chg \<Gamma> env V1 st st2" "hagree (wpaths \<Gamma> env V2 \<union> {q. nroot st \<le> fst q}) st2 st3"
    "nroot st2 \<le> nroot st3" "heap_fresh st3"
  shows "chg \<Gamma> env (V1 \<union> V2) st st3"
proof -
  from assms(1) have n: "nroot st \<le> nroot st2" and ag: "hagree (wpaths \<Gamma> env V1) st st2"
    by (simp_all add: chg_def)
  have "hagree (wpaths \<Gamma> env V1 \<union> (wpaths \<Gamma> env V2 \<union> {q. nroot st \<le> fst q})) st st3"
    by (rule hagree_trans[OF ag assms(2) n])
  then have "hagree (wpaths \<Gamma> env (V1 \<union> V2) \<union> {q. nroot st \<le> fst q}) st st3"
    by (simp add: wpaths_Un Un_assoc)
  from hagree_drop_fresh[OF this order_refl] n assms(3,4) show ?thesis by (simp add: chg_def)
qed

lemma chk_args_var:
  "chk_args C \<Gamma> \<sigma> (map (\<lambda>(fl, T). (Var, fl, T)) fs) es = Good (\<sigma>', bs) \<Longrightarrow>
   chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>' \<and> bs = []"
proof (induction fs arbitrary: es \<sigma> bs)
  case Nil
  then show ?case by (cases es) auto
next
  case (Cons fT fs)
  then show ?case by (cases es; cases fT) (auto split: prod.splits)
qed

lemma eargs_var: "eargs P \<Gamma> (map (\<lambda>(fl, T). (Var, fl, T)) fs) es \<subseteq> mroots_l P \<Gamma> es"
proof (induction fs arbitrary: es)
  case (Cons fT fs)
  then show ?case by (cases es; cases fT) auto
qed simp

lemma etypes_length: "etypes P \<Gamma> es = Good Ts \<Longrightarrow> length Ts = length es"
proof (induction es arbitrary: Ts)
  case (Cons e es)
  then show ?case by auto
qed simp

lemma eargs_var_eq:
  "length es = length fs \<Longrightarrow> eargs P \<Gamma> (map (\<lambda>(fl, T). (Var, fl, T)) fs) es = mroots_l P \<Gamma> es"
proof (induction fs arbitrary: es)
  case (Cons fT fs)
  then show ?case by (cases es; cases fT) auto
qed simp

lemma bargs_var: "bargs \<Gamma> (map (\<lambda>(fl, T). (Var, fl, T)) fs) es = {}"
  by (auto simp: bargs_def in_set_zip borrows_mut_def split: prod.splits expr.splits)

lemma ref_args_I:
  assumes "i < length ps" "i < length es" "es ! i = EPlace p" "fst (snd (ps ! i)) \<in> set ns"
  shows "p \<in> set (ref_args ps es ns)"
proof -
  have "(ps ! i, es ! i) \<in> set (zip ps es)" using assms(1,2) by (metis in_set_zip fst_conv snd_conv)
  with assms(3,4) show ?thesis unfolding ref_args_def by (cases "ps ! i") force
qed

lemma vt_fieldwise:
  assumes sd: "find_struct P f = Some sd" and d: "distinct (map fst (sd_fields sd))"
    and vs: "list_all2 (vt P) (map snd (sd_fields sd)) vs"
  shows "vt P (TStruct f) (VStruct f (zip (map fst (sd_fields sd)) vs))"
proof -
  have len: "length vs = length (sd_fields sd)" using vs list_all2_lengthD by fastforce
  have "\<forall>(fl, u) \<in> set (zip (map fst (sd_fields sd)) vs). \<exists>U. map_of (sd_fields sd) fl = Some U \<and> vt P U u"
  proof (clarify)
    fix fl u assume "(fl, u) \<in> set (zip (map fst (sd_fields sd)) vs)"
    then obtain i where i: "i < length vs" "fl = fst (sd_fields sd ! i)" "u = vs ! i"
      using len by (auto simp: in_set_zip)
    have "map_of (sd_fields sd) fl = Some (snd (sd_fields sd ! i))"
      using map_of_nth_distinct[OF d, of i] i len by simp
    moreover have "vt P (snd (sd_fields sd ! i)) u" using vs i len by (simp add: list_all2_conv_all_nth)
    ultimately show "\<exists>U. map_of (sd_fields sd) fl = Some U \<and> vt P U u" by blast
  qed
  with sd len show ?thesis by simp
qed

lemma out_not_own_args:
  assumes ao: "args_ok P \<Gamma> env \<sigma>' bs st1 st2 ps es benv" and dps: "distinct (map (fst \<circ> snd) ps)"
    and E0no: "\<forall>x T r. map_of \<Gamma>0 x = Some (KBorrow Out T) \<longrightarrow> map_of E0 x \<noteq> Some (Own r)"
  shows "\<forall>x T r. map_of (rev (map param_kind ps) @ \<Gamma>0) x = Some (KBorrow Out T) \<longrightarrow>
           map_of (rev benv @ E0) x \<noteq> Some (Own r)"
proof (intro allI impI notI)
  fix x T r assume xk: "map_of (rev (map param_kind ps) @ \<Gamma>0) x = Some (KBorrow Out T)"
    and xb: "map_of (rev benv @ E0) x = Some (Own r)"
  from ao have mf: "map fst benv = map (fst \<circ> snd) ps"
    and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs st1 st2 (ps ! i) (es ! i) (snd (benv ! i))"
    by (simp_all add: args_ok_def)
  from callee_var_cases[OF dps mf xk xb] show False
  proof
    assume "\<exists>i < length ps. x = fst (snd (ps ! i)) \<and> KBorrow Out T = snd (param_kind (ps ! i)) \<and>
              Own r = snd (benv ! i)"
    then obtain i where i: "i < length ps" "KBorrow Out T = snd (param_kind (ps ! i))" "Own r = snd (benv ! i)"
      by blast
    obtain c y U where pi: "ps ! i = (c, y, U)" by (cases "ps ! i")
    with i(2) have "c = Out" by (auto simp: param_kind_def split: if_splits)
    from ak[rule_format, OF i(1)] pi i(3)[symmetric] \<open>c = Out\<close> show False by (simp add: aok_def borrows_mut_def)
  next
    assume "map_of \<Gamma>0 x = Some (KBorrow Out T) \<and> map_of E0 x = Some (Own r)"
    with E0no show False by blast
  qed
qed

lemma args_conv_bm:
  assumes ak: "aok P \<Gamma> env \<sigma>' bs st1 st2 (c, y, T) e b" and bm: "borrows_mut c"
  shows "\<exists>q p. b = Bor q \<and> e = EPlace p \<and> (p, c) \<in> set bs \<and> ploc P \<Gamma> env p T q \<and> rloc env p q \<and>
           (\<exists>v. get st2 q = Ok v \<and> vt P T v) \<and> mut_ok \<Gamma> p = Good () \<and>
           (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>')"
  using assms by (cases b) (auto simp: aok_def)

text \<open>
  The new values of the mutably borrowed arguments, as left by the callee,
  in the form needed by @{text "caller_restore"}.
\<close>

lemma new_args:
  assumes post: "\<forall>x c T q. map_of (rev (map param_kind ps) @ \<Gamma>0) x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
                   map_of (rev benv @ E0) x = Some (Bor q) \<longrightarrow> (\<exists>v. get st3 q = Ok v \<and> vt P T v)"
    and dist: "distinct (map (fst \<circ> snd) ps @ map fst \<Gamma>0)" and mf: "map fst benv = map (fst \<circ> snd) ps"
  shows "\<forall>i < length ps. \<forall>q. snd (benv ! i) = Bor q \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow>
           (\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (ps ! i))) v)"
proof (intro allI impI)
  fix i q assume i: "i < length ps" and b: "snd (benv ! i) = Bor q" and bm: "borrows_mut (fst (ps ! i))"
  have nv: "fst (ps ! i) \<noteq> Var" "fst (ps ! i) \<noteq> Imm" using bm by (auto simp: borrows_mut_def)
  have k: "map_of (rev (map param_kind ps) @ \<Gamma>0) (fst (snd (ps ! i))) =
      Some (KBorrow (fst (ps ! i)) (snd (snd (ps ! i))))"
    using callee_param_lookup(1)[OF dist mf i] param_kind_nth[OF i] nv by simp
  have b': "map_of (rev benv @ E0) (fst (snd (ps ! i))) = Some (Bor q)"
    using callee_param_lookup(2)[OF dist mf i, of E0] b by simp
  from post[rule_format, OF k nv(2) b'] show "\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (ps ! i))) v" .
qed

lemma SCF_Suc:
  assumes IHa: "SA P n" and IHi: "SI P n" and IHes: "SES P n"
  shows "SCF P (Suc n)"
  unfolding SCF_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st f es \<sigma>' T
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and cc: "chk_call C \<Gamma> \<sigma> f es = Good \<sigma>'"
    and ty: "etype P \<Gamma> (ECall f es) = Good T"
  from cc CP obtain ps bs where cp: "call_params P f = Good ps" and ca: "chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs)"
    and ex: "exclusive \<Gamma> bs = Good ()" by (auto simp: chk_call_def)
  from ty cp have ts: "etypes P \<Gamma> es = Good (param_tys ps)" and T: "T = call_ret P f" by auto
  have mr: "mroots P \<Gamma> (ECall f es) = eargs P \<Gamma> ps es \<union> bargs \<Gamma> ps es" using cp by simp
  have fr: "heap_fresh st" using inv_heap_fresh[OF inv] .
  show "spec (call_fun P (Suc n) env st f es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and> cres P \<Gamma> env f es st' r)"
  proof (cases "find_struct P f")
    case (Some sd)
    note sdf = wf_struct_facts[OF wf Some]
    show ?thesis
    proof (cases "sd_init sd")
      case None
      with cp Some have fw: "sd_fieldwise sd" and ps: "ps = map (\<lambda>(fl, T). (Var, fl, T)) (sd_fields sd)"
        by (auto simp: call_params_def split: if_splits)
      from chk_args_var[OF ca[unfolded ps]] have ce: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>'" by blast
      have ts': "etypes P \<Gamma> es = Good (map snd (sd_fields sd))"
        using ts ps by (simp add: param_tys_def comp_def case_prod_unfold)
      have IH: "spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots_l P \<Gamma> es) st st' \<and> list_all2 (vt P) (map snd (sd_fields sd)) vs)"
        using IHes CP inv ce ts' unfolding SES_def by blast
      have lenes: "length es = length (sd_fields sd)"
        using ts' by (metis etypes_length length_map)
      have sub: "mroots_l P \<Gamma> es \<subseteq> mroots P \<Gamma> (ECall f es)"
        using mr ps eargs_var_eq[OF lenes] bargs_var by auto
      have unf: "call_fun P (Suc n) env st f es = do { (vs, st) \<leftarrow> evals P n env st es;
          if length vs = length (sd_fields sd)
          then Ok (RV (VStruct f (zip (map fst (sd_fields sd)) vs)), st) else Err ErrArity }"
        using \<open>find_struct P f = Some sd\<close> None fw by simp
      show ?thesis
        unfolding unf
      proof (rule spec_bind_pair[OF IH], elim conjE)
        fix vs st1 assume i1: "inv P C \<Gamma> \<sigma>' env st1" and c1: "chg \<Gamma> env (mroots_l P \<Gamma> es) st st1"
          and va: "list_all2 (vt P) (map snd (sd_fields sd)) vs"
        have len: "length vs = length (sd_fields sd)" using va list_all2_lengthD by fastforce
        have "vt P (TStruct f) (VStruct f (zip (map fst (sd_fields sd)) vs))"
          by (rule vt_fieldwise[OF Some sdf(1) va])
        with i1 chg_mono[OF c1 sub] len Some show "spec (if length vs = length (sd_fields sd)
              then Ok (RV (VStruct f (zip (map fst (sd_fields sd)) vs)), st1) else Err ErrArity)
            (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and>
               cres P \<Gamma> env f es st' r)" by (simp add: cres_def)
      qed
    next
      case (Some fd)
      note fdf = sdf(2)[OF Some]
      from fdf obtain sx ps0 where fp: "fd_params fd = (Out, sx, TStruct f) # ps0" by blast
      have fr0: "fd_ret fd = RNone" using fdf by blast
      have cb: "chk_body P RNone (map fst (sd_fields sd)) (fd_params fd) (fd_body fd) = Good ()" using fdf by blast
      from cp \<open>find_struct P f = Some sd\<close> Some fp have ps: "ps = ps0" by (simp add: call_params_def)
      define v0 where "v0 = VStruct f (map (\<lambda>(fl, _). (fl, VUndef)) (sd_fields sd))"
      obtain r st1 where al: "alloc st v0 = (r, st1)" by (cases "alloc st v0")
      note af = alloc_facts[OF al]
      have inv1: "inv P C \<Gamma> \<sigma> env st1" using inv_alloc[OF inv al] .
      have ch01: "chg \<Gamma> env {} st st1"
        by (rule chg_heap) (use af fr in auto)
      have IHa': "spec (pass_args P n env st1 ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st' \<and> args_ok P \<Gamma> env \<sigma>' bs st1 st' ps es benv)"
        using IHa CP inv1 ca ts ex unfolding SA_def by blast
      have unf: "call_fun P (Suc n) env st f es = do {
          (benv, st) \<leftarrow> pass_args P n env st1 ps es;
          (_, st) \<leftarrow> invoke P n st fd (rev benv @ [(sx, Bor (r, []))]);
          v \<leftarrow> get st (r, []);
          (case v of
             VStruct _ fs \<Rightarrow>
               if list_all (\<lambda>(_, u). u \<noteq> VUndef) fs then Ok (RV v, free st r)
               else Err ErrFieldInit
           | _ \<Rightarrow> Err ErrFieldInit) }"
        using \<open>find_struct P f = Some sd\<close> Some fp al ps by (simp add: v0_def)
      show ?thesis
        unfolding unf
      proof (rule spec_bind_pair[OF IHa'], elim conjE)
        fix benv st2 assume inv2: "inv P C \<Gamma> \<sigma>' env st2" and ch12: "chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st2"
          and ao: "args_ok P \<Gamma> env \<sigma>' bs st1 st2 ps es benv"
        have mf: "map fst benv = map (fst \<circ> snd) ps" using ao by (simp add: args_ok_def)
        have n01: "nroot st \<le> nroot st1" using af by simp
        have n12: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2" using ch12 by (simp_all add: chg_def)
        have rb: "r = nroot st" using af by simp
        have h2: "heap st2 r = Some v0"
        proof -
          have "r \<notin> fst ` wpaths \<Gamma> env (eargs P \<Gamma> ps es)" using wpaths_bound[OF inv] rb by fastforce
          moreover have "r < nroot st1" using af by simp
          ultimately have "heap st2 r = heap st1 r" using ch12 hagreeD1 by (fastforce simp: chg_def)
          with af show ?thesis by simp
        qed
        let ?C' = "\<lparr>c_prog = P, c_ret = RNone, c_fields = map fst (sd_fields sd)\<rparr>"
        let ?\<Gamma>0 = "[(sx, KBorrow Out (TStruct f))]" and ?E0 = "[(sx, Bor (r, []))]"
        have dall: "distinct (map (fst \<circ> snd) (fd_params fd))" using chk_body_facts(2)[OF cb] by simp
        have dist: "distinct (map (fst \<circ> snd) ps @ map fst ?\<Gamma>0)" using dall fp ps by auto
        have dall': "distinct (map (fst \<circ> snd) ps)" using dist by simp
        have Gc: "rev (map param_kind (fd_params fd)) = rev (map param_kind ps) @ ?\<Gamma>0"
          using fp ps by (simp add: param_kind_def)
        have oo: "one_out (rev (map param_kind ps) @ ?\<Gamma>0)"
          using one_out_params[OF chk_body_facts(3)[OF cb] dall] Gc by simp
        have noout: "\<forall>i < length ps. fst (ps ! i) \<noteq> Out"
        proof (intro allI impI notI)
          fix i assume i: "i < length ps" and o: "fst (ps ! i) = Out"
          have "ps ! i \<in> set (filter (\<lambda>(c, _, _). c = Out) ps)" using i o nth_mem[OF i] by (cases "ps ! i") auto
          then have "1 \<le> length (filter (\<lambda>(c, _, _). c = Out) ps)"
            by (metis Suc_leI length_pos_if_in_set One_nat_def)
          with chk_body_facts(3)[OF cb] fp ps show False by simp
        qed
        have ov: "out_val P ?C' (astate0 (fd_params fd)) (TStruct f) v0"
        proof (cases "sd_fields sd = []")
          case True
          with \<open>find_struct P f = Some sd\<close> show ?thesis by (simp add: out_val_def v0_def)
        next
          case False
          have "\<forall>(fl, u) \<in> set (map (\<lambda>(fl, _). (fl, VUndef)) (sd_fields sd)). \<exists>U. map_of (sd_fields sd) fl = Some U \<and>
                  wt_opt P U u \<and> (fl \<in> a_fields (astate0 (fd_params fd)) \<longrightarrow> vt P U u)"
            by (auto simp: wt_opt_def astate0_def dest: weak_map_of_SomeI)
          with False \<open>find_struct P f = Some sd\<close> show ?thesis
            by (simp add: out_val_def v0_def map_skel_fields comp_def)
        qed
        have ci: "inv P ?C' (rev (map param_kind ps) @ ?\<Gamma>0) (astate0 (fd_params fd)) (rev benv @ ?E0) st2"
        proof (rule callee_inv[OF inv ao n01 n12 fr2 dist oo])
          show "\<forall>(x, k) \<in> set ?\<Gamma>0. \<not> is_ref k" by simp
          show "\<forall>x k b. map_of ?\<Gamma>0 x = Some k \<longrightarrow> map_of ?E0 x = Some b \<longrightarrow>
              binding_ok P ?C' (rev (map param_kind ps) @ ?\<Gamma>0) (astate0 (fd_params fd)) (rev benv @ ?E0) st2 x k b \<and>
              nroot st \<le> fst (bpath b) \<and> fst (bpath b) < nroot st1"
            using h2 ov rb af by (auto simp: get_def)
          show "\<forall>i < length ps. fst (ps ! i) = Out \<longrightarrow> c_fields ?C' = []" using noout by blast
        qed simp_all
        have cok: "callee_ok P ?C' fd (rev benv @ ?E0) st2"
          unfolding callee_ok_def using fr0 cb ci Gc own_unique_args[OF ao, of ?E0]
            out_not_own_args[OF ao dall', of ?\<Gamma>0 ?E0, simplified] by simp
        have IHi': "spec (invoke P n st2 fd (rev benv @ ?E0)) (invoke_post P fd (rev benv @ ?E0) st2)"
          using IHi cok unfolding SI_def by blast
        show "spec (do { (_, st) \<leftarrow> invoke P n st2 fd (rev benv @ ?E0);
              v \<leftarrow> get st (r, []);
              (case v of VStruct _ fs \<Rightarrow> if list_all (\<lambda>(_, u). u \<noteq> VUndef) fs then Ok (RV v, free st r)
                                        else Err ErrFieldInit
               | _ \<Rightarrow> Err ErrFieldInit) })
            (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and>
               cres P \<Gamma> env f es st' r)"
        proof (rule spec_bind_pairQ[OF IHi'])
          fix rv st3 assume ip: "invoke_post P fd (rev benv @ ?E0) st2 (rv, st3)"
          then have n23: "nroot st2 \<le> nroot st3" and fr3: "heap_fresh st3"
            and ag3: "hagree (wpaths (rev (map param_kind ps) @ ?\<Gamma>0) (rev benv @ ?E0) UNIV \<union>
                {(r, []) | x r. (x, Own r) \<in> set (rev benv @ ?E0)}) st2 st3"
            and wr: "\<forall>x c T q. map_of (rev (map param_kind ps) @ ?\<Gamma>0) x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
                map_of (rev benv @ ?E0) x = Some (Bor q) \<longrightarrow> (\<exists>v. get st3 q = Ok v \<and> vt P T v)"
            by (simp_all add: invoke_post_def Gc)
          have sxn: "sx \<notin> set (map (fst \<circ> snd) ps)" using dist by simp
          have n1: "map_of (rev (map param_kind ps)) sx = None"
            using sxn by (force simp: map_of_eq_None_iff)
          have n2: "map_of (rev benv) sx = None"
            using sxn mf by (metis map_of_eq_None_iff set_map set_rev)
          have "map_of (rev (map param_kind ps) @ ?\<Gamma>0) sx = Some (KBorrow Out (TStruct f))"
            "map_of (rev benv @ ?E0) sx = Some (Bor (r, []))"
            by (simp_all add: map_add_def n1 n2)
          with wr obtain vS where gS: "get st3 (r, []) = Ok vS" "vt P (TStruct f) vS" by blast
          from gS(2) obtain fs where vS: "vS = VStruct f fs"
            "\<forall>(fl, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) fl = Some U \<and> vt P U u"
            using \<open>find_struct P f = Some sd\<close> by (cases vS) auto
          have all: "list_all (\<lambda>(_, u). u \<noteq> VUndef) fs"
            using vS(2) by (auto simp: list_all_iff)
          have new: "\<forall>i < length ps. \<forall>q. snd (benv ! i) = Bor q \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow>
              (\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (ps ! i))) v)"
            by (rule new_args[OF wr dist mf])
          have E0f: "\<forall>x b. (x, b) \<in> set ?E0 \<longrightarrow> nroot st \<le> fst (bpath b)" using rb by simp
          from caller_restore[OF inv inv2 ao n01 ag3 n23 fr3 new E0f] dall fp ps
          have cr: "inv P C \<Gamma> \<sigma>' env st3"
            "hagree (wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> {q. nroot st \<le> fst q}) st2 st3" by auto
          have ch02: "chg \<Gamma> env (eargs P \<Gamma> ps es) st st2" using chg_trans[OF ch01 ch12] by simp
          have ch03: "chg \<Gamma> env (eargs P \<Gamma> ps es \<union> bargs \<Gamma> ps es) st st3"
            by (rule chg_call[OF ch02 cr(2) n23 fr3])
          let ?st4 = "free st3 r"
          have same4: "\<forall>r' < nroot st. heap ?st4 r' = heap st3 r'" using rb by (simp add: free_def)
          have fr4: "heap_fresh ?st4" using fr3 by (simp add: heap_fresh_def free_def)
          have inv4: "inv P C \<Gamma> \<sigma>' env ?st4"
            by (rule inv_heap_envroots[OF cr(1)]) (use same4 envroots_bound[OF inv] fr4 in \<open>auto simp: free_def\<close>)
          have ch04: "chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st ?st4"
            using ch03 same4 fr4 mr unfolding chg_def by (auto simp: free_def intro: hagree_heap_after)
          show "spec (do { v \<leftarrow> get st3 (r, []);
              (case v of VStruct _ fs \<Rightarrow> if list_all (\<lambda>(_, u). u \<noteq> VUndef) fs then Ok (RV v, free st3 r)
                                        else Err ErrFieldInit
               | _ \<Rightarrow> Err ErrFieldInit) })
            (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and>
               cres P \<Gamma> env f es st' r)"
            using gS vS all inv4 ch04 \<open>find_struct P f = Some sd\<close> by (simp add: cres_def)
        qed
      qed
    qed
  next
    case None
    with cp obtain fd where fd: "find_fun P f = Some fd" and ps: "ps = fd_params fd"
      by (auto simp: call_params_def split: option.splits)
    have cb: "chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()" using wf_fun[OF wf fd] .
    have IHa': "spec (pass_args P n env st ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
        chg \<Gamma> env (eargs P \<Gamma> ps es) st st' \<and> args_ok P \<Gamma> env \<sigma>' bs st st' ps es benv)"
      using IHa CP inv ca ts ex unfolding SA_def by blast
    show ?thesis
      unfolding call_fun.simps None option.case fd ps[symmetric]
    proof (rule spec_bind_pair[OF IHa'], elim conjE)
      fix benv st2 assume inv2: "inv P C \<Gamma> \<sigma>' env st2" and ch12: "chg \<Gamma> env (eargs P \<Gamma> ps es) st st2"
        and ao: "args_ok P \<Gamma> env \<sigma>' bs st st2 ps es benv"
      have mf: "map fst benv = map (fst \<circ> snd) ps" and le: "length es = length ps"
        and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>' bs st st2 (ps ! i) (es ! i) (snd (benv ! i))"
        using ao by (simp_all add: args_ok_def)
      have n12: "nroot st \<le> nroot st2" and fr2: "heap_fresh st2" using ch12 by (simp_all add: chg_def)
      let ?C' = "\<lparr>c_prog = P, c_ret = fd_ret fd, c_fields = []\<rparr>"
      have dall: "distinct (map (fst \<circ> snd) ps)" using chk_body_facts(2)[OF cb] ps by simp
      have dist: "distinct (map (fst \<circ> snd) ps @ map fst ([] :: senv))" using dall by simp
      have oo: "one_out (rev (map param_kind ps) @ [])"
        using one_out_params[OF chk_body_facts(3)[OF cb] dall[unfolded ps]] ps by simp
      have ci: "inv P ?C' (rev (map param_kind ps) @ []) (astate0 (fd_params fd)) (rev benv @ []) st2"
        by (rule callee_inv[OF inv ao order_refl n12 fr2 dist oo]) auto
      text \<open>The parameters named in the origin of a returned reference are mutably borrowed places.\<close>
      have refpar: "\<exists>i < length ps. fst (snd (ps ! i)) = z \<and> borrows_mut (fst (ps ! i))"
        if rr: "fd_ret fd = RRef ns U" "z \<in> set ns" for ns U z
      proof -
        from chk_body_facts(4)[OF cb] rr obtain cy where
          "cy \<in> set ps" "fst (snd cy) = z" "fst cy = conv.Mut \<or> fst cy = Ref"
          by (auto simp: list_all_iff list_ex_iff ps)
        then show ?thesis by (auto simp: in_set_conv_nth borrows_mut_def)
      qed
      have bor: "\<exists>q. snd (benv ! i) = Bor q" if "i < length ps" "borrows_mut (fst (ps ! i))" for i
      proof -
        obtain c y T where pi: "ps ! i = (c, y, T)" by (cases "ps ! i")
        from args_conv_bm[of \<Gamma> env \<sigma>' bs st st2 c y T "es ! i" "snd (benv ! i)"]
          ak[rule_format, OF that(1)] pi that(2) show ?thesis by auto
      qed
      have cok: "callee_ok P ?C' fd (rev benv) st2"
        unfolding callee_ok_def
      proof (intro conjI)
        show "inv P ?C' (rev (map param_kind (fd_params fd))) (astate0 (fd_params fd)) (rev benv) st2"
          using ci ps by simp
        show "chk_body P (fd_ret fd) (c_fields ?C') (fd_params fd) (fd_body fd) = Good ()" using cb by simp
        show "case fd_ret fd of RRef ns _ \<Rightarrow> \<forall>z \<in> set ns. \<exists>q. map_of (rev benv) z = Some (Bor q) | _ \<Rightarrow> True"
        proof (cases "fd_ret fd")
          case (RRef ns U)
          have "\<exists>q. map_of (rev benv) z = Some (Bor q)" if z: "z \<in> set ns" for z
          proof -
            from refpar[OF RRef z] obtain i where i: "i < length ps" "fst (snd (ps ! i)) = z"
              "borrows_mut (fst (ps ! i))" by blast
            from bor[OF i(1,3)] obtain q where "snd (benv ! i) = Bor q" by blast
            with callee_param_lookup(2)[OF dist mf i(1), of "[]"] i(2) show ?thesis by auto
          qed
          with RRef show ?thesis by simp
        qed simp_all
      qed (use own_unique_args[OF ao, of "[]", simplified]
               out_not_own_args[OF ao dall, of "[]" "[]", simplified] ps in auto)
      have IHi': "spec (invoke P n st2 fd (rev benv)) (invoke_post P fd (rev benv) st2)"
        using IHi cok unfolding SI_def by blast
      show "spec (invoke P n st2 fd (rev benv)) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
          chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st' \<and> cres P \<Gamma> env f es st' r)"
      proof (rule spec_mono[OF IHi'], clarify)
        fix rv st3 assume ip: "invoke_post P fd (rev benv) st2 (rv, st3)"
        then have n23: "nroot st2 \<le> nroot st3" and fr3: "heap_fresh st3"
          and ag3: "hagree (wpaths (rev (map param_kind ps) @ []) (rev benv @ []) UNIV \<union>
              {(r, []) | x r. (x, Own r) \<in> set (rev benv @ [])}) st2 st3"
          and wr: "\<forall>x c T q. map_of (rev (map param_kind ps) @ []) x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
              map_of (rev benv @ []) x = Some (Bor q) \<longrightarrow> (\<exists>v. get st3 q = Ok v \<and> vt P T v)"
          and rr: "ret_res P (fd_ret fd) (rev (map param_kind ps)) (rev benv) st3 rv"
          using ps by (simp_all add: invoke_post_def)
        have new: "\<forall>i < length ps. \<forall>q. snd (benv ! i) = Bor q \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow>
            (\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (ps ! i))) v)"
          by (rule new_args[OF wr dist mf])
        from caller_restore[OF inv inv2 ao order_refl ag3 n23 fr3 new _ dall]
        have cr: "inv P C \<Gamma> \<sigma>' env st3"
          "hagree (wpaths \<Gamma> env (bargs \<Gamma> ps es) \<union> {q. nroot st \<le> fst q}) st2 st3" by auto
        have ch: "chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st3"
          using chg_call[OF ch12 cr(2) n23 fr3] mr by simp
        have res: "cres P \<Gamma> env f es st3 rv"
        proof (cases "fd_ret fd")
          case (RRef ns U)
          from rr RRef obtain q z kz bz ss where q: "rv = RP q" "\<exists>v. get st3 q = Ok v \<and> vt P U v"
            "z \<in> set ns" "map_of (rev (map param_kind ps)) z = Some kz" "\<not> is_ref kz"
            "map_of (rev benv) z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some U"
            by (auto simp: ret_res_def oloc_def)
          from refpar[OF RRef q(3)] obtain i where i: "i < length ps" "fst (snd (ps ! i)) = z"
            "borrows_mut (fst (ps ! i))" by blast
          obtain c y Ti where pi: "ps ! i = (c, y, Ti)" by (cases "ps ! i")
          note lk = callee_param_lookup(1)[OF dist mf i(1)] callee_param_lookup(2)[OF dist mf i(1), of "[]"]
          from args_conv_bm[OF ak[rule_format, OF i(1), unfolded pi] i(3)[unfolded pi, simplified]]
          obtain qi p where a: "snd (benv ! i) = Bor qi" "es ! i = EPlace p" "ploc P \<Gamma> env p Ti qi" by auto
          have kz: "kz = KBorrow c Ti" using lk(1) q(4) i(2) pi i(3)
            by (auto simp: param_kind_def borrows_mut_def)
          have bz: "bz = Bor qi" using lk(2) q(6) i(2) a(1) by simp
          from a(3) obtain w kw bw ss' where w: "w \<in> place_origin \<Gamma> p" "map_of \<Gamma> w = Some kw"
            "\<not> is_ref kw" "map_of env w = Some bw" "qi = pext (bpath bw) ss'" "sty P (kind_ty kw) ss' = Some Ti"
            by (auto simp: ploc_def)
          have "p \<in> set (ref_args (fd_params fd) es ns)"
            using ref_args_I[OF i(1) _ a(2)] le i q(3) ps by auto
          then have wR: "w \<in> ref_origin_of \<Gamma> fd es ns" using w(1) by (auto simp: ref_origin_of_def)
          have "q = pext (bpath bw) (ss' @ ss)" using q(7) bz w(5) by simp
          moreover have "sty P (kind_ty kw) (ss' @ ss) = Some U" using w(6) q(8) kz by (simp add: sty_append)
          ultimately have "oloc P \<Gamma> env (ref_origin_of \<Gamma> fd es ns) (ref_origin_of \<Gamma> fd es ns) U q"
            using wR w(2,3,4) unfolding oloc_def by blast
          with q None fd RRef show ?thesis by (simp add: cres_def)
        qed (use rr None fd in \<open>auto simp: cres_def ret_res_def\<close>)
        with cr(1) ch show "inv P C \<Gamma> \<sigma>' env st3 \<and> chg \<Gamma> env (mroots P \<Gamma> (ECall f es)) st st3 \<and>
            cres P \<Gamma> env f es st3 rv" by blast
      qed
    qed
  qed
qed

text \<open>A method receiver joins the arguments as one more borrowed place, in front.\<close>

lemma aok_sigma:
  "aok P \<Gamma> env \<sigma>2 bs st1 st2 prm e b \<Longrightarrow> a_inval \<sigma>2 \<subseteq> a_inval \<sigma>3 \<Longrightarrow> set bs \<subseteq> set bs' \<Longrightarrow>
   aok P \<Gamma> env \<sigma>3 bs' st1 st2 prm e b"
  by (cases prm; cases b) (auto simp: aok_def)

lemma args_ok_recv:
  assumes inv0: "inv P C \<Gamma> \<sigma> env st0" and ao: "args_ok P \<Gamma> env \<sigma>2 bs st1 st2 ps es benv"
    and pl: "ploc P \<Gamma> env p T q" "rloc env p q" and g: "\<exists>v. get st2 q = Ok v \<and> vt P T v"
    and cv: "c \<noteq> Var" "c \<noteq> Deinit"
    and bmp: "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and>
                (\<not> trivial_ty T \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>3)"
    and s23: "a_inval \<sigma>2 \<subseteq> a_inval \<sigma>3"
    and ex: "\<forall>y \<in> set bs. excl_ok \<Gamma> (p, c) y"
  shows "args_ok P \<Gamma> env \<sigma>3 ((p, c) # bs) st1 st2 ((c, x, T) # ps) (EPlace p # es) ((x, Bor q) # benv)"
proof -
  from ao have mf: "map fst benv = map (fst \<circ> snd) ps" and le: "length es = length ps"
    and ak: "\<forall>i < length ps. aok P \<Gamma> env \<sigma>2 bs st1 st2 (ps ! i) (es ! i) (snd (benv ! i))"
    and di: "distinct [r. (x, Own r) \<leftarrow> benv]"
    and pw: "\<forall>i j q q'. i < length ps \<longrightarrow> j < length ps \<longrightarrow> i \<noteq> j \<longrightarrow> snd (benv ! i) = Bor q \<longrightarrow>
        snd (benv ! j) = Bor q' \<longrightarrow> borrows_mut (fst (ps ! i)) \<longrightarrow> \<not> overlaps q q'"
    by (simp_all add: args_ok_def)
  have head: "aok P \<Gamma> env \<sigma>3 ((p, c) # bs) st1 st2 (c, x, T) (EPlace p) (Bor q)"
    using pl g cv bmp by (auto simp: aok_def)
  have tail: "aok P \<Gamma> env \<sigma>3 ((p, c) # bs) st1 st2 (ps ! j) (es ! j) (snd (benv ! j))" if "j < length ps" for j
    by (rule aok_sigma[OF ak[rule_format, OF that] s23]) auto
  have one: "\<not> overlaps q q'" if j: "j < length ps" and bj: "snd (benv ! j) = Bor q'"
    and bm: "borrows_mut c \<or> borrows_mut (fst (ps ! j))" for j q'
  proof -
    obtain c' y' T' where pj: "ps ! j = (c', y', T')" by (cases "ps ! j")
    from ak[rule_format, OF j] pj bj obtain p' where p': "(p', c') \<in> set bs" "ploc P \<Gamma> env p' T' q'"
      "rloc env p' q'" "borrows_mut c' \<longrightarrow> mut_ok \<Gamma> p' = Good ()" by (auto simp: aok_def)
    from ex p'(1) bm pj have no: "\<not> overlap \<Gamma> p p'" by (auto simp: excl_ok_def)
    show ?thesis
    proof (cases "borrows_mut c")
      case True
      with bmp have "mut_ok \<Gamma> p = Good ()" by blast
      from excl_args[OF inv0 pl p'(2,3) no this] show ?thesis .
    next
      case False
      with bm pj p'(4) have mo: "mut_ok \<Gamma> p' = Good ()" by auto
      from no have "\<not> overlap \<Gamma> p' p" by (simp add: overlap_sym)
      from excl_args[OF inv0 p'(2,3) pl this mo] show ?thesis by (simp add: overlaps_sym)
    qed
  qed
  show ?thesis
    unfolding args_ok_def
  proof (intro conjI allI impI)
    show "map fst ((x, Bor q) # benv) = map (fst \<circ> snd) ((c, x, T) # ps)" using mf by simp
    show "length (EPlace p # es) = length ((c, x, T) # ps)" using le by simp
    show "distinct [r. (x, Own r) \<leftarrow> (x, Bor q) # benv]" using di by simp
  next
    fix i assume "i < length ((c, x, T) # ps)"
    then show "aok P \<Gamma> env \<sigma>3 ((p, c) # bs) st1 st2 (((c, x, T) # ps) ! i) ((EPlace p # es) ! i)
                 (snd (((x, Bor q) # benv) ! i))"
      using head tail by (cases i) auto
  next
    fix i j q1 q2
    assume ij: "i < length ((c, x, T) # ps)" "j < length ((c, x, T) # ps)" "i \<noteq> j"
      and bi: "snd (((x, Bor q) # benv) ! i) = Bor q1" and bj: "snd (((x, Bor q) # benv) ! j) = Bor q2"
      and bm: "borrows_mut (fst (((c, x, T) # ps) ! i))"
    show "\<not> overlaps q1 q2"
    proof (cases i)
      case 0
      with ij obtain j' where "j = Suc j'" "j' < length ps" by (cases j) auto
      with 0 bi bj bm one show ?thesis by auto
    next
      case (Suc i')
      show ?thesis
      proof (cases j)
        case 0
        with Suc ij bi bj bm one[of i' q1] show ?thesis by (auto simp: overlaps_sym)
      next
        case (Suc j')
        with \<open>i = Suc i'\<close> ij bi bj bm pw[rule_format, of i' j' q1 q2] show ?thesis by auto
      qed
    qed
  qed
qed

lemma ex_Good_unit: "(\<exists>u :: unit. m = Good u \<and> Q u) \<longleftrightarrow> (m = Good () \<and> Q ())"
  by auto

lemma list_write:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and pl: "ploc P \<Gamma> env p T q" and mo: "mut_ok \<Gamma> p = Good ()"
    and g: "get st q = Ok v0" and nv: "vt P T vn"
  shows "\<exists>st'. put st q vn = Ok st' \<and> inv P C \<Gamma> (invalidate_place \<Gamma> \<sigma> p T) env st' \<and>
           chg \<Gamma> env (place_origin \<Gamma> p) st st' \<and> nroot st' = nroot st"
proof -
  have fr: "heap_fresh st" using inv_heap_fresh[OF inv] .
  from put_ok[OF fr g, of vn] obtain st' where p: "put st q vn = Ok st'" "nroot st' = nroot st"
    "heap_fresh st'" "hagree {q} st st'" "get st' q = Ok vn" by blast
  from pl obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
    "map_of env z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T"
    by (auto simp: ploc_def)
  have w: "writable kz" using mut_ok_writable[OF mo z(1-3)] .
  let ?\<sigma>' = "invalidate_place \<Gamma> \<sigma> p T"
  have wt: "wtarget P \<Gamma> env ?\<sigma>' st st' q"
    unfolding wtarget_def
    using z w g p(5) nv refs_into_mono[of "{z}" "place_origin \<Gamma> p" \<Gamma>]
    by (intro exI[of _ z] exI[of _ kz] exI[of _ bz] exI[of _ ss] exI[of _ T])
       (auto simp: invalidate_place_def)
  have i': "inv P C \<Gamma> ?\<sigma>' env st'"
    by (rule inv_chg[OF inv wff hagree_on_hagree[OF p(4)]]) (use p wt in \<open>auto simp: invalidate_place_def\<close>)
  have "bpath bz \<in> wpaths \<Gamma> env (place_origin \<Gamma> p)" using z w by (auto simp: wpaths_def)
  then have "hagree (wpaths \<Gamma> env (place_origin \<Gamma> p)) st st'"
    using hagree_mono[OF p(4)] z(5) by (metis below_pext singletonD)
  with p i' show ?thesis by (auto simp: chg_def)
qed

lemma SCM_Suc:
  assumes IHp: "SP P n" and IHe: "SE P n" and IHa: "SA P n" and IHi: "SI P n"
  shows "SCM P (Suc n)"
  unfolding SCM_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st p m es \<sigma>' T
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st"
    and chk: "chk_expr C \<Gamma> \<sigma> (EMeth p m es) = Good \<sigma>'" and ty: "etype P \<Gamma> (EMeth p m es) = Good T"
  from chk CP obtain \<sigma>1 Tp where c1: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1" and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()"
    and tp: "ptype P \<Gamma> p = Good Tp"
    and rest: "(case Tp of
        TList _ \<Rightarrow> do {
          mut_ok \<Gamma> p;
          check (place_origin \<Gamma> p \<inter> mroots_l P \<Gamma> es = {})
            ''the arguments of a method call may not move or mutate its receiver'';
          \<sigma> \<leftarrow> chk_exprs C \<Gamma> \<sigma>1 es;
          Good (invalidate_place \<Gamma> \<sigma> p Tp) }
      | TStruct S \<Rightarrow> do {
          fd \<leftarrow> meth_decl P S m;
          (case fd_params fd of
             (c, _, _) # ps \<Rightarrow> do {
               (if borrows_mut c then mut_ok \<Gamma> p else Good ());
               check (place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps es = {})
                 ''the arguments of a method call may not move or mutate its receiver'';
               check (case fd_ret fd of RRef _ U \<Rightarrow> trivial_ty U | _ \<Rightarrow> True)
                 ''a reference returned by a method is used as a value, which needs a trivial type'';
               (\<sigma>, bs) \<leftarrow> chk_args C \<Gamma> \<sigma>1 ps es;
               exclusive \<Gamma> ((p, c) # bs);
               Good (if borrows_mut c then invalidate_place \<Gamma> \<sigma> p Tp else \<sigma>) }
           | [] \<Rightarrow> Bad ''method without self'') }
      | _ \<Rightarrow> Bad ''method call on a value that is neither a struct nor a list'') = Good \<sigma>'"
    by (simp only: chk_expr.simps bind_ck_Good_iff ex_Good_unit) blast
  have IHp': "spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
       chg \<Gamma> env (mroots_p P \<Gamma> p) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P Tp v) \<and>
       ploc P \<Gamma> env p Tp q \<and> rloc env p q)"
    using IHp CP inv c1 tp ro unfolding SP_def by blast
  show "spec (call_meth P (Suc n) env st p m es) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and> (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
    unfolding call_meth.simps
  proof (rule spec_bind_pair[OF IHp'])
    fix q st1 assume h1: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots_p P \<Gamma> p) st st1 \<and>
       (\<exists>v. get st1 q = Ok v \<and> vt P Tp v) \<and> ploc P \<Gamma> env p Tp q \<and> rloc env p q"
    then obtain v1 where inv1: "inv P C \<Gamma> \<sigma>1 env st1" and ch1: "chg \<Gamma> env (mroots_p P \<Gamma> p) st st1"
      and g1: "get st1 q = Ok v1" and vt1: "vt P Tp v1" and pl: "ploc P \<Gamma> env p Tp q"
      and rl: "rloc env p q" by blast
    show "spec (do { v \<leftarrow> get st1 q;
        case v of
          VList _ vs \<Rightarrow>
            if m = ''append'' then (case es of
               [e] \<Rightarrow> do {
                 (x, st) \<leftarrow> eval P n env st1 e;
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
               else (case fresh_gen st1 of (g, st) \<Rightarrow> do {
                  st \<leftarrow> put st q (VList g (butlast vs));
                  Ok (RV (last vs), st) }))
            else Err (ErrUnknown m)
        | VStruct S _ \<Rightarrow> (case find_struct P S of
            None \<Rightarrow> Err (ErrUnknown S)
          | Some sd \<Rightarrow> (case find_method sd m of
              None \<Rightarrow> Err (ErrUnknown m)
            | Some fd \<Rightarrow> (case fd_params fd of
                (_, sx, _) # ps \<Rightarrow> do {
                  (benv, st) \<leftarrow> pass_args P n env st1 ps es;
                  invoke P n st fd (rev benv @ [(sx, Bor q)]) }
              | [] \<Rightarrow> Err ErrArity)))
        | VUndef \<Rightarrow> Err ErrUninit
        | _ \<Rightarrow> Err (ErrType ''method receiver'') })
      (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and>
         (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
    proof (cases Tp)
      case (TList U)
      from vt1 TList obtain g vs where v1: "v1 = VList g vs" "\<forall>u \<in> set vs. vt P U u" by (cases v1) auto
      from rest TList obtain \<sigma>2 where mo: "mut_ok \<Gamma> p = Good ()"
        and fl: "place_origin \<Gamma> p \<inter> mroots_l P \<Gamma> es = {}" and ce: "chk_exprs C \<Gamma> \<sigma>1 es = Good \<sigma>2"
        and s': "\<sigma>' = invalidate_place \<Gamma> \<sigma>2 p Tp" by auto
      have mr: "mroots P \<Gamma> (EMeth p m es) = mroots_p P \<Gamma> p \<union> (place_origin \<Gamma> p \<union> mroots_l P \<Gamma> es)"
        using tp TList by simp
      from ty tp TList obtain Ts where ts: "etypes P \<Gamma> es = Good Ts"
        and mt: "(if m = ''append'' then do { check (Ts = [U]) ''bad argument to append''; Good TNone }
                  else if m = ''pop'' then do { check (Ts = []) ''pop takes no arguments''; Good U }
                  else Bad (''no list method '' @ m)) = Good T"
        by (simp only: etype.simps bind_ck_Good_iff) (auto simp: ty.case)
      show ?thesis
      proof (cases "m = ''append''")
        case True
        with mt have Ts: "Ts = [U]" and T: "T = TNone" by auto
        with ts obtain e where es: "es = [e]" and te: "etype P \<Gamma> e = Good U"
          by (cases es; cases "tl es") auto
        from ce es have ce1: "chk_expr C \<Gamma> \<sigma>1 e = Good \<sigma>2" by auto
        have IHe': "spec (eval P n env st1 e) (\<lambda>(x, st2). inv P C \<Gamma> \<sigma>2 env st2 \<and>
            chg \<Gamma> env (mroots P \<Gamma> e) st1 st2 \<and> vt P U x)"
          using IHe CP inv1 ce1 te unfolding SE_def by blast
        have H: "spec (do {
                 (x, st) \<leftarrow> eval P n env st1 e;
                 v \<leftarrow> get st q;
                 (case v of
                    VList _ vs \<Rightarrow> (case fresh_gen st of (g, st) \<Rightarrow> do {
                       st \<leftarrow> put st q (VList g (vs @ [x]));
                       Ok (RUnit, st) })
                  | _ \<Rightarrow> Err (ErrType ''append'')) })
          (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and>
             (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
        proof (rule spec_bind_pair[OF IHe'], elim conjE)
          fix x st2 assume inv2: "inv P C \<Gamma> \<sigma>2 env st2" and ch2: "chg \<Gamma> env (mroots P \<Gamma> e) st1 st2"
            and vx: "vt P U x"
          have fl': "place_origin \<Gamma> p \<inter> mroots P \<Gamma> e = {}" using fl es by auto
          from chg_oloc[OF inv1 wff ch2 pl[unfolded ploc_oloc] fl' g1 vt1] obtain v2 where
            g2: "get st2 q = Ok v2" "vt P Tp v2" by blast
          from g2(2) TList obtain g' vs' where v2: "v2 = VList g' vs'" "\<forall>u \<in> set vs'. vt P U u"
            by (cases v2) auto
          let ?st2 = "st2\<lparr>ngen := Suc (ngen st2)\<rparr>"
          have inv2': "inv P C \<Gamma> \<sigma>2 env ?st2" using inv2 by simp
          have g2': "get ?st2 q = Ok v2" using g2 by (simp add: get_def)
          have nv: "vt P Tp (VList (ngen st2) (vs' @ [x]))" using v2 vx TList by auto
          from list_write[OF inv2' pl mo g2' nv] obtain st3 where
            w: "put ?st2 q (VList (ngen st2) (vs' @ [x])) = Ok st3" "inv P C \<Gamma> \<sigma>' env st3"
              "chg \<Gamma> env (place_origin \<Gamma> p) ?st2 st3" using s' by auto
          have ch23: "chg \<Gamma> env (place_origin \<Gamma> p) st2 st3"
            using w(3) by (auto simp: chg_def hagree_def get_def)
          have "chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st3"
            using chg_trans[OF chg_trans[OF ch1 ch2] ch23] mr es by (auto elim: chg_mono)
          with w g2 v2 T show "spec (do { v \<leftarrow> get st2 q;
                 (case v of
                    VList _ vs \<Rightarrow> (case fresh_gen st2 of (g, st) \<Rightarrow> do {
                       st \<leftarrow> put st q (VList g (vs @ [x]));
                       Ok (RUnit, st) })
                  | _ \<Rightarrow> Err (ErrType ''append'')) })
            (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and>
               (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
            by (simp add: fresh_gen_def rval_to_val_def)
        qed
        show ?thesis using H True es g1 v1 by simp
      next
        case False
        show ?thesis
        proof (cases "m = ''pop''")
          case True
          with False mt have Ts: "Ts = []" and T: "T = U" by auto
          with ts have es: "es = []" by (cases es) auto
          with ce have s2: "\<sigma>2 = \<sigma>1" by simp
          have mr': "mroots P \<Gamma> (EMeth p m es) \<supseteq> mroots_p P \<Gamma> p \<union> place_origin \<Gamma> p" using mr by auto
          show ?thesis
          proof (cases "vs = []")
            case True
            with False \<open>m = ''pop''\<close> es g1 v1 show ?thesis by (simp add: spec_ErrBounds)
          next
            case nvs: False
            let ?st1 = "st1\<lparr>ngen := Suc (ngen st1)\<rparr>"
            have inv1': "inv P C \<Gamma> \<sigma>1 env ?st1" using inv1 by simp
            have g1': "get ?st1 q = Ok v1" using g1 by (simp add: get_def)
            have nv: "vt P Tp (VList (ngen st1) (butlast vs))" using v1 TList by (auto dest: in_set_butlastD)
            from list_write[OF inv1' pl mo g1' nv] obtain st3 where
              w: "put ?st1 q (VList (ngen st1) (butlast vs)) = Ok st3" "inv P C \<Gamma> \<sigma>' env st3"
                "chg \<Gamma> env (place_origin \<Gamma> p) ?st1 st3" using s' s2 by auto
            have ch13: "chg \<Gamma> env (place_origin \<Gamma> p) st1 st3"
              using w(3) by (auto simp: chg_def hagree_def get_def)
            have ch: "chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st3"
              using chg_trans[OF ch1 ch13] mr' by (auto elim: chg_mono)
            have "vt P U (last vs)" using v1(2) nvs by simp
            with False \<open>m = ''pop''\<close> es nvs w ch T g1 v1 show ?thesis
              by (simp add: fresh_gen_def rval_to_val_def)
          qed
        next
          case False
          with \<open>m \<noteq> ''append''\<close> mt g1 v1 show ?thesis by simp
        qed
      qed
    next
      case (TStruct S)
      from vt1 TStruct obtain fs1 sd where v1: "v1 = VStruct S fs1" and sd: "find_struct P S = Some sd"
        by (cases v1) auto
      from rest TStruct obtain fd where md: "meth_decl P S m = Good fd"
        and rest2: "(case fd_params fd of
             (c, _, _) # ps \<Rightarrow> do {
               (if borrows_mut c then mut_ok \<Gamma> p else Good ());
               check (place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps es = {})
                 ''the arguments of a method call may not move or mutate its receiver'';
               check (case fd_ret fd of RRef _ U \<Rightarrow> trivial_ty U | _ \<Rightarrow> True)
                 ''a reference returned by a method is used as a value, which needs a trivial type'';
               (\<sigma>, bs) \<leftarrow> chk_args C \<Gamma> \<sigma>1 ps es;
               exclusive \<Gamma> ((p, c) # bs);
               Good (if borrows_mut c then invalidate_place \<Gamma> \<sigma> p Tp else \<sigma>) }
           | [] \<Rightarrow> Bad ''method without self'') = Good \<sigma>'" by auto
      have fm: "find_method sd m = Some fd" using md sd by (auto simp: meth_decl_def split: option.splits)
      note mf = wf_struct_facts(4)[OF wf sd fm]
      from mf obtain c sx ps where fp: "fd_params fd = (c, sx, TStruct S) # ps"
        and cc: "c = Imm \<or> c = conv.Mut \<or> c = Ref" by blast
      have cb: "chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()" using mf by blast
      from rest2 fp obtain \<sigma>2 bs where mo: "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good ()"
        and fl: "place_origin \<Gamma> p \<inter> eargs P \<Gamma> ps es = {}"
        and rt: "case fd_ret fd of RRef _ U \<Rightarrow> trivial_ty U | _ \<Rightarrow> True"
        and ca: "chk_args C \<Gamma> \<sigma>1 ps es = Good (\<sigma>2, bs)" and ex: "exclusive \<Gamma> ((p, c) # bs) = Good ()"
        and s': "\<sigma>' = (if borrows_mut c then invalidate_place \<Gamma> \<sigma>2 p Tp else \<sigma>2)"
        by (auto split: if_splits)
      from ty tp TStruct md fp have ts: "etypes P \<Gamma> es = Good (param_tys ps)" and T: "T = ret_ty (fd_ret fd)"
        by auto
      have mr: "mroots P \<Gamma> (EMeth p m es) = mroots_p P \<Gamma> p \<union>
          ((if borrows_mut c then place_origin \<Gamma> p else {}) \<union> eargs P \<Gamma> ps es \<union> bargs \<Gamma> ps es)"
        using tp TStruct md fp by simp
      have ex1: "exclusive \<Gamma> bs = Good ()" and exh: "\<forall>y \<in> set bs. excl_ok \<Gamma> (p, c) y"
        using exclusive_appendD[of \<Gamma> "[(p, c)]" bs] ex by auto
      have IHa': "spec (pass_args P n env st1 ps es) (\<lambda>(benv, st'). inv P C \<Gamma> \<sigma>2 env st' \<and>
          chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st' \<and> args_ok P \<Gamma> env \<sigma>2 bs st1 st' ps es benv)"
        using IHa CP inv1 ca ts ex1 unfolding SA_def by blast
      show ?thesis
        unfolding g1 bind_res.simps v1 val.case sd option.case fm fp list.case prod.case
      proof (rule spec_bind_pair[OF IHa'], elim conjE)
        fix benv st2 assume inv2: "inv P C \<Gamma> \<sigma>2 env st2" and ch12: "chg \<Gamma> env (eargs P \<Gamma> ps es) st1 st2"
          and ao: "args_ok P \<Gamma> env \<sigma>2 bs st1 st2 ps es benv"
        have n12: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2" using ch12 by (simp_all add: chg_def)
        from chg_oloc[OF inv1 wff ch12 pl[unfolded ploc_oloc] fl g1 vt1]
        have g2: "\<exists>v. get st2 q = Ok v \<and> vt P Tp v" .
        have inv2': "inv P C \<Gamma> \<sigma>' env st2" using inv2 s' inv_invalidate by (auto split: if_splits)
        have s23: "a_inval \<sigma>2 \<subseteq> a_inval \<sigma>'" using s' by (auto simp: invalidate_place_def)
        have bmp: "borrows_mut c \<longrightarrow> mut_ok \<Gamma> p = Good () \<and>
            (\<not> trivial_ty Tp \<longrightarrow> refs_into \<Gamma> (place_origin \<Gamma> p) \<subseteq> a_inval \<sigma>')"
          using mo s' by (auto simp: invalidate_place_def)
        have cv: "c \<noteq> Var" "c \<noteq> Deinit" using cc by auto
        let ?ps = "(c, sx, TStruct S) # ps" and ?es = "EPlace p # es" and ?benv = "(sx, Bor q) # benv"
        have ao': "args_ok P \<Gamma> env \<sigma>' ((p, c) # bs) st1 st2 ?ps ?es ?benv"
          using args_ok_recv[OF inv1 ao pl[unfolded TStruct] rl g2[unfolded TStruct] cv bmp[unfolded TStruct] s23 exh] .
        let ?C' = "\<lparr>c_prog = P, c_ret = fd_ret fd, c_fields = []\<rparr>"
        have dall: "distinct (map (fst \<circ> snd) ?ps)" using chk_body_facts(2)[OF cb] fp by simp
        have dist: "distinct (map (fst \<circ> snd) ?ps @ map fst ([] :: senv))" using dall by simp
        have oo: "one_out (rev (map param_kind ?ps) @ [])"
          using one_out_params[OF chk_body_facts(3)[OF cb] dall[folded fp]] fp by simp
        have ci: "inv P ?C' (rev (map param_kind ?ps) @ []) (astate0 (fd_params fd)) (rev ?benv @ []) st2"
          by (rule callee_inv[OF inv1 ao' order_refl n12 fr2 dist oo]) auto
        have mfb: "map fst ?benv = map (fst \<circ> snd) ?ps" and leb: "length ?es = length ?ps"
          and akb: "\<forall>i < length ?ps. aok P \<Gamma> env \<sigma>' ((p, c) # bs) st1 st2 (?ps ! i) (?es ! i) (snd (?benv ! i))"
          using ao' by (simp_all add: args_ok_def)
        have bor: "\<exists>q. snd (?benv ! i) = Bor q" if "i < length ?ps" "borrows_mut (fst (?ps ! i))" for i
        proof -
          obtain c' y T' where pi: "?ps ! i = (c', y, T')" by (cases "?ps ! i")
          from args_conv_bm[of \<Gamma> env \<sigma>' "(p, c) # bs" st1 st2 c' y T' "?es ! i" "snd (?benv ! i)"]
            akb[rule_format, OF that(1)] pi that(2) show ?thesis by auto
        qed
        have refpar: "\<exists>i < length ?ps. fst (snd (?ps ! i)) = z \<and> borrows_mut (fst (?ps ! i))"
          if rr: "fd_ret fd = RRef ns U" "z \<in> set ns" for ns U z
        proof -
          have "list_ex (\<lambda>(c, y, _). y = z \<and> (c = conv.Mut \<or> c = Ref)) ?ps"
            using chk_body_facts(4)[OF cb] rr fp by (simp add: list_all_iff)
          then obtain cy where
            "cy \<in> set ?ps" "fst (snd cy) = z" "fst cy = conv.Mut \<or> fst cy = Ref"
            unfolding list_ex_iff by (fastforce split: prod.splits)
          then show ?thesis by (auto simp: in_set_conv_nth borrows_mut_def)
        qed
        have cok: "callee_ok P ?C' fd (rev ?benv) st2"
          unfolding callee_ok_def
        proof (intro conjI)
          show "inv P ?C' (rev (map param_kind (fd_params fd))) (astate0 (fd_params fd)) (rev ?benv) st2"
            using ci fp by simp
          show "chk_body P (fd_ret fd) (c_fields ?C') (fd_params fd) (fd_body fd) = Good ()" using cb by simp
          show "case fd_ret fd of RRef ns _ \<Rightarrow> \<forall>z \<in> set ns. \<exists>q. map_of (rev ?benv) z = Some (Bor q) | _ \<Rightarrow> True"
          proof (cases "fd_ret fd")
            case (RRef ns U)
            have "\<exists>q. map_of (rev ?benv) z = Some (Bor q)" if z: "z \<in> set ns" for z
            proof -
              from refpar[OF RRef z] obtain i where i: "i < length ?ps" "fst (snd (?ps ! i)) = z"
                "borrows_mut (fst (?ps ! i))" by blast
              from bor[OF i(1,3)] obtain q' where "snd (?benv ! i) = Bor q'" by blast
              with callee_param_lookup(2)[OF dist mfb i(1), of "[]"] i(2) show ?thesis by auto
            qed
            with RRef show ?thesis by simp
          qed simp_all
        qed (use own_unique_args[OF ao', of "[]", simplified]
                 out_not_own_args[OF ao' dall, of "[]" "[]", simplified] fp in auto)
        have IHi': "spec (invoke P n st2 fd (rev ?benv)) (invoke_post P fd (rev ?benv) st2)"
          using IHi cok unfolding SI_def by blast
        show "spec (invoke P n st2 fd (rev benv @ [(sx, Bor q)])) (\<lambda>(r, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
            chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st' \<and> (\<exists>v. rval_to_val st' r = Ok v \<and> vt P T v))"
        proof (rule spec_mono[OF IHi'[simplified]], clarify)
          fix rv st3 assume ip: "invoke_post P fd (rev benv @ [(sx, Bor q)]) st2 (rv, st3)"
          then have n23: "nroot st2 \<le> nroot st3" and fr3: "heap_fresh st3"
            and ag3: "hagree (wpaths (rev (map param_kind ?ps) @ []) (rev ?benv @ []) UNIV \<union>
                {(r, []) | x r. (x, Own r) \<in> set (rev ?benv @ [])}) st2 st3"
            and wr: "\<forall>x c T q. map_of (rev (map param_kind ?ps) @ []) x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
                map_of (rev ?benv @ []) x = Some (Bor q) \<longrightarrow> (\<exists>v. get st3 q = Ok v \<and> vt P T v)"
            and rr: "ret_res P (fd_ret fd) (rev (map param_kind ?ps)) (rev ?benv) st3 rv"
            using fp by (simp_all add: invoke_post_def)
          have new: "\<forall>i < length ?ps. \<forall>q. snd (?benv ! i) = Bor q \<longrightarrow> borrows_mut (fst (?ps ! i)) \<longrightarrow>
              (\<exists>v. get st3 q = Ok v \<and> vt P (snd (snd (?ps ! i))) v)"
            by (rule new_args[OF wr dist mfb])
          from caller_restore[OF inv1 inv2' ao' order_refl ag3 n23 fr3 new _ dall]
          have cr: "inv P C \<Gamma> \<sigma>' env st3"
            "hagree (wpaths \<Gamma> env (bargs \<Gamma> ?ps ?es) \<union> {q. nroot st1 \<le> fst q}) st2 st3" by auto
          have ch13: "chg \<Gamma> env (eargs P \<Gamma> ps es \<union> bargs \<Gamma> ?ps ?es) st1 st3"
            by (rule chg_call[OF ch12 cr(2) n23 fr3])
          have bsub: "bargs \<Gamma> ?ps ?es \<subseteq> (if borrows_mut c then place_origin \<Gamma> p else {}) \<union> bargs \<Gamma> ps es"
            by (auto simp: bargs_def)
          have ch: "chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st3"
            using chg_trans[OF ch1 ch13] mr bsub by (auto elim!: chg_mono)
          have res: "\<exists>v. rval_to_val st3 rv = Ok v \<and> vt P T v"
          proof (cases "fd_ret fd")
            case (RRef ns U)
            with rr obtain q' v where "rv = RP q'" "get st3 q' = Ok v" "vt P U v"
              by (auto simp: ret_res_def)
            moreover have "trivial_ty U" using rt RRef by simp
            ultimately show ?thesis using T RRef
              by (auto simp: rval_to_val_def read_val_def dest: vt_trivial)
          qed (use rr T in \<open>auto simp: ret_res_def rval_to_val_def\<close>)
          with cr(1) ch show "inv P C \<Gamma> \<sigma>' env st3 \<and> chg \<Gamma> env (mroots P \<Gamma> (EMeth p m es)) st st3 \<and>
              (\<exists>v. rval_to_val st3 rv = Ok v \<and> vt P T v)" by blast
        qed
      qed
    qed (use rest in auto)
  qed
qed



section \<open>Function bodies\<close>

lemma ctx_eta: "C = \<lparr>c_prog = c_prog C, c_ret = c_ret C, c_fields = c_fields C\<rparr>"
  by (cases C) simp

lemma inv_own_typed:
  assumes "inv P C \<Gamma> \<sigma> env st" "(x, Own r) \<in> set env" "\<forall>T. map_of \<Gamma> x \<noteq> Some (KBorrow Out T)"
  shows "\<exists>v T. heap st r = Some v \<and> wt_opt P T v"
proof -
  have d: "distinct (map fst env)" using assms(1) wf_senv_distinct by (auto simp: inv_def)
  have xb: "map_of env x = Some (Own r)" using map_of_distinct_mem[OF d assms(2)] .
  have mf: "map fst env = map fst \<Gamma>" using assms(1) by (simp add: inv_def)
  have "x \<in> fst ` set env" using assms(2) by force
  then have "x \<in> fst ` set \<Gamma>" using mf by (metis set_map)
  then obtain k where xk: "map_of \<Gamma> x = Some k" by (meson map_of_eq_None_iff not_Some_eq)
  from inv_binding[OF assms(1) xk] xb have "binding_ok P C \<Gamma> \<sigma> env st x k (Own r)" by auto
  then show ?thesis
  proof (cases k)
    case (KOwned T)
    with \<open>binding_ok P C \<Gamma> \<sigma> env st x k (Own r)\<close> obtain v where
      "heap st r = Some v" "if x \<in> a_init \<sigma> then vt P T v else wt_opt P T v" by auto
    then have "heap st r = Some v \<and> wt_opt P T v" by (auto simp: wt_opt_def split: if_splits)
    then show ?thesis by blast
  next
    case (KBorrow c T)
    with \<open>binding_ok P C \<Gamma> \<sigma> env st x k (Own r)\<close> obtain v where
      "get st (r, []) = Ok v" "if c = Out then out_val P C \<sigma> T v else vt P T v" by auto
    then obtain w where "heap st r = Some w" "w = v" by (auto simp: get_def split: option.splits)
    have "c \<noteq> Out" using KBorrow xk assms(3) by auto
    show ?thesis
    proof (cases "v = VUndef")
      case True
      with \<open>heap st r = Some w\<close> \<open>w = v\<close> show ?thesis by (auto simp: wt_opt_def)
    next
      case False
      have "\<exists>U. vt P U v"
        using \<open>if c = Out then out_val P C \<sigma> T v else vt P T v\<close> \<open>c \<noteq> Out\<close> by auto
      with \<open>heap st r = Some w\<close> \<open>w = v\<close> show ?thesis by (auto simp: wt_opt_def)
    qed
  next
    case (KRef T og I)
    with \<open>binding_ok P C \<Gamma> \<sigma> env st x k (Own r)\<close> show ?thesis by simp
  qed
qed


lemma SI_Suc:
  assumes IHs: "SS P n" and IHc: "SC P n"
  shows "SI P (Suc n)"
  unfolding SI_def
proof (intro allI impI)
  fix C fd env st assume cok: "callee_ok P C fd env st"
  let ?ps = "fd_params fd" let ?\<Gamma> = "rev (map param_kind (fd_params fd))"
  from cok have CP: "c_prog C = P" and CR: "c_ret C = fd_ret fd"
    and cb: "chk_body P (fd_ret fd) (c_fields C) ?ps (fd_body fd) = Good ()"
    and inv0: "inv P C ?\<Gamma> (astate0 ?ps) env st"
    and ou: "\<forall>x y r. (x, Own r) \<in> set env \<longrightarrow> (y, Own r) \<in> set env \<longrightarrow> x = y"
    and rb: "case fd_ret fd of RRef ns _ \<Rightarrow> \<forall>z \<in> set ns. \<exists>q. map_of env z = Some (Bor q) | _ \<Rightarrow> True"
    by (simp_all add: callee_ok_def)
  have Ceq: "\<lparr>c_prog = P, c_ret = fd_ret fd, c_fields = c_fields C\<rparr> = C" using CP CR ctx_eta[of C] by simp
  from chk_body_facts(1)[OF cb] Ceq obtain \<Gamma>' o\<sigma> where
    cs: "chk_stmt C ?\<Gamma> (astate0 ?ps) (fd_body fd) = Good (\<Gamma>', o\<sigma>)"
    and en: "case o\<sigma> of None \<Rightarrow> True | Some \<sigma> \<Rightarrow> fd_ret fd = RNone \<and> set (c_fields C) \<subseteq> a_fields \<sigma>"
    by auto
  have fr0: "heap_fresh st" using inv_heap_fresh[OF inv0] .
  have ex: "spec (exec P n (fd_ret fd) env st (fd_body fd)) (spost P C ?\<Gamma> \<Gamma>' o\<sigma> env st)"
    using IHs CP inv0 cs CR unfolding SS_def by fastforce
  show "spec (invoke P (Suc n) st fd env) (invoke_post P fd env st)"
    unfolding invoke.simps
  proof (rule spec_bind, rule spec_mono[OF ex], clarify)
    fix oc env' st1 assume sp: "spost P C ?\<Gamma> \<Gamma>' o\<sigma> env st (oc, env', st1)"
    let ?res = "case oc of Normal \<Rightarrow> RUnit | Returned r \<Rightarrow> r"
    text \<open>At the end of the body, normally or by a return.\<close>
    have endst: "\<exists>\<Delta> \<Delta>e \<sigma>r. env' = \<Delta>e @ env \<and> (\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r) \<and>
        inv P C (\<Delta> @ ?\<Gamma>) \<sigma>r env' st1 \<and> (\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T) \<and>
        (fd_ret fd = RNone \<longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma>r) \<and> ret_res P (fd_ret fd) (\<Delta> @ ?\<Gamma>) env' st1 ?res"
    proof (cases oc)
      case Normal
      from chk_stmt_extends(1)[OF cs] obtain \<Delta> where "\<Gamma>' = \<Delta> @ ?\<Gamma>"
        "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T" by blast
      with sp Normal en show ?thesis by (auto simp: spost_def ret_res_def split: option.splits)
    next
      case (Returned r)
      with sp CR show ?thesis by (auto simp: spost_def)
    qed
    then obtain \<Delta> \<Delta>e \<sigma>r where e: "env' = \<Delta>e @ env" and fresh: "\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r"
      and i1: "inv P C (\<Delta> @ ?\<Gamma>) \<sigma>r env' st1" and nb: "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
      and fl0: "fd_ret fd = RNone \<longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma>r"
      and rr: "ret_res P (fd_ret fd) (\<Delta> @ ?\<Gamma>) env' st1 ?res"
      by blast
    have fl: "set (c_fields C) \<subseteq> a_fields \<sigma>r" using fl0 cok by (auto simp: callee_ok_def)
    have ch: "chg ?\<Gamma> env UNIV st st1" using sp by (simp add: spost_def)
    have mfe: "map fst env = map fst ?\<Gamma>" using inv0 by (simp add: inv_def)
    have len: "length \<Delta>e = length \<Delta>" using len_ext[OF i1[unfolded e] mfe] .
    note F = inv_restrict_facts[OF i1[unfolded e] len nb]
    have envroots0: "\<forall>x b. map_of env x = Some b \<longrightarrow> fst (bpath b) < nroot st"
      using inv0 by (simp add: inv_def)
    have own_env_lt: "r < nroot st" if "(x, Own r) \<in> set env" for x r
    proof -
      have d: "distinct (map fst env)" using inv0 wf_senv_distinct by (auto simp: inv_def)
      from envroots0 map_of_distinct_mem[OF d that] show ?thesis by fastforce
    qed
    have ok_env: "cleanup_ok P env st1"
      unfolding cleanup_ok_def
    proof (intro conjI allI impI)
      have d: "distinct (map fst env)" using inv0 wf_senv_distinct by (auto simp: inv_def)
      show "distinct [r. (x, Own r) \<leftarrow> env]" using distinct_own_roots[OF d] ou by blast
    next
      fix x r assume xr: "(x, Own r) \<in> set env"
      have "(x, Own r) \<in> set env'" using xr e by simp
      moreover have "\<forall>T. map_of (\<Delta> @ ?\<Gamma>) x \<noteq> Some (KBorrow Out T)"
      proof (intro allI notI)
        fix T assume a: "map_of (\<Delta> @ ?\<Gamma>) x = Some (KBorrow Out T)"
        have d: "distinct (map fst env)" using inv0 wf_senv_distinct by (auto simp: inv_def)
        have xb: "map_of env x = Some (Own r)" using map_of_distinct_mem[OF d xr] .
        have "map_of ?\<Gamma> x \<noteq> None" using xb mfe by (metis map_of_eq_None_iff option.distinct(1) set_map)
        with F(5) a have "map_of ?\<Gamma> x = Some (KBorrow Out T)" by simp
        with cok xb show False by (auto simp: callee_ok_def)
      qed
      ultimately show "\<exists>v T. heap st1 r = Some v \<and> wt_opt P T v" by (rule inv_own_typed[OF i1])
    qed
    have cok1: "cleanup_ok P env' st1"
      unfolding e
    proof (rule cleanup_ok_append[OF F(7) ok_env])
      show "owned_roots \<Delta>e \<inter> owned_roots env = {}"
        using fresh own_env_lt by (fastforce simp: owned_roots_set)
    qed
    have fr1: "heap_fresh st1" and n01: "nroot st \<le> nroot st1" and ag1: "hagree (wpaths ?\<Gamma> env UNIV) st st1"
      using ch by (simp_all add: chg_def)
    have cl: "spec (cleanup P n st1 env') (\<lambda>st'. nroot st1 \<le> nroot st' \<and> heap_fresh st' \<and>
        (\<forall>r. r < nroot st1 \<longrightarrow> r \<notin> owned_roots env' \<longrightarrow> heap st' r = heap st1 r))"
      using IHc cok1 fr1 unfolding SC_def by blast
    show "spec (bind_res (cleanup P n st1 env') (\<lambda>st. Ok (?res, st))) (invoke_post P fd env st)"
    proof (rule spec_bind, rule spec_mono[OF cl], clarify)
      fix st2 assume n12: "nroot st1 \<le> nroot st2" and fr2: "heap_fresh st2"
        and h2: "\<forall>r. r < nroot st1 \<longrightarrow> r \<notin> owned_roots env' \<longrightarrow> heap st2 r = heap st1 r"
      let ?O = "{(r, []) | x r. (x, Own r) \<in> set env}"
      text \<open>Roots of the caller that the callee does not own are not touched by the cleanup.\<close>
      have same: "heap st2 r = heap st1 r" if "r < nroot st" "r \<notin> owned_roots env" for r
      proof -
        have "r \<notin> owned_roots \<Delta>e" using that(1) fresh by (fastforce simp: owned_roots_set)
        with that h2 n01 e show ?thesis by (auto simp: owned_roots_set)
      qed
      have ag2: "hagree (wpaths ?\<Gamma> env UNIV \<union> ?O) st st2"
        unfolding hagree_def
      proof (intro conjI allI impI)
        fix r assume r: "r < nroot st" "r \<notin> fst ` (wpaths ?\<Gamma> env UNIV \<union> ?O)"
        have "r \<notin> owned_roots env"
        proof
          assume "r \<in> owned_roots env"
          then obtain y where "(y, Own r) \<in> set env" by (auto simp: owned_roots_set)
          then have "(r, []) \<in> ?O" by blast
          then have "r \<in> fst ` (wpaths ?\<Gamma> env UNIV \<union> ?O)" by (intro rev_image_eqI[of "(r, [])"]) simp_all
          with r(2) show False by blast
        qed
        with same r(1) have "heap st2 r = heap st1 r" by blast
        moreover have "heap st1 r = heap st r" using hagreeD1[OF ag1 r(1)] r(2) by blast
        ultimately show "heap st2 r = heap st r" by simp
      next
        fix p assume p: "fst p < nroot st" "\<forall>q \<in> wpaths ?\<Gamma> env UNIV \<union> ?O. \<not> below p q"
        have "fst p \<notin> owned_roots env"
        proof
          assume "fst p \<in> owned_roots env"
          then obtain y where "(y, Own (fst p)) \<in> set env" by (auto simp: owned_roots_set)
          then have "(fst p, []) \<in> ?O" by blast
          moreover have "below p (fst p, [])" by (simp add: below_def)
          ultimately show False using p(2) by blast
        qed
        with same p(1) have "get st2 p = get st1 p" by (intro get_root_cong) blast
        moreover have "rskel (get st1 p) = rskel (get st p)" using hagreeD2[OF ag1 p(1)] p(2) by blast
        ultimately show "rskel (get st2 p) = rskel (get st p)" by simp
      qed
      text \<open>Locations of borrowed parameters are not owned roots.\<close>
      have notown: "fst q \<notin> owned_roots env" if xq: "map_of env x = Some (Bor q)" "map_of ?\<Gamma> x = Some k"
        "writable k" for x q k
      proof
        assume "fst q \<in> owned_roots env"
        then obtain y where yr: "(y, Own (fst q)) \<in> set env" by (auto simp: owned_roots_set)
        have d: "distinct (map fst env)" using inv0 wf_senv_distinct by (auto simp: inv_def)
        have yb: "map_of env y = Some (Own (fst q))" using map_of_distinct_mem[OF d yr] .
        have "y \<in> fst ` set ?\<Gamma>" using yb mfe by (metis map_of_eq_None_iff option.distinct(1) set_map)
        then obtain ky where yk: "map_of ?\<Gamma> y = Some ky" by (meson map_of_eq_None_iff not_Some_eq)
        have nr: "\<not> is_ref ky" using yk by (auto dest!: map_of_SomeD simp: param_kind_def split: if_splits)
        have "y \<noteq> x" using xq(1) yb by auto
        from excl_D[OF inv_excl[OF inv0] xq(2,3,1) yk nr yb this] show False
          by (simp add: overlaps_def below_def)
      qed
      have q1: "q \<in> fst ` set ?\<Gamma> \<longrightarrow> True" for q by simp
      have wr: "\<forall>x c T q. map_of ?\<Gamma> x = Some (KBorrow c T) \<longrightarrow> c \<noteq> Imm \<longrightarrow>
          map_of env x = Some (Bor q) \<longrightarrow> (\<exists>v. get st2 q = Ok v \<and> vt P T v)"
      proof (intro allI impI)
        fix x c T q assume xk: "map_of ?\<Gamma> x = Some (KBorrow c T)" and ci: "c \<noteq> Imm"
          and xb: "map_of env x = Some (Bor q)"
        have "map_of (\<Delta> @ ?\<Gamma>) x = Some (KBorrow c T)" "map_of env' x = Some (Bor q)"
          using F(5)[of x] xk xb e by auto
        from inv_binding[OF i1 this(1)] this(2) obtain v where g: "get st1 q = Ok v"
          and vv: "if c = Out then out_val P C \<sigma>r T v else vt P T v" by auto
        have "vt P T v" using vv out_val_full[OF _ fl] by (auto split: if_splits)
        moreover have "fst q < nroot st" using envroots0 xb by fastforce
        moreover have "fst q \<notin> owned_roots env" using notown[OF xb xk] ci by simp
        ultimately show "\<exists>v. get st2 q = Ok v \<and> vt P T v"
          using same g by (metis get_root_cong)
      qed
      have res: "ret_res P (fd_ret fd) ?\<Gamma> env st2 ?res"
      proof (cases "fd_ret fd")
        case (RRef ns U)
        have rr': "\<exists>q. ?res = RP q \<and> (\<exists>v. get st1 q = Ok v \<and> vt P U v) \<and>
            oloc P (\<Delta> @ ?\<Gamma>) env' (set ns) UNIV U q"
          using rr RRef by (simp add: ret_res_def)
        then obtain q v where q0: "?res = RP q" "get st1 q = Ok v" "vt P U v"
          and ol: "oloc P (\<Delta> @ ?\<Gamma>) env' (set ns) UNIV U q" by blast
        from ol obtain z kz bz ss where qz: "z \<in> set ns" "map_of (\<Delta> @ ?\<Gamma>) z = Some kz" "\<not> is_ref kz"
          "map_of env' z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some U"
          unfolding oloc_def by blast
        note q = q0 qz
        from rb RRef q(4) obtain qz where zb: "map_of env z = Some (Bor qz)" by auto
        have zG: "map_of ?\<Gamma> z \<noteq> None" using zb mfe by (metis map_of_eq_None_iff option.distinct(1) set_map)
        have kz: "map_of ?\<Gamma> z = Some kz" and bz: "bz = Bor qz" using F(5)[OF zG] q(5,7) zb e by auto
        have "writable kz"
        proof -
          from chk_body_facts(4)[OF cb] RRef q(4) have
            "list_ex (\<lambda>(c, y, _). y = z \<and> (c = conv.Mut \<or> c = Ref)) ?ps" by (simp add: list_all_iff)
          then obtain c y T' where cy: "(c, y, T') \<in> set ?ps" "y = z" "c = conv.Mut \<or> c = Ref"
            by (auto simp: list_ex_iff)
          have d: "distinct (map fst (map param_kind ?ps))"
            using chk_body_facts(2)[OF cb] by simp
          have "(z, KBorrow c T') \<in> set ?\<Gamma>" using cy by (force simp: param_kind_def)
          then have "map_of ?\<Gamma> z = Some (KBorrow c T')"
            using map_of_distinct_mem d by (metis distinct_rev rev_map set_rev)
          with kz cy show ?thesis by auto
        qed
        have "fst q \<notin> owned_roots env" using notown[OF zb kz \<open>writable kz\<close>] q(8) bz by simp
        moreover have "fst q < nroot st" using envroots0 zb q(8) bz by fastforce
        ultimately have "get st2 q = get st1 q" using same by (metis get_root_cong)
        with q kz zb bz RRef show ?thesis
          by (auto simp: ret_res_def oloc_def intro!: exI[of _ z] exI[of _ ss])
      qed (use rr in \<open>auto simp: ret_res_def\<close>)
      show "invoke_post P fd env st (?res, st2)"
        using n01 n12 fr2 ag2 wr res by (simp add: invoke_post_def)
    qed
  qed
qed



section \<open>Statements\<close>

lemma inv_add_ref_gen:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "x \<notin> fst ` set \<Gamma>"
    and pl: "oloc P \<Gamma> env R I T q" and g: "get st q = Ok v" "vt P T v"
    and og: "R \<subseteq> fst ` set \<Gamma>"
  shows "inv P C ((x, KRef T R I) # \<Gamma>) \<sigma> ((x, Bor q) # env) st"
proof -
  let ?k = "KRef T R I"
  have xe: "x \<notin> fst ` set env" using inv x by (simp add: inv_def) (metis set_map)
  have xG: "map_of \<Gamma> x = None" "map_of env x = None" using x xe by (simp_all add: map_of_eq_None_iff)
  have bounds: "\<And>z bz. map_of env z = Some bz \<Longrightarrow> fst (bpath bz) < nroot st"
    using inv by (simp add: inv_def)
  from pl obtain z kz bz ss where z: "z \<in> R" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
    "map_of env z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T"
    "has_idx ss \<longrightarrow> z \<in> I"
    unfolding oloc_def by blast
  have zx: "z \<noteq> x" using z(2) xG by auto
  have new: "binding_ok P C ((x, ?k) # \<Gamma>) \<sigma> ((x, Bor q) # env) st x ?k (Bor q)"
    using z zx g by (simp only: binding_ok.simps) (auto intro!: exI[of _ z])
  have old: "binding_ok P C ((x, ?k) # \<Gamma>) \<sigma> ((x, Bor q) # env) st y k b"
    if "map_of \<Gamma> y = Some k" "map_of env y = Some b" "binding_ok P C \<Gamma> \<sigma> env st y k b" for y k b
  proof (rule binding_ok_transfer[OF that(3)])
    show "\<And>z. map_of \<Gamma> z \<noteq> None \<Longrightarrow> map_of ((x, ?k) # \<Gamma>) z = map_of \<Gamma> z" using xG by auto
    show "\<And>z. map_of env z \<noteq> None \<Longrightarrow> map_of ((x, Bor q) # env) z = map_of env z" using xG by auto
  qed (use bounds that(2) in auto)
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have excl': "excl ((x, ?k) # \<Gamma>) ((x, Bor q) # env)"
    using excl xG unfolding excl_def by (auto split: if_splits)
  show ?thesis
    unfolding inv_def
  proof (intro conjI allI impI)
    show "wf_senv ((x, ?k) # \<Gamma>)" using inv x og by (simp add: inv_def)
    show "one_out ((x, ?k) # \<Gamma>)" using inv xG by (auto simp: inv_def one_out_def)
    show "map fst ((x, Bor q) # env) = map fst ((x, ?k) # \<Gamma>)" using inv by (simp add: inv_def)
    show "excl ((x, ?k) # \<Gamma>) ((x, Bor q) # env)" by (rule excl')
    fix y k assume yk: "map_of ((x, ?k) # \<Gamma>) y = Some k"
    show "\<exists>b. map_of ((x, Bor q) # env) y = Some b \<and>
              binding_ok P C ((x, ?k) # \<Gamma>) \<sigma> ((x, Bor q) # env) st y k b"
    proof (cases "y = x")
      case True
      with yk new show ?thesis by auto
    next
      case False
      with yk inv_binding[OF inv, of y k] old show ?thesis by fastforce
    qed
  next
    fix y b assume "map_of ((x, Bor q) # env) y = Some b"
    with bounds z(4,5) show "fst (bpath b) < nroot st" by (fastforce split: if_splits)
  next
    fix r' assume "nroot st \<le> r'"
    with inv show "heap st r' = None" by (auto simp: inv_def)
  qed
qed

lemma inv_drop_owned:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "map_of \<Gamma> x = Some (KOwned U)"
    and r: "map_of env x = Some (Own r)" and d: "dpost st (r, []) st'"
  shows "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env st'"
proof -
  let ?st0 = "st\<lparr>heap := (heap st)(r := Some VUndef)\<rparr>"
  have i0: "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env ?st0"
    by (rule inv_move[OF inv x r]) simp_all
  have rb: "r < nroot st" using inv_bounds[OF inv r] by simp
  from d have n: "nroot st \<le> nroot st'" and fr: "heap_fresh st'" and ag: "hagree {(r, [])} st st'"
    and u: "get st' (r, []) = Ok VUndef" by (simp_all add: dpost_def)
  have hr: "heap st' r = Some VUndef" using u by (auto simp: get_def split: option.splits)
  have same: "heap st' r' = heap ?st0 r'" if "r' \<in> envroots env" for r'
  proof (cases "r' = r")
    case True with hr show ?thesis by simp
  next
    case False
    have "r' < nroot st" using that inv by (auto simp: envroots_def dest: inv_bounds)
    with hagreeD1[OF ag this] False show ?thesis by simp
  qed
  show ?thesis by (rule inv_heap_envroots[OF i0]) (use same n fr in simp_all)
qed

lemma wpaths_ext:
  assumes inv: "inv P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st" and mf: "map fst env = map fst \<Gamma>"
    and nb: "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
    and fresh: "\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> M \<le> r"
  shows "wpaths (\<Delta> @ \<Gamma>) (\<Delta>e @ env) UNIV \<subseteq> wpaths \<Gamma> env UNIV \<union> {q. M \<le> fst q}"
proof
  have len: "length \<Delta>e = length \<Delta>" using len_ext[OF inv mf] .
  note F = inv_restrict_facts[OF inv len nb]
  fix q assume "q \<in> wpaths (\<Delta> @ \<Gamma>) (\<Delta>e @ env) UNIV"
  then obtain x k b where xk: "map_of (\<Delta> @ \<Gamma>) x = Some k" and w: "writable k"
    and xb: "map_of (\<Delta>e @ env) x = Some b" and q: "q = bpath b" unfolding wpaths_def by blast
  show "q \<in> wpaths \<Gamma> env UNIV \<union> {q. M \<le> fst q}"
  proof (cases "map_of \<Gamma> x")
    case (Some k')
    then have "map_of \<Gamma> x \<noteq> None" by simp
    from F(5)[OF this] xk xb have "map_of \<Gamma> x = Some k" "map_of env x = Some b" by auto
    with w q show ?thesis by (auto simp: wpaths_def)
  next
    case None
    from xk None have dk: "map_of \<Delta> x = Some k" by (auto simp: map_add_def split: option.splits)
    from nb map_of_SomeD[OF dk] w obtain U where kU: "k = KOwned U" by (cases k) auto
    from inv_binding[OF inv xk] xb kU obtain r where "b = Own r" by auto
    have "map_of env x = None" using None mf by (metis map_of_eq_None_iff set_map)
    with xb have "map_of \<Delta>e x = Some b" by (auto simp: map_add_def split: option.splits)
    with \<open>b = Own r\<close> have "(x, Own r) \<in> set \<Delta>e" by (auto dest: map_of_SomeD)
    with fresh q \<open>b = Own r\<close> show ?thesis by auto
  qed
qed

lemma spost_normal:
  "inv P C \<Gamma>'' \<sigma>'' env st'' \<Longrightarrow> chg \<Gamma> env UNIV st st'' \<Longrightarrow>
   spost P C \<Gamma> \<Gamma>'' (Some \<sigma>'') env st (Normal, env, st'')"
  by (auto simp: spost_def intro: exI[of _ "[]"])

text \<open>
  Assignment at the heap level: evaluate the place, destroy the old value,
  write the new one. The invariant is restored by @{text "inv_chg"} with one
  changed location.
\<close>

lemma assign_tail:
  assumes SD: "SD P n" and inv2: "inv P C \<Gamma> \<sigma>2 env st2" and g: "get st2 q = Ok u" "wt_opt P T u"
    and z: "map_of \<Gamma> z = Some kz" "writable kz" "map_of env z = Some bz"
    and q: "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T" and vv: "vt P T v"
    and zR: "z \<in> place_origin \<Gamma> p" and res: "\<sigma>' = invalidate_place \<Gamma> \<sigma>2' p T"
    and inval: "a_inval \<sigma>2 \<subseteq> a_inval \<sigma>2'"
    and init: "\<forall>y. y \<in> a_init \<sigma>2' \<longrightarrow> y \<notin> a_init \<sigma>2 \<longrightarrow> (\<exists>r. map_of env y = Some (Own r) \<and> (r, []) = q)"
    and flds: "\<forall>f. f \<in> a_fields \<sigma>2' \<longrightarrow> f \<notin> a_fields \<sigma>2 \<longrightarrow>
                 (\<forall>s T b. map_of \<Gamma> s = Some (KBorrow Out T) \<longrightarrow> map_of env s = Some b \<longrightarrow>
                    ext (bpath b) (Fld f) = q)"
  shows "spec (do { st \<leftarrow> drop_path P n st2 q; st \<leftarrow> put st q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and>
              chg \<Gamma> env UNIV st2 st')"
proof -
  have fr2: "heap_fresh st2" using inv_heap_fresh[OF inv2] .
  have D: "spec (drop_path P n st2 q) (dpost st2 q)" using SD g fr2 unfolding SD_def by blast
  show ?thesis
  proof (rule spec_bind_mono[OF D])
    fix st3 assume d: "dpost st2 q st3"
    then have fr3: "heap_fresh st3" and g3: "get st3 q = Ok VUndef" and n23: "nroot st2 \<le> nroot st3"
      and ag3: "hagree {q} st2 st3" by (simp_all add: dpost_def)
    from put_ok[OF fr3 g3, of v] obtain st4 where p: "put st3 q v = Ok st4" "nroot st4 = nroot st3"
      "heap_fresh st4" "hagree {q} st3 st4" "get st4 q = Ok v" by blast
    have ag: "hagree {q} st2 st4" using hagree_trans[OF ag3 p(4) n23] by simp
    have wt: "wtarget P \<Gamma> env \<sigma>' st2 st4 q"
      unfolding wtarget_def using z q g(1) p(5) vv zR refs_into_mono[of "{z}" "place_origin \<Gamma> p" \<Gamma>]
      by (intro exI[of _ z] exI[of _ kz] exI[of _ bz] exI[of _ ss] exI[of _ T])
         (auto simp: res invalidate_place_def)
    have i4: "inv P C \<Gamma> \<sigma>' env st4"
    proof (rule inv_chg[OF inv2 wff hagree_on_hagree[OF ag]])
      show "nroot st2 \<le> nroot st4" using n23 p(2) by simp
      show "heap_fresh st4" by (rule p(3))
      show "\<forall>q' \<in> {q}. wtarget P \<Gamma> env \<sigma>' st2 st4 q'" using wt by simp
      show "a_inval \<sigma>2 \<subseteq> a_inval \<sigma>'" using inval res by (auto simp: invalidate_place_def)
      show "\<forall>y. y \<in> a_init \<sigma>' \<longrightarrow> y \<notin> a_init \<sigma>2 \<longrightarrow> (\<exists>r. map_of env y = Some (Own r) \<and> (r, []) \<in> {q})"
        using init res by (auto simp: invalidate_place_def)
      show "\<forall>f. f \<in> a_fields \<sigma>' \<longrightarrow> f \<notin> a_fields \<sigma>2 \<longrightarrow>
          (\<forall>s T b. map_of \<Gamma> s = Some (KBorrow Out T) \<longrightarrow> map_of env s = Some b \<longrightarrow> ext (bpath b) (Fld f) \<in> {q})"
        using flds res by (auto simp: invalidate_place_def)
    qed
    have "bpath bz \<in> wpaths \<Gamma> env UNIV" using z by (auto simp: wpaths_def)
    then have "hagree (wpaths \<Gamma> env UNIV) st2 st4"
      using hagree_mono[OF ag] q(1) by (metis below_pext singletonD)
    then have ch: "chg \<Gamma> env UNIV st2 st4" using n23 p(2,3) by (simp add: chg_def)
    show "spec (do { st \<leftarrow> put st3 q v; Ok (Normal, env, st) })
        (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env UNIV st2 st')"
      using p(1) i4 ch by simp
  qed
qed

lemma assign_core2:
  assumes CP: "c_prog C = P" and SP: "SP P n" and SD: "SD P n"
    and inv: "inv P C \<Gamma> \<sigma>1 env st1" and vv: "vt P T v"
    and pt: "ptype P \<Gamma> p = Good T" and ca: "chk_assign C \<Gamma> \<sigma>1 p T = Good \<sigma>'"
  shows "spec (do { (q, st) \<leftarrow> eval_place P n env st1 p; st \<leftarrow> drop_path P n st q;
                    st \<leftarrow> put st q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and>
              chg \<Gamma> env UNIV st1 st')"
proof -
  have oo: "one_out \<Gamma>" using inv by (simp add: inv_def)
  from chk_assign_cases[OF ca] show ?thesis
  proof (elim disjE exE conjE)
    fix x U assume p: "p = PVar x" and xU: "map_of \<Gamma> x = Some (KOwned U)"
      and res: "\<sigma>' = invalidate_place \<Gamma> (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>) p T"
    from pt p xU have TU: "T = U" by simp
    from inv_binding[OF inv xU] obtain r w where r: "map_of env x = Some (Own r)"
      "heap st1 r = Some w" "if x \<in> a_init \<sigma>1 then vt P U w else wt_opt P U w" by auto
    have g: "get st1 (r, []) = Ok w" "wt_opt P T w" using r TU by (auto simp: get_def wt_opt_def split: if_splits)
    have R: "x \<in> place_origin \<Gamma> p" using p xU by (simp add: place_origin_def static_roots_def)
    have t: "spec (do { st \<leftarrow> drop_path P n st1 (r, []); st \<leftarrow> put st (r, []) v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env UNIV st1 st')"
      by (rule assign_tail[OF SD inv g xU _ r(1) _ _ vv R res, where ss = "[]"])
         (use TU r(1) in auto)
    with r p show ?thesis by (cases n) (simp_all add: eval_place_PVar)
  next
    fix s f U0 assume p: "p = PField (PVar s) f" and sU: "map_of \<Gamma> s = Some (KBorrow Out U0)"
      and res: "\<sigma>' = invalidate_place \<Gamma> (\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>) p T"
    from pt p sU obtain S where U0: "U0 = TStruct S" and ft: "field_ty P S f = Good T"
      by (cases U0) auto
    from inv_binding[OF inv sU] obtain b u where b: "map_of env s = Some b" "get st1 (bpath b) = Ok u"
      "out_val P C \<sigma>1 U0 u" by auto
    from out_field_wt[OF b(3)[unfolded U0] ft] obtain uf where uf: "walk u [Fld f] = Ok uf" "wt_opt P T uf"
      by blast
    let ?q = "pext (bpath b) [Fld f]"
    have g: "get st1 ?q = Ok uf" using b(2) uf(1) by (simp add: get_pext)
    have R: "s \<in> place_origin \<Gamma> p" using p sU by (simp add: place_origin_def static_roots_def)
    have fl: "\<forall>f'. f' \<in> a_fields (\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>) \<longrightarrow> f' \<notin> a_fields \<sigma>1 \<longrightarrow>
        (\<forall>s' T' b'. map_of \<Gamma> s' = Some (KBorrow Out T') \<longrightarrow> map_of env s' = Some b' \<longrightarrow> ext (bpath b') (Fld f') = ?q)"
    proof (intro allI impI)
      fix f' s' T' b' assume f': "f' \<in> a_fields (\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>)" "f' \<notin> a_fields \<sigma>1"
        and s': "map_of \<Gamma> s' = Some (KBorrow Out T')" "map_of env s' = Some b'"
      have "s' = s" using oo s'(1) sU by (auto simp: one_out_def)
      with s'(2) b(1) f' show "ext (bpath b') (Fld f') = ?q" by (simp add: ext_pext)
    qed
    have t: "spec (do { st \<leftarrow> drop_path P n st1 ?q; st \<leftarrow> put st ?q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env UNIV st1 st')"
      by (rule assign_tail[OF SD inv g(1) uf(2) sU _ b(1) _ _ vv R res _ _ fl])
         (use U0 ft in \<open>auto simp: sty_append\<close>)
    have ep: "eval_place P n env st1 p = (if n < 2 then OutOfFuel else Ok (?q, st1))"
      using b(1) p by (cases n; cases "n - 1") (auto simp: eval_place_PVar ext_pext split: binding.splits)
    show ?thesis using t by (cases "n < 2") (simp_all add: ep spec_OutOfFuel)
  next
    fix \<sigma>2 assume ci: "chk_idx C \<Gamma> \<sigma>1 p = Good \<sigma>2" and ro: "root_ok C \<Gamma> \<sigma>2 p = Good ()"
      and mo: "mut_ok \<Gamma> p = Good ()" and res: "\<sigma>' = invalidate_place \<Gamma> \<sigma>2 p T"
    have pl: "spec (eval_place P n env st1 p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>2 env st' \<and>
        chg \<Gamma> env (mroots_p P \<Gamma> p) st1 st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
        ploc P \<Gamma> env p T q \<and> rloc env p q)"
      using SP CP inv ci pt ro unfolding SP_def by blast
    show ?thesis
    proof (rule spec_bind_pair[OF pl])
      fix q st2 assume h: "inv P C \<Gamma> \<sigma>2 env st2 \<and> chg \<Gamma> env (mroots_p P \<Gamma> p) st1 st2 \<and>
          (\<exists>v. get st2 q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q \<and> rloc env p q"
      then obtain u where inv2: "inv P C \<Gamma> \<sigma>2 env st2" and ch2: "chg \<Gamma> env (mroots_p P \<Gamma> p) st1 st2"
        and g: "get st2 q = Ok u" "vt P T u" and plq: "ploc P \<Gamma> env p T q" by blast
      from plq obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz"
        "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
        "sty P (kind_ty kz) ss = Some T" unfolding ploc_def by blast
      have wr: "writable kz" using mut_ok_writable[OF mo z(1-3)] .
      have t: "spec (do { st \<leftarrow> drop_path P n st2 q; st \<leftarrow> put st q v; Ok (Normal, env, st) })
          (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env UNIV st2 st')"
        by (rule assign_tail[OF SD inv2 g(1) _ z(2) wr z(4,5,6) vv z(1) res])
           (use g(2) in \<open>auto simp: wt_opt_def\<close>)
      show "spec (do { st \<leftarrow> drop_path P n st2 q; st \<leftarrow> put st q v; Ok (Normal, env, st) })
          (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env UNIV st1 st')"
        by (rule spec_mono[OF t]) (use chg_trans_sub[OF ch2] in auto)
    qed
  qed
qed

lemma chg_after:
  "chg \<Gamma> env V st0 st1 \<Longrightarrow> nroot st1 \<le> nroot st2 \<Longrightarrow> heap_fresh st2 \<Longrightarrow>
   (\<forall>r < nroot st0. heap st2 r = heap st1 r) \<Longrightarrow> chg \<Gamma> env V st0 st2"
  unfolding chg_def using hagree_heap_after by (metis order_trans)

lemma chg_out: "chg \<Gamma> env V st st' \<Longrightarrow> chg \<Gamma> env V st (st'\<lparr>out_lines := x\<rparr>)"
  by (auto simp: chg_def heap_fresh_def hagree_def get_def)

lemma eval_ty_init:
  assumes SE: "SE P n" and CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st"
    and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'" and ti: "ty_init P \<Gamma> T e = Good ()"
  shows "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
proof (cases "e = EList []")
  case True
  with ty_init_cases[OF ti] obtain U where T: "T = TList U" by auto
  from ce True have s: "\<sigma>' = \<sigma>" by simp
  have c0: "chg \<Gamma> env (mroots P \<Gamma> e) st st" by (rule chg_init[OF inv])
  show ?thesis
  proof (cases n)
    case (Suc m)
    show ?thesis
    proof (cases m)
      case (Suc k)
      with \<open>n = Suc m\<close> True T s inv c0 show ?thesis by (simp add: fresh_gen_def chg_ngen)
    qed (use \<open>n = Suc m\<close> True in simp)
  qed (use True in simp)
next
  case False
  with ty_init_cases[OF ti] have "etype P \<Gamma> e = Good T" by blast
  with SE CP inv ce show ?thesis unfolding SE_def by blast
qed

lemma root_ok_bound: "root_ok C \<Gamma> \<sigma> p = Good u \<Longrightarrow> map_of \<Gamma> (root_of p) \<noteq> None"
  by (auto simp: root_ok_def Let_def split: option.splits)

lemma chk_args_roots:
  "chk_args C \<Gamma> \<sigma> ps es = Good (\<sigma>', bs) \<Longrightarrow> i < length ps \<Longrightarrow> es ! i = EPlace p \<Longrightarrow>
   fst (ps ! i) \<noteq> Var \<Longrightarrow> fst (ps ! i) \<noteq> Deinit \<Longrightarrow> map_of \<Gamma> (root_of p) \<noteq> None"
proof (induction ps arbitrary: es \<sigma> bs i)
  case Nil
  then show ?case by simp
next
  case (Cons prm ps)
  obtain c x T where prm: "prm = (c, x, T)" by (cases prm)
  from Cons.prems(1) obtain e es' where es: "es = e # es'" by (cases es) (auto simp: prm)
  from chk_args_cons[OF Cons.prems(1)[unfolded prm es]] obtain \<sigma>1 bs1 bs2 where
    tl: "chk_args C \<Gamma> \<sigma>1 ps es' = Good (\<sigma>', bs2)" and hd: "((c = Var \<or> c = Deinit) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = []) \<or>
      (c \<noteq> Var \<and> c \<noteq> Deinit \<and> (\<exists>p \<sigma>a U. e = EPlace p \<and> chk_idx C \<Gamma> \<sigma> p = Good \<sigma>a \<and>
         root_ok C \<Gamma> \<sigma>a p = Good () \<and> ptype (c_prog C) \<Gamma> p = Good U \<and> True)) \<or>
      (c = Imm \<and> (\<forall>p. e \<noteq> EPlace p) \<and> chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1 \<and> bs1 = [])"
    by blast
  show ?case
  proof (cases i)
    case 0
    with Cons.prems prm es hd show ?thesis by (auto dest: root_ok_bound)
  next
    case (Suc j)
    with Cons.prems prm es show ?thesis by (intro Cons.IH[OF tl]) auto
  qed
qed

lemma ref_args_D:
  "p \<in> set (ref_args ps es ns) \<Longrightarrow> \<exists>i. i < length ps \<and> i < length es \<and> es ! i = EPlace p \<and> fst (snd (ps ! i)) \<in> set ns"
  unfolding ref_args_def by (auto simp: in_set_zip split: prod.splits expr.splits) (metis fst_conv snd_conv)+

lemma ref_origin_dom:
  assumes wf\<Gamma>: "wf_senv \<Gamma>" and fd: "find_fun P f = Some fd" and rr: "fd_ret fd = RRef ns T"
    and ca: "chk_args C \<Gamma> \<sigma> (fd_params fd) es = Good (\<sigma>', bs)"
  shows "ref_origin_of \<Gamma> fd es ns \<subseteq> fst ` set \<Gamma>"
proof
  have cb: "chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()" using wf_fun[OF wf fd] .
  have d: "distinct (map (fst \<circ> snd) (fd_params fd))" using chk_body_facts(2)[OF cb] by simp
  fix y assume "y \<in> ref_origin_of \<Gamma> fd es ns"
  then obtain p where p: "p \<in> set (ref_args (fd_params fd) es ns)" "y \<in> place_origin \<Gamma> p"
    by (auto simp: ref_origin_of_def)
  from ref_args_D[OF p(1)] obtain i where i: "i < length (fd_params fd)" "i < length es"
    "es ! i = EPlace p" "fst (snd (fd_params fd ! i)) \<in> set ns" by blast
  have "list_ex (\<lambda>(c, z, _). z = fst (snd (fd_params fd ! i)) \<and> (c = conv.Mut \<or> c = Ref)) (fd_params fd)"
    using chk_body_facts(4)[OF cb] rr i(4) by (simp add: list_all_iff)
  then obtain j where j: "j < length (fd_params fd)" "fst (snd (fd_params fd ! j)) = fst (snd (fd_params fd ! i))"
    "fst (fd_params fd ! j) = conv.Mut \<or> fst (fd_params fd ! j) = Ref"
    by (auto simp: list_ex_iff in_set_conv_nth split: prod.splits)
  have "j = i" using nth_eq_iff_index_eq[OF d, of j i] j(1,2) i(1) by simp
  with j(3) have "fst (fd_params fd ! i) \<noteq> Var" "fst (fd_params fd ! i) \<noteq> Deinit" by auto
  from chk_args_roots[OF ca i(1,3) this] have "map_of \<Gamma> (root_of p) \<noteq> None" .
  from place_origin_dom[OF wf\<Gamma> this] p(2) show "y \<in> fst ` set \<Gamma>" by blast
qed

lemma SB_Suc:
  assumes IHs: "SS P n" and IHc: "SC P n"
  shows "SB P (Suc n)"
  unfolding SB_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  from chk_stmt_extends(1)[OF chk] obtain \<Delta> where \<Delta>: "\<Gamma>' = \<Delta> @ \<Gamma>"
    "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T" by blast
  have ex: "spec (exec P n (c_ret C) env st s) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    using IHs CP inv chk unfolding SS_def by blast
  have mfe: "map fst env = map fst \<Gamma>" using inv by (simp add: inv_def)
  show "spec (exec_block P (Suc n) (c_ret C) env st s) (bpost P C \<Gamma> o\<sigma> env st)"
    unfolding exec_block.simps
  proof (rule spec_bind, rule spec_mono[OF ex], clarify)
    fix oc env' st' assume post: "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (oc, env', st')"
    from post obtain \<Delta>e where e: "env' = \<Delta>e @ env" and fresh: "\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st \<le> r"
      and ch: "chg \<Gamma> env UNIV st st'" by (auto simp: spost_def)
    show "spec (case oc of
                  Normal \<Rightarrow> bind_res (cleanup P n st' (take (length env' - length env) env'))
                              (\<lambda>st. Ok (Normal, env, st))
                | Returned r \<Rightarrow> Ok (Returned r, env', st')) (bpost P C \<Gamma> o\<sigma> env st)"
    proof (cases oc)
      case Normal
      with post \<Delta> obtain \<sigma>' where o: "o\<sigma> = Some \<sigma>'"
        and inv': "inv P C (\<Delta> @ \<Gamma>) \<sigma>' (\<Delta>e @ env) st'" using e by (auto simp: spost_def)
      have len: "length \<Delta>e = length \<Delta>" using len_ext[OF inv' mfe] .
      have tk: "take (length env' - length env) env' = \<Delta>e" using e by simp
      note F = inv_restrict_facts[OF inv' len \<Delta>(2)]
      have fr': "heap_fresh st'" using ch by (simp add: chg_def)
      have cl: "spec (cleanup P n st' \<Delta>e) (\<lambda>st''. nroot st' \<le> nroot st'' \<and> heap_fresh st'' \<and>
          (\<forall>r. r < nroot st' \<longrightarrow> r \<notin> owned_roots \<Delta>e \<longrightarrow> heap st'' r = heap st' r))"
        using IHc F(7) fr' unfolding SC_def by blast
      show ?thesis
        unfolding Normal outcome.case tk
      proof (rule spec_bind_mono[OF cl])
        fix st'' assume h: "nroot st' \<le> nroot st'' \<and> heap_fresh st'' \<and>
          (\<forall>r. r < nroot st' \<longrightarrow> r \<notin> owned_roots \<Delta>e \<longrightarrow> heap st'' r = heap st' r)"
        then have i'': "inv P C \<Gamma> \<sigma>' env st''" using inv_restrict[OF inv' len \<Delta>(2)] by blast
        have "\<forall>r < nroot st. heap st'' r = heap st' r"
        proof (intro allI impI)
          fix r assume r: "r < nroot st"
          have "r \<notin> owned_roots \<Delta>e"
          proof
            assume "r \<in> owned_roots \<Delta>e"
            then obtain x where "(x, Own r) \<in> set \<Delta>e" by (auto simp: owned_roots_set)
            with fresh r show False by (meson leD)
          qed
          moreover have "r < nroot st'" using r ch by (auto simp: chg_def)
          ultimately show "heap st'' r = heap st' r" using h by blast
        qed
        then have "chg \<Gamma> env UNIV st st''" using chg_after[OF ch] h by blast
        with o i'' show "spec (Ok (Normal, env, st'')) (bpost P C \<Gamma> o\<sigma> env st)"
          by (simp add: bpost_def)
      qed
    next
      case (Returned r)
      with post show ?thesis by (auto simp: spost_def bpost_def)
    qed
  qed
qed

lemma spost_seq:
  assumes inv1: "inv P C (\<Delta>1 @ \<Gamma>) \<sigma>1 (\<Delta>1e @ env) st1" and nb1: "\<forall>(x, k) \<in> set \<Delta>1. \<forall>c T. k \<noteq> KBorrow c T"
    and fresh1: "\<forall>x r. (x, Own r) \<in> set \<Delta>1e \<longrightarrow> nroot st \<le> r" and ch1: "chg \<Gamma> env UNIV st st1"
    and mfe: "map fst env = map fst \<Gamma>"
    and sp2: "spost P C (\<Delta>1 @ \<Gamma>) \<Gamma>' o\<sigma> (\<Delta>1e @ env) st1 (oc, env2, st2)"
  shows "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (oc, env2, st2)"
proof -
  from sp2 obtain \<Delta>2e where e2: "env2 = \<Delta>2e @ \<Delta>1e @ env" and fresh2: "\<forall>x r. (x, Own r) \<in> set \<Delta>2e \<longrightarrow> nroot st1 \<le> r"
    and ch2: "chg (\<Delta>1 @ \<Gamma>) (\<Delta>1e @ env) UNIV st1 st2" by (auto simp: spost_def)
  have n01: "nroot st \<le> nroot st1" using ch1 by (simp add: chg_def)
  have sub: "wpaths (\<Delta>1 @ \<Gamma>) (\<Delta>1e @ env) UNIV \<subseteq> wpaths \<Gamma> env UNIV \<union> {q. nroot st \<le> fst q}"
    by (rule wpaths_ext[OF inv1 mfe nb1 fresh1])
  have "hagree (wpaths \<Gamma> env UNIV \<union> {q. nroot st \<le> fst q}) st1 st2"
    using ch2 hagree_mono[of "wpaths (\<Delta>1 @ \<Gamma>) (\<Delta>1e @ env) UNIV" st1 st2] sub
    by (auto simp: chg_def intro: below_refl)
  then have ch: "chg \<Gamma> env UNIV st st2"
    using chg_call[OF ch1 _ _ _, of UNIV st2] ch2 by (auto simp: chg_def)
  have fresh: "\<forall>x r. (x, Own r) \<in> set (\<Delta>2e @ \<Delta>1e) \<longrightarrow> nroot st \<le> r"
    using fresh1 fresh2 n01 order_trans by fastforce
  show ?thesis
  proof (cases oc)
    case Normal
    with sp2 e2 ch fresh show ?thesis by (auto simp: spost_def)
  next
    case (Returned rv)
    with sp2 obtain \<Delta> \<sigma>r where r: "inv P C (\<Delta> @ \<Delta>1 @ \<Gamma>) \<sigma>r env2 st2"
      "c_ret C = RNone \<longrightarrow> set (c_fields C) \<subseteq> a_fields \<sigma>r" "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
      "ret_res P (c_ret C) (\<Delta> @ \<Delta>1 @ \<Gamma>) env2 st2 rv" by (auto simp: spost_def)
    have "\<forall>(x, k) \<in> set (\<Delta> @ \<Delta>1). \<forall>c T. k \<noteq> KBorrow c T" using r(3) nb1 by auto
    with r e2 ch fresh Returned show ?thesis
      by (auto simp: spost_def intro!: exI[of _ "\<Delta>2e @ \<Delta>1e"] exI[of _ "\<Delta> @ \<Delta>1"])
  qed
qed

lemma spost_pre:
  "inv P C \<Gamma> \<sigma>1 env st1 \<Longrightarrow> chg \<Gamma> env UNIV st st1 \<Longrightarrow> spost P C \<Gamma> \<Gamma>' o\<sigma> env st1 r \<Longrightarrow>
   spost P C \<Gamma> \<Gamma>' o\<sigma> env st r"
  using spost_seq[of C "[]" \<Gamma> \<sigma>1 "[]" env st1 st \<Gamma>' o\<sigma>] by (cases r) (auto simp: inv_def)

lemma bpost_spost:
  assumes bp: "bpost P C \<Gamma> o\<sigma>b env st1 (Returned rv, env', st2)" and ch1: "chg \<Gamma> env UNIV st st1"
  shows "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (Returned rv, env', st2)"
proof -
  from bp obtain \<Delta>e where e: "env' = \<Delta>e @ env" and fresh: "\<forall>x r. (x, Own r) \<in> set \<Delta>e \<longrightarrow> nroot st1 \<le> r"
    and ch2: "chg \<Gamma> env UNIV st1 st2" by (auto simp: bpost_def)
  have n01: "nroot st \<le> nroot st1" using ch1 by (simp add: chg_def)
  have "chg \<Gamma> env UNIV st st2" using chg_trans[OF ch1 ch2] by simp
  with bp e fresh n01 show ?thesis by (fastforce simp: bpost_def spost_def)
qed

lemma oloc_mono: "oloc P \<Gamma> env R I T q \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> I \<subseteq> I' \<Longrightarrow> oloc P \<Gamma> env R' I' T q"
  by (auto simp: oloc_def) blast

text \<open>Statements, one lemma per form.\<close>

lemma SS_seq:
  assumes IHs: "SS P n" and CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st"
    and chk: "chk_stmt C \<Gamma> \<sigma> (SSeq a b) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SSeq a b)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  have IHs': "\<And>\<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<Longrightarrow>
      spec (exec P n (c_ret C) env st s) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    using IHs CP unfolding SS_def by blast
  from chk obtain \<Gamma>1 o\<sigma>1 where ca: "chk_stmt C \<Gamma> \<sigma> a = Good (\<Gamma>1, o\<sigma>1)"
    and rest: "(case o\<sigma>1 of None \<Rightarrow> Good (\<Gamma>1, None) | Some \<sigma>1 \<Rightarrow> chk_stmt C \<Gamma>1 \<sigma>1 b) = Good (\<Gamma>', o\<sigma>)"
    by auto
  from chk_stmt_extends(1)[OF ca] obtain \<Delta>1 where \<Delta>1: "\<Gamma>1 = \<Delta>1 @ \<Gamma>"
    "\<forall>(x, k) \<in> set \<Delta>1. \<forall>c T. k \<noteq> KBorrow c T" by blast
  have mfe: "map fst env = map fst \<Gamma>" using inv by (simp add: inv_def)
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind, rule spec_mono[OF IHs'[OF inv ca]], clarify)
    fix oc env1 st1 assume post: "spost P C \<Gamma> \<Gamma>1 o\<sigma>1 env st (oc, env1, st1)"
    show "spec (case oc of Normal \<Rightarrow> exec P n (c_ret C) env1 st1 b
                | Returned r \<Rightarrow> Ok (Returned r, env1, st1)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    proof (cases oc)
      case Normal
      with post obtain \<sigma>1 \<Delta>1e where o1: "o\<sigma>1 = Some \<sigma>1" and e1: "env1 = \<Delta>1e @ env"
        and fresh1: "\<forall>x r. (x, Own r) \<in> set \<Delta>1e \<longrightarrow> nroot st \<le> r" and ch1: "chg \<Gamma> env UNIV st st1"
        and inv1: "inv P C \<Gamma>1 \<sigma>1 env1 st1" by (auto simp: spost_def)
      with rest have cb: "chk_stmt C \<Gamma>1 \<sigma>1 b = Good (\<Gamma>', o\<sigma>)" by simp
      have inv1': "inv P C (\<Delta>1 @ \<Gamma>) \<sigma>1 (\<Delta>1e @ env) st1" using inv1 \<Delta>1(1) e1 by simp
      show ?thesis unfolding Normal outcome.case
      proof (rule spec_mono[OF IHs'[OF inv1 cb]])
        fix r assume "spost P C \<Gamma>1 \<Gamma>' o\<sigma> env1 st1 r"
        then show "spost P C \<Gamma> \<Gamma>' o\<sigma> env st r"
          using spost_seq[OF inv1' \<Delta>1(2) fresh1 ch1 mfe] \<Delta>1(1) e1 by (cases r) auto
      qed
    next
      case (Returned r)
      with post show ?thesis by (auto simp: spost_def)
    qed
  qed
qed

lemma SS_var:
  assumes SE: "SE P n" and CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st"
    and chk: "chk_stmt C \<Gamma> \<sigma> (SVar x T eo) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SVar x T eo)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof (cases eo)
  case None
  from chk None have x: "x \<notin> fst ` set \<Gamma>" and o: "\<Gamma>' = (x, KOwned T) # \<Gamma>"
    "o\<sigma> = Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>)" by auto
  obtain r st2 where al: "alloc st VUndef = (r, st2)" by (cases "alloc st VUndef")
  have i2: "inv P C ((x, KOwned T) # \<Gamma>) (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) ((x, Own r) # env) st2"
    by (rule inv_alloc_owned[OF inv x al]) (auto simp: wt_opt_def)
  have ch: "chg \<Gamma> env UNIV st st2" using chg_alloc[OF chg_init[OF inv] al] .
  have "r = nroot st" using alloc_facts(1)[OF al] .
  with i2 ch o al None show ?thesis
    by (auto simp: spost_def intro!: exI[of _ "[(x, Own r)]"])
next
  case (Some e)
  with chk obtain \<sigma>1 where x: "x \<notin> fst ` set \<Gamma>" and ti: "ty_init P \<Gamma> T e = Good ()"
    and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
    and o: "\<Gamma>' = (x, KOwned T) # \<Gamma>" "o\<sigma> = Some (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>)"
    using CP by auto
  show ?thesis
    unfolding Some exec.simps stmt.case option.case
  proof (rule spec_bind_pair[OF eval_ty_init[OF SE CP inv ce ti]])
    fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and> vt P T v"
    obtain r st2 where al: "alloc st1 v = (r, st2)" by (cases "alloc st1 v")
    have i2: "inv P C ((x, KOwned T) # \<Gamma>) (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>) ((x, Own r) # env) st2"
      by (rule inv_alloc_owned[OF h[THEN conjunct1] x al]) (use h in auto)
    have ch: "chg \<Gamma> env UNIV st st2" using chg_alloc[OF chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] al] h by simp
    have "r = nroot st1" "nroot st \<le> nroot st1" using alloc_facts(1)[OF al] h by (auto simp: chg_def)
    with i2 ch o al show "spec (case alloc st1 v of (r, st) \<Rightarrow> Ok (Normal, (x, Own r) # env, st))
        (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
      by (auto simp: spost_def intro!: exI[of _ "[(x, Own r)]"])
  qed
qed

lemma SS_ref:
  assumes SR: "SR P n" and CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st"
    and chk: "chk_stmt C \<Gamma> \<sigma> (SRef x e) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SRef x e)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  have wf\<Gamma>: "wf_senv \<Gamma>" using inv by (simp add: inv_def)
  from chk have x: "x \<notin> fst ` set \<Gamma>" by auto
  have "\<exists>\<sigma>1 T R I. ref_chk C \<Gamma> \<sigma> e \<sigma>1 T R I \<and> R \<subseteq> fst ` set \<Gamma> \<and>
          \<Gamma>' = (x, KRef T R I) # \<Gamma> \<and> o\<sigma> = Some \<sigma>1"
  proof (cases e)
    case (EPlace p)
    with chk obtain \<sigma>1 T where ci: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and pt: "ptype P \<Gamma> p = Good T"
      and o: "\<Gamma>' = (x, KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)) # \<Gamma>" "o\<sigma> = Some \<sigma>1"
      using CP by auto
    have og: "place_origin \<Gamma> p \<subseteq> fst ` set \<Gamma>"
      using place_origin_dom[OF wf\<Gamma> root_ok_bound[OF ro]] .
    show ?thesis using ci ro pt o og CP EPlace by (auto simp: ref_chk_def)
  next
    case (ECall f es)
    with chk obtain fd where fd: "find_fun P f = Some fd" using CP by (auto split: option.splits)
    with chk ECall CP obtain ns T T0 \<sigma>1 where rr: "fd_ret fd = RRef ns T"
      and te: "etype P \<Gamma> e = Good T0" and cc: "chk_call C \<Gamma> \<sigma> f es = Good \<sigma>1"
      and o: "\<Gamma>' = (x, KRef T (ref_origin_of \<Gamma> fd es ns) (ref_origin_of \<Gamma> fd es ns)) # \<Gamma>" "o\<sigma> = Some \<sigma>1"
      by (auto simp: ref_origin_of_def split: ret.splits)
    have nsf: "find_struct P f = None" using wf_fun_not_struct[OF wf fd] .
    have TT: "T0 = T" using te ECall fd nsf rr by (auto simp: call_ret_def call_params_def)
    from cc fd nsf CP obtain \<sigma>a bs where ca: "chk_args C \<Gamma> \<sigma> (fd_params fd) es = Good (\<sigma>a, bs)"
      by (auto simp: chk_call_def call_params_def)
    have og: "ref_origin_of \<Gamma> fd es ns \<subseteq> fst ` set \<Gamma>" using ref_origin_dom[OF wf\<Gamma> fd rr ca] .
    show ?thesis using ECall fd rr cc te TT o og CP by (auto simp: ref_chk_def)
  next
  qed (use chk in auto)
  then obtain \<sigma>1 T R I where rc: "ref_chk C \<Gamma> \<sigma> e \<sigma>1 T R I" and og: "R \<subseteq> fst ` set \<Gamma>"
    and o: "\<Gamma>' = (x, KRef T R I) # \<Gamma>" "o\<sigma> = Some \<sigma>1" by blast
  have r: "spec (eval_ref P n env st e) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       oloc P \<Gamma> env R I T q \<and> (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q))"
    using SR CP inv rc unfolding SR_def by blast
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF r])
    fix q st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
       (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and> oloc P \<Gamma> env R I T q \<and> (\<forall>p. e = EPlace p \<longrightarrow> rloc env p q)"
    then obtain v where g: "get st1 q = Ok v" "vt P T v" by blast
    have i1: "inv P C ((x, KRef T R I) # \<Gamma>) \<sigma>1 ((x, Bor q) # env) st1"
      using inv_add_ref_gen[OF h[THEN conjunct1] x _ g og] h by blast
    have ch: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] h by simp
    show "spec (Ok (Normal, (x, Bor q) # env, st1)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
      using i1 ch o by (auto simp: spost_def intro!: exI[of _ "[(x, Bor q)]"])
  qed
qed

lemma SS_assign:
  assumes SE: "SE P n" and SP: "SP P n" and SD: "SD P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SAssign p e) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SAssign p e)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  from chk obtain T \<sigma>1 \<sigma>' where pt: "ptype P \<Gamma> p = Good T" and ti: "ty_init P \<Gamma> T e = Good ()"
    and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" and ca: "chk_assign C \<Gamma> \<sigma>1 p T = Good \<sigma>'"
    and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>'"
    using CP by auto
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF eval_ty_init[OF SE CP inv ce ti]])
    fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and> vt P T v"
    have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] h by simp
    show "spec (do { (q, st) \<leftarrow> eval_place P n env st1 p; st \<leftarrow> drop_path P n st q;
                     st \<leftarrow> put st q v; Ok (Normal, env, st) }) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    proof (rule spec_mono[OF assign_core2[OF CP SP SD h[THEN conjunct1] h[THEN conjunct2, THEN conjunct2] pt ca]],
           clarify)
      fix st2 assume "inv P C \<Gamma> \<sigma>' env st2" "chg \<Gamma> env UNIV st1 st2"
      then show "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (Normal, env, st2)"
        using spost_normal chg_trans[OF ch1] o by fastforce
    qed
  qed
qed

lemma SS_expr:
  assumes SE: "SE P n" and SD: "SD P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SExpr e) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SExpr e)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  from chk obtain T \<sigma>1 where et: "etype P \<Gamma> e = Good T" and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
    and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>1"
    using CP by auto
  have ev: "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
      chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
    using SE CP inv ce et unfolding SE_def by blast
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF ev])
    fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and> vt P T v"
    have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] h by simp
    obtain r st2 where al: "alloc st1 v = (r, st2)" by (cases "alloc st1 v")
    note A = alloc_facts[OF al]
    have fr1: "heap_fresh st1" using h inv_heap_fresh by blast
    have fr2: "heap_fresh st2" using A(4)[OF fr1] .
    have g: "get st2 (r, []) = Ok v" using A by (simp add: get_def)
    have D: "spec (drop_path P n st2 (r, [])) (dpost st2 (r, []))"
      using SD g fr2 h unfolding SD_def by (meson wt_opt_def)
    show "spec (case alloc st1 v of (r, st) \<Rightarrow>
                  bind_res (drop_path P n st (r, [])) (\<lambda>st. Ok (Normal, env, free st r)))
               (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
      unfolding al prod.case
    proof (rule spec_bind_mono[OF D])
      fix st3 assume d: "dpost st2 (r, []) st3"
      have same: "\<forall>r' < nroot st1. heap (free st3 r) r' = heap st1 r'"
      proof (intro allI impI)
        fix r' assume r': "r' < nroot st1"
        then have "r' \<noteq> r" "r' < nroot st2" using A by auto
        with hagreeD1[of "{(r, [])}" st2 st3 r'] d A show "heap (free st3 r) r' = heap st1 r'"
          by (auto simp: dpost_def free_def)
      qed
      have n: "nroot st1 \<le> nroot (free st3 r)" using d A by (auto simp: dpost_def free_def)
      have fr: "heap_fresh (free st3 r)" using d by (auto simp: dpost_def heap_fresh_def free_def)
      have i3: "inv P C \<Gamma> \<sigma>1 env (free st3 r)"
        by (rule inv_heap_frame[OF h[THEN conjunct1]]) (use same n fr in auto)
      have "chg \<Gamma> env UNIV st (free st3 r)" by (rule chg_extend[OF ch1 n fr same])
      with i3 o show "spec (Ok (Normal, env, free st3 r)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
        by (simp add: spost_normal)
    qed
  qed
qed

lemma SS_print:
  assumes SES: "SES P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SPrint es) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SPrint es)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  from chk obtain Ts \<sigma>1 where et: "etypes P \<Gamma> es = Good Ts"
    and ce: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>1" and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>1"
    using CP by auto
  have ev: "spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
       chg \<Gamma> env (mroots_l P \<Gamma> es) st st' \<and> list_all2 (vt P) Ts vs)"
    using SES CP inv ce et unfolding SES_def by blast
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF ev])
    fix vs st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots_l P \<Gamma> es) st st1 \<and> list_all2 (vt P) Ts vs"
    let ?st2 = "st1\<lparr>out_lines := out_lines st1 @ [vs]\<rparr>"
    have i2: "inv P C \<Gamma> \<sigma>1 env ?st2"
      by (rule inv_heap_frame[OF h[THEN conjunct1]]) (use h in \<open>auto simp: heap_fresh_def dest: inv_heap_fresh\<close>)
    have "chg \<Gamma> env UNIV st ?st2"
      using chg_out[OF chg_mono[of \<Gamma> env "mroots_l P \<Gamma> es" st st1 UNIV]] h by simp
    with i2 o show "spec (Ok (Normal, env, ?st2)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
      by (simp add: spost_normal)
  qed
qed

lemma SS_drop:
  assumes SD: "SD P n" and inv: "inv P C \<Gamma> \<sigma> env st"
    and chk: "chk_stmt C \<Gamma> \<sigma> (SDrop p) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SDrop p)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  obtain x where p: "p = PVar x" using chk by (cases p) simp_all
  obtain U where xU: "map_of \<Gamma> x = Some (KOwned U)"
    using chk p by (cases "map_of \<Gamma> x"; cases "the (map_of \<Gamma> x)") auto
  have o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>)" using chk p xU by simp_all
  from inv_binding[OF inv xU] obtain r w where r: "map_of env x = Some (Own r)"
    "heap st r = Some w" "if x \<in> a_init \<sigma> then vt P U w else wt_opt P U w" by auto
  have g: "get st (r, []) = Ok w" "wt_opt P U w" using r by (auto simp: get_def wt_opt_def split: if_splits)
  have D: "spec (drop_path P n st (r, [])) (dpost st (r, []))"
    using SD g inv_heap_fresh[OF inv] unfolding SD_def by blast
  have dr: "spec (bind_res (drop_path P n st (r, [])) (\<lambda>st. Ok (Normal, env, st))) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
  proof (rule spec_bind_mono[OF D])
    fix st2 assume d: "dpost st (r, []) st2"
    have i2: "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env st2" by (rule inv_drop_owned[OF inv xU r(1) d])
    have "(r, []) \<in> wpaths \<Gamma> env UNIV" using wpaths_owned[OF xU r(1)] by simp
    then have "\<forall>w \<in> {(r, [])}. \<exists>x \<in> wpaths \<Gamma> env UNIV. below w x" using below_refl by blast
    then have "hagree (wpaths \<Gamma> env UNIV) st st2"
      using d hagree_mono[of "{(r, [])}" st st2 "wpaths \<Gamma> env UNIV"] by (auto simp: dpost_def)
    then have "chg \<Gamma> env UNIV st st2" using d by (auto simp: dpost_def chg_def)
    with i2 o show "spec (Ok (Normal, env, st2)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)" by (simp add: spost_normal)
  qed
  show ?thesis
    unfolding exec.simps stmt.case p
    using dr r by (cases n) (simp_all add: eval_place_PVar)
qed

lemma SS_return:
  assumes SE: "SE P n" and SR: "SR P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SReturn eo) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SReturn eo)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof (cases eo)
  case None
  with chk have o: "c_ret C = RNone" "set (c_fields C) \<subseteq> a_fields \<sigma>" by auto
  with None inv chg_init[OF inv] show ?thesis
    by (auto simp: spost_def ret_res_def intro!: exI[of _ "[]"])
next
  case (Some e)
  show ?thesis
  proof (cases "c_ret C")
    case RNone
    with chk Some show ?thesis by simp
  next
    case (RVal T)
    with chk Some obtain \<sigma>1 where ti: "ty_init P \<Gamma> T e = Good ()"
      and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" using CP by auto
    show ?thesis
      unfolding Some exec.simps stmt.case option.case RVal ret.case
    proof (rule spec_bind_pair[OF eval_ty_init[OF SE CP inv ce ti]])
      fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and> vt P T v"
      have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] h by simp
      show "spec (Ok (Returned (RV v), env, st1)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
        using h ch1 RVal by (auto simp: spost_def ret_res_def intro!: exI[of _ "[]"])
    qed
  next
    case (RRef ns T)
    with chk Some obtain p \<sigma>1 where e: "e = EPlace p" and ci: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and pt: "ptype P \<Gamma> p = Good T"
      and sub: "place_origin \<Gamma> p \<subseteq> set ns"
      using CP by (auto split: expr.splits)
    have rc: "ref_chk C \<Gamma> \<sigma> e \<sigma>1 T (place_origin \<Gamma> p) (place_interior \<Gamma> p)"
      using e ci ro pt CP by (simp add: ref_chk_def)
    have r: "spec (eval_ref P n env st e) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
       chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and>
       oloc P \<Gamma> env (place_origin \<Gamma> p) (place_interior \<Gamma> p) T q \<and> (\<forall>p'. e = EPlace p' \<longrightarrow> rloc env p' q))"
      using SR CP inv rc unfolding SR_def by blast
    show ?thesis
      unfolding Some exec.simps stmt.case option.case RRef ret.case
    proof (rule spec_bind_pair[OF r])
      fix q st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> e) st st1 \<and>
         (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and> oloc P \<Gamma> env (place_origin \<Gamma> p) (place_interior \<Gamma> p) T q \<and>
         (\<forall>p'. e = EPlace p' \<longrightarrow> rloc env p' q)"
      have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> e" st st1 UNIV] h by simp
      have ol: "oloc P \<Gamma> env (set ns) UNIV T q" using oloc_mono[of \<Gamma> env _ _ T q] h sub by blast
      show "spec (Ok (Returned (RP q), env, st1)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
        using h ch1 ol RRef by (auto simp: spost_def ret_res_def intro!: exI[of _ "[]"])
    qed
  qed
qed

lemma bpost_normal_spost:
  assumes bp: "bpost P C \<Gamma> ob env st1 (oc, env', st2)" and ch1: "chg \<Gamma> env UNIV st st1"
    and w: "\<And>\<sigma>b. oc = Normal \<Longrightarrow> ob = Some \<sigma>b \<Longrightarrow> \<exists>\<sigma>'. o\<sigma> = Some \<sigma>' \<and> weaker \<sigma>' \<sigma>b"
  shows "spost P C \<Gamma> \<Gamma> o\<sigma> env st (oc, env', st2)"
proof (cases oc)
  case Normal
  with bp obtain \<sigma>b where e': "env' = env" and ob: "ob = Some \<sigma>b" and ib: "inv P C \<Gamma> \<sigma>b env st2"
    and ch2: "chg \<Gamma> env UNIV st1 st2" by (auto simp: bpost_def)
  from w[OF Normal ob] obtain \<sigma>' where "o\<sigma> = Some \<sigma>'" "weaker \<sigma>' \<sigma>b" by blast
  with inv_weaken[OF ib] chg_trans[OF ch1 ch2] e' Normal show ?thesis by (simp add: spost_normal)
next
  case (Returned rv)
  with bpost_spost[OF bp[unfolded Returned] ch1] show ?thesis by simp
qed

lemma SS_if:
  assumes SE: "SE P n" and SB: "SB P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SIf c a b) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SIf c a b)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  from chk obtain \<sigma>1 \<Gamma>a o1 \<Gamma>b o2 where et: "etype P \<Gamma> c = Good TBool"
    and cc: "chk_expr C \<Gamma> \<sigma> c = Good \<sigma>1" and ca: "chk_stmt C \<Gamma> \<sigma>1 a = Good (\<Gamma>a, o1)"
    and cb: "chk_stmt C \<Gamma> \<sigma>1 b = Good (\<Gamma>b, o2)" and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = join_opt o1 o2"
    using CP by auto
  have IHb': "\<And>s \<Gamma>s os st. inv P C \<Gamma> \<sigma>1 env st \<Longrightarrow> chk_stmt C \<Gamma> \<sigma>1 s = Good (\<Gamma>s, os) \<Longrightarrow>
      spec (exec_block P n (c_ret C) env st s) (bpost P C \<Gamma> os env st)"
    using SB CP unfolding SB_def by blast
  have ev: "spec (eval P n env st c) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>1 env st' \<and>
      chg \<Gamma> env (mroots P \<Gamma> c) st st' \<and> vt P TBool v)"
    using SE CP inv cc et unfolding SE_def by blast
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF ev])
    fix cv st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> c) st st1 \<and> vt P TBool cv"
    then obtain bb where cv: "cv = VBool bb" by (cases cv) auto
    have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> c" st st1 UNIV] h by simp
    have blk: "spec (exec_block P n (c_ret C) env st1 (if bb then a else b))
                 (bpost P C \<Gamma> (if bb then o1 else o2) env st1)"
      using IHb'[OF h[THEN conjunct1]] ca cb by (cases bb) auto
    have "spec (exec_block P n (c_ret C) env st1 (if bb then a else b)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    proof (rule spec_mono[OF blk], clarify)
      fix oc env' st' assume bp: "bpost P C \<Gamma> (if bb then o1 else o2) env st1 (oc, env', st')"
      show "spost P C \<Gamma> \<Gamma>' o\<sigma> env st (oc, env', st')"
        unfolding o(1)
      proof (rule bpost_normal_spost[OF bp ch1])
        fix \<sigma>b assume "(if bb then o1 else o2) = Some \<sigma>b"
        then show "\<exists>\<sigma>'. o\<sigma> = Some \<sigma>' \<and> weaker \<sigma>' \<sigma>b"
          using join_opt_weaker[of o1 \<sigma>b o2] join_opt_weaker(2)[of o2 \<sigma>b o1] o(2) by (cases bb) auto
      qed
    qed
    with cv show "spec (case cv of VBool b' \<Rightarrow> exec_block P n (c_ret C) env st1 (if b' then a else b)
                        | _ \<Rightarrow> Err (ErrType ''if condition'')) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
      by simp
  qed
qed

lemma SS_while:
  assumes SE: "SE P n" and SB: "SB P n" and SS: "SS P n" and CP: "c_prog C = P"
    and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> (SWhile c b) = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P (Suc n) (c_ret C) env st (SWhile c b)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
proof -
  from chk obtain o\<sigma>' where et: "etype P \<Gamma> c = Good TBool"
    and cl: "chk_loop (Suc (Suc (length \<Gamma> + size b + length (c_fields C)))) C \<Gamma> \<sigma> c b = Good o\<sigma>'"
    and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = o\<sigma>'"
    using CP by (simp only: chk_stmt.simps bind_ck_Good_iff check_Good_iff ck.inject prod.inject) blast
  from chk_loop_fix[OF cl] obtain \<sigma>f \<sigma>c \<Gamma>b ob where w: "weaker \<sigma>f \<sigma>"
    and cc: "chk_expr C \<Gamma> \<sigma>f c = Good \<sigma>c" and cb: "chk_stmt C \<Gamma> \<sigma>c b = Good (\<Gamma>b, ob)"
    and j: "join_opt (Some \<sigma>f) ob = Some \<sigma>f" and os: "o\<sigma>' = Some \<sigma>c" by blast
  have invf: "inv P C \<Gamma> \<sigma>f env st" using inv_weaken[OF inv w] .
  have again: "chk_stmt C \<Gamma> \<sigma>f (SWhile c b) = Good (\<Gamma>, Some \<sigma>c)"
    using et CP chk_loop_stable[OF cc cb j] by simp
  have ev: "spec (eval P n env st c) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>c env st' \<and>
      chg \<Gamma> env (mroots P \<Gamma> c) st st' \<and> vt P TBool v)"
    using SE CP invf cc et unfolding SE_def by blast
  show ?thesis
    unfolding exec.simps stmt.case
  proof (rule spec_bind_pair[OF ev])
    fix cv st1 assume h: "inv P C \<Gamma> \<sigma>c env st1 \<and> chg \<Gamma> env (mroots P \<Gamma> c) st st1 \<and> vt P TBool cv"
    then obtain bb where cv: "cv = VBool bb" by (cases cv) auto
    have ch1: "chg \<Gamma> env UNIV st st1" using chg_mono[of \<Gamma> env "mroots P \<Gamma> c" st st1 UNIV] h by simp
    show "spec (case cv of
                  VBool True \<Rightarrow> bind_res (exec_block P n (c_ret C) env st1 b)
                    (\<lambda>(oc, env', st). case oc of Normal \<Rightarrow> exec P n (c_ret C) env st (SWhile c b)
                                       | Returned r \<Rightarrow> Ok (Returned r, env', st))
                | VBool False \<Rightarrow> Ok (Normal, env, st1)
                | _ \<Rightarrow> Err (ErrType ''while condition'')) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
    proof (cases bb)
      case False
      with cv h ch1 o os show ?thesis by (simp add: spost_normal)
    next
      case True
      have blk: "spec (exec_block P n (c_ret C) env st1 b) (bpost P C \<Gamma> ob env st1)"
        using SB CP h cb unfolding SB_def by blast
      from True have bbT: "bb = True" by simp
      show ?thesis
        unfolding cv bbT val.case bool.case
      proof (rule spec_bind, rule spec_mono[OF blk], clarify)
        fix oc env' st2 assume bp: "bpost P C \<Gamma> ob env st1 (oc, env', st2)"
        show "spec (case oc of Normal \<Rightarrow> exec P n (c_ret C) env st2 (SWhile c b)
                    | Returned r \<Rightarrow> Ok (Returned r, env', st2)) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
        proof (cases oc)
          case Normal
          with bp obtain \<sigma>b where e': "env' = env" and ob: "ob = Some \<sigma>b"
            and ib: "inv P C \<Gamma> \<sigma>b env st2" and ch2: "chg \<Gamma> env UNIV st1 st2" by (auto simp: bpost_def)
          have "weaker \<sigma>f \<sigma>b" using join_opt_Some_weaker[OF j] ob by blast
          then have i2: "inv P C \<Gamma> \<sigma>f env st2" by (rule inv_weaken[OF ib])
          have ch12: "chg \<Gamma> env UNIV st st2" using chg_trans[OF ch1 ch2] by simp
          have rec: "spec (exec P n (c_ret C) env st2 (SWhile c b)) (spost P C \<Gamma> \<Gamma> (Some \<sigma>c) env st2)"
            using SS CP i2 again unfolding SS_def by blast
          show ?thesis unfolding Normal outcome.case
            by (rule spec_mono[OF rec]) (use spost_pre[OF i2 ch12] o os in auto)
        next
          case (Returned r)
          with bpost_spost[OF bp[unfolded Returned] ch1] show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma SS_Suc:
  assumes "SS P n" "SB P n" "SE P n" "SES P n" "SR P n" "SP P n" "SD P n"
  shows "SS P (Suc n)"
  unfolding SS_def
proof (intro allI impI)
  fix C \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>
  assume CP: "c_prog C = P" and inv: "inv P C \<Gamma> \<sigma> env st" and chk: "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  show "spec (exec P (Suc n) (c_ret C) env st s) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
  proof (cases s)
    case SPass
    with chk inv show ?thesis by (auto simp: spost_normal chg_init)
  next
    case (SSeq a b) show ?thesis unfolding SSeq by (rule SS_seq[OF assms(1) CP inv], rule chk[unfolded SSeq])
  next
    case (SVar x T eo) show ?thesis unfolding SVar by (rule SS_var[OF assms(3) CP inv], rule chk[unfolded SVar])
  next
    case (SRef x e) show ?thesis unfolding SRef by (rule SS_ref[OF assms(5) CP inv], rule chk[unfolded SRef])
  next
    case (SAssign p e) show ?thesis unfolding SAssign by (rule SS_assign[OF assms(3,6,7) CP inv], rule chk[unfolded SAssign])
  next
    case (SExpr e) show ?thesis unfolding SExpr by (rule SS_expr[OF assms(3,7) CP inv], rule chk[unfolded SExpr])
  next
    case (SPrint es) show ?thesis unfolding SPrint by (rule SS_print[OF assms(4) CP inv], rule chk[unfolded SPrint])
  next
    case (SIf c a b) show ?thesis unfolding SIf by (rule SS_if[OF assms(3,2) CP inv], rule chk[unfolded SIf])
  next
    case (SWhile c b) show ?thesis unfolding SWhile by (rule SS_while[OF assms(3,2,1) CP inv], rule chk[unfolded SWhile])
  next
    case (SReturn eo) show ?thesis unfolding SReturn by (rule SS_return[OF assms(3,5) CP inv], rule chk[unfolded SReturn])
  next
    case (SDrop p) show ?thesis unfolding SDrop by (rule SS_drop[OF assms(7) inv], rule chk[unfolded SDrop])
  qed
qed



section \<open>Soundness\<close>

text \<open>All thirteen statements hold at every fuel, by induction on the fuel.\<close>

lemma sound_all: "sound_all_at P n"
proof (induction n)
  case 0
  show ?case by (rule sound_all_at_0)
next
  case (Suc n)
  then have SP: "SP P n" and SE: "SE P n" and SES: "SES P n" and SR: "SR P n" and SA: "SA P n"
    and SCF: "SCF P n" and SCM: "SCM P n" and SI: "SI P n" and SS: "SS P n" and SB: "SB P n"
    and SD: "SD P n" and SDS: "SDS P n" and SC: "SC P n"
    by (simp_all add: sound_all_at_def)
  show ?case unfolding sound_all_at_def
    using SP_Suc[OF SP SE] SE_Suc[OF SP SE SES SCF SCM] SES_Suc[OF SE SES] SR_Suc[OF SP SCF]
      SA_Suc[OF SE SR SA] SCF_Suc[OF SA SI SES] SCM_Suc[OF SP SE SA SI] SI_Suc[OF SS SC]
      SS_Suc[OF SS SB SE SES SR SP SD] SB_Suc[OF SS SC] SD_Suc[OF SS SC SDS] SDS_Suc[OF SD SDS]
      SC_Suc[OF SD SC]
    by blast
qed

text \<open>
  The entry of @{text "main"}: no parameters, an empty environment and an
  empty heap satisfy the callee precondition.
\<close>

lemma inv_empty: "inv P C [] (astate0 []) [] init_state"
  by (simp add: inv_def init_state_def one_out_def excl_def)

lemma main_ok:
  assumes fd: "find_fun P ''main'' = Some fd"
  shows "callee_ok P \<lparr>c_prog = P, c_ret = fd_ret fd, c_fields = []\<rparr> fd [] init_state"
proof -
  have np: "fd_params fd = []"
    using wf fd by (auto simp: wf_prog_def check_prog_def split: if_splits)
  have cb: "chk_body P (fd_ret fd) [] (fd_params fd) (fd_body fd) = Good ()" using wf_fun[OF wf fd] .
  have rr: "case fd_ret fd of RRef ns _ \<Rightarrow> \<forall>z \<in> set ns. \<exists>q. map_of [] z = Some (Bor q) | _ \<Rightarrow> True"
    using chk_body_facts(4)[OF cb] np by (auto split: ret.splits simp: list_all_iff)
  show ?thesis
    unfolding callee_ok_def using cb rr inv_empty np by simp
qed

end

text \<open>
  \<^bold>\<open>The main theorem.\<close> Running a well-formed program never fails with an
  error other than an out-of-bounds list access, whatever the fuel. In
  particular no ownership error (use of a moved or uninitialized value, of
  a dangling or invalidated reference, a copy of a non-copyable value, or a
  return before @{text "out self"} is initialized) and no type or arity
  error occurs at run time. Running out of fuel is not an error.
\<close>

theorem run_safe:
  assumes "wf_prog P"
  shows "safe (run fuel P)"
proof (cases "find_fun P ''main''")
  case None
  with assms have False by (auto simp: wf_prog_def check_prog_def)
  then show ?thesis ..
next
  case (Some fd)
  have "SI P fuel" using sound_all[OF assms, of fuel] by (simp add: sound_all_at_def)
  then have "spec (invoke P fuel init_state fd []) (invoke_post P fd [] init_state)"
    using main_ok[OF assms Some] unfolding SI_def by blast
  then have "spec (invoke P fuel init_state fd []) (\<lambda>_. spec (Ok ()) (\<lambda>_. True))"
    by (rule spec_mono) simp
  then have "spec (run fuel P) (\<lambda>_. True)"
    unfolding run_def Some option.case by (intro spec_bind) (auto simp: spec_def safe_def split: prod.splits)
  then show ?thesis by (simp add: spec_def)
qed

corollary run_no_ownership_error:
  assumes "wf_prog P" and "run fuel P = Err e"
  shows "e = ErrBounds" and "\<not> ownership_err e"
  using run_safe[OF assms(1), of fuel] assms(2) by (auto simp: safe_def ownership_err_def)

text \<open>The same holds for every statement and block of a well-formed program.\<close>

theorem stmt_sound_calls:
  assumes "wf_prog P" "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  shows "spec (exec P n (c_ret C) env st s) (spost P C \<Gamma> \<Gamma>' o\<sigma> env st)"
  using sound_all[OF assms(1), of n] assms(2-) unfolding sound_all_at_def SS_def by blast

theorem expr_sound_calls:
  assumes "wf_prog P" "c_prog C = P" "inv P C \<Gamma> \<sigma> env st"
    and "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'" "etype P \<Gamma> e = Good T"
  shows "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v)"
proof -
  have "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
      chg \<Gamma> env (mroots P \<Gamma> e) st st' \<and> vt P T v)"
    using sound_all[OF assms(1), of n] assms(2-) unfolding sound_all_at_def SE_def by blast
  then show ?thesis by (rule spec_mono) auto
qed


end
