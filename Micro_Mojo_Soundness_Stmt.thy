(*
  Micro_Mojo_Soundness_Stmt.thy

  Soundness of the micro-Mojo checker for statements within one frame.
*)

theory Micro_Mojo_Soundness_Stmt
  imports Micro_Mojo_Soundness
begin

section \<open>Overview\<close>

text \<open>
  This theory extends the soundness proof from expressions to statements
  without calls. Destruction is the one place where a statement runs other
  code: @{text "drop_path"} runs @{text "__deinit__"} bodies, which are
  calls. Here it is specified by a hypothesis, @{text "sound_drop"}: dropping
  a well-typed value at a path does not go wrong, changes the heap only
  below that path (and in fresh roots), and leaves @{text "VUndef"} there.
  The part on calls will prove the hypothesis, by the same induction on
  the fuel.
\<close>

section \<open>Values along paths\<close>

lemma walk_typed:
  "vt P T v \<Longrightarrow> sty P T ss = Some U \<Longrightarrow> walk v ss = Ok u \<Longrightarrow> vt P U u"
proof (induction ss arbitrary: T v)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases s)
    case (Fld f)
    with Cons.prems obtain S where T: "T = TStruct S" by (cases T) auto
    with Cons.prems Fld obtain U1 where f: "field_ty P S f = Good U1" "sty P U1 ss = Some U"
      by (auto split: ck.splits)
    from vt_field[OF Cons.prems(1)[unfolded T] f(1)] obtain u1 where
      u1: "walk v [Fld f] = Ok u1" "vt P U1 u1" by blast
    from Cons.prems(3) Fld u1(1) have "walk u1 ss = Ok u"
      using walk_append[of v "[Fld f]" ss] by simp
    with Cons.IH[OF u1(2) f(2)] show ?thesis by simp
  next
    case (Idx i g)
    with Cons.prems obtain U1 where T: "T = TList U1" "sty P U1 ss = Some U" by (cases T) auto
    with Cons.prems(1) obtain g' vs where v: "v = VList g' vs" "\<forall>u \<in> set vs. vt P U1 u"
      by (cases v) auto
    with Cons.prems(3) Idx have "i < length vs" "walk (vs ! i) ss = Ok u"
      by (auto split: if_splits)
    with v Cons.IH[OF _ T(2)] show ?thesis by (meson nth_mem)
  qed
qed

lemma walk_fields_typed:
  "vt P T v \<Longrightarrow> sty P T ss = Some U \<Longrightarrow> \<not> has_idx ss \<Longrightarrow> \<exists>u. walk v ss = Ok u \<and> vt P U u"
proof (induction ss arbitrary: T v)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  from Cons.prems(3) obtain f where s: "s = Fld f" and nss: "\<not> has_idx ss"
    by (cases s) (auto simp: has_idx_def)
  with Cons.prems obtain S where T: "T = TStruct S" by (cases T) auto
  with Cons.prems s obtain U1 where f: "field_ty P S f = Good U1" "sty P U1 ss = Some U"
    by (auto split: ck.splits)
  from vt_field[OF Cons.prems(1)[unfolded T] f(1)] obtain u1 where
    u1: "walk v [Fld f] = Ok u1" "vt P U1 u1" by blast
  from Cons.IH[OF u1(2) f(2) nss] obtain u where "walk u1 ss = Ok u" "vt P U u" by blast
  with u1 s show ?case using walk_append[of v "[Fld f]" ss] by simp
qed

text \<open>Updating one field of a field list.\<close>

definition upd_field :: "fname \<Rightarrow> val \<Rightarrow> (fname \<times> val) list \<Rightarrow> (fname \<times> val) list" where
  "upd_field f x fs = map (\<lambda>(f', u). if f' = f then (f', x) else (f', u)) fs"

lemma map_of_upd_field:
  "map_of (upd_field f x fs) g = (case map_of fs g of None \<Rightarrow> None | Some u \<Rightarrow> Some (if g = f then x else u))"
  by (induction fs) (auto simp: upd_field_def)

lemma map_fst_upd_field [simp]: "map fst (upd_field f x fs) = map fst fs"
  by (induction fs) (auto simp: upd_field_def)

lemma set_upd_field: "(g, u) \<in> set (upd_field f x fs) \<Longrightarrow> (g = f \<and> u = x) \<or> (g \<noteq> f \<and> (g, u) \<in> set fs)"
  by (induction fs) (auto simp: upd_field_def split: if_splits)

lemma update_at_Fld:
  "update_at (VStruct S fs) (Fld f # ss) w =
     (case map_of fs f of None \<Rightarrow> Err (ErrType ''no such field'')
      | Some v \<Rightarrow> bind_res (update_at v ss w) (\<lambda>v'. Ok (VStruct S (upd_field f v' fs))))"
  unfolding upd_field_def by simp

declare update_at.simps(2) [simp del]
declare update_at_Fld [simp]

lemma walk_update_same: "update_at w ss v = Ok w' \<Longrightarrow> walk w' ss = Ok v"
  by (induction w ss v arbitrary: w' rule: update_at.induct)
     (auto simp: bind_res_Ok_iff map_of_upd_field split: option.splits if_splits)

lemma walk_update_below: "update_at w ss v = Ok w' \<Longrightarrow> walk w' (ss @ rs) = walk v rs"
  by (simp add: walk_append walk_update_same)

lemma update_typed:
  "vt P T w \<Longrightarrow> sty P T ss = Some U \<Longrightarrow> walk w ss = Ok u \<Longrightarrow> vt P U v \<Longrightarrow>
   \<exists>w'. update_at w ss v = Ok w' \<and> vt P T w'"
proof (induction ss arbitrary: T w u)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases s)
    case (Fld f)
    with Cons.prems obtain S where T: "T = TStruct S" by (cases T) auto
    with Cons.prems Fld obtain U1 where f: "field_ty P S f = Good U1" "sty P U1 ss = Some U"
      by (auto split: ck.splits)
    from Cons.prems(1) T obtain fs sd where w: "w = VStruct S fs" and sd: "find_struct P S = Some sd"
      and names: "map fst fs = map fst (sd_fields sd)"
      and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> vt P U u"
      by (cases w) auto
    from f(1) sd have U1: "map_of (sd_fields sd) f = Some U1"
      by (auto simp: field_ty_def split: option.splits)
    from Cons.prems(3) w Fld obtain u1 where u1: "map_of fs f = Some u1" "walk u1 ss = Ok u"
      by (auto split: option.splits)
    from map_of_SomeD[OF u1(1)] fs U1 have vt1: "vt P U1 u1" by fastforce
    from Cons.IH[OF vt1 f(2) u1(2) Cons.prems(4)] obtain u1' where
      u1': "update_at u1 ss v = Ok u1'" "vt P U1 u1'" by blast
    have "vt P T (VStruct S (upd_field f u1' fs))"
      using T sd names fs U1 u1'(2) by (auto dest!: set_upd_field)
    with w Fld u1(1) u1'(1) show ?thesis by simp
  next
    case (Idx i g)
    with Cons.prems obtain U1 where T: "T = TList U1" "sty P U1 ss = Some U" by (cases T) auto
    with Cons.prems(1) obtain g' vs where w: "w = VList g' vs" "\<forall>u \<in> set vs. vt P U1 u"
      by (cases w) auto
    with Cons.prems(3) Idx have gi: "g' = g" "i < length vs" "walk (vs ! i) ss = Ok u"
      by (auto split: if_splits)
    from Cons.IH[OF _ T(2) gi(3) Cons.prems(4)] w gi(2) obtain v' where
      v': "update_at (vs ! i) ss v = Ok v'" "vt P U1 v'" by (meson nth_mem)
    have "vt P T (VList g (vs[i := v']))"
      using T w v'(2) by (auto dest: set_update_subset_insert[THEN subsetD])
    with w gi Idx v'(1) show ?thesis by simp
  qed
qed

text \<open>
  Updating a value at a path does not change what is found at a path that
  neither extends it nor is extended by it: the generations of lists along
  the updated path are kept.
\<close>

lemma walk_update_disjoint:
  "update_at w ss v = Ok w' \<Longrightarrow> \<not> (\<exists>us. ts = ss @ us) \<Longrightarrow> \<not> (\<exists>us. ss = ts @ us) \<Longrightarrow>
   walk w' ts = walk w ts"
proof (induction w ss v arbitrary: w' ts rule: update_at.induct)
  case (2 S fs f ss w)
  then obtain u u' where u: "map_of fs f = Some u" "update_at u ss w = Ok u'"
    and w': "w' = VStruct S (upd_field f u' fs)"
    by (auto simp: bind_res_Ok_iff split: option.splits)
  show ?case
  proof (cases ts)
    case Nil
    with "2.prems" show ?thesis by auto
  next
    case (Cons t ts')
    show ?thesis
    proof (cases "t = Fld f")
      case True
      with Cons "2.prems" have "\<not> (\<exists>us. ts' = ss @ us)" "\<not> (\<exists>us. ss = ts' @ us)" by auto
      with "2.IH"[OF u(1) u(2)] u w' Cons True show ?thesis
        by (simp add: map_of_upd_field)
    next
      case False
      with w' Cons u show ?thesis
        by (cases t) (auto simp: map_of_upd_field split: option.splits)
    qed
  qed
next
  case (3 g vs i g' ss w)
  then have gi: "g = g'" "i < length vs" by (auto split: if_splits)
  with "3.prems" obtain v' where v': "update_at (vs ! i) ss w = Ok v'"
    and w': "w' = VList g (vs[i := v'])"
    by (auto simp: bind_res_Ok_iff)
  show ?case
  proof (cases ts)
    case Nil
    with "3.prems" show ?thesis by auto
  next
    case (Cons t ts')
    show ?thesis
    proof (cases "t = Idx i g'")
      case True
      with Cons "3.prems" have "\<not> (\<exists>us. ts' = ss @ us)" "\<not> (\<exists>us. ss = ts' @ us)" by auto
      with "3.IH"[OF _ _ v'] gi w' Cons True show ?thesis by simp
    next
      case False
      with w' Cons gi show ?thesis
        by (cases t) auto
    qed
  qed
qed auto

lemma walk_update_prefix:
  "update_at w (ts @ rs) v = Ok w' \<Longrightarrow> walk w ts = Ok u \<Longrightarrow>
   \<exists>u'. walk w' ts = Ok u' \<and> update_at u rs v = Ok u'"
proof (induction ts arbitrary: w w')
  case Nil
  then show ?case by (simp add: walk_update_same)
next
  case (Cons t ts)
  show ?case
  proof (cases t)
    case (Fld f)
    with Cons.prems obtain S fs u1 u1' where w: "w = VStruct S fs" "map_of fs f = Some u1"
      and up: "update_at u1 (ts @ rs) v = Ok u1'" and w': "w' = VStruct S (upd_field f u1' fs)"
      and wk: "walk u1 ts = Ok u"
      by (cases w) (auto simp: bind_res_Ok_iff split: option.splits if_splits)
    from Cons.IH[OF up wk] w w' Fld show ?thesis by (simp add: map_of_upd_field)
  next
    case (Idx i g)
    with Cons.prems obtain vs u1' where w: "w = VList g vs" "i < length vs"
      and up: "update_at (vs ! i) (ts @ rs) v = Ok u1'" and w': "w' = VList g (vs[i := u1'])"
      and wk: "walk (vs ! i) ts = Ok u"
      by (cases w) (auto simp: bind_res_Ok_iff split: if_splits)
    from Cons.IH[OF up wk] w w' Idx show ?thesis by simp
  qed
qed

lemma update_walk_ok: "update_at w ss v = Ok w' \<Longrightarrow> \<exists>u. walk w ss = Ok u"
  by (induction w ss v arbitrary: w' rule: update_at.induct)
     (auto simp: bind_res_Ok_iff split: option.splits if_splits)

text \<open>Updating twice at the same path is updating once, and the second update succeeds.\<close>

lemma update_again:
  "update_at w ss x = Ok w1 \<Longrightarrow> \<exists>w2. update_at w1 ss y = Ok w2 \<and> update_at w ss y = Ok w2"
proof (induction w ss x arbitrary: w1 rule: update_at.induct)
  case (2 S fs f ss w)
  then obtain u u' where u: "map_of fs f = Some u" "update_at u ss w = Ok u'"
    and w1: "w1 = VStruct S (upd_field f u' fs)"
    by (auto simp: bind_res_Ok_iff split: option.splits)
  from "2.IH"[OF u] obtain u2 where "update_at u' ss y = Ok u2" "update_at u ss y = Ok u2" by blast
  moreover have "upd_field f u2 (upd_field f u' fs) = upd_field f u2 fs"
    by (induction fs) (auto simp: upd_field_def)
  ultimately show ?case using u w1 by (simp add: map_of_upd_field)
next
  case (3 g vs i g' ss w)
  then obtain v' where gi: "g = g'" "i < length vs" and v': "update_at (vs ! i) ss w = Ok v'"
    and w1: "w1 = VList g (vs[i := v'])"
    by (auto simp: bind_res_Ok_iff split: if_splits)
  from "3.IH"[OF _ _ v'] gi obtain u2 where "update_at v' ss y = Ok u2" "update_at (vs ! i) ss y = Ok u2"
    by auto
  with gi w1 show ?case by simp
qed auto

lemma sty_trivial: "trivial_ty T \<Longrightarrow> sty P T rs = Some U \<Longrightarrow> rs = [] \<and> U = T"
  by (induction P T rs rule: sty.induct) auto

lemma refs_into_I:
  "map_of \<Gamma> y = Some (KRef T og I) \<Longrightarrow> z \<in> I \<Longrightarrow> z \<in> R \<Longrightarrow> y \<in> refs_into \<Gamma> R"
  by (force simp: refs_into_def dest: map_of_SomeD)

lemma append_prefix_cases:
  "xs @ ys = zs @ ws \<Longrightarrow> (\<exists>us. zs = xs @ us) \<or> (\<exists>us. xs = zs @ us)"
  by (auto simp: append_eq_append_conv2)

lemma below_trans: "below a b \<Longrightarrow> below b c \<Longrightarrow> below a c"
  by (auto simp: below_def)

text \<open>Paths below two non-overlapping locations do not overlap.\<close>

lemma below_disjoint:
  assumes "below a la" "below b lb" "\<not> overlaps la lb"
  shows "\<not> overlaps a b"
proof
  assume "overlaps a b"
  then have "below a b \<or> below b a" by (simp add: overlaps_def)
  then show False
  proof
    assume "below a b"
    from this assms(2) have "below a lb" by (rule below_trans)
    with assms(1) assms(3) show False
      by (auto simp: below_def overlaps_def append_eq_append_conv2; metis)
  next
    assume "below b a"
    from this assms(1) have "below b la" by (rule below_trans)
    with assms(2) assms(3) show False
      by (auto simp: below_def overlaps_def append_eq_append_conv2; metis)
  qed
qed

lemma below_refl [simp]: "below a a"
  by (auto simp: below_def)

section \<open>Writing preserves the invariant\<close>

lemma out_val_fields_eq: "a_fields \<sigma>' = a_fields \<sigma> \<Longrightarrow> out_val P C \<sigma>' T v = out_val P C \<sigma> T v"
  by (simp add: out_val_def)

text \<open>
  The central lemma for assignment. A well-typed value @{text "v"} of type
  @{text "T"} is written at a path @{text "q"} below the location of a
  writable variable @{text "z"}, the heap changes only at that root (and in
  fresh roots), and @{text "z"} itself satisfies its new binding condition
  (which the caller proves: it depends on whether @{text "z"} is owned,
  borrowed or @{text "out self"}). Then the invariant holds again, provided
  the references into the interior of the written place are invalidated
  when @{text "T"} is not trivial (@{text "R"} is the origin of the place).

  Every other non-reference variable lives elsewhere, by exclusivity. A
  reference with another base is unaffected for the same reason. A
  reference with base @{text "z"} either points at or below @{text "q"}, and then
  reaches its value through fields only (or is invalidated), or points
  above @{text "q"}, where the value changed only inside, keeping its type,
  or points elsewhere.
\<close>

lemma inv_write:
  assumes inv: "inv P C \<Gamma> \<sigma> env st"
    and z: "map_of \<Gamma> z = Some kz" "writable kz" "map_of env z = Some bz"
    and q: "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T" "vt P T v"
    and w: "heap st (fst q) = Some w" "update_at w (snd q) v = Ok w'"
    and st': "heap st' (fst q) = Some w'" "\<forall>r. r < nroot st \<longrightarrow> r \<noteq> fst q \<longrightarrow> heap st' r = heap st r"
       "nroot st \<le> nroot st'" "\<forall>r. nroot st' \<le> r \<longrightarrow> heap st' r = None"
    and \<sigma>1: "a_inval \<sigma>1 = a_inval \<sigma>" "\<forall>y. y \<noteq> z \<longrightarrow> (y \<in> a_init \<sigma>1 \<longleftrightarrow> y \<in> a_init \<sigma>)"
       "a_fields \<sigma>1 = a_fields \<sigma> \<or> (\<exists>U. kz = KBorrow Out U)"
       "\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>1 \<longrightarrow> z \<notin> a_init \<sigma> \<longrightarrow> ss = []"
    and zok: "binding_ok P C \<Gamma> \<sigma>1 env st' z kz bz"
    and R: "z \<in> R"
  shows "inv P C \<Gamma> (if trivial_ty T then \<sigma>1 else \<sigma>1\<lparr>a_inval := a_inval \<sigma>1 \<union> refs_into \<Gamma> R\<rparr>) env st'"
proof -
  define \<sigma>' where "\<sigma>' = (if trivial_ty T then \<sigma>1 else \<sigma>1\<lparr>a_inval := a_inval \<sigma>1 \<union> refs_into \<Gamma> R\<rparr>)"
  have \<sigma>'1: "a_init \<sigma>' = a_init \<sigma>1" "a_fields \<sigma>' = a_fields \<sigma>1" "a_inval \<sigma>1 \<subseteq> a_inval \<sigma>'"
    by (auto simp: \<sigma>'_def)
  have inval: "y \<notin> a_inval \<sigma>' \<Longrightarrow> \<not> trivial_ty T \<Longrightarrow> y \<notin> refs_into \<Gamma> R" for y
    by (simp add: \<sigma>'_def)
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have bounds: "\<And>x b. map_of env x = Some b \<Longrightarrow> fst (bpath b) < nroot st"
    using inv by (simp add: inv_def)
  have oo: "one_out \<Gamma>" using inv by (simp add: inv_def)
  have qz: "below q (bpath bz)" using q(1) by simp
  text \<open>Paths that do not overlap the written one keep their values.\<close>
  have unch: "get st' p0 = get st p0" if "fst p0 < nroot st" "\<not> overlaps p0 q" for p0
  proof (cases "fst p0 = fst q")
    case False
    with that st'(2) show ?thesis by (intro get_root_cong) simp
  next
    case True
    with that(2) have "\<not> (\<exists>us. snd p0 = snd q @ us)" "\<not> (\<exists>us. snd q = snd p0 @ us)"
      by (auto simp: overlaps_def below_def)
    from walk_update_disjoint[OF w(2) this] True w st'(1) show ?thesis
      by (simp add: get_def)
  qed
  text \<open>A non-reference variable other than @{text "z"} lies elsewhere.\<close>
  have elsewhere: "\<not> overlaps a q"
    if "map_of \<Gamma> y = Some ky" "\<not> is_ref ky" "map_of env y = Some yb" "y \<noteq> z" "below a (bpath yb)"
    for y ky yb a
  proof -
    have "\<not> overlaps (bpath bz) (bpath yb)" using excl_D[OF excl z that(1-4)] .
    then have "\<not> overlaps (bpath yb) (bpath bz)" by (auto simp: overlaps_def)
    from below_disjoint[OF that(5) qz this] show ?thesis .
  qed
  have bind: "\<exists>b. map_of env y = Some b \<and> binding_ok P C \<Gamma> \<sigma>' env st' y k b"
    if yk: "map_of \<Gamma> y = Some k" for y k
  proof -
    from inv_binding[OF inv yk] obtain b where b: "map_of env y = Some b"
      "binding_ok P C \<Gamma> \<sigma> env st y k b" by blast
    show ?thesis
    proof (cases "y = z")
      case True
      have "binding_ok P C \<Gamma> \<sigma>' env st' z kz bz"
        using zok z(2) \<sigma>'1 by (cases kz) (auto simp: out_val_fields_eq[OF \<sigma>'1(2)])
      then show ?thesis using True z(1,3) yk b(1) by auto
    next
      case False
      show ?thesis
      proof (cases k)
        case (KOwned U)
        from b(2) KOwned obtain r v0 where bo: "b = Own r" "heap st r = Some v0"
          "if y \<in> a_init \<sigma> then vt P U v0 else wt_opt P U v0" by auto
        have "\<not> overlaps (r, []) q" using elsewhere[OF yk _ b(1) False] KOwned bo by simp
        then have "r \<noteq> fst q" by (auto simp: overlaps_def below_def)
        moreover have "r < nroot st" using bounds[OF b(1)] bo by simp
        ultimately have "heap st' r = heap st r" using st'(2) by simp
        with bo b(1) KOwned False \<sigma>1(2) \<sigma>'1 show ?thesis by simp
      next
        case (KBorrow c U)
        have "get st' (bpath b) = get st (bpath b)"
          using unch bounds[OF b(1)] elsewhere[OF yk _ b(1) False] KBorrow by simp
        moreover have "a_fields \<sigma>' = a_fields \<sigma> \<or> c \<noteq> Out"
          using \<sigma>1(3) \<sigma>'1 oo z yk KBorrow False by (auto simp: one_out_def)
        ultimately show ?thesis using b KBorrow
          by (auto simp: out_val_def split: if_splits)
      next
        case (KRef Ty og I)
        with b obtain qy x kx bx ssy where rf: "b = Bor qy" "x \<in> og" "map_of \<Gamma> x = Some kx"
          "\<not> is_ref kx" "map_of env x = Some bx" "qy = pext (bpath bx) ssy"
          "sty P (kind_ty kx) ssy = Some Ty" "has_idx ssy \<longrightarrow> x \<in> I"
          "y \<notin> a_inval \<sigma> \<and> (\<forall>U. kx = KOwned U \<longrightarrow> x \<in> a_init \<sigma>) \<longrightarrow>
             (\<exists>v. get st qy = Ok v \<and> vt P Ty v)"
          by (simp only: binding_ok.simps) blast
        have live: "\<exists>v. get st' qy = Ok v \<and> vt P Ty v"
          if l: "y \<notin> a_inval \<sigma>' \<and> (\<forall>U. kx = KOwned U \<longrightarrow> x \<in> a_init \<sigma>')"
        proof (cases "x = z")
          case False
          with l \<sigma>1 \<sigma>'1 have old: "\<exists>v. get st qy = Ok v \<and> vt P Ty v" using rf(9) by auto
          have "get st' qy = get st qy"
            using unch bounds[OF rf(5)] elsewhere[OF rf(3,4,5) False] rf(6) by simp
          with old show ?thesis by simp
        next
          case True
          with rf z have bx: "bx = bz" "kx = kz" by simp_all
          have pre: "snd qy = snd (bpath bz) @ ssy" "snd q = snd (bpath bz) @ ss"
            "fst qy = fst q"
            using rf(6) q(1) bx by (simp_all add: pext_def)
          show ?thesis
          proof (cases "\<exists>rs. ssy = ss @ rs")
            case True
            then obtain rs where rs: "ssy = ss @ rs" by blast
            from rf(7) bx q(2) rs have trs: "sty P T rs = Some Ty" by (simp add: sty_append)
            have "\<exists>u. walk v rs = Ok u \<and> vt P Ty u"
            proof (cases "trivial_ty T")
              case True
              with sty_trivial[OF True trs] q(3) show ?thesis by simp
            next
              case False
              with l inval have "y \<notin> refs_into \<Gamma> R" by blast
              with refs_into_I[OF yk[unfolded KRef]] R rf(8) \<open>x = z\<close> have "\<not> has_idx ssy" by blast
              with rs have "\<not> has_idx rs" by simp
              from walk_fields_typed[OF q(3) trs this] show ?thesis .
            qed
            moreover have "get st' qy = walk v rs"
              using pre rs st'(1) walk_update_below[OF w(2)] by (simp add: get_def)
            ultimately show ?thesis by simp
          next
            case nb: False
            have oldl: "y \<notin> a_inval \<sigma> \<and> (\<forall>U. kx = KOwned U \<longrightarrow> x \<in> a_init \<sigma>)"
            proof -
              have "y \<notin> a_inval \<sigma>" using l \<sigma>1(1) \<sigma>'1 by auto
              moreover have "x \<in> a_init \<sigma>" if "kx = KOwned U" for U
              proof (rule ccontr)
                assume "x \<notin> a_init \<sigma>"
                with l that \<sigma>'1 have "z \<in> a_init \<sigma>1" "z \<notin> a_init \<sigma>" using True by auto
                with \<sigma>1(4) that bx have "ss = []" by simp
                with nb show False by simp
              qed
              ultimately show ?thesis by blast
            qed
            with rf(9) obtain u where u: "get st qy = Ok u" "vt P Ty u" by blast
            show ?thesis
            proof (cases "\<exists>rs. ss = ssy @ rs")
              case True
              then obtain rs where rs: "ss = ssy @ rs" by blast
              from rf(7) bx q(2) rs have trs: "sty P Ty rs = Some T" by (simp add: sty_append)
              have wu: "walk w (snd qy) = Ok u" using u(1) pre w(1) by (simp add: get_def)
              have "update_at w (snd qy @ rs) v = Ok w'" using w(2) pre rs by simp
              from walk_update_prefix[OF this wu] obtain u' where
                u': "walk w' (snd qy) = Ok u'" "update_at u rs v = Ok u'" by blast
              from update_walk_ok[OF u'(2)] obtain ur where "walk u rs = Ok ur" by blast
              from update_typed[OF u(2) trs this q(3)] u'(2) have "vt P Ty u'" by auto
              with u' pre st'(1) show ?thesis by (simp add: get_def)
            next
              case False
              have "\<not> overlaps qy q"
                using nb False pre by (auto simp: overlaps_def below_def)
              then have "get st' qy = get st qy"
                using unch bounds[OF rf(5)] rf(6) by simp
              with u show ?thesis by simp
            qed
          qed
        qed
        have "binding_ok P C \<Gamma> \<sigma>' env st' y k b"
          unfolding KRef binding_ok.simps using rf(1-8) live by blast
        with b(1) show ?thesis by blast
      qed
    qed
  qed
  have "inv P C \<Gamma> \<sigma>' env st'"
    unfolding inv_def using inv bind st' bounds by (fastforce simp: inv_def)
  then show ?thesis by (simp add: \<sigma>'_def)
qed

section \<open>Other changes of state\<close>

definition heap_fresh :: "state \<Rightarrow> bool" where
  "heap_fresh st \<longleftrightarrow> (\<forall>r. nroot st \<le> r \<longrightarrow> heap st r = None)"

lemma inv_heap_fresh: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> heap_fresh st"
  by (simp add: inv_def heap_fresh_def)

lemma inv_bounds: "inv P C \<Gamma> \<sigma> env st \<Longrightarrow> map_of env x = Some b \<Longrightarrow> fst (bpath b) < nroot st"
  by (simp add: inv_def)

text \<open>
  The invariant survives any change of the heap that keeps the roots
  below the old @{text "nroot"}, such as allocating and freeing fresh
  roots, printing, or running code that only touches fresh memory.
\<close>

lemma inv_heap_frame:
  assumes "inv P C \<Gamma> \<sigma> env st" "\<forall>r. r < nroot st \<longrightarrow> heap st' r = heap st r"
    "nroot st \<le> nroot st'" "heap_fresh st'"
  shows "inv P C \<Gamma> \<sigma> env st'"
proof -
  have get: "get st' p0 = get st p0" if "fst p0 < nroot st" for p0
    using that assms(2) by (intro get_root_cong) simp
  have "binding_ok P C \<Gamma> \<sigma> env st' x k b" if "map_of \<Gamma> x = Some k" "map_of env x = Some b"
    "binding_ok P C \<Gamma> \<sigma> env st x k b" for x k b
  proof (cases k)
    case (KOwned T)
    with that assms(2) inv_bounds[OF assms(1) that(2)] show ?thesis by (auto split: if_splits)
  next
    case (KBorrow c T)
    with that get[of "bpath b"] inv_bounds[OF assms(1) that(2)] show ?thesis by simp
  next
    case (KRef T og I)
    with that(3) obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
      "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    have "get st' q = get st q" using get inv_bounds[OF assms(1) rf(5)] rf(6) by simp
    with rf have "binding_ok P C \<Gamma> \<sigma> env st' x (KRef T og I) b"
      unfolding binding_ok.simps by (metis (no_types, lifting))
    with KRef show ?thesis by simp
  qed
  with assms show ?thesis
    by (fastforce simp: inv_def heap_fresh_def dest: less_le_trans)
qed

text \<open>
  The invariant survives weakening the abstract state: fewer initialized
  variables and fields, more invalidated references. Joins at the end of
  an @{text "if"} and the loop fixpoint are such weakenings.
\<close>

definition weaker :: "astate \<Rightarrow> astate \<Rightarrow> bool" where
  "weaker \<sigma>' \<sigma> \<longleftrightarrow> a_init \<sigma>' \<subseteq> a_init \<sigma> \<and> a_inval \<sigma> \<subseteq> a_inval \<sigma>' \<and> a_fields \<sigma>' \<subseteq> a_fields \<sigma>"

lemma weaker_refl [simp]: "weaker \<sigma> \<sigma>"
  by (simp add: weaker_def)

lemma weaker_trans: "weaker \<sigma>2 \<sigma>1 \<Longrightarrow> weaker \<sigma>1 \<sigma> \<Longrightarrow> weaker \<sigma>2 \<sigma>"
  by (auto simp: weaker_def)

lemma weaker_join: "weaker (join \<sigma>a \<sigma>b) \<sigma>a" "weaker (join \<sigma>a \<sigma>b) \<sigma>b"
  by (auto simp: weaker_def join_def)

lemma out_val_weaker:
  "out_val P C \<sigma> T v \<Longrightarrow> a_fields \<sigma>' \<subseteq> a_fields \<sigma> \<Longrightarrow> out_val P C \<sigma>' T v"
  by (auto simp: out_val_def split: if_splits) blast

lemma inv_weaken:
  assumes "inv P C \<Gamma> \<sigma> env st" "weaker \<sigma>' \<sigma>"
  shows "inv P C \<Gamma> \<sigma>' env st"
proof -
  have "binding_ok P C \<Gamma> \<sigma>' env st x k b" if "binding_ok P C \<Gamma> \<sigma> env st x k b" for x k b
  proof (cases k)
    case (KOwned T)
    with that assms(2) show ?thesis by (auto simp: weaker_def wt_opt_def split: if_splits)
  next
    case (KBorrow c T)
    with that assms(2) show ?thesis
      by (auto simp: weaker_def intro: out_val_weaker split: if_splits)
  next
    case (KRef T og I)
    from that KRef obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
      "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    have "x \<notin> a_inval \<sigma>' \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>') \<longrightarrow>
          x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>)"
      using assms(2) by (auto simp: weaker_def)
    with rf KRef show ?thesis by (simp only: binding_ok.simps) blast
  qed
  with assms(1) show ?thesis by (fastforce simp: inv_def)
qed

section \<open>Destruction\<close>

text \<open>
  The specification of @{text "drop_path"}, assumed here and to be proved
  with calls: dropping a well-typed (or uninitialized) value at a path
  leaves @{text "VUndef"} there, changes no other root below
  @{text "nroot"}, and keeps the heap fresh.
\<close>

definition drop_post :: "state \<Rightarrow> path \<Rightarrow> state \<Rightarrow> bool" where
  "drop_post st q st' \<longleftrightarrow> nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
     (\<forall>r. r < nroot st \<longrightarrow> r \<noteq> fst q \<longrightarrow> heap st' r = heap st r) \<and>
     (\<exists>w w'. heap st (fst q) = Some w \<and> update_at w (snd q) VUndef = Ok w' \<and>
             heap st' (fst q) = Some w')"

definition sound_drop :: "prog \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_drop P n \<longleftrightarrow> (\<forall>st q v T. get st q = Ok v \<longrightarrow> wt_opt P T v \<longrightarrow> heap_fresh st \<longrightarrow>
     spec (drop_path P n st q) (drop_post st q))"

definition owned_roots :: "env \<Rightarrow> nat set" where
  "owned_roots env = {r. \<exists>x. (x, Own r) \<in> set env}"

lemma owned_roots_simps [simp]:
  "owned_roots [] = {}"
  "owned_roots ((x, Own r) # env) = insert r (owned_roots env)"
  "owned_roots ((x, Bor q) # env) = owned_roots env"
  by (auto simp: owned_roots_def)

definition cleanup_ok :: "prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool" where
  "cleanup_ok P env st \<longleftrightarrow> distinct [r. (x, Own r) \<leftarrow> env] \<and>
     (\<forall>x r. (x, Own r) \<in> set env \<longrightarrow> (\<exists>v T. heap st r = Some v \<and> wt_opt P T v))"

lemma own_roots_mem: "(x, Own r) \<in> set env \<Longrightarrow> r \<in> set [r. (x, Own r) \<leftarrow> env]"
  by (induction env) auto

lemma cleanup_sound:
  assumes drops: "\<And>m. sound_drop P m"
  shows "cleanup_ok P env st \<Longrightarrow> heap_fresh st \<Longrightarrow>
    spec (cleanup P n st env) (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
      (\<forall>r. r < nroot st \<longrightarrow> r \<notin> owned_roots env \<longrightarrow> heap st' r = heap st r))"
proof (induction n arbitrary: st env)
  case 0
  then show ?case by (simp add: spec_def safe_def)
next
  case (Suc n)
  show ?case
  proof (cases env)
    case Nil
    with Suc.prems show ?thesis by (simp add: spec_def safe_def)
  next
    case (Cons xb env')
    obtain x b where xb: "xb = (x, b)" by (cases xb)
    show ?thesis
    proof (cases b)
      case (Bor q)
      with Suc.prems Cons xb have "cleanup_ok P env' st" by (auto simp: cleanup_ok_def)
      from Suc.IH[OF this Suc.prems(2)] Cons xb Bor show ?thesis by simp
    next
      case (Own r)
      with Cons xb have "(x, Own r) \<in> set env" by simp
      with Suc.prems(1) obtain v T where rv: "heap st r = Some v" "wt_opt P T v"
        unfolding cleanup_ok_def by blast
      have dp: "spec (drop_path P n st (r, [])) (drop_post st (r, []))"
        using drops[of n, unfolded sound_drop_def, rule_format, of st "(r, [])" v T] rv Suc.prems(2)
        by (simp add: get_def)
      show ?thesis
        unfolding Cons xb Own cleanup.simps list.case prod.case binding.case
      proof (rule spec_bind, rule spec_mono[OF dp])
        fix st1 assume d: "drop_post st (r, []) st1"
        let ?st2 = "free st1 r"
        have r_lt: "r < nroot st" using rv Suc.prems(2) by (auto simp: heap_fresh_def not_less[symmetric])
        have ok2: "cleanup_ok P env' ?st2"
          unfolding cleanup_ok_def
        proof (intro conjI allI impI)
          show "distinct [r. (x, Own r) \<leftarrow> env']"
            using Suc.prems(1) Cons xb Own by (simp add: cleanup_ok_def)
          fix x' r' assume xr: "(x', Own r') \<in> set env'"
          then have "r' \<noteq> r"
            using Suc.prems(1) Cons xb Own by (auto simp: cleanup_ok_def own_roots_mem)
          from xr Suc.prems(1) Cons obtain v' T' where v': "heap st r' = Some v'" "wt_opt P T' v'"
            unfolding cleanup_ok_def by fastforce
          then have "r' < nroot st" using Suc.prems(2) by (auto simp: heap_fresh_def not_less[symmetric])
          with \<open>r' \<noteq> r\<close> d v' show "\<exists>v T. heap ?st2 r' = Some v \<and> wt_opt P T v"
            by (auto simp: drop_post_def free_def)
        qed
        have fr2: "heap_fresh ?st2"
          using d by (auto simp: drop_post_def heap_fresh_def free_def)
        show "spec (cleanup P n ?st2 env') (\<lambda>st'. nroot st \<le> nroot st' \<and> heap_fresh st' \<and>
            (\<forall>r'. r' < nroot st \<longrightarrow> r' \<notin> owned_roots ((x, Own r) # env') \<longrightarrow> heap st' r' = heap st r'))"
          by (rule spec_mono[OF Suc.IH[OF ok2 fr2]]) (use d r_lt in \<open>auto simp: drop_post_def free_def\<close>)
      qed
    qed
  qed
qed

section \<open>Declarations and the end of a block\<close>

lemma wf_senv_ref_og:
  "wf_senv \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some (KRef T og I) \<Longrightarrow> og \<subseteq> fst ` set \<Gamma>"
  by (induction \<Gamma> rule: wf_senv.induct) (auto split: if_splits vkind.splits)

lemma wf_senv_append:
  "wf_senv (\<Delta> @ \<Gamma>) \<Longrightarrow> wf_senv \<Gamma> \<and> fst ` set \<Delta> \<inter> fst ` set \<Gamma> = {}"
  by (induction \<Delta>) force+

lemma place_origin_dom:
  assumes "wf_senv \<Gamma>" "map_of \<Gamma> (root_of p) \<noteq> None"
  shows "place_origin \<Gamma> p \<subseteq> fst ` set \<Gamma>"
proof -
  from assms(2) obtain k where k: "map_of \<Gamma> (root_of p) = Some k" by blast
  have r: "root_of p \<in> fst ` set \<Gamma>" using assms(2) by (metis map_of_eq_None_iff)
  show ?thesis
  proof (cases k)
    case (KRef T og I)
    with k assms(1) show ?thesis
      by (simp add: place_origin_def static_roots_def wf_senv_ref_og)
  qed (use k r in \<open>simp_all add: place_origin_def static_roots_def\<close>)
qed

text \<open>
  A binding stays valid when the environments grow, the heap changes only
  at or above the old @{text "nroot"}, and the abstract state agrees on the
  variables involved.
\<close>

lemma binding_ok_transfer:
  assumes b: "binding_ok P C \<Gamma> \<sigma> env st x k b"
    and \<Gamma>': "\<And>z. map_of \<Gamma> z \<noteq> None \<Longrightarrow> map_of \<Gamma>' z = map_of \<Gamma> z"
    and env': "\<And>z. map_of env z \<noteq> None \<Longrightarrow> map_of env' z = map_of env z"
    and init: "\<And>z. map_of \<Gamma> z \<noteq> None \<Longrightarrow> z \<in> a_init \<sigma>' \<longleftrightarrow> z \<in> a_init \<sigma>" "x \<in> a_init \<sigma>' \<longleftrightarrow> x \<in> a_init \<sigma>"
    and inval: "a_inval \<sigma> \<subseteq> a_inval \<sigma>'" and flds: "a_fields \<sigma>' = a_fields \<sigma>"
    and heap: "\<And>r. r < nroot st \<Longrightarrow> heap st' r = heap st r"
    and bounds: "\<And>z bz. map_of env z = Some bz \<Longrightarrow> fst (bpath bz) < nroot st" "fst (bpath b) < nroot st"
  shows "binding_ok P C \<Gamma>' \<sigma>' env' st' x k b"
proof -
  have get: "get st' p0 = get st p0" if "fst p0 < nroot st" for p0
    using that heap by (intro get_root_cong) simp
  show ?thesis
  proof (cases k)
    case (KOwned T)
    with b init(2) heap bounds(2) show ?thesis by auto
  next
    case (KBorrow c T)
    with b get[OF bounds(2)] show ?thesis by (auto simp: out_val_fields_eq[OF flds] split: if_splits)
  next
    case (KRef T og I)
    from b KRef obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of \<Gamma> z = Some kz"
      "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
      "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
      "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
      by (simp only: binding_ok.simps) blast
    have "get st' q = get st q" using get bounds(1)[OF rf(5)] rf(6) by simp
    moreover have "map_of \<Gamma>' z = Some kz" "map_of env' z = Some bz"
      using \<Gamma>'[of z] env'[of z] rf(3,5) by simp_all
    moreover have "x \<notin> a_inval \<sigma>' \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>') \<longrightarrow>
                   x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>)"
      using inval init(1)[of z] rf(3) by auto
    ultimately show ?thesis using rf KRef by (simp only: binding_ok.simps) metis
  qed
qed

lemma inv_alloc_owned:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "x \<notin> fst ` set \<Gamma>" and al: "alloc st v = (r, st')"
    and hv: "if x \<in> a_init \<sigma>' then vt P T v else wt_opt P T v"
    and \<sigma>': "a_inval \<sigma>' = a_inval \<sigma>" "a_fields \<sigma>' = a_fields \<sigma>"
       "\<And>y. y \<noteq> x \<Longrightarrow> y \<in> a_init \<sigma>' \<longleftrightarrow> y \<in> a_init \<sigma>"
  shows "inv P C ((x, KOwned T) # \<Gamma>) \<sigma>' ((x, Own r) # env) st'"
proof -
  have r: "r = nroot st" "heap st' = (heap st)(r := Some v)" "nroot st' = Suc (nroot st)"
    using al by (auto simp: alloc_def)
  have xe: "x \<notin> fst ` set env" using inv x by (simp add: inv_def) (metis set_map)
  have xG: "map_of \<Gamma> x = None" "map_of env x = None" using x xe by (simp_all add: map_of_eq_None_iff)
  have bounds: "\<And>z bz. map_of env z = Some bz \<Longrightarrow> fst (bpath bz) < nroot st"
    using inv by (simp add: inv_def)
  have old: "binding_ok P C ((x, KOwned T) # \<Gamma>) \<sigma>' ((x, Own r) # env) st' y k b"
    if "map_of \<Gamma> y = Some k" "map_of env y = Some b" "binding_ok P C \<Gamma> \<sigma> env st y k b" for y k b
  proof (rule binding_ok_transfer[OF that(3)])
    show "\<And>z. map_of \<Gamma> z \<noteq> None \<Longrightarrow> map_of ((x, KOwned T) # \<Gamma>) z = map_of \<Gamma> z" using xG by auto
    show "\<And>z. map_of env z \<noteq> None \<Longrightarrow> map_of ((x, Own r) # env) z = map_of env z" using xG by auto
    show "\<And>z. map_of \<Gamma> z \<noteq> None \<Longrightarrow> z \<in> a_init \<sigma>' \<longleftrightarrow> z \<in> a_init \<sigma>"
      using \<sigma>'(3) xG by metis
    show "y \<in> a_init \<sigma>' \<longleftrightarrow> y \<in> a_init \<sigma>" using \<sigma>'(3) xG that(1) by (metis option.distinct(1))
  qed (use \<sigma>' r bounds that(2) in auto)
  have excl: "excl \<Gamma> env" using inv by (simp add: inv_def)
  have excl': "excl ((x, KOwned T) # \<Gamma>) ((x, Own r) # env)"
    unfolding excl_def
  proof (intro allI impI, elim conjE)
    fix a ka ba c kc bc
    assume h: "map_of ((x, KOwned T) # \<Gamma>) a = Some ka" "writable ka"
      "map_of ((x, Own r) # env) a = Some ba" "map_of ((x, KOwned T) # \<Gamma>) c = Some kc"
      "\<not> is_ref kc" "map_of ((x, Own r) # env) c = Some bc" "c \<noteq> a"
    show "\<not> overlaps (bpath ba) (bpath bc)"
    proof (cases "a = x \<or> c = x")
      case True
      then show ?thesis
      proof
        assume "a = x"
        with h have "ba = Own r" "map_of env c = Some bc" by auto
        with bounds r(1) show ?thesis by (fastforce simp: overlaps_def below_def)
      next
        assume "c = x"
        with h have "bc = Own r" "map_of env a = Some ba" by auto
        with bounds r(1) show ?thesis by (fastforce simp: overlaps_def below_def)
      qed
    next
      case False
      with h excl show ?thesis by (auto simp: excl_def)
    qed
  qed
  show ?thesis
    unfolding inv_def
  proof (intro conjI allI impI)
    show "wf_senv ((x, KOwned T) # \<Gamma>)" using inv x by (simp add: inv_def)
    show "one_out ((x, KOwned T) # \<Gamma>)" using inv xG by (auto simp: inv_def one_out_def)
    show "map fst ((x, Own r) # env) = map fst ((x, KOwned T) # \<Gamma>)" using inv by (simp add: inv_def)
    show "excl ((x, KOwned T) # \<Gamma>) ((x, Own r) # env)" by (rule excl')
    fix y k assume yk: "map_of ((x, KOwned T) # \<Gamma>) y = Some k"
    show "\<exists>b. map_of ((x, Own r) # env) y = Some b \<and>
              binding_ok P C ((x, KOwned T) # \<Gamma>) \<sigma>' ((x, Own r) # env) st' y k b"
    proof (cases "y = x")
      case True
      with yk hv r show ?thesis by auto
    next
      case False
      with yk inv_binding[OF inv, of y k] old show ?thesis by fastforce
    qed
  next
    fix y b assume "map_of ((x, Own r) # env) y = Some b"
    with bounds r show "fst (bpath b) < nroot st'" by (fastforce split: if_splits)
  next
    fix r' assume "nroot st' \<le> r'"
    with inv r show "heap st' r' = None" by (auto simp: inv_def)
  qed
qed

lemma inv_add_ref:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "x \<notin> fst ` set \<Gamma>"
    and pl: "ploc P \<Gamma> env p T q" and g: "get st q = Ok v" "vt P T v"
    and og: "place_origin \<Gamma> p \<subseteq> fst ` set \<Gamma>"
  shows "inv P C ((x, KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)) # \<Gamma>) \<sigma> ((x, Bor q) # env) st"
proof -
  let ?k = "KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)"
  have xe: "x \<notin> fst ` set env" using inv x by (simp add: inv_def) (metis set_map)
  have xG: "map_of \<Gamma> x = None" "map_of env x = None" using x xe by (simp_all add: map_of_eq_None_iff)
  have bounds: "\<And>z bz. map_of env z = Some bz \<Longrightarrow> fst (bpath bz) < nroot st"
    using inv by (simp add: inv_def)
  from pl obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz" "\<not> is_ref kz"
    "map_of env z = Some bz" "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T"
    "has_idx ss \<longrightarrow> z \<in> place_interior \<Gamma> p"
    unfolding ploc_def by blast
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

lemma wf_senv_distinct: "wf_senv \<Gamma> \<Longrightarrow> distinct (map fst \<Gamma>)"
  by (induction \<Gamma> rule: wf_senv.induct) auto

lemma map_of_distinct_mem: "distinct (map fst xs) \<Longrightarrow> (x, v) \<in> set xs \<Longrightarrow> map_of xs x = Some v"
  by (induction xs) (auto simp: image_iff)

text \<open>
  At the end of a block, its declarations @{text "\<Delta>"} (bound to @{text "\<Delta>e"}
  at run time) are discarded and their owned roots destroyed. The
  invariant for the enclosing block holds again, as long as the heap is
  unchanged at every other root: no outer variable lives at a root owned by
  the block, by exclusivity, and no outer reference points into one,
  because origins only contain variables declared before the reference.
\<close>

lemma distinct_own_roots:
  "distinct (map fst E) \<Longrightarrow> (\<And>x y r. (x, Own r) \<in> set E \<Longrightarrow> (y, Own r) \<in> set E \<Longrightarrow> x = y) \<Longrightarrow>
   distinct [r. (x, Own r) \<leftarrow> E]"
proof (induction E)
  case (Cons xb E)
  obtain x b where xb: "xb = (x, b)" by (cases xb)
  have IH: "distinct [r. (x, Own r) \<leftarrow> E]" using Cons by auto
  show ?case
  proof (cases b)
    case (Own r)
    have "r \<notin> set [r. (x, Own r) \<leftarrow> E]"
    proof
      assume "r \<in> set [r. (x, Own r) \<leftarrow> E]"
      then obtain y where y: "(y, Own r) \<in> set E" by (induction E) (auto split: binding.splits)
      with Cons.prems(2)[of x r y] xb Own have "y = x" by auto
      with y Cons.prems(1) xb show False by (auto simp: image_iff)
    qed
    with IH xb Own show ?thesis by simp
  qed (use IH xb in simp)
qed simp

lemma inv_restrict_facts:
  assumes inv: "inv P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st" and len: "length \<Delta>e = length \<Delta>"
    and nb: "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
  shows "map fst \<Delta>e = map fst \<Delta>" "map fst env = map fst \<Gamma>" "wf_senv \<Gamma>"
    "fst ` set \<Delta> \<inter> fst ` set \<Gamma> = {}"
    "\<And>x. map_of \<Gamma> x \<noteq> None \<Longrightarrow> map_of (\<Delta> @ \<Gamma>) x = map_of \<Gamma> x \<and> map_of (\<Delta>e @ env) x = map_of env x"
    "\<And>x r. (x, Own r) \<in> set \<Delta>e \<Longrightarrow> \<exists>T. map_of (\<Delta> @ \<Gamma>) x = Some (KOwned T) \<and>
             map_of (\<Delta>e @ env) x = Some (Own r)"
    "cleanup_ok P \<Delta>e st"
proof -
  have wf: "wf_senv (\<Delta> @ \<Gamma>)" and mf: "map fst (\<Delta>e @ env) = map fst (\<Delta> @ \<Gamma>)"
    using inv by (simp_all add: inv_def)
  from mf len show mfd: "map fst \<Delta>e = map fst \<Delta>" and mfe: "map fst env = map fst \<Gamma>"
    by (simp_all add: append_eq_append_conv)
  from wf_senv_append[OF wf] show wfg: "wf_senv \<Gamma>" and dj: "fst ` set \<Delta> \<inter> fst ` set \<Gamma> = {}"
    by auto
  have dist: "distinct (map fst (\<Delta>e @ env))" using wf_senv_distinct[OF wf] mf by simp
  show dom: "map_of (\<Delta> @ \<Gamma>) x = map_of \<Gamma> x \<and> map_of (\<Delta>e @ env) x = map_of env x"
    if "map_of \<Gamma> x \<noteq> None" for x
  proof -
    have "x \<in> fst ` set \<Gamma>" using that by (metis map_of_eq_None_iff)
    with dj have "x \<notin> fst ` set \<Delta>" by blast
    moreover have "fst ` set \<Delta>e = fst ` set \<Delta>" using mfd by (metis set_map)
    ultimately have "map_of \<Delta> x = None" "map_of \<Delta>e x = None" by (simp_all add: map_of_eq_None_iff)
    then show ?thesis by (simp add: map_add_def)
  qed
  show own: "\<exists>T. map_of (\<Delta> @ \<Gamma>) x = Some (KOwned T) \<and> map_of (\<Delta>e @ env) x = Some (Own r)"
    if xr: "(x, Own r) \<in> set \<Delta>e" for x r
  proof -
    have e: "map_of (\<Delta>e @ env) x = Some (Own r)" using map_of_distinct_mem[OF dist] xr by simp
    have "x \<in> fst ` set \<Delta>" using xr mfd by (metis fst_conv image_eqI set_map)
    then obtain k where k: "map_of \<Delta> x = Some k" by (metis map_of_eq_None_iff not_Some_eq)
    then have g: "map_of (\<Delta> @ \<Gamma>) x = Some k" by simp
    from inv_binding[OF inv g] e have "binding_ok P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st x k (Own r)" by auto
    moreover have "\<forall>c T. k \<noteq> KBorrow c T" using nb map_of_SomeD[OF k] by blast
    ultimately obtain T where "k = KOwned T" by (cases k) auto
    with g e show ?thesis by blast
  qed
  show "cleanup_ok P \<Delta>e st"
    unfolding cleanup_ok_def
  proof (intro conjI allI impI)
    show "distinct [r. (x, Own r) \<leftarrow> \<Delta>e]"
    proof (rule distinct_own_roots)
      show "distinct (map fst \<Delta>e)" using dist by simp
      have excl: "excl (\<Delta> @ \<Gamma>) (\<Delta>e @ env)" using inv by (simp add: inv_def)
      show "x = y" if "(x, Own r) \<in> set \<Delta>e" "(y, Own r) \<in> set \<Delta>e" for x y r
      proof (rule ccontr)
        assume "x \<noteq> y"
        from own[OF that(1)] own[OF that(2)] obtain Tx Ty where
          "map_of (\<Delta> @ \<Gamma>) x = Some (KOwned Tx)" "map_of (\<Delta>e @ env) x = Some (Own r)"
          "map_of (\<Delta> @ \<Gamma>) y = Some (KOwned Ty)" "map_of (\<Delta>e @ env) y = Some (Own r)"
          by blast
        with excl_D[OF excl] \<open>x \<noteq> y\<close> show False by (fastforce simp: overlaps_def below_def)
      qed
    qed
  next
    fix x r assume "(x, Own r) \<in> set \<Delta>e"
    from own[OF this] obtain T where "map_of (\<Delta> @ \<Gamma>) x = Some (KOwned T)"
      "map_of (\<Delta>e @ env) x = Some (Own r)" by blast
    with inv_binding[OF inv, of x "KOwned T"] show "\<exists>v T. heap st r = Some v \<and> wt_opt P T v"
      by (fastforce simp: wt_opt_def split: if_splits)
  qed
qed

lemma inv_restrict:
  assumes inv: "inv P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st" and len: "length \<Delta>e = length \<Delta>"
    and nb: "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T"
    and st': "nroot st \<le> nroot st'" "heap_fresh st'"
      "\<forall>r. r < nroot st \<longrightarrow> r \<notin> owned_roots \<Delta>e \<longrightarrow> heap st' r = heap st r"
  shows "inv P C \<Gamma> \<sigma> env st'"
proof -
  note F = inv_restrict_facts[OF inv len nb]
  have excl: "excl (\<Delta> @ \<Gamma>) (\<Delta>e @ env)" using inv by (simp add: inv_def)
  have bounds: "\<And>x b. map_of (\<Delta>e @ env) x = Some b \<Longrightarrow> fst (bpath b) < nroot st"
    using inv by (simp add: inv_def)
  text \<open>No outer non-reference variable lives at a root owned by the block.\<close>
  have loc: "fst (bpath bx) \<notin> owned_roots \<Delta>e"
    if x: "map_of \<Gamma> x = Some kx" "\<not> is_ref kx" "map_of env x = Some bx" for x kx bx
  proof
    assume "fst (bpath bx) \<in> owned_roots \<Delta>e"
    then obtain y where y: "(y, Own (fst (bpath bx))) \<in> set \<Delta>e" by (auto simp: owned_roots_def)
    from F(6)[OF y] obtain T where yk: "map_of (\<Delta> @ \<Gamma>) y = Some (KOwned T)"
      "map_of (\<Delta>e @ env) y = Some (Own (fst (bpath bx)))" by blast
    have xd: "map_of (\<Delta> @ \<Gamma>) x = Some kx" "map_of (\<Delta>e @ env) x = Some bx"
      using F(5)[of x] x by simp_all
    have "y \<noteq> x"
    proof
      assume "y = x"
      with y F(1) have "x \<in> fst ` set \<Delta>" by (metis fst_conv image_eqI set_map)
      moreover have "x \<in> fst ` set \<Gamma>" using x(1) by (metis map_of_eq_None_iff option.distinct(1))
      ultimately show False using F(4) by blast
    qed
    from excl_D[OF excl yk(1) _ yk(2) xd(1) x(2) xd(2)] \<open>y \<noteq> x\<close> show False
      by (simp add: overlaps_def below_def)
  qed
  have heq: "get st' p0 = get st p0" if "fst p0 < nroot st" "fst p0 \<notin> owned_roots \<Delta>e" for p0
    using that st'(3) by (intro get_root_cong) simp
  have bind: "binding_ok P C \<Gamma> \<sigma> env st' x k b"
    if xk: "map_of \<Gamma> x = Some k" "map_of env x = Some b" for x k b
  proof -
    have xd: "map_of (\<Delta> @ \<Gamma>) x = Some k" "map_of (\<Delta>e @ env) x = Some b"
      using F(5)[of x] xk by simp_all
    from inv_binding[OF inv xd(1)] xd(2) have b: "binding_ok P C (\<Delta> @ \<Gamma>) \<sigma> (\<Delta>e @ env) st x k b"
      by auto
    show ?thesis
    proof (cases k)
      case (KOwned T)
      with b obtain r where "b = Own r" by auto
      with loc[OF xk(1) _ xk(2)] KOwned bounds[OF xd(2)] st'(3) b show ?thesis by auto
    next
      case (KBorrow c T)
      with b heq[of "bpath b"] loc[OF xk(1) _ xk(2)] bounds[OF xd(2)] show ?thesis by simp
    next
      case (KRef T og I)
      from b KRef obtain q z kz bz ss where rf: "b = Bor q" "z \<in> og" "map_of (\<Delta> @ \<Gamma>) z = Some kz"
        "\<not> is_ref kz" "map_of (\<Delta>e @ env) z = Some bz" "q = pext (bpath bz) ss"
        "sty P (kind_ty kz) ss = Some T" "has_idx ss \<longrightarrow> z \<in> I"
        "x \<notin> a_inval \<sigma> \<and> (\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>) \<longrightarrow> (\<exists>v. get st q = Ok v \<and> vt P T v)"
        by (simp only: binding_ok.simps) blast
      have "z \<in> fst ` set \<Gamma>" using wf_senv_ref_og[OF F(3) xk(1)[unfolded KRef]] rf(2) by blast
      then have "map_of \<Gamma> z \<noteq> None" by (simp add: map_of_eq_None_iff)
      with F(5)[of z] rf(3,5) have zg: "map_of \<Gamma> z = Some kz" "map_of env z = Some bz" by simp_all
      have "get st' q = get st q"
        using heq loc[OF zg(1) rf(4) zg(2)] bounds[OF rf(5)] rf(6) by simp
      with rf zg KRef show ?thesis by (simp only: binding_ok.simps) metis
    qed
  qed
  have exclg: "excl \<Gamma> env"
    using excl F(5) unfolding excl_def by (metis option.distinct(1))
  show ?thesis
    unfolding inv_def
  proof (intro conjI allI impI)
    show "wf_senv \<Gamma>" by (rule F(3))
    show "one_out \<Gamma>" using inv F(5) by (simp add: inv_def one_out_def)
    show "map fst env = map fst \<Gamma>" by (rule F(2))
    show "excl \<Gamma> env" by (rule exclg)
    fix x k assume "map_of \<Gamma> x = Some k"
    moreover from this obtain b where "map_of env x = Some b"
      using F(2) by (metis map_of_eq_None_iff not_Some_eq set_map)
    ultimately show "\<exists>b. map_of env x = Some b \<and> binding_ok P C \<Gamma> \<sigma> env st' x k b"
      using bind by blast
  next
    fix x b assume xb: "map_of env x = Some b"
    have "map_of \<Gamma> x \<noteq> None" using xb F(2) by (metis map_of_eq_None_iff option.distinct(1) set_map)
    with xb F(5) have "map_of (\<Delta>e @ env) x = Some b" by simp
    with bounds st'(1) show "fst (bpath b) < nroot st'" by (meson less_le_trans)
  next
    fix r assume "nroot st' \<le> r"
    with st'(2) show "heap st' r = None" by (simp add: heap_fresh_def)
  qed
qed

section \<open>Static facts about statements\<close>

lemma ex_cons_append:
  "\<forall>c T. k \<noteq> KBorrow c T \<Longrightarrow>
   \<exists>\<Delta>. (x, k) # \<Gamma> = \<Delta> @ \<Gamma> \<and> (\<forall>(y, k') \<in> set \<Delta>. \<forall>c T. k' \<noteq> KBorrow c T)"
  by (intro exI[of _ "[(x, k)]"]) auto

lemma chk_stmt_extends:
  "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<Longrightarrow>
     \<exists>\<Delta>. \<Gamma>' = \<Delta> @ \<Gamma> \<and> (\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T)"
  "chk_loop k C \<Gamma> \<sigma> c b = Good o\<sigma>' \<Longrightarrow> True"
proof (induction C \<Gamma> \<sigma> s and k C \<Gamma> \<sigma> c b arbitrary: \<Gamma>' o\<sigma> and o\<sigma>' rule: chk_stmt_chk_loop.induct)
  case (2 C \<Gamma> \<sigma> a b)
  then obtain \<Gamma>1 o\<sigma>1 where a: "chk_stmt C \<Gamma> \<sigma> a = Good (\<Gamma>1, o\<sigma>1)"
    and rest: "(case o\<sigma>1 of None \<Rightarrow> Good (\<Gamma>1, None) | Some \<sigma> \<Rightarrow> chk_stmt C \<Gamma>1 \<sigma> b) = Good (\<Gamma>', o\<sigma>)"
    by auto
  from "2.IH"(1)[OF a] obtain \<Delta>1 where \<Delta>1: "\<Gamma>1 = \<Delta>1 @ \<Gamma>" "\<forall>(x, k) \<in> set \<Delta>1. \<forall>c T. k \<noteq> KBorrow c T"
    by blast
  show ?case
  proof (cases o\<sigma>1)
    case None
    with rest \<Delta>1 show ?thesis by auto
  next
    case (Some \<sigma>1)
    with rest have b: "chk_stmt C \<Gamma>1 \<sigma>1 b = Good (\<Gamma>', o\<sigma>)" by simp
    from "2.IH"(2)[OF a[unfolded Some] refl refl b] obtain \<Delta>2 where
      "\<Gamma>' = \<Delta>2 @ \<Gamma>1" "\<forall>(x, k) \<in> set \<Delta>2. \<forall>c T. k \<noteq> KBorrow c T" by auto
    with \<Delta>1 show ?thesis by (intro exI[of _ "\<Delta>2 @ \<Delta>1"]) auto
  qed
next
  case (3 C \<Gamma> \<sigma> x T eo)
  then show ?case by (auto split: option.splits intro!: exI[of _ "[(x, KOwned T)]"])
next
  case (4 C \<Gamma> \<sigma> x e)
  then show ?case
    by (auto split: expr.splits option.splits ret.splits intro: ex_cons_append)
next
  case (12 C \<Gamma> \<sigma> p)
  then show ?case by (auto split: prod.splits place.splits option.splits vkind.splits)
next
  case (11 C \<Gamma> \<sigma> e)
  then show ?case by (auto split: ret.splits expr.splits)
qed (auto intro: exI[of _ "[]"])

lemma join_opt_Some_weaker:
  "join_opt (Some \<sigma>) ob = Some \<sigma>' \<Longrightarrow> weaker \<sigma>' \<sigma> \<and> (\<forall>\<sigma>b. ob = Some \<sigma>b \<longrightarrow> weaker \<sigma>' \<sigma>b)"
  by (cases ob) (auto simp: weaker_join)

lemma chk_loop_fix:
  "chk_loop k C \<Gamma> \<sigma> c b = Good o\<sigma> \<Longrightarrow>
   \<exists>\<sigma>f \<sigma>c \<Gamma>b ob. weaker \<sigma>f \<sigma> \<and> chk_expr C \<Gamma> \<sigma>f c = Good \<sigma>c \<and> chk_stmt C \<Gamma> \<sigma>c b = Good (\<Gamma>b, ob) \<and>
     join_opt (Some \<sigma>f) ob = Some \<sigma>f \<and> o\<sigma> = Some \<sigma>c"
proof (induction k arbitrary: \<sigma>)
  case 0
  then show ?case by simp
next
  case (Suc k)
  from Suc.prems obtain \<sigma>c \<Gamma>b ob where c: "chk_expr C \<Gamma> \<sigma> c = Good \<sigma>c"
    and bd: "chk_stmt C \<Gamma> \<sigma>c b = Good (\<Gamma>b, ob)"
    and rest: "(case join_opt (Some \<sigma>) ob of
                 Some \<sigma>' \<Rightarrow> if \<sigma>' = \<sigma> then Good (Some \<sigma>c) else chk_loop k C \<Gamma> \<sigma>' c b
               | None \<Rightarrow> Good None) = Good o\<sigma>"
    by auto
  obtain \<sigma>' where j: "join_opt (Some \<sigma>) ob = Some \<sigma>'" by (cases ob) auto
  show ?case
  proof (cases "\<sigma>' = \<sigma>")
    case True
    with rest j c bd show ?thesis
      by (intro exI[of _ \<sigma>] exI[of _ \<sigma>c] exI[of _ \<Gamma>b] exI[of _ ob]) auto
  next
    case False
    with rest j have "chk_loop k C \<Gamma> \<sigma>' c b = Good o\<sigma>" by simp
    from Suc.IH[OF this] obtain \<sigma>f \<sigma>c' \<Gamma>b' ob' where
      "weaker \<sigma>f \<sigma>'" "chk_expr C \<Gamma> \<sigma>f c = Good \<sigma>c'" "chk_stmt C \<Gamma> \<sigma>c' b = Good (\<Gamma>b', ob')"
      "join_opt (Some \<sigma>f) ob' = Some \<sigma>f" "o\<sigma> = Some \<sigma>c'" by blast
    moreover have "weaker \<sigma>' \<sigma>" using join_opt_Some_weaker[OF j] by blast
    ultimately show ?thesis by (blast intro: weaker_trans)
  qed
qed

lemma chk_loop_stable:
  "chk_expr C \<Gamma> \<sigma>f c = Good \<sigma>c \<Longrightarrow> chk_stmt C \<Gamma> \<sigma>c b = Good (\<Gamma>b, ob) \<Longrightarrow>
   join_opt (Some \<sigma>f) ob = Some \<sigma>f \<Longrightarrow> chk_loop (Suc k) C \<Gamma> \<sigma>f c b = Good (Some \<sigma>c)"
  by simp

section \<open>Initializing expressions and assignments at the heap level\<close>

lemma ty_init_cases:
  "ty_init P \<Gamma> T e = Good () \<Longrightarrow>
   (e = EList [] \<and> (\<exists>U. T = TList U)) \<or> (etype P \<Gamma> e = Good T)"
  by (cases e rule: expr.exhaust; simp add: ty_init_def split: ty.splits list.splits)
     (auto split: ty.splits)

lemma sound_ty_init:
  assumes "sound_expr P C \<Gamma> n" "inv P C \<Gamma> \<sigma> env st" "simple_expr e"
    "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'" "ty_init P \<Gamma> T e = Good ()"
  shows "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v)"
proof (cases "e = EList [] \<and> (\<exists>U. T = TList U)")
  case True
  then obtain U where e: "e = EList []" and T: "T = TList U" by blast
  from assms(4) e have "\<sigma>' = \<sigma>" by simp
  with assms(2) e T show ?thesis
    by (cases n; cases "n - 1") (auto simp: fresh_gen_def)
next
  case False
  with ty_init_cases[OF assms(5)] have "etype P \<Gamma> e = Good T" by blast
  with assms(1-4) have "spec (eval P n env st e)
      (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
    unfolding sound_expr_def by blast
  then show ?thesis by (rule spec_mono) auto
qed

text \<open>Dropping the value at a path and then writing a new one.\<close>

lemma put_after_drop:
  assumes "drop_post st q st3"
  shows "\<exists>w w4. heap st (fst q) = Some w \<and> update_at w (snd q) v = Ok w4 \<and>
           put st3 q v = Ok (st3\<lparr>heap := (heap st3)(fst q := Some w4)\<rparr>)"
proof -
  from assms obtain w w3 where w: "heap st (fst q) = Some w" "update_at w (snd q) VUndef = Ok w3"
    "heap st3 (fst q) = Some w3" by (auto simp: drop_post_def)
  from update_again[OF w(2)] obtain w4 where "update_at w3 (snd q) v = Ok w4"
    "update_at w (snd q) v = Ok w4" by blast
  with w show ?thesis by (auto simp: put_def)
qed

lemma inv_drop_var:
  assumes inv: "inv P C \<Gamma> \<sigma> env st" and x: "map_of \<Gamma> x = Some (KOwned U)"
    and r: "map_of env x = Some (Own r)" and d: "drop_post st (r, []) st'"
  shows "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env st'"
proof -
  let ?st0 = "st\<lparr>heap := (heap st)(r := Some VUndef)\<rparr>"
  have i0: "inv P C \<Gamma> (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) env ?st0"
    by (rule inv_move[OF inv x r]) simp_all
  show ?thesis
  proof (rule inv_heap_frame[OF i0])
    show "\<forall>r'. r' < nroot ?st0 \<longrightarrow> heap st' r' = heap ?st0 r'"
      using d by (auto simp: drop_post_def)
  qed (use d in \<open>auto simp: drop_post_def\<close>)
qed

section \<open>Writing into \<open>out self\<close>\<close>

lemma out_field_wt:
  assumes "out_val P C \<sigma> (TStruct S) u" "field_ty P S f = Good U"
  shows "\<exists>uf. walk u [Fld f] = Ok uf \<and> wt_opt P U uf"
proof (cases "c_fields C = []")
  case True
  with assms vt_field[of P S u f U] show ?thesis by (auto simp: out_val_def wt_opt_def)
next
  case False
  with assms(1) obtain sd fs where sd: "find_struct P S = Some sd" and u: "u = VStruct S fs"
    and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                                   (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)"
    by (auto simp: out_val_def)
  from assms(2) sd have U: "map_of (sd_fields sd) f = Some U"
    by (auto simp: field_ty_def split: option.splits)
  then have "f \<in> fst ` set fs" using names by (metis map_of_eq_None_iff option.distinct(1) set_map)
  then obtain uf where uf: "map_of fs f = Some uf" by (meson map_of_eq_None_iff not_Some_eq)
  from map_of_SomeD[OF uf] fs U have "wt_opt P U uf" by fastforce
  with uf u show ?thesis by simp
qed

text \<open>
  Updating a field of a partially initialized @{text "out self"}: with a
  well-typed value, at the field itself (which may have been uninitialized,
  and is then initialized) or below it (when the field is initialized).
\<close>

lemma out_val_update:
  assumes ov: "out_val P C \<sigma> (TStruct S) u" and ft: "field_ty P S f = Good Uf"
    and st: "sty P Uf rest = Some T" and vv: "vt P T v"
    and up: "update_at u (Fld f # rest) v = Ok u'"
    and init: "rest = [] \<or> (\<exists>u0. walk u (Fld f # rest) = Ok u0 \<and> vt P T u0)"
  shows "out_val P C (\<sigma>\<lparr>a_fields := insert f (a_fields \<sigma>)\<rparr>) (TStruct S) u'"
proof (cases "c_fields C = []")
  case True
  with ov have vu: "vt P (TStruct S) u" by (simp add: out_val_def)
  have st2: "sty P (TStruct S) (Fld f # rest) = Some T" using ft st by simp
  from update_walk_ok[OF up] obtain u0 where "walk u (Fld f # rest) = Ok u0" by blast
  from update_typed[OF vu st2 this vv] up True show ?thesis by (auto simp: out_val_def)
next
  case False
  with ov obtain sd fs where sd: "find_struct P S = Some sd" and cf: "c_fields C = map fst (sd_fields sd)"
    and u: "u = VStruct S fs" and names: "map fst fs = map fst (sd_fields sd)"
    and fs: "\<forall>(f, u) \<in> set fs. \<exists>U. map_of (sd_fields sd) f = Some U \<and> wt_opt P U u \<and>
                                   (f \<in> a_fields \<sigma> \<longrightarrow> vt P U u)"
    by (auto simp: out_val_def)
  from ft sd have Uf: "map_of (sd_fields sd) f = Some Uf"
    by (auto simp: field_ty_def split: option.splits)
  from up u obtain uf uf' where uf: "map_of fs f = Some uf" "update_at uf rest v = Ok uf'"
    and u': "u' = VStruct S (upd_field f uf' fs)"
    by (auto simp: bind_res_Ok_iff split: option.splits)
  have "vt P Uf uf'"
  proof (cases "rest = []")
    case True
    with uf(2) st vv show ?thesis by simp
  next
    case False
    with init uf u obtain u0 where w0: "walk uf rest = Ok u0" "vt P T u0" by auto
    from map_of_SomeD[OF uf(1)] fs Uf have "wt_opt P Uf uf" by fastforce
    moreover have "uf \<noteq> VUndef" using w0(1) False by (cases rest) auto
    ultimately have "vt P Uf uf" by (simp add: wt_opt_def)
    from update_typed[OF this st w0(1) vv] uf(2) show ?thesis by auto
  qed
  then have "\<forall>(g, w) \<in> set (upd_field f uf' fs). \<exists>U. map_of (sd_fields sd) g = Some U \<and> wt_opt P U w \<and>
               (g \<in> insert f (a_fields \<sigma>) \<longrightarrow> vt P U w)"
    using fs Uf by (auto simp: wt_opt_def dest!: set_upd_field)
  with False sd cf u' names show ?thesis by (simp add: out_val_def)
qed

lemma out_val_replace:
  assumes "out_val P C \<sigma> T u" "vt P T v"
  shows "out_val P C \<sigma>' T v"
proof (cases "c_fields C = []")
  case True
  with assms show ?thesis by (simp add: out_val_def)
next
  case False
  with assms(1) obtain S sd where T: "T = TStruct S" "find_struct P S = Some sd"
    "c_fields C = map fst (sd_fields sd)" by (auto simp: out_val_def)
  with assms(2) False show ?thesis by (cases v) (auto simp: out_val_def wt_opt_def)
qed

lemma out_val_fields_insert:
  "out_val P C \<sigma> T u \<Longrightarrow> f \<in> a_fields \<sigma> \<Longrightarrow> out_val P C (\<sigma>\<lparr>a_fields := insert f (a_fields \<sigma>)\<rparr>) T u"
  by (simp add: insert_absorb)

section \<open>Assignment\<close>

lemma chk_assign_cases:
  "chk_assign C \<Gamma> \<sigma> p T = Good \<sigma>' \<Longrightarrow>
   (\<exists>x U. p = PVar x \<and> map_of \<Gamma> x = Some (KOwned U) \<and>
      \<sigma>' = invalidate_place \<Gamma> (\<sigma>\<lparr>a_init := insert x (a_init \<sigma>)\<rparr>) p T) \<or>
   (\<exists>s f U. p = PField (PVar s) f \<and> map_of \<Gamma> s = Some (KBorrow Out U) \<and>
      \<sigma>' = invalidate_place \<Gamma> (\<sigma>\<lparr>a_fields := insert f (a_fields \<sigma>)\<rparr>) p T) \<or>
   (\<exists>\<sigma>2. chk_idx C \<Gamma> \<sigma> p = Good \<sigma>2 \<and> root_ok C \<Gamma> \<sigma>2 p = Good () \<and> mut_ok \<Gamma> p = Good () \<and>
      \<sigma>' = invalidate_place \<Gamma> \<sigma>2 p T)"
  unfolding chk_assign_def
  by (auto split: place.splits option.splits vkind.splits conv.splits)

lemma drop_then_put:
  assumes "drop_post st q st3" "heap_fresh st"
  shows "\<exists>w w4 st4. put st3 q v = Ok st4 \<and> heap st (fst q) = Some w \<and>
     update_at w (snd q) v = Ok w4 \<and> heap st4 (fst q) = Some w4 \<and>
     (\<forall>r. r < nroot st \<longrightarrow> r \<noteq> fst q \<longrightarrow> heap st4 r = heap st r) \<and> nroot st \<le> nroot st4 \<and>
     (\<forall>r. nroot st4 \<le> r \<longrightarrow> heap st4 r = None)"
proof -
  from put_after_drop[OF assms(1)] obtain w w4 where w: "heap st (fst q) = Some w"
    "update_at w (snd q) v = Ok w4" "put st3 q v = Ok (st3\<lparr>heap := (heap st3)(fst q := Some w4)\<rparr>)"
    by blast
  have "fst q < nroot st" using w(1) assms(2) by (auto simp: heap_fresh_def not_less[symmetric])
  with assms(1) w show ?thesis
    by (intro exI[of _ w] exI[of _ w4] exI[of _ "st3\<lparr>heap := (heap st3)(fst q := Some w4)\<rparr>"])
       (auto simp: drop_post_def heap_fresh_def)
qed

lemma drop_spec:
  "sound_drop P n \<Longrightarrow> get st q = Ok v \<Longrightarrow> wt_opt P T v \<Longrightarrow> heap_fresh st \<Longrightarrow>
   spec (drop_path P n st q) (drop_post st q)"
  unfolding sound_drop_def by blast

text \<open>
  The heap-level part of an assignment @{text "p = e"}, once @{text "e"} has been
  evaluated to @{text "v"}: evaluate the place, destroy the old value and
  write the new one. The three cases are those of @{text "chk_assign"}.
\<close>

lemma assign_core:
  assumes CP: "c_prog C = P" and drops: "\<And>m. sound_drop P m"
    and inv: "inv P C \<Gamma> \<sigma>1 env st1" and vv: "vt P T v" and sp: "simple_place p"
    and pt: "ptype P \<Gamma> p = Good T" and ca: "chk_assign C \<Gamma> \<sigma>1 p T = Good \<sigma>'"
  shows "spec (do { (q, st) \<leftarrow> eval_place P n env st1 p; st \<leftarrow> drop_path P n st q;
                    st \<leftarrow> put st q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
proof -
  text \<open>The common tail: drop at @{text "q"}, write @{text "v"}, and conclude by @{text "inv_write"}.\<close>
  have tail: "spec (do { st \<leftarrow> drop_path P n st2 q; st \<leftarrow> put st q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
    if inv2: "inv P C \<Gamma> \<sigma>2 env st2" and g: "get st2 q = Ok u" "wt_opt P T u"
      and z: "map_of \<Gamma> z = Some kz" "writable kz" "map_of env z = Some bz"
      and q: "q = pext (bpath bz) ss" "sty P (kind_ty kz) ss = Some T"
      and s1: "a_inval \<sigma>2' = a_inval \<sigma>2" "\<forall>y. y \<noteq> z \<longrightarrow> (y \<in> a_init \<sigma>2' \<longleftrightarrow> y \<in> a_init \<sigma>2)"
        "a_fields \<sigma>2' = a_fields \<sigma>2 \<or> (\<exists>U. kz = KBorrow Out U)"
        "\<forall>U. kz = KOwned U \<longrightarrow> z \<in> a_init \<sigma>2' \<longrightarrow> z \<notin> a_init \<sigma>2 \<longrightarrow> ss = []"
      and zok: "\<And>w w4 (st4 :: state). heap st2 (fst q) = Some w \<Longrightarrow> update_at w (snd q) v = Ok w4 \<Longrightarrow>
                  heap st4 (fst q) = Some w4 \<Longrightarrow>
                  (\<forall>r. r < nroot st2 \<longrightarrow> r \<noteq> fst q \<longrightarrow> heap st4 r = heap st2 r) \<Longrightarrow>
                  binding_ok P C \<Gamma> \<sigma>2' env st4 z kz bz"
      and R: "z \<in> place_origin \<Gamma> p" and res: "\<sigma>' = invalidate_place \<Gamma> \<sigma>2' p T"
    for st2 q u \<sigma>2 z kz bz ss \<sigma>2'
  proof (rule spec_bind, rule spec_mono[OF drop_spec[OF drops g inv_heap_fresh[OF inv2]]])
    fix st3 assume d: "drop_post st2 q st3"
    from drop_then_put[OF d inv_heap_fresh[OF inv2], of v] obtain w w4 st4 where
      p4: "put st3 q v = Ok st4" "heap st2 (fst q) = Some w" "update_at w (snd q) v = Ok w4"
      "heap st4 (fst q) = Some w4" "\<forall>r. r < nroot st2 \<longrightarrow> r \<noteq> fst q \<longrightarrow> heap st4 r = heap st2 r"
      "nroot st2 \<le> nroot st4" "\<forall>r. nroot st4 \<le> r \<longrightarrow> heap st4 r = None"
      by blast
    have "inv P C \<Gamma> \<sigma>' env st4"
      using inv_write[OF inv2 z q vv p4(2,3,4,5,6,7) s1 zok[OF p4(2,3,4,5)] R] res
      by (simp add: invalidate_place_def)
    with p4(1) show "spec (bind_res (put st3 q v) (\<lambda>st. Ok (Normal, env, st)))
        (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
      by (simp add: spec_def safe_def)
  qed
  from chk_assign_cases[OF ca] show ?thesis
  proof (elim disjE exE conjE)
    text \<open>Assigning a whole owned variable.\<close>
    fix x U assume p: "p = PVar x" and xU: "map_of \<Gamma> x = Some (KOwned U)"
      and res: "\<sigma>' = invalidate_place \<Gamma> (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>) p T"
    from pt p xU have TU: "T = U" by simp
    from inv_binding[OF inv xU] obtain r w where r: "map_of env x = Some (Own r)"
      "heap st1 r = Some w" "if x \<in> a_init \<sigma>1 then vt P U w else wt_opt P U w" by auto
    have g: "get st1 (r, []) = Ok w" "wt_opt P T w" using r TU by (auto simp: get_def wt_opt_def split: if_splits)
    have R: "x \<in> place_origin \<Gamma> p" using p xU by (simp add: place_origin_def static_roots_def)
    have t: "spec (do { st \<leftarrow> drop_path P n st1 (r, []); st \<leftarrow> put st (r, []) v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
    proof (rule tail[OF inv g, of x "KOwned U" "Own r" "[]" "\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>"])
      fix w0 w4 and st4 :: state assume "heap st1 (fst (r, [])) = Some w0" "update_at w0 (snd (r, [])) v = Ok w4"
        "heap st4 (fst (r, [])) = Some w4"
      with vv TU show "binding_ok P C \<Gamma> (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>) env st4 x (KOwned U) (Own r)"
        by auto
    qed (use xU r TU R res in auto)
    with r p show ?thesis by (cases n) (simp_all add: eval_place_PVar)
  next
    text \<open>Assigning a field of @{text "out self"}.\<close>
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
    have t: "spec (do { st \<leftarrow> drop_path P n st1 ?q; st \<leftarrow> put st ?q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
    proof (rule tail[OF inv g, of s "KBorrow Out U0" b "[Fld f]" "\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>"])
      fix w w4 and st4 :: state assume w: "heap st1 (fst ?q) = Some w" "update_at w (snd ?q) v = Ok w4"
        "heap st4 (fst ?q) = Some w4"
      have wb: "walk w (snd (bpath b)) = Ok u" using b(2) w(1) by (simp add: get_def pext_def)
      have "update_at w (snd (bpath b) @ [Fld f]) v = Ok w4" using w(2) by (simp add: pext_def)
      from walk_update_prefix[OF this wb] obtain u' where u': "walk w4 (snd (bpath b)) = Ok u'"
        "update_at u [Fld f] v = Ok u'" by blast
      have "out_val P C (\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>) U0 u'"
        using out_val_update[OF b(3)[unfolded U0] ft _ vv u'(2)] U0 by simp
      moreover have "get st4 (bpath b) = Ok u'" using w(3) u'(1) by (simp add: get_def pext_def)
      ultimately show "binding_ok P C \<Gamma> (\<sigma>1\<lparr>a_fields := insert f (a_fields \<sigma>1)\<rparr>) env st4 s
                         (KBorrow Out U0) b" by simp
    qed (use sU b U0 ft R res uf(2) in auto)
    have ep: "eval_place P n env st1 p = (if n < 2 then OutOfFuel else Ok (?q, st1))"
      using b(1) p by (cases n; cases "n - 1") (auto simp: eval_place_PVar ext_pext split: binding.splits)
    show ?thesis using t by (cases "n < 2") (simp_all add: ep spec_OutOfFuel)
  next
    text \<open>Assigning any other usable, mutable place.\<close>
    fix \<sigma>2 assume ci: "chk_idx C \<Gamma> \<sigma>1 p = Good \<sigma>2" and ro: "root_ok C \<Gamma> \<sigma>2 p = Good ()"
      and mo: "mut_ok \<Gamma> p = Good ()" and res: "\<sigma>' = invalidate_place \<Gamma> \<sigma>2 p T"
    have pl: "spec (eval_place P n env st1 p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>2 env st' \<and>
        frame \<Gamma> env \<sigma>2 st1 st' \<and> (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q)"
      using sound_all[OF CP, of \<Gamma> n] inv sp ci pt ro unfolding sound_place_def by blast
    show ?thesis
    proof (rule spec_bind, rule spec_mono_pair[OF pl], unfold prod.case, elim conjE exE)
      fix q st2 u assume inv2: "inv P C \<Gamma> \<sigma>2 env st2" and fr: "frame \<Gamma> env \<sigma>2 st1 st2" and g: "get st2 q = Ok u" "vt P T u"
        and plq: "ploc P \<Gamma> env p T q"
      from plq obtain z kz bz ss where z: "z \<in> place_origin \<Gamma> p" "map_of \<Gamma> z = Some kz"
        "\<not> is_ref kz" "map_of env z = Some bz" "q = pext (bpath bz) ss"
        "sty P (kind_ty kz) ss = Some T" unfolding ploc_def by blast
      have wr: "writable kz"
        using mo z(1,2,3) by (cases kz) (auto simp: mut_ok_def)
      show "spec (do { st \<leftarrow> drop_path P n st2 q; st \<leftarrow> put st q v; Ok (Normal, env, st) })
           (\<lambda>(oc, env', st'). oc = Normal \<and> env' = env \<and> inv P C \<Gamma> \<sigma>' env st')"
      proof (rule tail[OF inv2 g(1) _ z(2) wr z(4,5,6), of \<sigma>2])
        show "wt_opt P T u" using g(2) by (simp add: wt_opt_def)
        fix w w4 and st4 :: state assume w: "heap st2 (fst q) = Some w" "update_at w (snd q) v = Ok w4"
          "heap st4 (fst q) = Some w4"
        have wq: "walk w (snd q) = Ok u" using g(1) w(1) by (simp add: get_def)
        show "binding_ok P C \<Gamma> \<sigma>2 env st4 z kz bz"
        proof (cases kz)
          case (KOwned U)
          have zi: "z \<in> a_init \<sigma>2" using origin_init[OF ro z(1)] z(2) KOwned by simp
          from inv_binding[OF inv2 z(2)] z(4) KOwned zi obtain r w0 where
            r: "bz = Own r" "heap st2 r = Some w0" "vt P U w0" by auto
          with z(5) w(1) have ww: "w0 = w" "snd q = ss" by (simp_all add: pext_def)
          have "vt P U w4"
            using update_typed[OF r(3)[unfolded ww(1)] _ wq[unfolded ww(2)] vv] z(6) KOwned
              w(2)[unfolded ww(2)] by auto
          with r w(3) z(5) zi KOwned show ?thesis by (simp add: pext_def)
        next
          case (KBorrow c U)
          from inv_binding[OF inv2 z(2)] z(4) KBorrow obtain ub where
            ub: "get st2 (bpath bz) = Ok ub" "if c = Out then out_val P C \<sigma>2 U ub else vt P U ub" by auto
          have wb: "walk w (snd (bpath bz)) = Ok ub" using ub(1) w(1) z(5) by (simp add: get_def pext_def)
          have "update_at w (snd (bpath bz) @ ss) v = Ok w4" using w(2) z(5) by (simp add: pext_def)
          from walk_update_prefix[OF this wb] obtain ub' where
            ub': "walk w4 (snd (bpath bz)) = Ok ub'" "update_at ub ss v = Ok ub'" by blast
          have g4: "get st4 (bpath bz) = Ok ub'" using ub'(1) w(3) z(5) by (simp add: get_def pext_def)
          have wu: "walk ub ss = Ok u" using wq wb z(5) by (simp add: pext_def walk_append)
          show ?thesis
          proof (cases "c = Out")
            case False
            with ub(2) have "vt P U ub" by simp
            from update_typed[OF this _ wu vv] z(6) KBorrow ub'(2) have "vt P U ub'" by auto
            with g4 KBorrow False show ?thesis by simp
          next
            case True
            with ub(2) have ov: "out_val P C \<sigma>2 U ub" by simp
            have "out_val P C \<sigma>2 U ub'"
            proof (cases "c_fields C = []")
              case True
              with ov have "vt P U ub" by (simp add: out_val_def)
              from update_typed[OF this _ wu vv] z(6) KBorrow ub'(2) have "vt P U ub'" by auto
              with True show ?thesis by (simp add: out_val_def)
            next
              case cf: False
              with ov obtain S0 where U0: "U = TStruct S0" by (auto simp: out_val_def)
              show ?thesis
            proof (cases ss)
              case Nil
              with ub'(2) wu g(2) z(6) KBorrow have "ub' = v" "T = U" by simp_all
              with out_val_replace[OF ov] vv show ?thesis by simp
            next
              case (Cons s1 rest)
              with z(6) KBorrow U0 obtain S f Uf where s1: "s1 = Fld f" "U = TStruct S"
                "field_ty P S f = Good Uf" "sty P Uf rest = Some T"
                by (cases s1) (auto split: ck.splits)
              have "out_val P C (\<sigma>2\<lparr>a_fields := insert f (a_fields \<sigma>2)\<rparr>) U ub'"
                using out_val_update[OF ov[unfolded s1(2)] s1(3,4) vv] ub'(2) wu g(2) Cons s1
                by simp
              then show ?thesis by (rule out_val_weaker) auto
            qed
            qed
            with g4 KBorrow True show ?thesis by simp
          qed
        next
          case (KRef T' og I)
          with z(3) show ?thesis by simp
        qed
      qed (use z res in auto)
    qed
  qed
qed

section \<open>Statements\<close>

fun simple_stmt :: "stmt \<Rightarrow> bool" where
  "simple_stmt SPass = True"
| "simple_stmt (SSeq a b) = (simple_stmt a \<and> simple_stmt b)"
| "simple_stmt (SVar _ _ eo) = (case eo of None \<Rightarrow> True | Some e \<Rightarrow> simple_expr e)"
| "simple_stmt (SRef _ e) = (case e of EPlace p \<Rightarrow> simple_place p | _ \<Rightarrow> False)"
| "simple_stmt (SAssign p e) = (simple_place p \<and> simple_expr e)"
| "simple_stmt (SExpr e) = simple_expr e"
| "simple_stmt (SPrint es) = simple_exprs es"
| "simple_stmt (SIf c a b) = (simple_expr c \<and> simple_stmt a \<and> simple_stmt b)"
| "simple_stmt (SWhile c b) = (simple_expr c \<and> simple_stmt b)"
| "simple_stmt (SReturn eo) = (case eo of None \<Rightarrow> True | Some e \<Rightarrow> simple_expr e)"
| "simple_stmt (SDrop p) = simple_place p"

text \<open>A returned result matches the declared result of the function.\<close>

definition ret_ok :: "prog \<Rightarrow> ret \<Rightarrow> state \<Rightarrow> rval \<Rightarrow> bool" where
  "ret_ok P rt st r \<longleftrightarrow> (case rt of
     RNone \<Rightarrow> r = RUnit
   | RVal T \<Rightarrow> (\<exists>v. r = RV v \<and> vt P T v)
   | RRef _ T \<Rightarrow> (\<exists>q v. r = RP q \<and> get st q = Ok v \<and> vt P T v))"

text \<open>
  After a statement that completes normally, the environment has grown by
  its declarations and the invariant holds for the checker's resulting
  static environment and abstract state. After a @{text "return"}, the
  invariant holds for the environment at that point (which the frame's
  cleanup destroys), and the result matches the declared one. After a
  block, its declarations are gone again.
\<close>

definition stmt_post :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate option \<Rightarrow> env \<Rightarrow>
                         outcome \<times> env \<times> state \<Rightarrow> bool" where
  "stmt_post P C \<Gamma>' o\<sigma> env r = (case r of (oc, env', st') \<Rightarrow> (case oc of
     Normal \<Rightarrow> \<exists>\<sigma>' \<Delta>. o\<sigma> = Some \<sigma>' \<and> env' = \<Delta> @ env \<and> inv P C \<Gamma>' \<sigma>' env' st'
   | Returned rv \<Rightarrow> (\<exists>\<Gamma>r \<sigma>r. inv P C \<Gamma>r \<sigma>r env' st') \<and> ret_ok P (c_ret C) st' rv))"

definition block_post :: "prog \<Rightarrow> ctx \<Rightarrow> senv \<Rightarrow> astate option \<Rightarrow> env \<Rightarrow>
                          outcome \<times> env \<times> state \<Rightarrow> bool" where
  "block_post P C \<Gamma> o\<sigma> env r = (case r of (oc, env', st') \<Rightarrow> (case oc of
     Normal \<Rightarrow> env' = env \<and> (\<exists>\<sigma>'. o\<sigma> = Some \<sigma>' \<and> inv P C \<Gamma> \<sigma>' env st')
   | Returned rv \<Rightarrow> (\<exists>\<Gamma>r \<sigma>r. inv P C \<Gamma>r \<sigma>r env' st') \<and> ret_ok P (c_ret C) st' rv))"

definition sound_stmt :: "prog \<Rightarrow> ctx \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_stmt P C n \<longleftrightarrow> (\<forall>\<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. inv P C \<Gamma> \<sigma> env st \<longrightarrow> simple_stmt s \<longrightarrow>
     chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<longrightarrow>
     spec (exec P n (c_ret C) env st s) (stmt_post P C \<Gamma>' o\<sigma> env))"

definition sound_block :: "prog \<Rightarrow> ctx \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_block P C n \<longleftrightarrow> (\<forall>\<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. inv P C \<Gamma> \<sigma> env st \<longrightarrow> simple_stmt s \<longrightarrow>
     chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<longrightarrow>
     spec (exec_block P n (c_ret C) env st s) (block_post P C \<Gamma> o\<sigma> env))"

subsection \<open>Expressions, restated\<close>

lemma expr_spec:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_expr e" "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'"
    "etype P \<Gamma> e = Good T"
  shows "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v)"
proof -
  have "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and> vt P T v)"
    using sound_all[OF assms(1), of \<Gamma> n] assms(2-) unfolding sound_expr_def by blast
  then show ?thesis by (rule spec_mono) auto
qed

lemma exprs_spec:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_exprs es" "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>'"
    "etypes P \<Gamma> es = Good Ts"
  shows "spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st')"
proof -
  have "spec (evals P n env st es) (\<lambda>(vs, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
           list_all2 (vt P) Ts vs)"
    using sound_all[OF assms(1), of \<Gamma> n] assms(2-) unfolding sound_exprs_def by blast
  then show ?thesis by (rule spec_mono) auto
qed

lemma place_spec:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_place p" "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>'"
    "ptype P \<Gamma> p = Good T" "root_ok C \<Gamma> \<sigma>' p = Good ()"
  shows "spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and>
           (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q)"
proof -
  have "spec (eval_place P n env st p) (\<lambda>(q, st'). inv P C \<Gamma> \<sigma>' env st' \<and> frame \<Gamma> env \<sigma>' st st' \<and>
           (\<exists>v. get st' q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q)"
    using sound_all[OF assms(1), of \<Gamma> n] assms(2-) unfolding sound_place_def by blast
  then show ?thesis by (rule spec_mono) auto
qed

lemma ty_init_spec:
  assumes "c_prog C = P" "inv P C \<Gamma> \<sigma> env st" "simple_expr e" "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>'"
    "ty_init P \<Gamma> T e = Good ()"
  shows "spec (eval P n env st e) (\<lambda>(v, st'). inv P C \<Gamma> \<sigma>' env st' \<and> vt P T v)"
  using sound_ty_init[OF sound_all[OF assms(1), THEN conjunct2, THEN conjunct1] assms(2-)] .

lemma join_opt_weaker:
  "o1 = Some \<sigma>a \<Longrightarrow> \<exists>\<sigma>''. join_opt o1 o2 = Some \<sigma>'' \<and> weaker \<sigma>'' \<sigma>a"
  "o2 = Some \<sigma>b \<Longrightarrow> \<exists>\<sigma>''. join_opt o1 o2 = Some \<sigma>'' \<and> weaker \<sigma>'' \<sigma>b"
  by (cases o1; cases o2; auto simp: weaker_join)+

subsection \<open>Blocks\<close>

lemma sound_block_Suc:
  assumes drops: "\<And>m. sound_drop P m" and IH: "sound_stmt P C n"
  shows "sound_block P C (Suc n)"
  unfolding sound_block_def
proof (intro allI impI)
  fix \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>
  assume inv: "inv P C \<Gamma> \<sigma> env st" and sim: "simple_stmt s" and chk: "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  from chk_stmt_extends(1)[OF chk] obtain \<Delta> where \<Delta>: "\<Gamma>' = \<Delta> @ \<Gamma>"
    "\<forall>(x, k) \<in> set \<Delta>. \<forall>c T. k \<noteq> KBorrow c T" by blast
  have ex: "spec (exec P n (c_ret C) env st s) (stmt_post P C \<Gamma>' o\<sigma> env)"
    using IH inv sim chk unfolding sound_stmt_def by blast
  show "spec (exec_block P (Suc n) (c_ret C) env st s) (block_post P C \<Gamma> o\<sigma> env)"
    unfolding exec_block.simps
  proof (rule spec_bind, rule spec_mono[OF ex], clarify)
    fix oc env' st' assume post: "stmt_post P C \<Gamma>' o\<sigma> env (oc, env', st')"
    show "spec (case oc of
                  Normal \<Rightarrow> bind_res (cleanup P n st' (take (length env' - length env) env'))
                              (\<lambda>st. Ok (Normal, env, st))
                | Returned r \<Rightarrow> Ok (Returned r, env', st')) (block_post P C \<Gamma> o\<sigma> env)"
    proof (cases oc)
      case Normal
      with post obtain \<sigma>' \<Delta>e where o: "o\<sigma> = Some \<sigma>'" "env' = \<Delta>e @ env"
        and inv': "inv P C (\<Delta> @ \<Gamma>) \<sigma>' (\<Delta>e @ env) st'"
        using \<Delta> by (auto simp: stmt_post_def)
      have len: "length \<Delta>e = length \<Delta>"
        using inv inv' by (auto simp: inv_def dest!: arg_cong[where f = length])
      have tk: "take (length env' - length env) env' = \<Delta>e" using o(2) by simp
      note F = inv_restrict_facts[OF inv' len \<Delta>(2)]
      have cl: "spec (cleanup P n st' \<Delta>e) (\<lambda>st''. nroot st' \<le> nroot st'' \<and> heap_fresh st'' \<and>
          (\<forall>r. r < nroot st' \<longrightarrow> r \<notin> owned_roots \<Delta>e \<longrightarrow> heap st'' r = heap st' r))"
        using cleanup_sound[OF drops F(7) inv_heap_fresh[OF inv']] .
      show ?thesis
        unfolding Normal outcome.case tk
      proof (rule spec_bind, rule spec_mono[OF cl])
        fix st'' assume h: "nroot st' \<le> nroot st'' \<and> heap_fresh st'' \<and>
          (\<forall>r. r < nroot st' \<longrightarrow> r \<notin> owned_roots \<Delta>e \<longrightarrow> heap st'' r = heap st' r)"
        then have "inv P C \<Gamma> \<sigma>' env st''" using inv_restrict[OF inv' len \<Delta>(2)] by blast
        with o show "spec (Ok (Normal, env, st'')) (block_post P C \<Gamma> o\<sigma> env)"
          by (auto simp: block_post_def)
      qed
    next
      case (Returned r)
      with post show ?thesis by (auto simp: stmt_post_def block_post_def) blast
    qed
  qed
qed

subsection \<open>Statements, by cases\<close>

lemma spec_Ok_iff [simp]: "spec (Ok a) Q \<longleftrightarrow> Q a"
  by (simp add: spec_def safe_def)

lemma spec_OutOfFuel_iff [simp]: "spec OutOfFuel Q"
  by (simp add: spec_def safe_def)

lemma sound_stmt_Suc:
  assumes CP: "c_prog C = P" and drops: "\<And>m. sound_drop P m"
    and IHs: "sound_stmt P C n" and IHb: "sound_block P C n"
  shows "sound_stmt P C (Suc n)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>
  assume inv: "inv P C \<Gamma> \<sigma> env st" and sim: "simple_stmt s" and chk: "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  have IHs': "\<And>\<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_stmt s \<Longrightarrow>
      chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<Longrightarrow> spec (exec P n (c_ret C) env st s) (stmt_post P C \<Gamma>' o\<sigma> env)"
    using IHs unfolding sound_stmt_def by blast
  have IHb': "\<And>\<Gamma> \<sigma> env st s \<Gamma>' o\<sigma>. inv P C \<Gamma> \<sigma> env st \<Longrightarrow> simple_stmt s \<Longrightarrow>
      chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>) \<Longrightarrow> spec (exec_block P n (c_ret C) env st s) (block_post P C \<Gamma> o\<sigma> env)"
    using IHb unfolding sound_block_def by blast
  have normal: "stmt_post P C \<Gamma>'' (Some \<sigma>'') env (Normal, env, st'')"
    if "inv P C \<Gamma>'' \<sigma>'' env st''" for \<Gamma>'' \<sigma>'' st''
    using that by (auto simp: stmt_post_def intro: exI[of _ "[]"])
  show "spec (exec P (Suc n) (c_ret C) env st s) (stmt_post P C \<Gamma>' o\<sigma> env)"
  proof (cases s)
    case SPass
    with chk inv normal show ?thesis by auto
  next
    case (SSeq a b)
    from chk SSeq obtain \<Gamma>1 o\<sigma>1 where ca: "chk_stmt C \<Gamma> \<sigma> a = Good (\<Gamma>1, o\<sigma>1)"
      and rest: "(case o\<sigma>1 of None \<Rightarrow> Good (\<Gamma>1, None) | Some \<sigma>1 \<Rightarrow> chk_stmt C \<Gamma>1 \<sigma>1 b) = Good (\<Gamma>', o\<sigma>)"
      by auto
    from sim SSeq have sa: "simple_stmt a" and sb: "simple_stmt b" by simp_all
    show ?thesis
      unfolding SSeq exec.simps stmt.case
    proof (rule spec_bind, rule spec_mono[OF IHs'[OF inv sa ca]], clarify)
      fix oc env1 st1 assume post: "stmt_post P C \<Gamma>1 o\<sigma>1 env (oc, env1, st1)"
      show "spec (case oc of Normal \<Rightarrow> exec P n (c_ret C) env1 st1 b
                  | Returned r \<Rightarrow> Ok (Returned r, env1, st1)) (stmt_post P C \<Gamma>' o\<sigma> env)"
      proof (cases oc)
        case Normal
        with post obtain \<sigma>1 \<Delta>1 where o1: "o\<sigma>1 = Some \<sigma>1" "env1 = \<Delta>1 @ env"
          and inv1: "inv P C \<Gamma>1 \<sigma>1 env1 st1" by (auto simp: stmt_post_def)
        with rest have cb: "chk_stmt C \<Gamma>1 \<sigma>1 b = Good (\<Gamma>', o\<sigma>)" by simp
        show ?thesis unfolding Normal outcome.case
          by (rule spec_mono[OF IHs'[OF inv1 sb cb]])
             (use o1 in \<open>auto simp: stmt_post_def split: outcome.splits\<close>)
      next
        case (Returned r)
        with post show ?thesis by (auto simp: stmt_post_def)
      qed
    qed
  next
    case (SVar x T eo)
    from chk SVar have x: "x \<notin> fst ` set \<Gamma>" by auto
    show ?thesis
    proof (cases eo)
      case None
      with chk SVar have o: "\<Gamma>' = (x, KOwned T) # \<Gamma>" "o\<sigma> = Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>)" by auto
      obtain r st2 where al: "alloc st VUndef = (r, st2)" by (cases "alloc st VUndef")
      have "inv P C ((x, KOwned T) # \<Gamma>) (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>) ((x, Own r) # env) st2"
        by (rule inv_alloc_owned[OF inv x al]) (auto simp: wt_opt_def)
      with o al None SVar show ?thesis
        by (auto simp: stmt_post_def intro!: exI[of _ "[(x, Own r)]"])
    next
      case (Some e)
      with chk SVar obtain \<sigma>1 where ti: "ty_init P \<Gamma> T e = Good ()" and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
        and o: "\<Gamma>' = (x, KOwned T) # \<Gamma>" "o\<sigma> = Some (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>)"
        using CP by auto
      from sim SVar Some have se: "simple_expr e" by simp
      show ?thesis
        unfolding SVar Some exec.simps stmt.case option.case
      proof (rule spec_bind, rule spec_mono_pair[OF ty_init_spec[OF CP inv se ce ti]], unfold prod.case)
        fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> vt P T v"
        obtain r st2 where al: "alloc st1 v = (r, st2)" by (cases "alloc st1 v")
        have "inv P C ((x, KOwned T) # \<Gamma>) (\<sigma>1\<lparr>a_init := insert x (a_init \<sigma>1)\<rparr>) ((x, Own r) # env) st2"
          by (rule inv_alloc_owned[OF h[THEN conjunct1] x al]) (use h in auto)
        with o al show "spec (case alloc st1 v of (r, st) \<Rightarrow> Ok (Normal, (x, Own r) # env, st))
            (stmt_post P C \<Gamma>' o\<sigma> env)"
          by (auto simp: stmt_post_def intro!: exI[of _ "[(x, Own r)]"])
      qed
    qed
  next
    case (SRef x e)
    from sim SRef obtain p where e: "e = EPlace p" and sp: "simple_place p"
      by (cases e) auto
    from chk SRef e obtain \<sigma>1 T where x: "x \<notin> fst ` set \<Gamma>" and ci: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
      and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and pt: "ptype P \<Gamma> p = Good T"
      and o: "\<Gamma>' = (x, KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)) # \<Gamma>" "o\<sigma> = Some \<sigma>1"
      using CP by auto
    have og: "place_origin \<Gamma> p \<subseteq> fst ` set \<Gamma>"
      using place_origin_dom[of \<Gamma> p] inv ro by (auto simp: inv_def root_ok_def Let_def split: option.splits)
    show ?thesis
    proof (cases n)
      case 0
      with SRef e show ?thesis by simp
    next
      case (Suc m)
      show ?thesis
        unfolding SRef e exec.simps stmt.case Suc eval_ref.simps expr.case
      proof (rule spec_bind, rule spec_mono_pair[OF place_spec[OF CP inv sp ci pt ro]], unfold prod.case)
        fix q st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> (\<exists>v. get st1 q = Ok v \<and> vt P T v) \<and> ploc P \<Gamma> env p T q"
        then obtain v where "get st1 q = Ok v" "vt P T v" by blast
        from inv_add_ref[OF h[THEN conjunct1] x _ this og] h
        have "inv P C ((x, KRef T (place_origin \<Gamma> p) (place_interior \<Gamma> p)) # \<Gamma>) \<sigma>1 ((x, Bor q) # env) st1"
          by blast
        with o show "spec (Ok (Normal, (x, Bor q) # env, st1)) (stmt_post P C \<Gamma>' o\<sigma> env)"
          by (auto simp: stmt_post_def intro!: exI[of _ "[(x, Bor q)]"])
      qed
    qed
  next
    case (SAssign p e)
    from chk SAssign obtain T \<sigma>1 \<sigma>' where pt: "ptype P \<Gamma> p = Good T" and ti: "ty_init P \<Gamma> T e = Good ()"
      and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" and ca: "chk_assign C \<Gamma> \<sigma>1 p T = Good \<sigma>'"
      and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>'"
      using CP by auto
    from sim SAssign have sp: "simple_place p" and se: "simple_expr e" by simp_all
    show ?thesis
      unfolding SAssign exec.simps stmt.case
    proof (rule spec_bind, rule spec_mono_pair[OF ty_init_spec[OF CP inv se ce ti]], unfold prod.case)
      fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> vt P T v"
      show "spec (do { (q, st) \<leftarrow> eval_place P n env st1 p; st \<leftarrow> drop_path P n st q;
                       st \<leftarrow> put st q v; Ok (Normal, env, st) }) (stmt_post P C \<Gamma>' o\<sigma> env)"
        by (rule spec_mono[OF assign_core[OF CP drops h[THEN conjunct1] h[THEN conjunct2] sp pt ca]])
           (use o normal in auto)
    qed
  next
    case (SExpr e)
    from chk SExpr obtain T \<sigma>1 where et: "etype P \<Gamma> e = Good T" and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1"
      and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>1"
      using CP by auto
    from sim SExpr have se: "simple_expr e" by simp
    show ?thesis
      unfolding SExpr exec.simps stmt.case
    proof (rule spec_bind, rule spec_mono_pair[OF expr_spec[OF CP inv se ce et]], unfold prod.case)
      fix v st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> vt P T v"
      obtain r st2 where al: "alloc st1 v = (r, st2)" by (cases "alloc st1 v")
      have r: "r = nroot st1" "heap st2 = (heap st1)(r := Some v)" "nroot st2 = Suc (nroot st1)"
        using al by (auto simp: alloc_def)
      have fr1: "heap_fresh st1" using h inv_heap_fresh by blast
      have fr2: "heap_fresh st2" using fr1 r by (auto simp: heap_fresh_def)
      have g: "get st2 (r, []) = Ok v" using r by (simp add: get_def)
      show "spec (case alloc st1 v of (r, st) \<Rightarrow>
                    bind_res (drop_path P n st (r, [])) (\<lambda>st. Ok (Normal, env, free st r)))
                 (stmt_post P C \<Gamma>' o\<sigma> env)"
        unfolding al prod.case
      proof (rule spec_bind, rule spec_mono[OF drop_spec[OF drops g _ fr2]])
        show "wt_opt P T v" using h by (simp add: wt_opt_def)
        fix st3 assume d: "drop_post st2 (r, []) st3"
        have "inv P C \<Gamma> \<sigma>1 env (free st3 r)"
        proof (rule inv_heap_frame[OF h[THEN conjunct1]])
          show "\<forall>r'. r' < nroot st1 \<longrightarrow> heap (free st3 r) r' = heap st1 r'"
            using d r by (auto simp: drop_post_def free_def)
          show "nroot st1 \<le> nroot (free st3 r)" using d r by (auto simp: drop_post_def free_def)
          show "heap_fresh (free st3 r)" using d by (auto simp: drop_post_def heap_fresh_def free_def)
        qed
        with o normal show "spec (Ok (Normal, env, free st3 r)) (stmt_post P C \<Gamma>' o\<sigma> env)" by simp
      qed
    qed
  next
    case (SPrint es)
    from chk SPrint obtain Ts \<sigma>1 where et: "etypes P \<Gamma> es = Good Ts"
      and ce: "chk_exprs C \<Gamma> \<sigma> es = Good \<sigma>1" and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some \<sigma>1"
      using CP by auto
    from sim SPrint have se: "simple_exprs es" by simp
    show ?thesis
      unfolding SPrint exec.simps stmt.case
      by (rule spec_bind, rule spec_mono_pair[OF exprs_spec[OF CP inv se ce et]])
         (use o normal in auto)
  next
    case (SIf c a b)
    from chk SIf obtain \<sigma>1 \<Gamma>a o1 \<Gamma>b o2 where et: "etype P \<Gamma> c = Good TBool"
      and cc: "chk_expr C \<Gamma> \<sigma> c = Good \<sigma>1" and ca: "chk_stmt C \<Gamma> \<sigma>1 a = Good (\<Gamma>a, o1)"
      and cb: "chk_stmt C \<Gamma> \<sigma>1 b = Good (\<Gamma>b, o2)" and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = join_opt o1 o2"
      using CP by auto
    from sim SIf have sc: "simple_expr c" and sa: "simple_stmt a" and sb: "simple_stmt b" by simp_all
    show ?thesis
      unfolding SIf exec.simps stmt.case
    proof (rule spec_bind, rule spec_mono_pair[OF expr_spec[OF CP inv sc cc et]], unfold prod.case)
      fix cv st1 assume h: "inv P C \<Gamma> \<sigma>1 env st1 \<and> vt P TBool cv"
      then obtain bb where cv: "cv = VBool bb" by (cases cv) auto
      have blk: "spec (exec_block P n (c_ret C) env st1 (if bb then a else b))
                   (block_post P C \<Gamma> (if bb then o1 else o2) env)"
        using IHb'[OF h[THEN conjunct1]] sa sb ca cb by (cases bb) auto
      have "spec (exec_block P n (c_ret C) env st1 (if bb then a else b)) (stmt_post P C \<Gamma>' o\<sigma> env)"
      proof (rule spec_mono[OF blk], clarify)
        fix oc env' st' assume bp: "block_post P C \<Gamma> (if bb then o1 else o2) env (oc, env', st')"
        show "stmt_post P C \<Gamma>' o\<sigma> env (oc, env', st')"
        proof (cases oc)
          case Normal
          with bp obtain \<sigma>i where e': "env' = env" and oi: "(if bb then o1 else o2) = Some \<sigma>i"
            and ii: "inv P C \<Gamma> \<sigma>i env st'" by (auto simp: block_post_def)
          obtain \<sigma>'' where j: "join_opt o1 o2 = Some \<sigma>''" "weaker \<sigma>'' \<sigma>i"
            using join_opt_weaker[of o1 \<sigma>i o2] join_opt_weaker(2)[of o2 \<sigma>i o1] oi
            by (cases bb) auto
          with ii e' o Normal normal[OF inv_weaken[OF ii j(2)]] show ?thesis by simp
        next
          case (Returned r)
          with bp show ?thesis by (auto simp: block_post_def stmt_post_def)
        qed
      qed
      with cv show "spec (case cv of VBool b' \<Rightarrow> exec_block P n (c_ret C) env st1 (if b' then a else b)
                          | _ \<Rightarrow> Err (ErrType ''if condition'')) (stmt_post P C \<Gamma>' o\<sigma> env)"
        by simp
    qed
  next
    case (SWhile c b)
    from chk SWhile obtain o\<sigma>' where et: "etype P \<Gamma> c = Good TBool"
      and cl: "chk_loop (Suc (Suc (length \<Gamma> + size b + length (c_fields C)))) C \<Gamma> \<sigma> c b = Good o\<sigma>'"
      and o: "\<Gamma>' = \<Gamma>" "o\<sigma> = o\<sigma>'"
      using CP by (simp only: chk_stmt.simps bind_ck_Good_iff check_Good_iff ck.inject prod.inject) blast
    from chk_loop_fix[OF cl] obtain \<sigma>f \<sigma>c \<Gamma>b ob where w: "weaker \<sigma>f \<sigma>"
      and cc: "chk_expr C \<Gamma> \<sigma>f c = Good \<sigma>c" and cb: "chk_stmt C \<Gamma> \<sigma>c b = Good (\<Gamma>b, ob)"
      and j: "join_opt (Some \<sigma>f) ob = Some \<sigma>f" and os: "o\<sigma>' = Some \<sigma>c" by blast
    from sim SWhile have sc: "simple_expr c" and sb: "simple_stmt b" by simp_all
    have invf: "inv P C \<Gamma> \<sigma>f env st" using inv_weaken[OF inv w] .
    have again: "chk_stmt C \<Gamma> \<sigma>f (SWhile c b) = Good (\<Gamma>, Some \<sigma>c)"
      using et CP chk_loop_stable[OF cc cb j] by simp
    show ?thesis
      unfolding SWhile exec.simps stmt.case
    proof (rule spec_bind, rule spec_mono_pair[OF expr_spec[OF CP invf sc cc et]], unfold prod.case)
      fix cv st1 assume h: "inv P C \<Gamma> \<sigma>c env st1 \<and> vt P TBool cv"
      then obtain bb where cv: "cv = VBool bb" by (cases cv) auto
      show "spec (case cv of
                    VBool True \<Rightarrow> bind_res (exec_block P n (c_ret C) env st1 b)
                      (\<lambda>(oc, env', st). case oc of Normal \<Rightarrow> exec P n (c_ret C) env st (SWhile c b)
                                         | Returned r \<Rightarrow> Ok (Returned r, env', st))
                  | VBool False \<Rightarrow> Ok (Normal, env, st1)
                  | _ \<Rightarrow> Err (ErrType ''while condition'')) (stmt_post P C \<Gamma>' o\<sigma> env)"
      proof (cases bb)
        case False
        with cv h o os normal show ?thesis by simp
      next
        case True
        then have bbT: "bb = True" by simp
        show ?thesis
          unfolding cv bbT val.case bool.case
        proof (rule spec_bind, rule spec_mono[OF IHb'[OF h[THEN conjunct1] sb cb]], clarify)
          fix oc env' st2 assume bp: "block_post P C \<Gamma> ob env (oc, env', st2)"
          show "spec (case oc of Normal \<Rightarrow> exec P n (c_ret C) env st2 (SWhile c b)
                      | Returned r \<Rightarrow> Ok (Returned r, env', st2)) (stmt_post P C \<Gamma>' o\<sigma> env)"
          proof (cases oc)
            case Normal
            with bp obtain \<sigma>b where e': "env' = env" and ob: "ob = Some \<sigma>b"
              and ib: "inv P C \<Gamma> \<sigma>b env st2" by (auto simp: block_post_def)
            have "weaker \<sigma>f \<sigma>b" using join_opt_Some_weaker[OF j] ob by blast
            then have i2: "inv P C \<Gamma> \<sigma>f env st2" by (rule inv_weaken[OF ib])
            from IHs'[OF i2 _ again] sim SWhile e' o os Normal show ?thesis by simp
          next
            case (Returned r)
            with bp show ?thesis by (auto simp: block_post_def stmt_post_def)
          qed
        qed
      qed
    qed
  next
    case (SReturn eo)
    show ?thesis
    proof (cases eo)
      case None
      with chk SReturn have o: "c_ret C = RNone" "o\<sigma> = None" by auto
      with None SReturn inv show ?thesis by (auto simp: stmt_post_def ret_ok_def)
    next
      case (Some e)
      from sim SReturn Some have se: "simple_expr e" by simp
      show ?thesis
      proof (cases "c_ret C")
        case RNone
        with chk SReturn Some show ?thesis by simp
      next
        case (RVal T)
        with chk SReturn Some obtain \<sigma>1 where ti: "ty_init P \<Gamma> T e = Good ()"
          and ce: "chk_expr C \<Gamma> \<sigma> e = Good \<sigma>1" using CP by auto
        show ?thesis
          unfolding SReturn Some exec.simps stmt.case option.case RVal ret.case
          by (rule spec_bind, rule spec_mono_pair[OF ty_init_spec[OF CP inv se ce ti]])
             (use RVal in \<open>auto simp: stmt_post_def ret_ok_def\<close>)
      next
        case (RRef ns T)
        with chk SReturn Some obtain p \<sigma>1 where e: "e = EPlace p" and ci: "chk_idx C \<Gamma> \<sigma> p = Good \<sigma>1"
          and ro: "root_ok C \<Gamma> \<sigma>1 p = Good ()" and pt: "ptype P \<Gamma> p = Good T"
          using CP by (auto split: expr.splits)
        from se e have sp: "simple_place p" by simp
        show ?thesis
        proof (cases n)
          case 0
          with SReturn Some RRef e show ?thesis by simp
        next
          case (Suc m)
          show ?thesis
            unfolding SReturn Some exec.simps stmt.case option.case RRef ret.case e Suc
              eval_ref.simps expr.case
            by (rule spec_bind, rule spec_mono_pair[OF place_spec[OF CP inv sp ci pt ro]])
               (use RRef in \<open>auto simp: stmt_post_def ret_ok_def\<close>)
        qed
      qed
    qed
  next
    case (SDrop p)
    from chk SDrop have c: "chk_stmt C \<Gamma> \<sigma> (SDrop p) = Good (\<Gamma>', o\<sigma>)" by simp
    obtain x where p: "p = PVar x" using c by (cases p) simp_all
    obtain U where xU: "map_of \<Gamma> x = Some (KOwned U)"
      using c p by (cases "map_of \<Gamma> x"; cases "the (map_of \<Gamma> x)") auto
    have o: "\<Gamma>' = \<Gamma>" "o\<sigma> = Some (\<sigma>\<lparr>a_init := a_init \<sigma> - {x}\<rparr>)" using c p xU by simp_all
    from inv_binding[OF inv xU] obtain r w where r: "map_of env x = Some (Own r)"
      "heap st r = Some w" "if x \<in> a_init \<sigma> then vt P U w else wt_opt P U w" by auto
    have g: "get st (r, []) = Ok w" "wt_opt P U w" using r by (auto simp: get_def wt_opt_def split: if_splits)
    have dr: "spec (bind_res (drop_path P n st (r, [])) (\<lambda>st. Ok (Normal, env, st))) (stmt_post P C \<Gamma>' o\<sigma> env)"
    proof (rule spec_bind, rule spec_mono[OF drop_spec[OF drops g inv_heap_fresh[OF inv]]])
      fix st2 assume "drop_post st (r, []) st2"
      from inv_drop_var[OF inv xU r(1) this] o normal
      show "spec (Ok (Normal, env, st2)) (stmt_post P C \<Gamma>' o\<sigma> env)" by simp
    qed
    show ?thesis
      unfolding SDrop exec.simps stmt.case p
      using dr r by (cases n) (simp_all add: eval_place_PVar)
  qed
qed

subsection \<open>The soundness theorem for statements\<close>

lemma sound_stmt_block:
  assumes "c_prog C = P" "\<And>m. sound_drop P m"
  shows "sound_stmt P C n \<and> sound_block P C n"
proof (induction n)
  case 0
  show ?case by (simp add: sound_stmt_def sound_block_def)
next
  case (Suc n)
  then show ?case using sound_stmt_Suc[OF assms] sound_block_Suc[OF assms(2)] by blast
qed

text \<open>
  A call-free statement accepted by the checker, executed in a state that
  satisfies the invariant, goes wrong at most with @{text "ErrBounds"}. If
  it completes normally, the invariant holds for the checker's resulting
  state; if it returns, the result has the declared type. This assumes
  @{text "sound_drop"}, the specification of destruction, which the part on
  calls will prove.
\<close>

theorem stmt_sound:
  assumes "c_prog C = P" "\<And>m. sound_drop P m"
    and "inv P C \<Gamma> \<sigma> env st" "simple_stmt s" "chk_stmt C \<Gamma> \<sigma> s = Good (\<Gamma>', o\<sigma>)"
  shows "safe (exec P n (c_ret C) env st s)"
    and "exec P n (c_ret C) env st s = Ok r \<Longrightarrow> stmt_post P C \<Gamma>' o\<sigma> env r"
proof -
  have "spec (exec P n (c_ret C) env st s) (stmt_post P C \<Gamma>' o\<sigma> env)"
    using sound_stmt_block[OF assms(1,2), of n] assms(3-) unfolding sound_stmt_def by blast
  then show "safe (exec P n (c_ret C) env st s)"
    and "exec P n (c_ret C) env st s = Ok r \<Longrightarrow> stmt_post P C \<Gamma>' o\<sigma> env r"
    by (auto simp: spec_def)
qed

section \<open>Next steps\<close>

text \<open>
  What remains for the soundness of whole programs:
  ┌ \<^bold>\<open>Calls\<close> (@{text "ECall"}, @{text "EMeth"}, reference-returning calls in
    @{text "ref"} bindings). The callee's invariant is built from the
    arguments; argument exclusivity provides @{text "excl"} for its
    borrowed parameters. On return, the caller's invariant is restored
    because the callee changed only memory below its writable parameters
    and fresh roots. This needs a frame condition for statements, which
    @{text "stmt_post"} does not yet state.
  ┌ \<^bold>\<open>List methods\<close> change generations; the invariant must additionally
    say that every generation in the heap is below @{text "ngen"}.
  ┌ \<^bold>\<open>Destruction\<close>: proving @{text "sound_drop"}, which runs
    @{text "__deinit__"} bodies, by the same induction on the fuel.
  ┌ \<^bold>\<open>The elaboration\<close>: showing that the inserted @{text "DROP"}s keep
    programs accepted by the checker.
\<close>

end
