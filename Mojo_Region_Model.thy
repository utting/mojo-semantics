(*
  Mojo_Region_Model.thy

  A formal model of the "region"-based memory-safety proposal described by
  nmsmith in the gist

    "An alternative model for 'lifetimes' in Mojo"
    https://gist.github.com/nmsmith/cdaa94aa74e8e0611221e65db8e41f7b

  including the clarifications given in the comment thread on that gist,
  in particular the exchange between nmsmith, seanbaxter and verdagon about
  *why* regions must satisfy two distinct disjointness conditions
  (comments 5272844, 5277073, 5278468, 5278470), and the pointer to
  "InvalML" (Gao & Parreaux, OOPSLA 2025) and the Rust NLL model raised by
  MattPD and seanbaxter.

  Author's own disclaimer applies here even more strongly than to the
  original gist: the gist itself is explicitly an *early design sketch*,
  not a specification ("The 'regions' that I present in this document have
  not been given a formal semantics, and I have not explained where they
  originate from"). What follows is therefore not a transcription of an
  existing formal semantics, but a *first attempt at inventing one* that is
  faithful to the informal description and to the follow-up clarifications
  in the comments. Every section below documents the choices made and the
  alternatives that were considered but not taken.
*)

theory Mojo_Region_Model
  imports Main
begin

section \<open>Overview\<close>

text \<open>
  The gist's central move is to re-interpret a Rust/Mojo "lifetime"
  (nowadays "origin") not as an opaque token tracking a memory range, but
  as a first-class, *typed* compile-time value denoting a \<^emph>\<open>set of
  variables\<close> that a pointer might target. On top of that single idea, the
  gist builds:

    (1) a dereference-safety discipline based on tracking, for every
        variable in a region, whether it is currently initialized;

    (2) a model of \<^emph>\<open>dynamic containers\<close> (resizable buffers such as
        @{text List} and tagged unions such as @{text Variant}) whose
        item regions are invalidated precisely when the container's
        \<^emph>\<open>shape\<close> (not merely its items) is mutated;

    (3) a replacement for Rust's "aliasing XOR mutability" rule on
        individual references by an analogous rule applied to \<^emph>\<open>region
        parameters\<close> of function signatures: a region that is mutated
        must be disjoint from every other region parameter, while
        pointers that share the \<^emph>\<open>same\<close> region parameter may alias
        (even mutably) with no restriction at all;

    (4) a shift of "mutability" from being a property of a pointer/origin
        \<^emph>\<open>type\<close> to being an \<^emph>\<open>effect\<close> that a function declares, so that
        trait conformance cannot silently add a mutation requirement that
        the trait itself does not declare.

  This theory formalizes each of these four ingredients as a separate
  part, reusing one common notion of "region" (Part 1) throughout. Parts
  are intentionally kept as independent as possible: a reader interested
  only in, say, the dynamic-container invalidation model (Part 3) does not
  need to follow the ownership-tree machinery of Part 1 in detail (only
  the definitions of \<^const>\<open>True\<close>/\<^const>\<open>False\<close>-valued stores are shared
  with Part 2).

  \<^bold>\<open>What is deliberately *not* attempted.\<close> The gist is explicit that it is
  a "high-level overview, not a specification", and several aspects are
  left as open questions even informally (how @{text Variant} should be
  modelled as a dynamic container; whether non-reallocating containers
  such as @{text InlineFixedVector} can avoid invalidating pointers on
  @{text append}; what "invalidation" actually does operationally). This
  theory does not resolve those open questions either -- it builds a
  model that is precise enough to \<^emph>\<open>state\<close> them, and comments on how each
  could plausibly be accommodated. See the final section,
  "Limitations, open questions, and alternative formal approaches".
\<close>



section \<open>Part 1: Regions as sets of variables, and the ownership tree\<close>

text \<open>
  \<^bold>\<open>Decision.\<close> The gist repeatedly stresses that a region must be
  understood as denoting a \<^emph>\<open>set of variables\<close>, not a range of memory
  addresses -- and that this distinction has real teeth, because a
  variable can \<^emph>\<open>own\<close> other variables (a struct owns its fields; a list
  owns its elements). This ownership structure is what later lets us
  define two genuinely different notions of "disjoint": disjoint as
  \<^emph>\<open>sets\<close> of variable-names versus disjoint as \<^emph>\<open>memory footprints\<close>. The
  comment thread (5278468, 5278470) makes this precise: regions
  @{text "{thing}"} and @{text "{thing.x}"} are disjoint as sets (they are
  literally different variables) but \<^emph>\<open>not\<close> disjoint as memory, because
  @{text "thing.x"} lives inside @{text thing}.

  To capture this we need, underneath the notion of "region", a model of
  which variables own which other variables. We use an abstract type
  @{text "'l"} of \<^emph>\<open>locations\<close> (one location per variable: a local, a
  field, or a list element, exactly as in the gist's definition of
  "variable") together with a single \<^emph>\<open>direct ownership\<close> function

    @{text "owner :: 'l \<Rightarrow> 'l option"}

  where @{text "owner c = Some p"} means "@{text c} is directly owned by
  (nested one level inside) @{text p}" -- e.g. @{text c} is a field of the
  struct @{text p}, or @{text c} is an item of the list @{text p}.
  @{text "owner c = None"} means @{text c} is a top-level variable with no
  enclosing owner.

  \<^bold>\<open>Alternative not taken.\<close> One could instead axiomatize the ownership
  structure as a general relation @{text "owned_by :: ('l \<times> 'l) set"},
  without requiring that every location have \<^emph>\<open>at most one\<close> direct owner.
  We reject this: in the source model every variable is a well-defined
  piece of syntax (a field-access path, a list-index expression, etc.)
  with a unique immediately-enclosing variable, so direct ownership really
  is functional. Modelling it as a function (rather than an arbitrary
  relation) is both more faithful and, as shown below, essential to the
  cheap proof of the "ancestors of a variable form a chain" lemma that
  underlies the rest of Part 1.

  \<^bold>\<open>On well-formedness.\<close> One might expect we additionally need to
  \<^emph>\<open>assume\<close> that @{text owner} is acyclic (nothing owns itself, directly
  or indirectly), mirroring the fact that, physically, a struct cannot
  contain itself. Perhaps surprisingly, none of the lemmas below require
  this as a global hypothesis: the central disjointness result
  (@{text wf_region_footprint_disjoint}) only needs the *local*
  non-containment hypothesis between the two specific variables in
  question, and that hypothesis is already part of the definition of a
  "well-formed region" that the gist's Rule 1 imposes. We still flag, as a
  sanity check, that if @{text owner} genuinely contains a cycle then no
  region containing both of the cyclic variables can be well-formed (as it
  should be) -- see @{text demo_cycle_is_never_wellformed} near the end of
  this part.
\<close>

locale mojo_regions =
  fixes owner :: "'l \<Rightarrow> 'l option"
begin

text \<open>
  \<^bold>\<open>Ancestry chains.\<close> We define, for each @{text n}, the result of
  following @{text owner} exactly @{text n} times starting from a
  location @{text v}. This "operational" definition (iterate the partial
  function) is chosen over the perhaps more standard "take the transitive
  closure of the @{text owned_by} relation" definition because it makes
  the forthcoming linearity lemma (ancestors of a common descendant are
  totally ordered by containment) a two-line consequence of elementary
  arithmetic on the iteration count @{text n}, rather than requiring an
  induction on the transitive closure combined with a separate
  single-valuedness argument. The two definitions agree extensionally
  (one could prove @{text "strictly_contains p v \<longleftrightarrow> (v, p) \<in> {(c,p). owner c = Some p}\<^sup>+"}
  as a sanity check; we omit this since it is not needed below and would
  only duplicate the linearity proof).
\<close>

primrec ancestor_at :: "nat \<Rightarrow> 'l \<Rightarrow> 'l option" where
  "ancestor_at 0 v = Some v"
| "ancestor_at (Suc n) v =
     (case ancestor_at n v of None \<Rightarrow> None | Some p \<Rightarrow> owner p)"

text \<open>
  @{text "strictly_contains p v"} means: @{text p} is a \<^emph>\<open>strict\<close> ancestor
  of @{text v} in the ownership tree, i.e. @{text v} is nested somewhere
  (at depth \<open>\<ge> 1\<close>) inside @{text p}. This is the formal counterpart of
  phrases like "the ownership tree of @{text thing}" in the gist's
  discussion.
\<close>

definition strictly_contains :: "'l \<Rightarrow> 'l \<Rightarrow> bool" where
  "strictly_contains p v \<longleftrightarrow> (\<exists>n. ancestor_at (Suc n) v = Some p)"

text \<open>
  The \<^emph>\<open>footprint\<close> of a variable @{text v} is @{text v} together with
  everything it (transitively) owns -- i.e. all the memory that destroying
  or moving @{text v} would also destroy or move. This is the "memory"
  reading of a variable, as opposed to its bare identity as a set element.
\<close>

definition footprint :: "'l \<Rightarrow> 'l set" where
  "footprint v = {c. c = v \<or> strictly_contains v c}"

text \<open>
  The footprint of a \<^emph>\<open>region\<close> (a set of variables) is the union of the
  footprints of its members. This is the set of all memory addresses that
  \<^emph>\<open>some\<close> variable in the region owns.
\<close>

definition region_footprint :: "'l set \<Rightarrow> 'l set" where
  "region_footprint R = (\<Union>v\<in>R. footprint v)"

lemma mem_footprint_self [simp]: "v \<in> footprint v"
  unfolding footprint_def by simp

lemma region_subset_footprint: "R \<subseteq> region_footprint R"
  unfolding region_footprint_def using mem_footprint_self by blast

text \<open>
  \<^bold>\<open>Two notions of disjointness.\<close> This is the crux of the 5278470
  comment: a region, understood purely as a mathematical \<^emph>\<open>set\<close> of
  variable-names, can be disjoint from another region as sets while still
  overlapping as memory (because one region's variable owns the other
  region's variable). We therefore introduce two predicates:

    \<^item> @{text set_disjoint}: the regions share no \<^emph>\<open>variable\<close> (disjoint as
      sets of names);
    \<^item> @{text mem_disjoint}: the regions' \<^emph>\<open>footprints\<close> do not overlap
      (disjoint as memory).

  @{text mem_disjoint} is the strictly stronger, and semantically
  relevant, notion whenever we care about aliasing of the underlying
  storage (Rule 2 in Part 4 below). @{text set_disjoint} is included
  because it is the \<^emph>\<open>naive\<close> reading that one might mistakenly reach for,
  and because making the gap between the two explicit is exactly what the
  gist's comment thread asked for.
\<close>

definition set_disjoint :: "'l set \<Rightarrow> 'l set \<Rightarrow> bool" where
  "set_disjoint R1 R2 \<longleftrightarrow> R1 \<inter> R2 = {}"

definition mem_disjoint :: "'l set \<Rightarrow> 'l set \<Rightarrow> bool" where
  "mem_disjoint R1 R2 \<longleftrightarrow> region_footprint R1 \<inter> region_footprint R2 = {}"

lemma mem_disjoint_imp_set_disjoint:
  assumes "mem_disjoint R1 R2"
  shows "set_disjoint R1 R2"
proof -
  from assms have "region_footprint R1 \<inter> region_footprint R2 = {}"
    unfolding mem_disjoint_def .
  moreover have "R1 \<subseteq> region_footprint R1" "R2 \<subseteq> region_footprint R2"
    by (rule region_subset_footprint)+
  ultimately show ?thesis unfolding set_disjoint_def by blast
qed

text \<open>
  The converse of @{text mem_disjoint_imp_set_disjoint} is false in
  general: this is exactly the @{text "{thing}"} / @{text "{thing.x}"}
  example from the comments, worked out concretely below
  (@{text demo_set_disjoint_not_mem_disjoint}).
\<close>

subsection \<open>The forest property: well-formed regions have disjoint footprints\<close>

text \<open>
  We now derive the lemma that justifies the gist's first disjointness
  rule, as clarified in comment 5278468 ("Rule 1"): "Given a pair of
  variables in a region, e.g. @{text "{x, y}"}, neither variable is
  allowed to be a container that stores the other variable as an
  element." We call a region satisfying this \<^emph>\<open>well-formed\<close>
  (@{text wf_region}), and show that well-formed regions automatically
  have pairwise disjoint footprints. This is exactly why the rule is
  needed: it is what makes two pointers drawn from a region such as
  @{text "{x, y}"} genuinely independent in memory, so that (as the gist
  puts it) "mutating one pointee cannot trigger the deallocation of the
  other pointee".

  The key technical fact underneath this is that the strict ancestors of
  any fixed variable @{text v} are totally ordered by
  @{text strictly_contains}: you cannot have two "incomparable"
  containers that both directly or indirectly own the same @{text v},
  because direct ownership is a \<^emph>\<open>function\<close> (every variable has at most
  one direct owner). We prove this (@{text ancestors_linear}) as a short
  consequence of the following compositionality property of
  @{text ancestor_at}: following the ownership chain for @{text "n + m"}
  steps is the same as following it for @{text n} steps and then, if that
  succeeds, continuing for @{text m} more steps. This is associativity
  of Kleisli composition for the partial function @{text owner}, and it
  holds \<^emph>\<open>unconditionally\<close> -- no acyclicity assumption on @{text owner}
  is needed anywhere in this development; see the remark near the top of
  this part about why @{text wf_region}'s local hypothesis is doing all
  the necessary work.
\<close>

lemma ancestor_at_add:
  "ancestor_at (n + m) v =
     (case ancestor_at n v of None \<Rightarrow> None | Some w \<Rightarrow> ancestor_at m w)"
proof (induct m)
  case 0
  show ?case by (cases "ancestor_at n v") simp_all
next
  case (Suc m)
  then show ?case by (cases "ancestor_at n v") simp_all
qed

lemma ancestors_linear:
  assumes "strictly_contains p1 v" "strictly_contains p2 v"
  shows "p1 = p2 \<or> strictly_contains p1 p2 \<or> strictly_contains p2 p1"
proof -
  from assms obtain n1 n2
    where n1: "ancestor_at (Suc n1) v = Some p1"
      and n2: "ancestor_at (Suc n2) v = Some p2"
    unfolding strictly_contains_def by blast
  have "n1 \<le> n2 \<or> n2 \<le> n1" by (rule nat_le_linear)
  then show ?thesis
  proof
    assume "n1 \<le> n2"
    then obtain k where k: "n2 = n1 + k" using le_Suc_ex by blast
    have "Some p2 = ancestor_at (Suc n1 + k) v"
      using n2 by (simp add: k)
    also have "\<dots> = (case ancestor_at (Suc n1) v of None \<Rightarrow> None | Some w \<Rightarrow> ancestor_at k w)"
      by (rule ancestor_at_add)
    also have "\<dots> = ancestor_at k p1" by (subst n1) simp
    finally have eq: "ancestor_at k p1 = Some p2" by simp
    show ?thesis
    proof (cases k)
      case 0
      with eq show ?thesis by simp
    next
      case (Suc k')
      with eq show ?thesis unfolding strictly_contains_def by auto
    qed
  next
    assume "n2 \<le> n1"
    then obtain k where k: "n1 = n2 + k" using le_Suc_ex by blast
    have "Some p1 = ancestor_at (Suc n2 + k) v"
      using n1 by (simp add: k)
    also have "\<dots> = (case ancestor_at (Suc n2) v of None \<Rightarrow> None | Some w \<Rightarrow> ancestor_at k w)"
      by (rule ancestor_at_add)
    also have "\<dots> = ancestor_at k p2" by (subst n2) simp
    finally have eq: "ancestor_at k p2 = Some p1" by simp
    show ?thesis
    proof (cases k)
      case 0
      with eq show ?thesis by simp
    next
      case (Suc k')
      with eq show ?thesis unfolding strictly_contains_def by auto
    qed
  qed
qed

text \<open>
  @{text wf_region} formalizes Rule 1: a region is well-formed when no
  two of its (distinct) members stand in the @{text strictly_contains}
  relation in either direction.
\<close>

definition wf_region :: "'l set \<Rightarrow> bool" where
  "wf_region R \<longleftrightarrow>
     (\<forall>x\<in>R. \<forall>y\<in>R. x \<noteq> y \<longrightarrow> \<not> strictly_contains x y \<and> \<not> strictly_contains y x)"

text \<open>
  This is the main payoff of Part 1: a well-formed region's members have
  pairwise disjoint footprints, i.e.\ they really do denote independent
  pieces of memory, not merely independent \<^emph>\<open>names\<close>. Note how the proof
  needs \<^emph>\<open>both\<close> halves of @{text wf_region} (ruling out
  @{text "x \<^bold>\<supset> y"} \<^emph>\<open>and\<close> @{text "y \<^bold>\<supset> x"}) together with
  @{text ancestors_linear}: if some @{text z} were shared between the two
  footprints, @{text z} would have to be reached from both @{text x} and
  @{text y} by iterating @{text owner}, and @{text ancestors_linear} would
  then force @{text x} and @{text y} to be comparable -- directly
  contradicting @{text wf_region}.
\<close>

theorem wf_region_footprint_disjoint:
  assumes "wf_region R" "x \<in> R" "y \<in> R" "x \<noteq> y"
  shows "footprint x \<inter> footprint y = {}"
proof (rule equals0I)
  fix z
  assume "z \<in> footprint x \<inter> footprint y"
  then have hx: "z = x \<or> strictly_contains x z"
    and hy: "z = y \<or> strictly_contains y z"
    unfolding footprint_def by auto
  from assms have no_rel: "\<not> strictly_contains x y" "\<not> strictly_contains y x"
    unfolding wf_region_def by auto
  from hx hy show False
  proof (elim disjE)
    assume "z = x" and "z = y"
    with \<open>x \<noteq> y\<close> show False by simp
  next
    assume "z = x" and contains: "strictly_contains y z"
    with no_rel show False by simp
  next
    assume contains: "strictly_contains x z" and "z = y"
    with no_rel show False by simp
  next
    assume cx: "strictly_contains x z" and cy: "strictly_contains y z"
    from ancestors_linear [OF cx cy] and \<open>x \<noteq> y\<close> and no_rel show False by blast
  qed
qed

end

text \<open>
  \<^bold>\<open>Worked example.\<close> We instantiate the (assumption-free!) locale
  @{text mojo_regions} at a two-point type representing a struct
  @{text Thing} with one field @{text ThingX} (so @{text "owner ThingX =
  Some Thing"}), matching the discussion in comment 5278470 verbatim. The
  interpretation needs no proof obligations because the locale carries no
  @{text "assumes"} clause.
\<close>

datatype demo_loc = Thing | ThingX

definition demo_owner :: "demo_loc \<Rightarrow> demo_loc option" where
  "demo_owner l = (if l = ThingX then Some Thing else None)"

interpretation demo: mojo_regions demo_owner .

text \<open>
  The following two auxiliary facts are all we need to pin down the
  footprints. @{text demo_owner} never maps anything to
  @{text "Some ThingX"} (its only possible results are @{text "Some Thing"}
  and @{text None}), and @{text ancestor_at} only ever produces a value by
  applying @{text owner} (@{text demo_owner}, after interpretation) to some
  intermediate point. Hence @{text ancestor_at} can never produce
  @{text "Some ThingX"} either -- i.e.\ @{text ThingX} never contains
  anything, and in particular does not contain @{text Thing}. This is
  exactly the fact needed to show @{text "footprint ThingX"} is the
  singleton @{text "{ThingX}"} below. Note that this argument needs only a
  single case split (on whether the one-step-shorter chain already failed),
  not an induction on the chain length @{text n}.
\<close>

lemma demo_owner_range: "demo_owner l \<noteq> Some ThingX"
  by (simp add: demo_owner_def)

lemma demo_ancestor_at_ne_ThingX: "demo.ancestor_at (Suc n) v \<noteq> Some ThingX"
proof (cases "demo.ancestor_at n v")
  case None
  then show ?thesis by simp
next
  case (Some p)
  then show ?thesis using demo_owner_range by simp
qed

lemma demo_footprint_Thing: "demo.footprint Thing = {Thing, ThingX}"
proof -
  have contains: "demo.strictly_contains Thing ThingX"
    unfolding demo.strictly_contains_def
  proof (intro exI)
    show "demo.ancestor_at (Suc 0) ThingX = Some Thing"
      by (simp add: demo_owner_def)
  qed
  have upper: "demo.footprint Thing \<subseteq> {Thing, ThingX}"
  proof
    fix c :: demo_loc
    assume "c \<in> demo.footprint Thing"
    then show "c \<in> {Thing, ThingX}" by (cases c) simp_all
  qed
  have lower: "{Thing, ThingX} \<subseteq> demo.footprint Thing"
    using contains unfolding demo.footprint_def by auto
  from upper lower show ?thesis by (rule equalityI)
qed

lemma demo_footprint_ThingX: "demo.footprint ThingX = {ThingX}"
proof -
  have not_contains: "\<not> demo.strictly_contains ThingX Thing"
  proof
    assume "demo.strictly_contains ThingX Thing"
    then obtain m where "demo.ancestor_at (Suc m) Thing = Some ThingX"
      unfolding demo.strictly_contains_def ..
    with demo_ancestor_at_ne_ThingX show False by simp
  qed
  have upper: "demo.footprint ThingX \<subseteq> {ThingX}"
  proof
    fix c :: demo_loc
    assume "c \<in> demo.footprint ThingX"
    then have "c = ThingX \<or> demo.strictly_contains ThingX c"
      unfolding demo.footprint_def by simp
    then show "c \<in> {ThingX}"
    proof
      assume "demo.strictly_contains ThingX c"
      with not_contains have "c \<noteq> Thing" by auto
      then show "c \<in> {ThingX}" by (cases c) simp_all
    qed simp
  qed
  have lower: "{ThingX} \<subseteq> demo.footprint ThingX" by simp
  from upper lower show ?thesis by (rule equalityI)
qed

text \<open>
  Now the punch line: as \<^emph>\<open>sets\<close>, @{text "{Thing}"} and @{text "{ThingX}"}
  are disjoint (they are different variables); but as \<^emph>\<open>memory\<close>, they are
  not, because @{text ThingX} lives inside @{text Thing}.
\<close>

lemma demo_set_disjoint_not_mem_disjoint:
  "demo.set_disjoint {Thing} {ThingX}"
  "\<not> demo.mem_disjoint {Thing} {ThingX}"
proof -
  show "demo.set_disjoint {Thing} {ThingX}"
    unfolding demo.set_disjoint_def using demo_loc.distinct(1) by auto
next
  show "\<not> demo.mem_disjoint {Thing} {ThingX}"
    unfolding demo.mem_disjoint_def demo.region_footprint_def
    using demo_footprint_Thing demo_footprint_ThingX by auto
qed

text \<open>
  \<^bold>\<open>Sanity check.\<close> As promised above: even though we never assume
  @{text owner} is acyclic, a cyclic @{text owner} can never produce a
  @{text wf_region} containing both of the cyclic elements. We check this
  on the smallest possible cycle, two locations that directly own each
  other.
\<close>

datatype cycle_loc = CycA | CycB

definition cycle_owner :: "cycle_loc \<Rightarrow> cycle_loc option" where
  "cycle_owner l = (case l of CycA \<Rightarrow> Some CycB | CycB \<Rightarrow> Some CycA)"

interpretation cyc: mojo_regions cycle_owner .

lemma demo_cycle_is_never_wellformed: "\<not> cyc.wf_region {CycA, CycB}"
proof
  assume wf: "cyc.wf_region {CycA, CycB}"
  have "cyc.strictly_contains CycA CycB"
    unfolding cyc.strictly_contains_def
    by (intro exI [of _ 0]) (simp add: cycle_owner_def)
  with wf show False
    unfolding cyc.wf_region_def by auto
qed



section \<open>Part 2: Dereference safety via initialization tracking\<close>

text \<open>
  \<^bold>\<open>Decision.\<close> The gist's dereference-safety rule is: "A dereference is
  rejected if any variable in the pointer's region may be uninitialized
  at that point." We model "may be initialized" at the simplest possible
  level of precision: a \<^emph>\<open>store\<close> is a function from locations to
  booleans, recording, for every location, whether it is \<^emph>\<open>currently\<close>
  initialized. This deliberately does \<^emph>\<open>not\<close> track \<^emph>\<open>which\<close> member of a
  region a given pointer actually targets at runtime -- exactly as in the
  source material, where the whole point of the region abstraction is
  that the compiler does not need (and often cannot know) the pointer's
  precise target. A pointer typed with region @{text R} must therefore be
  treated, for safety purposes, as if it \<^emph>\<open>might\<close> target \<^emph>\<open>any\<close> member of
  @{text R}; dereferencing it is sound exactly when \<^emph>\<open>every\<close> member of
  @{text R} is initialized, which is what @{text safe_to_deref} below
  says.

  \<^bold>\<open>Alternative not taken.\<close> A more precise (and more complicated) model
  would carry, for each pointer \<^emph>\<open>value\<close>, the exact location it denotes
  (e.g.\ as part of an operational semantics with a genuine heap and
  pointer values), and define safety for a specific pointer \<^emph>\<open>value\<close>
  rather than for a pointer \<^emph>\<open>type\<close>/region. That finer-grained model is
  necessary if one wants to state and prove that the region-based check
  is a \<^emph>\<open>sound over-approximation\<close> of the "true" runtime safety
  condition; we do exactly that below (@{text safe_to_deref_sound}), but
  phrase the true condition simply as "the pointer's actual target is
  initialized", leaving the target as a free variable rather than
  modelling pointer values explicitly. This is enough to justify the
  design decision (conservatively rejecting whenever \<^emph>\<open>any\<close> region
  member might be uninitialized) without the overhead of a full pointer
  semantics, which Part 4 needs anyway and introduces independently.
\<close>

type_synonym 'l store = "'l \<Rightarrow> bool"

definition safe_to_deref :: "'l set \<Rightarrow> 'l store \<Rightarrow> bool" where
  "safe_to_deref R s \<longleftrightarrow> (\<forall>v \<in> R. s v)"

text \<open>
  Soundness: whatever the pointer's actual (unknown-to-the-type-system)
  target @{text target} happens to be, if it lies in the region @{text R}
  and the static check @{text safe_to_deref} passes, then @{text target}
  really is initialized. This is the formal justification for rejecting a
  dereference whenever \<^emph>\<open>any\<close> region member might be uninitialized: the
  check must hold for the whole region because the type system does not
  know which member is the real target.
\<close>

lemma safe_to_deref_sound:
  assumes "safe_to_deref R s" and "target \<in> R"
  shows "s target"
  using assms unfolding safe_to_deref_def by blast

text \<open>
  \<^bold>\<open>Worked example.\<close> This reconstructs the gist's own illustration
  verbatim:
@{verbatim [display]
\<open>x = String(...)
y = String(...)
p: Pointer[{x, y}] = Pointer(...)
foo(x^)          # We might want/need to deinitialize x
print(p[])       # This operation is NOT safe
x = String(...)  # We can reinitialize x later on
print(p[])       # This operation is now safe again\<close>}
  using an abstract two-point location type @{text "{ex_x, ex_y}"} to
  stand for @{text x} and @{text y}. We track the store through the three
  successive program states (initially both initialized, then after
  deinitializing @{text x}, then after reinitializing it), and confirm
  that @{text safe_to_deref} tracks exactly the "NOT safe" / "safe again"
  verdicts given in the gist.
\<close>

datatype ex_loc = ex_x | ex_y

lemma example_x_y_dangling_and_restored:
  fixes s0 :: "ex_loc store"
  defines "s0 \<equiv> (\<lambda>_. True)"
  defines "s1 \<equiv> s0 (ex_x := False)"
  defines "s2 \<equiv> s1 (ex_x := True)"
  shows "safe_to_deref {ex_x, ex_y} s0"
    and "\<not> safe_to_deref {ex_x, ex_y} s1"
    and "safe_to_deref {ex_x, ex_y} s2"
  unfolding s0_def s1_def s2_def safe_to_deref_def by auto



section \<open>Part 3: Dynamic containers and pointer invalidation\<close>

text \<open>
  \<^bold>\<open>Decision.\<close> The gist's model of a dynamic container (@{text List},
  @{text Variant}, ...) is: operations that change the buffer's \<^emph>\<open>shape\<close>
  (allocation, deallocation, item addition, item removal) require the
  buffer to be mutable, and \<^emph>\<open>that\<close> mutability is used as the signal that
  pointers into the buffer's item region must be invalidated; operations
  that mutate only \<^emph>\<open>items\<close> (e.g.\ @{text sort}, @{text reverse}, or an
  assignment through an item pointer) leave outstanding pointers valid.
  The gist explicitly simplifies to a model where \<^emph>\<open>every\<close> shape-changing
  operation invalidates (acknowledging that, in reality, @{text append}
  can sometimes preserve pointers when no reallocation is needed -- this
  is listed among the gist's open questions, see the final section of
  this theory).

  We formalize exactly this simplified two-way distinction with a
  \<^emph>\<open>generation counter\<close>: the buffer carries a natural number that is
  bumped by every shape-changing operation and left untouched by every
  item-only operation. A pointer remembers the generation at the moment
  it was created; it is valid later on exactly when the buffer's current
  generation still matches. This is a standard "epoch"/"stamp" technique
  for modelling iterator invalidation, and it is adequate here because
  the gist's own simplified model only ever needs a binary
  distinction (did a shape-change happen since this pointer was taken,
  or not) rather than tracking individual item identities.

  \<^bold>\<open>Alternative not taken.\<close> A more refined model would track, per
  operation, \<^emph>\<open>which\<close> items were added/removed/relocated, and allow a
  pointer to survive an @{text append} that happened not to reallocate
  (open question 2 in the gist, about @{text InlineFixedVector}).
  Formalizing that would mean replacing the single @{text nat} generation
  by, e.g., a finite partial injection recording how old item locations
  map to new ones, and defining validity as "the pointer's location is in
  the domain of every relocation map composed since creation". We do not
  attempt this: it is explicitly open even in the source material, and
  the coarser generation-counter model is exactly what the gist's own
  simplified presentation (Section "Dynamic containers") describes.
\<close>

datatype buf_op = Shape | Item

text \<open>
  @{text buf_step} models the effect of a single operation on the
  buffer's generation counter: a @{text Shape} operation (alloc, dealloc,
  add item, remove item -- i.e.\ anything that today's Mojo would require
  @{text self} to be @{text mut} for) always advances the generation;
  an @{text Item} operation (anything typed as @{text "mut self*"}, i.e.\
  mutating only the item region) leaves it alone.
\<close>

primrec buf_step :: "buf_op \<Rightarrow> nat \<Rightarrow> nat" where
  "buf_step Shape g = Suc g"
| "buf_step Item  g = g"

primrec buf_run :: "buf_op list \<Rightarrow> nat \<Rightarrow> nat" where
  "buf_run [] g = g"
| "buf_run (op # ops) g = buf_run ops (buf_step op g)"

text \<open>
  A pointer created when the buffer's generation was @{text g_created}
  remains valid, after a further sequence of operations @{text ops} is
  run (continuing from that same generation), exactly when the resulting
  generation is unchanged.
\<close>

definition valid_ptr :: "nat \<Rightarrow> buf_op list \<Rightarrow> bool" where
  "valid_ptr g_created ops \<longleftrightarrow> buf_run ops g_created = g_created"

lemma buf_run_mono: "g \<le> buf_run ops g"
proof (induct ops arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons op ops)
  show ?case
  proof (cases op)
    case Shape
    have "g \<le> Suc g" by simp
    also have "... \<le> buf_run ops (Suc g)" using Cons.hyps by blast
    finally show ?thesis using Shape by simp
  next
    case Item
    then show ?thesis using Cons.hyps by simp
  qed
qed

lemma buf_run_strict_if_Shape: "Shape \<in> set ops \<Longrightarrow> g < buf_run ops g"
proof (induct ops arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons op ops)
  show ?case
  proof (cases "op = Shape")
    case True
    then have "g < buf_step op g" by simp
    also have "\<dots> \<le> buf_run ops (buf_step op g)" by (rule buf_run_mono)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "Shape \<in> set ops" by (cases op) auto
    then have "buf_step op g < buf_run ops (buf_step op g)" using Cons.hyps by blast
    moreover have "g \<le> buf_step op g" by (cases op) simp_all
    ultimately show ?thesis by simp
  qed
qed

text \<open>
  The main theorem of this part: a pointer survives a sequence of
  operations if and only if \<^emph>\<open>none\<close> of them was a shape-changing
  operation -- regardless of how many item-only mutations (swaps,
  in-place assignments, sorts, ...) occurred among them. This is exactly
  the content of the gist's section "Mutating items without mutating the
  entire buffer".
\<close>

lemma buf_run_eq_if_no_Shape: "Shape \<notin> set ops \<Longrightarrow> buf_run ops g = g"
proof (induct ops arbitrary: g)
  case Nil
  then show ?case by simp
next
  case (Cons a ops)
  then have a_ne: "a \<noteq> Shape" and rest: "Shape \<notin> set ops" by auto
  have step_eq: "buf_step a g = g" using a_ne by (cases a) simp_all
  then show ?case using Cons.hyps [OF rest] by simp
qed

theorem valid_ptr_iff: "valid_ptr g ops \<longleftrightarrow> Shape \<notin> set ops"
proof
  assume "valid_ptr g ops"
  then show "Shape \<notin> set ops"
    using buf_run_strict_if_Shape [of ops g] unfolding valid_ptr_def by auto
next
  assume "Shape \<notin> set ops"
  then show "valid_ptr g ops"
    unfolding valid_ptr_def using buf_run_eq_if_no_Shape by blast
qed

text \<open>
  \<^bold>\<open>Worked example.\<close> The gist's @{text "names.pop()"} illustration: a
  pointer survives any number of item-only operations (@{text sort},
  @{text reverse}, in-place writes through other item pointers, ...) but
  is invalidated the moment a single shape-changing operation (such as
  @{text pop}) occurs, no matter where in the sequence.
\<close>

lemma example_item_ops_preserve_pointer:
  "valid_ptr g [Item, Item, Item]"
  unfolding valid_ptr_def by simp

lemma example_pop_invalidates_even_after_many_item_ops:
  "\<not> valid_ptr g [Item, Item, Shape, Item]"
  by (simp add: valid_ptr_iff)



section \<open>Part 4: Aliasing-xor-mutability for region parameters\<close>

text \<open>
  \<^bold>\<open>Decision.\<close> This is the central safety argument of the gist, and the
  one the comment thread sharpens the most. The gist's Rule 2 (comment
  5278468) reads: "Given a pair of region parameters in a function
  signature, if either of the regions are mutated by the function, the
  memory owned by the variables in region A must not overlap the memory
  owned by the variables in region B." The gist motivates this with a
  concrete hazard:
@{verbatim [display]
\<open>fn set_names[name_rgn, value_rgn]
    (names: List[Pointer[name_rgn]], value: Pointer[value_rgn]) mut name_rgn:
        for name in names:
            name[] = value[]\<close>}
  If @{text name_rgn} and @{text value_rgn} overlapped, a single call
  could have @{text name} and @{text value} point at the \<^emph>\<open>same\<close>
  variable; the assignment @{text "name[] = value[]"} first destroys the
  left-hand side (to overwrite it), and if that happens to be the same
  variable as the right-hand side, the subsequent read of @{text "value[]"}
  reads from memory that was just destroyed. The gist also gives the
  single-region version of the same hazard directly:
@{verbatim [display]
\<open>fn foo[r: Region[String]](names: List[Pointer[r]]) mut r:
    p1 = names[0]
    p2 = names[1]
    p1[] = p2[]     # Error: cannot copy p2[]; it might be uninitialized.\<close>}

  We formalize this precisely by modelling the statement
  @{text "name[] = value[]"} as an abstract three-step operation,
  @{text copy_step}, on a store: (1) deinitialize the \<^emph>\<open>entire footprint\<close>
  of the target (not just the target variable itself -- a destructor runs
  recursively over everything the target owns, which is why we need the
  ownership-aware notion of footprint from Part 1, not just set
  membership); (2) check that the source is initialized, reading it if
  so; (3) reinitialize the target. If step (2) finds the source
  uninitialized, the whole operation gets stuck -- this @{text None}
  result is our formal stand-in for the memory-safety violation
  ("reading from memory that might be invalid") that Rule 2 exists to
  prevent.

  Because the compiler does not know \<^emph>\<open>which\<close> member of @{text name_rgn}
  and @{text value_rgn} a given call will actually use (this is, after
  all, the entire point of the region abstraction -- see Part 2), proving
  the call safe means proving @{text copy_step} never gets stuck for
  \<^emph>\<open>any\<close> choice of target in @{text name_rgn} and source in
  @{text value_rgn}. That is exactly @{text
  region_disjointness_prevents_aliasing_bug} below, and it is proved
  \<^emph>\<open>from\<close> @{text mem_disjoint} -- which is why Part 1 insists on the
  memory-footprint notion of disjointness rather than the naive
  set-membership one: it is precisely strong enough to guarantee that
  destroying the target's whole footprint cannot possibly touch the
  source.

  We also prove the necessity direction: a region can never be
  @{text mem_disjoint} from \<^emph>\<open>itself\<close> (unless it is empty), which is the
  formal reason the single-region @{text foo} example above must be
  rejected: @{text p1} and @{text p2} share one region parameter, so there
  is no disjointness obligation available to rule out them aliasing, and
  indeed @{text copy_step} can get stuck when they do.

  \<^bold>\<open>Alternative not taken.\<close> The gist itself discusses an alternative
  design (its first alternative): instead of imposing disjointness between
  mutated and other region parameters, one could allow region parameters
  to overlap freely and instead reject the specific \<^emph>\<open>copy expression\<close>
  @{text "name[] = value[]"} with the error "cannot copy value[]; it
  might be uninitialized" -- i.e.\ push the conservatism from signatures
  down to individual statements. The gist rejects this because it rejects
  far more programs (every copy between two same-region pointers, even
  when the specific call site never aliases them) and gives function
  authors much weaker reasoning principles about their own code. Our
  @{text copy_step_safe} theorem is, in effect, a formal demonstration of
  \<^emph>\<open>why\<close> the chosen alternative (disjointness on mutated region
  parameters) is the one that actually buys safety: it is exactly the
  hypothesis that makes the theorem go through.
\<close>

context mojo_regions
begin

text \<open>
  Deinitializing a variable @{text t} deinitializes its \<^emph>\<open>entire
  footprint\<close> -- this models a destructor that recursively tears down
  everything @{text t} owns, not just @{text t} itself.
\<close>

definition deinit_footprint :: "'l \<Rightarrow> 'l store \<Rightarrow> 'l store" where
  "deinit_footprint t s = (\<lambda>l. if l \<in> footprint t then False else s l)"

definition copy_step :: "'l \<Rightarrow> 'l \<Rightarrow> 'l store \<Rightarrow> 'l store option" where
  "copy_step t s store =
     (let store1 = deinit_footprint t store
      in if store1 s then Some (store1 (t := True)) else None)"

text \<open>
  The crucial corollary of @{text mem_disjoint}: if two regions'
  footprints do not overlap, then deinitializing (the footprint of) any
  member of one cannot possibly affect any member of the other.
\<close>

lemma mem_disjoint_excludes_footprint:
  assumes "mem_disjoint R_t R_s" "t \<in> R_t" "s \<in> R_s"
  shows "s \<notin> footprint t"
proof
  assume "s \<in> footprint t"
  then have "s \<in> region_footprint R_t"
    unfolding region_footprint_def using \<open>t \<in> R_t\<close> by auto
  moreover have "s \<in> region_footprint R_s"
    using \<open>s \<in> R_s\<close> region_subset_footprint by blast
  ultimately have "s \<in> region_footprint R_t \<inter> region_footprint R_s" by simp
  with \<open>mem_disjoint R_t R_s\<close> show False unfolding mem_disjoint_def by simp
qed

theorem copy_step_safe:
  assumes "mem_disjoint R_t R_s" "t \<in> R_t" "s \<in> R_s" "store s"
  shows "copy_step t s store \<noteq> None"
proof -
  from assms(1-3) have "s \<notin> footprint t" by (rule mem_disjoint_excludes_footprint)
  then have "deinit_footprint t store s = store s"
    unfolding deinit_footprint_def by simp
  with \<open>store s\<close> have "deinit_footprint t store s" by simp
  then show ?thesis unfolding copy_step_def by simp
qed

text \<open>
  The quantified form matching the @{text set_names} example: if
  @{text name_rgn} and @{text value_rgn} are memory-disjoint and every
  potential source is initialized, then \<^emph>\<open>every\<close> choice of target and
  source the loop body might make is safe -- regardless of which specific
  pointers @{text names} and @{text value} happen to denote at runtime.
\<close>

corollary region_disjointness_prevents_aliasing_bug:
  assumes "mem_disjoint R_t R_s" and "\<forall>s \<in> R_s. store s"
  shows "\<forall>t \<in> R_t. \<forall>s \<in> R_s. copy_step t s store \<noteq> None"
  using copy_step_safe [OF assms(1)] assms(2) by blast

text \<open>
  Necessity, part 1: a region can only be memory-disjoint from itself if
  it is empty.
\<close>

lemma region_never_mem_disjoint_from_itself:
  assumes "v \<in> R"
  shows "\<not> mem_disjoint R R"
  using assms mem_footprint_self unfolding mem_disjoint_def region_footprint_def by blast

text \<open>
  Necessity, part 2: and indeed, when a target and source alias (the
  @{text "p1[] = p2[]"} hazard), @{text copy_step} really does get stuck,
  for \<^emph>\<open>any\<close> fully-initialized store. Together with the previous lemma,
  this shows that the single-region @{text foo} example is not merely
  \<^emph>\<open>conservatively\<close> rejected -- it is rejected because it can
  \<^emph>\<open>genuinely\<close> go wrong, and @{text mem_disjoint} is exactly the
  condition whose absence permits that.
\<close>

lemma copy_step_self_alias_fails: "copy_step v v (\<lambda>_. True) = None"
proof -
  have "v \<in> footprint v" by (rule mem_footprint_self)
  then have "deinit_footprint v (\<lambda>_. True) v = False"
    unfolding deinit_footprint_def by simp
  then show ?thesis unfolding copy_step_def by simp
qed

end



section \<open>Part 5: Mutation as an effect, not a type\<close>

text \<open>
  \<^bold>\<open>Decision.\<close> The gist's final major move is to stop recording
  mutability in pointer/origin \<^emph>\<open>types\<close> and instead record it as an
  \<^emph>\<open>effect\<close> that a function declares (@{text "mut region"},
  @{text "mut self*"}, ...), with the rule that "trait methods cannot add
  mutation effects beyond what the trait declares" while "read effects
  may be added" freely. The motivating example is @{text StringWrapper}:
  if its origin parameter is a @{text MutableOrigin} merely because
  \<^emph>\<open>one\<close> method (@{text capitalize}) needs to mutate, then \<^emph>\<open>every\<close>
  method -- including @{text "__str__"}, which only reads -- is treated as
  potentially mutating, which wrongly blocks @{text "print_args(x, x)"}
  (passing @{text x} to a function that only uses it as @{text Stringable}
  twice).

  We do not attempt to formalize a full trait/method dispatch system
  here -- that would require modelling far more of Mojo's type system
  than the other four parts need. Instead we isolate the \<^emph>\<open>semantic
  core\<close> of the decision: an effect-\<^emph>\<open>declaration\<close> discipline (you may
  only ever \<^emph>\<open>remove\<close> a @{text Mut} effect when implementing a trait
  method, never add one, while @{text Read} is unrestricted) together
  with a demonstration of \<^emph>\<open>why\<close> this is exactly the right discipline:
  @{text Mut} is the effect that triggers the disjointness obligation of
  Part 4 (@{text copy_step} needs to deinitialize-and-reinitialize, which
  is where the hazard lives), whereas a pure read never mutates the store
  at all, so it can never be unsafe under aliasing, with no side
  condition required. This is a direct payoff of Part 4's machinery: it
  explains, rather than merely asserts, why "read effects are always safe
  to add" and "mutation effects are not".

  \<^bold>\<open>Alternative not taken.\<close> One could instead keep mutability attached
  to the origin/region \<^emph>\<open>type\<close> but make the attachment itself
  polymorphic, as today's Mojo already does for whole-function
  signatures via a boolean flag on @{text Origin} (illustrated in the
  comment thread, comment 5740661: @{text "fn foo[o: Origin]"} is
  polymorphic over mutability, @{text "fn bar[o: Origin[mut=False]]"} is
  not). That mechanism is a genuine, shipped alternative to the
  gist's proposal, but it is polymorphism over a single declaration site
  (the origin parameter), and does not solve the @{text StringWrapper}
  problem: a struct's stored origin parameter is fixed once, for the
  whole struct, so individual \<^emph>\<open>methods\<close> of that struct still cannot
  independently vary whether they need mutable access. The gist's
  effect-on-methods design is finer-grained precisely because the
  granularity that matters is "per method", not "per struct" or
  "per function".
\<close>

datatype effect = Read | Mut

text \<open>
  @{text "subsumes trait_effects impl_effects"} holds when
  @{text impl_effects} is a legitimate implementation of a trait method
  that declares @{text trait_effects}: the implementation may not
  introduce a @{text Mut} effect that the trait did not already declare.
  (We leave @{text Read} unconstrained, matching the gist: "it's
  perfectly fine for types to add extra read effects to a trait
  conformance, because reading aliased state is always safe, as long as
  nobody else is mutating it".)
\<close>

definition subsumes :: "effect set \<Rightarrow> effect set \<Rightarrow> bool" where
  "subsumes trait_effects impl_effects \<longleftrightarrow> (Mut \<in> impl_effects \<longrightarrow> Mut \<in> trait_effects)"

lemma no_mut_trait_forces_no_mut_impl:
  assumes "subsumes trait_effects impl_effects" "Mut \<notin> trait_effects"
  shows "Mut \<notin> impl_effects"
  using assms unfolding subsumes_def by blast

text \<open>
  This is the formal reconstruction of the @{text StringWrapper} example:
  if a trait such as @{text Stringable} declares no @{text Mut} effect
  for @{text "__str__"}, then \<^emph>\<open>every\<close> legitimate implementation -- for
  instance @{text "StringWrapper.__str__"} -- also has no @{text Mut}
  effect, by @{text no_mut_trait_forces_no_mut_impl}. We now show that
  this is exactly the condition under which aliasing is unconditionally
  safe, by contrasting a pure read with @{text copy_step} from Part 4.
  @{text read_step} models "reading through a pointer": check that the
  target is initialized, and -- unlike @{text copy_step} -- leave the
  store untouched.
\<close>

definition read_step :: "'l \<Rightarrow> 'l store \<Rightarrow> 'l store option" where
  "read_step v store = (if store v then Some store else None)"

text \<open>
  Unconditional aliasing safety for reads: no disjointness side condition
  is needed at all, in sharp contrast to @{text copy_step_safe}. This is
  precisely why @{text "print_args(x, x)"} is safe: both occurrences of
  @{text x} only ever go through @{text read_step}-like operations
  (@{text "__str__"} performs no mutation), so they may alias freely.
\<close>

lemma read_step_alias_safe:
  assumes "store v"
  shows "read_step v store \<noteq> None"
  using assms unfolding read_step_def by simp

text \<open>
  And conversely, Part 4 already showed that @{text copy_step} (which
  models a @{text Mut}-effect operation: it deinitializes, reads, then
  reinitializes) is \<^emph>\<open>not\<close> unconditionally safe under aliasing
  (@{text copy_step_self_alias_fails}) -- a side condition
  (@{text mem_disjoint}) really is required. Together,
  @{text read_step_alias_safe} and @{text copy_step_self_alias_fails}
  are the formal content of "mutation effects require a disjointness
  obligation; read effects never do", which is exactly the asymmetry the
  gist's design exploits when it allows @{text Read} to be added freely
  to a trait conformance but forbids adding @{text Mut}.
\<close>



section \<open>Limitations, open questions, and alternative formal approaches\<close>

text \<open>
  This final section is pure commentary: it does not introduce further
  Isabelle definitions, but records, against the backdrop of the model
  built above, what the gist (and its comment thread) explicitly leaves
  open, and what alternative formalization strategies exist for the same
  design.

  \<^bold>\<open>1. No uniqueness guarantee for same-region pointers.\<close> The gist's own
  "Limitations" section states this plainly: Rust guarantees that a list
  of mutable references sharing one lifetime never alias each other
  ("unique references"); this design offers no such compile-time
  guarantee, because -- as Part 4 demonstrates concretely
  (@{text copy_step_self_alias_fails}) -- pointers sharing a region
  parameter are \<^emph>\<open>allowed\<close> to alias. Nothing in this theory proves or
  disproves that trade-off is "worth it"; we have simply made it
  checkable \<^emph>\<open>what\<close> is and is not guaranteed. A natural (unattempted)
  extension would add a ghost/ghost-state "uniqueness" predicate on top
  of a region -- e.g.\ a refinement @{text "unique R store"} asserting
  that the pointers currently drawn from @{text R} happen to be pairwise
  distinct -- recovering Rust-style guarantees \<^emph>\<open>opt-in\<close>, exactly as the
  gist suggests could be done with unsafe code (as in its @{text swap}
  example, whose @{text "__address_of"} check is precisely a run-time
  witness of this kind of uniqueness fact).

  \<^bold>\<open>2. Tagged unions (@{text Variant}) as dynamic containers.\<close> Left open
  by the gist ("I suspect we'll want to follow in the footsteps of C
  unions, and expose a different region for each payload type"). Our
  Part 3 model would extend naturally: give @{text buf_op} a
  payload-indexed family of @{text Shape} constructors (one per variant
  tag, modelling "reassigned to a different payload type" as a shape
  change only for pointers typed at a \<^emph>\<open>different\<close> tag than the new one),
  while same-tag reads/writes become @{text Item} operations. We have not
  carried this out, since the gist itself does not commit to a design
  here.

  \<^bold>\<open>3. Non-reallocating containers (@{text InlineFixedVector}).\<close> Also
  explicitly open in the gist. As noted in Part 3's own commentary, this
  would replace the single generation counter by something that can
  distinguish "the buffer moved" from "an item was added but the buffer
  stayed put", e.g.\ splitting @{text buf_op} into a reallocating and a
  non-reallocating @{text Append}, with the latter @{text step}ping as
  the identity -- a direct, small extension of the @{text buf_step}
  table, not a redesign.

  \<^bold>\<open>4. What invalidation actually does at runtime.\<close> The gist poses three
  options verbatim: the pointer is destroyed, it can be "fixed" by
  updating its address, or dereferencing an invalidated pointer is simply
  a fatal (compile-time-prevented) error. Our @{text valid_ptr} predicate
  is deliberately agnostic between these: it only characterizes \<^emph>\<open>when\<close>
  a pointer is valid, not what happens when it is not. Modelling "fix-up"
  would need @{text valid_ptr} to carry relocation information (as in
  point 3 above); modelling "fatal error" is already exactly what
  @{text valid_ptr_iff} gives, if one reads "the type system rejects any
  dereference once @{text valid_ptr} can no longer be shown" as the
  intended discipline (which is the reading consistent with Parts 1-2 of
  this theory, where @{text safe_to_deref} is likewise a static,
  rejection-based check rather than a runtime one).

  \<^bold>\<open>5. The "region" vs "set of variables" naming, and the two
  disjointness rules.\<close> The gist's main text proposes the terms
  "region", "domain", and "group" and settles (tentatively) on "region",
  while flagging in a footnote that this risks confusion between
  "overlapping memory" and "overlapping sets" -- exactly the distinction
  Part 1 makes precise as @{text set_disjoint} versus @{text mem_disjoint}.
  That distinction, together with the \<^emph>\<open>two separate\<close> disjointness rules
  (Rule 1, intra-region well-formedness, formalized as @{text wf_region}
  in Part 1; Rule 2, inter-region aliasing-xor-mutability, formalized via
  @{text mem_disjoint} in Part 4) is not actually spelled out in the
  gist's main text at all -- it only emerges from the comment thread
  (5272844, 5277073, 5278468, 5278470), where verdagon first raises Rule
  1 and nmsmith's replies separate the two rules and give the
  @{text "{thing}"}/@{text "{thing.x}"} counterexample that Part 1's
  @{text demo_set_disjoint_not_mem_disjoint} reproduces. We consider this
  one of the more important clarifications to carry into a formalization,
  since conflating the two rules (or conflating @{text set_disjoint} with
  @{text mem_disjoint}) would make several of the theorems above either
  false or unstatable.

  \<^bold>\<open>6. Rust's NLL ("non-lexical lifetimes") model, as a genuine
  alternative foundation.\<close> In the comment thread, seanbaxter asks why
  regions must be disjoint at all, from the point of view of Rust's NLL
  borrow checker, where "region variables just indicate liveness for a
  reference on a per-instruction basis" and loans are checked against
  liveness rather than against an explicit set of variables. This is a
  substantively different formal foundation: NLL regions are (roughly)
  sets of \<^emph>\<open>program points\<close> at which a borrow is live, solved via a
  constraint system, whereas the gist's regions -- and this theory's
  @{text "'l set"} -- are sets of \<^emph>\<open>variables\<close>, static for the duration
  of the pointer's existence. nmsmith's reply (5278468) is explicit that
  the design is "a clean sheet", not a reformulation of NLL, and that a
  single Rust-style lifetime parameter shared between an argument and a
  result would need \<^emph>\<open>two\<close> region parameters here precisely because
  disjointness is a property of \<^emph>\<open>region parameters\<close>, not of merged
  liveness ranges. We likewise did not attempt to formalize NLL-style
  liveness regions or to relate them formally to our set-of-variables
  model; the two are different enough (points-in-a-CFG vs.\ variables)
  that a faithful comparison would be a substantial project of its own.

  \<^bold>\<open>7. InvalML and "arenas with higher-order reachability tracking", as
  alternative formal systems with a known expressiveness gap.\<close> MattPD's
  comment points to Gao and Parreaux's "A Lightweight Type-and-Effect
  System for Invalidation Safety" (OOPSLA 2025) and a related arena
  system (Wei et al., "When Lifetimes Liberate", arXiv:2509.04253), both
  of which tackle essentially the same problem (tracking when a
  reference into mutable, dynamically-sized memory becomes invalid) using
  a type-and-effect discipline with constraint-based subtype inference,
  rather than an explicit region-as-set-of-variables model. nmsmith's
  follow-up (5953468) reports a conversation with InvalML's lead author
  confirming a real limitation: InvalML cannot model \<^emph>\<open>first-class\<close>
  pointers into dynamic containers -- references can only appear as
  parameters of higher-order functions such as @{text map}/@{text filter},
  not as values produced by, say, a hand-written loop that collects
  pointers to every non-zero element of an array into a second array.
  This is directly relevant to what we formalized in Part 3
  (@{text valid_ptr}): our model is deliberately built around exactly the
  first-class, loop-producible item pointers that InvalML cannot express,
  because that is the use case the gist is targeting (C/C++/Rust-style
  imperative code, not "mostly-functional" code built from combinators).
  We record this as the clearest piece of outside evidence that the
  design decision underlying Part 3 -- first-class pointers with an
  explicit, checkable validity predicate, rather than an effect system
  confined to higher-order combinators -- is doing real work, rather than
  being an arbitrary modelling choice.

  \<^bold>\<open>8. GhostCell-style branded mechanisms.\<close> burdges's comment raises
  @{text GhostCell} (and the general pattern of "branding" a lifetime to
  a single value to allow several simultaneously-live borrows into
  disjoint parts of it) as a Rust mechanism for a related but distinct
  problem: obtaining two simultaneous mutable borrows out of \<^emph>\<open>one\<close>
  method call pair (@{text "foo(&mut self, ...)"} and
  @{text "bar(&mut self, ...)"}) that each return something borrowed. We
  have not modelled this, or Rust's "partial borrowing" proposals
  (referenced in the same comment) for inferring disjoint field-level
  borrows automatically; both are substantially about \<^emph>\<open>ergonomics\<close> of
  obtaining disjoint regions in the first place, which is orthogonal to
  what this theory formalizes (what it \<^emph>\<open>means\<close> for regions to be
  disjoint, and why that matters for safety).
\<close>

end
