theory Language
  imports "$AFP/Kleene_Algebra/Kleene_Algebra" Lazy_Sum_List Fixpoint Omega_Algebra
begin

(* Old coinduction princples from old version of coinductive packages. Newer coinduction principles
   for lazy lists are somewhat awkard to use, mostly because they lack the nice case_conclusion names for
   subgoals. *)

no_notation Linear_Temporal_Logic_on_Streams.HLD_nxt (infixr "\<cdot>" 65)

definition Valid :: "'a llist \<Rightarrow> (unit + unit) llist \<Rightarrow> 'b llist \<Rightarrow> bool" where
  "Valid xs t ys \<equiv> llength (\<ll> t) = llength xs \<and> llength (\<rr> t) = llength ys"

lemma llist_equalityI
  [consumes 1, case_names Eqllist, case_conclusion Eqllist EqLNil EqLCons]:
  assumes r: "(l1, l2) \<in> r"
    and step: "\<And>q. q \<in> r \<Longrightarrow>
      q = (LNil, LNil) \<or>
        (\<exists>l1 l2 a b.
          q = (LCons a l1, LCons b l2) \<and> a = b \<and>
            ((l1, l2) \<in> r \<or> l1 = l2))"
      (is "\<And>q. _ \<Longrightarrow> ?EqLNil q \<or> ?EqLCons q")
  shows "l1 = l2"
  using r
  by (coinduct rule: llist.coinduct_strong) (auto dest: step)  

lemma llist_fun_equalityI
  [case_names LNil LCons, case_conclusion LCons EqLNil EqLCons]:
  assumes fun_LNil: "f LNil = g LNil"
    and fun_LCons: "\<And>x l.
      (f (LCons x l), g (LCons x l)) = (LNil, LNil) \<or>
        (\<exists>l1 l2 a b.
          (f (LCons x l), g (LCons x l)) = (LCons a l1, LCons b l2) \<and>
            a = b \<and> ((l1, l2) \<in> {(f u, g u) | u. True} \<or> l1 = l2))"

      (is "\<And>x l. ?fun_LCons x l")
  shows "f l = g l"
proof -
  have "(f l, g l) \<in> {(f l, g l) | l. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain l where q: "q = (f l, g l)" by blast
    show ?case
    proof (cases l)
      case LNil
      with fun_LNil and q have "q = (g LNil, g LNil)" by simp
      then show ?thesis by (cases "g LNil") simp_all
    next
      case (LCons x l')
      with `?fun_LCons x l'` q LCons show ?thesis by blast
    qed
  qed
qed

section {* Potentially infinite languages with shuffle product *}

notation lappend (infixl "\<frown>" 75)

type_synonym 'a lan = "'a llist set"

subsection {* Language product *}

no_notation Groups.times_class.times (infixl "\<cdot>" 70)

definition l_prod :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<cdot>" 80) where
  "l_prod X Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> lfinite xs}"

lemma l_prod_def_var: "X \<cdot> Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> ys \<in> Y} \<union> {xs. xs \<in> X \<and> \<not> lfinite xs}"
  by (auto simp add: l_prod_def) (metis lappend_inf)

lemma l_prod_assoc: "(X \<cdot> Y) \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
  apply (simp add: l_prod_def)
  apply safe
  by (metis lappend_assoc lfinite_lappend)+

lemma l_prod_isol: "X \<subseteq> Y \<Longrightarrow> X \<cdot> Z \<subseteq> Y \<cdot> Z"
  by (auto simp add: l_prod_def)

lemma l_prod_isor: "X \<subseteq> Y \<Longrightarrow> Z \<cdot> X \<subseteq> Z \<cdot> Y"
  by (auto simp add: l_prod_def)

lemma l_prod_one [simp]: shows "{LNil} \<cdot> X = X" and "X \<cdot> {LNil} = X"
  by (auto simp add: l_prod_def)

lemma l_prod_inf_distr: "\<Union>\<XX> \<cdot> Y = \<Union>{X \<cdot> Y|X. X \<in> \<XX>}"
  by (auto simp add: l_prod_def)

lemma l_prod_distr [simp]: "(X \<union> Y) \<cdot> Z = X \<cdot> Z \<union> Y \<cdot> Z"
  by (insert l_prod_inf_distr[of "{X, Y}" Z]) auto

lemma l_prod_distl [simp]: "X \<cdot> (Y \<union> Z) = X \<cdot> Y \<union> X \<cdot> Z"
  by (auto simp add: l_prod_def)

lemma l_prod_zero [simp]: shows "{} \<cdot> X = {}"
  by (simp add: l_prod_def)

subsection {* Shuffling words *}

text {* The \sha\ operator generates a language by shuffling two words together. *}

definition tshuffle_words :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) lan" (infix "\<sha>" 75) where
  "tshuffle_words xs ys = {zs. lefts zs = xs \<and> rights zs = ys}"

text {* The resulting language contains strings where each symbol is labelled by either @{term Inl} or @{term Inr},
depending on which input it came from. This means that @{prop "\<forall>zs \<in> (xs \<sha> ys). \<ll> zs = xs \<and> \<rr> zs = ys"}.
If a function @{term f} has type @{typ "'a \<Rightarrow> 'c"} and @{term g} has type @{typ "'b \<Rightarrow> 'c"}, then the sum elimination function @{term "\<langle>f,g\<rangle>"}
can be used to eliminate values of @{typ "('a,'b) sum"} by transforming them to values of type @{typ "'c"}.
The function @{term "\<langle>id,id\<rangle>"} is therefore often used when both components of the sum have the same type. *}

text {* When both words are infinite, this definition results in a fair shuffle. *}

lemma lfinite_lfilter_prop: "P (lnth zs n) \<Longrightarrow> \<forall>m>n. \<not> P (lnth zs m) \<Longrightarrow> lfinite (lfilter P zs)"
  apply (simp add: lfinite_lfilter)
  apply (intro disjI2)
  by (metis (erased, lifting) infinite_nat_iff_unbounded mem_Collect_eq)

lemma shuffle_fair: "\<not> lfinite xs \<Longrightarrow> \<not> lfinite ys \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> fair zs"
  apply (auto simp add: tshuffle_words_def fair_def rights_def lefts_def)
  apply (metis infinite_lfilter)
  apply (metis infinite_lfilter)
  apply (rule ccontr)
  apply simp
  apply (subgoal_tac "lfinite (lfilter is_right zs)")
  apply simp
  apply (metis lfinite_lfilter_prop not_is_right)
  apply (rule ccontr)
  apply simp
  apply (subgoal_tac "lfinite (lfilter is_left zs)")
  apply simp
  by (metis (full_types) lfinite_lfilter_prop not_is_right)

lemma tshuffle_words_comm: "lmap \<langle>id,id\<rangle> ` (x \<sha> y) = lmap \<langle>id,id\<rangle> ` (y \<sha> x)"
  by (auto simp add: tshuffle_words_def image_def) (rule_tac x = "lmap swap xa" in exI, simp)+

lemma tshuffle_words_assoc:
  "lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {ws. \<ll> ws = xs \<and> \<ll> (\<rr> ws) = ys \<and> \<rr> (\<rr> ws) = zs} = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {ws. \<ll> (\<ll> ws) = xs \<and> \<rr> (\<ll> ws) = ys \<and> \<rr> ws = zs}"
  apply (auto simp add: image_def)
  apply (rule_tac x = "lmap rbr1 xa" in exI)
  apply simp
  defer
  apply (rule_tac x = "lmap rbr2 xa" in exI)
  by simp

subsection {* Typed shuffle product *}

definition tshuffle :: "'a lan \<Rightarrow> 'b lan \<Rightarrow> ('a + 'b) lan" (infixl "\<Sha>" 75) where
  "X \<Sha> Y \<equiv> \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> Y}"

lemma tshuffle_lr: "xs \<in> X \<Sha> Y \<longleftrightarrow> \<ll> xs \<in> X \<and> \<rr> xs \<in> Y"
  by (auto simp add: tshuffle_def tshuffle_words_def)

lemma tshuffle_comm: "lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) = lmap \<langle>id,id\<rangle> ` (Y \<Sha> X)"
proof -
  have "lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) = \<Union>{lmap \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"
    by (auto simp add: tshuffle_def)
  also have "... = \<Union>{lmap \<langle>id,id\<rangle> ` (y \<sha> x)|x y. x \<in> X \<and> y \<in> Y}"
    by (simp add: tshuffle_words_comm)
  also have "... = lmap \<langle>id,id\<rangle> ` (Y \<Sha> X)"
    by (auto simp add: tshuffle_def)
  finally show ?thesis .
qed

lemma tshuffle3_right:
  "X \<Sha> (Y \<Sha> Z) = \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
  by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle3_left:
  "(X \<Sha> Y) \<Sha> Z = \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
 by (simp only: tshuffle_def tshuffle_words_def) blast

lemma tshuffle_assoc: "lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
proof -
  have "lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z) = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` \<Union>{{w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle3_left)
  also have "... = \<Union>{lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` {w. \<ll> (\<ll> w) = x \<and> \<rr> (\<ll> w) = y \<and> \<rr> w = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = \<Union>{lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` {w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (simp add: tshuffle_words_assoc)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` \<Union>{{w. \<ll> w = x \<and> \<ll> (\<rr> w) = y \<and> \<rr> (\<rr> w) = z}|x y z. x \<in> X \<and> y \<in> Y \<and> z \<in> Z}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (simp add: tshuffle3_right)
  finally show ?thesis .
qed

subsection {* Shuffle product *}

no_notation Sublist.parallel (infixl "\<parallel>" 50)

definition shuffle :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixl "\<parallel>" 75) where
  "shuffle X Y \<equiv> \<Union>{lmap \<langle>id,id\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> Y}"

lemma shuffle_to_tshuffle: "X \<parallel> Y = lmap \<langle>id,id\<rangle> ` (X \<Sha> Y)"
  by (auto simp add: shuffle_def tshuffle_def image_def)

lemma shuffle_comm: "X \<parallel> Y = Y \<parallel> X"
  by (metis shuffle_to_tshuffle tshuffle_comm)

definition traj :: "('a + 'b) llist \<Rightarrow> (unit + unit) llist" where
  "traj \<equiv> lmap \<langle>(\<lambda>x. Inl ()), (\<lambda>x. Inr ())\<rangle>"

text {* The @{term traj} function takes an @{typ "('a + 'b) llist"} and returns a lazy list which contains either @{term "Inl ()"} or
@{term "Inr ()"} if the original list contained @{term Inl} and @{term Inr} anything respectively. *} 

lemma [simp]: "(case x of () \<Rightarrow> y) = y"
  apply (cases x)
  by (metis old.unit.case)

definition interleave :: "(unit + unit) llist \<Rightarrow> 'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) llist" where
  "interleave t l r \<equiv> unfold_llist
     (\<lambda>(t, l, r). t = LNil)
     (\<lambda>(t, l, r). case (lhd t) of (Inl ()) \<Rightarrow> Inl (lhd l) | (Inr ()) \<Rightarrow> Inr (lhd r))
     (\<lambda>(t, l, r). case (lhd t) of (Inl ()) \<Rightarrow> (ltl t, ltl l, r) | (Inr ()) \<Rightarrow> (ltl t, l, ltl r))
     (t, l, r)"

text {* The @{term interleave} function takes a trajectory (as returned by @{term traj}) and combines two lists by picking elements according
to the trajectory. *}

abbreviation interleave' ("_ \<triangleright> _ \<triangleleft> _" [55,55,55] 55) where "xs \<triangleright> t \<triangleleft> ys \<equiv> interleave t xs ys"

lemma interleave_LCons [simp]: "\<ll> (LCons z zs) \<triangleright> traj (LCons z zs) \<triangleleft> \<rr> (LCons z zs) = LCons z (\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs)"
  by (cases z) (simp_all add: traj_def interleave_def)

lemma reinterleave: "\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs = zs"
proof (coinduct zs rule: llist_fun_equalityI)
  case LNil show ?case
    by (auto simp add: traj_def interleave_def)
next
  case (LCons z zs)
  have ?EqLCons
  proof (intro exI conjI)
    show "(\<ll> (LCons z zs) \<triangleright> traj (LCons z zs) \<triangleleft> \<rr> (LCons z zs), LCons z zs) = (LCons z (\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs), LCons z zs)"
      by simp
    have "(\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs, zs) \<in> {(\<ll> u \<triangleright> traj u \<triangleleft> \<rr> u, u) |u. True}"
      by auto
    thus "(\<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs, zs) \<in> {(\<ll> u \<triangleright> traj u \<triangleleft> \<rr> u, u) |u. True} \<or> \<ll> zs \<triangleright> traj zs \<triangleleft> \<rr> zs = zs"
      by blast
  qed simp
  thus ?case
    by auto
qed

text {* Two values of type @{typ "('a + 'b) llist"} are equal if they have the same left values, right values, and trajectory *}

lemma traj_equality: "traj xs = traj ys \<Longrightarrow> \<ll> xs = \<ll> ys \<Longrightarrow> \<rr> xs = \<rr> ys \<Longrightarrow> xs = ys"
  by (metis reinterleave)

lemma traj_LNil [simp]: "xs \<triangleright> LNil \<triangleleft> ys = LNil"
  by (simp add: interleave_def)

lemma interleave_only_left: "interleave (lmap (\<lambda>x. Inl ()) xs) xs ys = lmap Inl xs"
proof (coinduct xs rule: llist_fun_equalityI)
  case LNil show ?case by simp
next
  case (LCons x xs)
  have ?EqLCons
  proof (intro exI conjI)
    show "(interleave (lmap (\<lambda>x. Inl ()) (LCons x xs)) (LCons x xs) ys, lmap Inl (LCons x xs))
        = (LCons (Inl x) (interleave (lmap (\<lambda>x. Inl ()) xs) xs ys), LCons (Inl x) (lmap Inl xs))"
      by (simp add: interleave_def)
    show "(interleave (lmap (\<lambda>x. Inl ()) xs) xs ys, lmap Inl xs) \<in> {(interleave (lmap (\<lambda>x. Inl ()) u) u ys, lmap Inl u) |u. True}
        \<or> interleave (lmap (\<lambda>x. Inl ()) xs) xs ys = lmap Inl xs"
      by auto
  qed simp
  thus ?case by auto
qed

lemma interleave_only_right: "interleave (lmap (\<lambda>x. Inr ()) ys) xs ys = lmap Inr ys"
proof (coinduct ys rule: llist_fun_equalityI)
  case LNil show ?case by simp
next
  case (LCons y ys)
  have ?EqLCons
  proof (intro exI conjI)
    show "(interleave (lmap (\<lambda>x. Inr ()) (LCons y ys)) xs (LCons y ys), lmap Inr (LCons y ys))
        = (LCons (Inr y) (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys), LCons (Inr y) (lmap Inr ys))"
      by (simp add: interleave_def)
    show "(interleave (lmap (\<lambda>x. Inr ()) ys) xs ys, lmap Inr ys) \<in> {(interleave (lmap (\<lambda>x. Inr ()) u) xs u, lmap Inr u)|u. True}
        \<or> interleave (lmap (\<lambda>x. Inr ()) ys) xs ys = lmap Inr ys"
      by auto
  qed simp
  thus ?case by auto
qed

inductive_set ltls :: "'a llist \<Rightarrow> 'a llist set" for xs :: "'a llist" where
  "xs \<in> ltls xs"
| "xs' \<in> ltls xs \<Longrightarrow> ltl xs' \<in> ltls xs"

text {* @{term "ltls xs"} is the set of all tails of @{term xs} *}

lemma sum_list_cases: "\<lbrakk>ys = LNil \<Longrightarrow> P ys; \<And>x xs. ys = LCons (Inl x) xs \<Longrightarrow> P ys; \<And>x xs. ys = LCons (Inr x) xs \<Longrightarrow> P ys\<rbrakk> \<Longrightarrow> P ys"
  apply (cases ys)
  apply auto
  by (metis sumE)

lemma lfinite_induct [consumes 1, case_names Nil Cons]:
  assumes fin: "lfinite xs"
  and Nil: "P LNil"
  and Cons: "\<And>x xs. \<lbrakk>lfinite xs; P xs\<rbrakk> \<Longrightarrow> P (LCons x xs)"
  shows "P xs"
proof -
  from fin obtain xs' where xs: "xs = llist_of xs'"
    unfolding lfinite_eq_range_llist_of by blast
  show ?thesis unfolding xs
    by (induct xs') (auto simp add: Nil Cons)
qed

lemma lfinite_induct_pair [consumes 1, case_names Nil Cons]:
  assumes fin: "lfinite x"
  and Nil: "P LNil"
  and Cons: "\<And>\<sigma> \<sigma>' x'. \<lbrakk>lfinite x'; P x'\<rbrakk> \<Longrightarrow> P (LCons (\<sigma>,\<sigma>') x')"
  shows "P x"
  by (metis Language.lfinite_induct fin local.Cons local.Nil prod.collapse)

lemma interleave_ltakeWhile_is_right: "lfinite ys \<Longrightarrow> xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<longrightarrow> is_right x"
proof (induct ys arbitrary: xs' t ys' rule: lfinite_induct)
  case Nil show ?case
  proof (cases t, simp_all)
    fix t :: "unit + unit" and ts :: "(unit + unit) llist"
    have "xs' \<triangleright> LCons (Inr (unr t)) (ltakeWhile is_right ts) \<triangleleft> ys' = LCons x zs \<longrightarrow> is_right x"
      by (simp add: interleave_def)
    thus "is_right t \<longrightarrow> xs' \<triangleright> LCons t (ltakeWhile is_right ts) \<triangleleft> ys' = LCons x zs \<longrightarrow> is_right x"
      by (metis is_left.simps(1) not_is_left sum.exhaust unr.simps(1))
  qed
next
  case (Cons y ys) thus ?case
    apply (cases t)
    apply simp
    apply (simp only: mp)
  proof -
    fix t ts
    assume ys_fin: "lfinite ys"
    and "\<And>t xs' ys'. xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<longrightarrow> is_right x"
    hence ih: "\<And>t xs' ys'. xs' \<triangleright> ltakeWhile is_right t \<triangleleft> ys' = ys \<frown> LCons x zs \<Longrightarrow> is_right x"
      by auto
    show "xs' \<triangleright> ltakeWhile is_right (LCons t ts) \<triangleleft> ys' = LCons y ys \<frown> LCons x zs \<longrightarrow> is_right x"
      by (cases t) (auto intro: ih simp add: interleave_def)
  qed
qed

lemma llist_of_replicate:
  assumes "lfinite xs" and "(\<forall>x\<in>lset xs. x = y)"
  shows "\<exists>n. xs = llist_of (replicate n y)"
proof -
  obtain xs' where "xs = llist_of xs'"
    by (metis assms(1) llist_of_list_of)
  hence "\<forall>x\<in>set xs'. x = y"
    by (metis assms(2) lset_llist_of)
  hence "xs' = replicate (length xs') y"
    by (simp add: map_replicate_const[symmetric]) (metis map_idI)
  thus ?thesis
    by (metis `xs = llist_of xs'`)
qed

lemma lfilter_left_traj1:
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "lfilter is_left (xs \<triangleright> t \<triangleleft> ys) = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys)"
proof -
  have "\<exists>n. ltakeWhile is_right t = llist_of (replicate n (Inr ()))"
    apply (rule llist_of_replicate)
    apply (metis assms(1) lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
    by (metis (full_types) is_left.simps(1) lset_ltakeWhileD not_is_right swap.cases unit.exhaust)
  then obtain n where rights: "ltakeWhile is_right t = llist_of (replicate n (Inr ()))" by auto
  hence n_def: "enat n = llength (ltakeWhile is_right t)"
    by (metis length_replicate llength_llist_of)

  have "lfilter is_left (xs \<triangleright> t \<triangleleft> ys) = lfilter is_left (xs \<triangleright> ltakeWhile is_right t \<frown> ldropWhile is_right t \<triangleleft> ys)"
    by (metis lappend_ltakeWhile_ldropWhile)
  also have "... = lfilter is_left (xs \<triangleright> llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ys)"
    by (simp only: rights)
  also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat n) ys)"
  proof (induct n arbitrary: ys)
    case 0 show ?case
      by simp (metis ldrop_0 zero_enat_def)
  next
    case (Suc n)
    let ?lhs =  "lfilter is_left (xs \<triangleright> llist_of (replicate (Suc n) (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ys)"
    have "?lhs = lfilter is_left (xs \<triangleright> LCons (Inr ()) (llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t) \<triangleleft> ys)"
      by simp
    also have "... = lfilter is_left (xs \<triangleright> llist_of (replicate n (Inr ())) \<frown> ldropWhile is_right t \<triangleleft> ltl ys)"
      apply (subst interleave_def)
      apply (subst unfold_llist.code)
      by (simp_all add: interleave_def[symmetric])   
    also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat n) (ltl ys))"
      by (simp add: Suc)
    also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (enat (Suc n)) ys)"
      by (metis eSuc_enat ldrop_ltl)
    finally show ?case .
  qed
  also have "... = lfilter is_left (xs \<triangleright> ldropWhile is_right t \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys)"
    by (metis n_def)
  finally show ?thesis .
qed

lemma lfilter_left_traj2:
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "xs \<triangleright> lfilter is_left t \<triangleleft> ys = xs \<triangleright> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys" (is "?lhs = ?rhs")
proof -
  have lfinite_rights: "lfinite (ltakeWhile is_right t)"
    by (metis assms(1) lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)

  have "?lhs = xs \<triangleright> lfilter is_left (ltakeWhile is_right t \<frown> ldropWhile is_right t) \<triangleleft> ys"
    by (metis lappend_ltakeWhile_ldropWhile)
  also have "... = xs \<triangleright> lfilter is_left (ltakeWhile is_right t) \<frown> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by (metis lfilter_lappend_lfinite lfinite_rights)
  also have "... = xs \<triangleright> LNil \<frown> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by (metis Not_is_left lfilter_ltakeWhile)
  also have "... = xs \<triangleright> lfilter is_left (ldropWhile is_right t) \<triangleleft> ys"
    by simp
  finally show ?thesis .
qed

find_theorems ldropWhile LNil

lemma ldropWhile_LCons_lhd: "ldropWhile P t = LCons y ys \<Longrightarrow> \<not> P y"
  by (metis ldropWhile_eq_LNil_iff lhd_LCons lhd_ldropWhile llist.distinct(1))

lemma ldropWhile_rights_not_LNil:
  fixes t :: "(unit + unit) llist"
  assumes "ldropWhile is_right t \<noteq> LNil"
  shows "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))" (is "?lhs = ?rhs")
proof -
  have "?lhs = LCons (lhd (ldropWhile is_right t)) (ltl (ldropWhile is_right t))"
    by (meson assms llist.exhaust_sel)
  also have "... = ?rhs"
    apply (rule arg_cong) back
    using assms
    apply auto
    by (metis (poly_guards_query) ldropWhile_LCons_lhd is_right.simps(1) old.unit.exhaust sumE)
  finally show ?thesis .
qed

lemma only_left_traj: "xs \<triangleright> lfilter is_left t \<triangleleft> ys = xs \<triangleright> lfilter is_left t \<triangleleft> ys'"
proof -
  have "(xs \<triangleright> lfilter is_left t \<triangleleft> ys, xs \<triangleright> lfilter is_left t \<triangleleft> ys')
      \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys')|xs' t ys ys'. xs' \<in> ltls xs}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys ys' where q_def: "q = (xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys')"
    and xs_tl: "xs' \<in> ltls xs"
      by auto
    {
      assume all_right: "ldropWhile is_right t = LNil"
      have ?EqLNil
      proof (auto simp add: q_def)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subgoal_tac "lfilter is_left (ltakeWhile is_right t) = LNil")
          apply simp
          apply simp
          by (metis Not_is_left lfilter_ltakeWhile)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subgoal_tac "lfilter is_left (ltakeWhile is_right t) = LNil")
          apply simp_all
          by (metis Not_is_left lfilter_ltakeWhile)
      qed
    }
    moreover
    {
      assume not_all_right: "ldropWhile is_right t \<noteq> LNil"
      hence finite_rights: "lfinite (ltakeWhile is_right t)"
        by (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
      have ldropWhile_right_LCons: "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))"
        by (metis ldropWhile_rights_not_LNil not_all_right)
      have ?EqLCons
      proof (intro exI conjI)
        show "q = (LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys),
                   LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys'))"
        proof (auto simp add: q_def)
          show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys)"
            apply (subst lfilter_left_traj2[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            by (simp add: interleave_def)
          show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')"
            apply (subst lfilter_left_traj2[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            by (simp add: interleave_def)
        qed
        have "(ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys, ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')
            \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys') |xs' t ys ys'. xs' \<in> ltls xs}"
          apply auto
          by (metis ltls.intros(2) xs_tl)
        thus "(ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys, ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys')
            \<in> {(xs' \<triangleright> lfilter is_left t \<triangleleft> ys, xs' \<triangleright> lfilter is_left t \<triangleleft> ys') |xs' t ys ys'. xs' \<in> ltls xs}
          \<or> ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys = ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ys'"
          by auto
      qed auto
    }
    ultimately show ?case
      by fast
  qed
qed

lemma ldrop_ltls: "ys' \<in> ltls ys \<Longrightarrow> ldrop (enat n) ys' \<in> ltls ys"
  apply (induct n)
  apply (auto simp add: enat_0)
  by (metis eSuc_enat ldrop_ltl ltl_ldrop ltls.intros(2))

lemma lfilter_left_interleave: "lfilter is_left (interleave t xs ys) = interleave (lfilter is_left t) xs ys"
proof -
  let ?f = "\<lambda>t xs ys. lfilter is_left (interleave t xs ys)"
  let ?g = "\<lambda>t xs ys. interleave (lfilter is_left t) xs ys"

  have "(?f t xs ys, ?g t xs ys) \<in> {(?f t xs' ys', ?g t xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus "?f t xs ys = ?g t xs ys"
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
    {
      assume all_right: "ldropWhile is_right t = LNil"
      have ?EqLNil
      proof (auto simp only: q_def)
        show "lfilter is_left (xs' \<triangleright> t \<triangleleft> ys') = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (auto simp add: lfilter_eq_LNil)
          apply (drule split_llist)
          apply auto
          by (metis interleave_ltakeWhile_is_right)
        show "xs' \<triangleright> lfilter is_left t \<triangleleft> ys' = LNil"
          apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
          apply (simp add: all_right)
          apply (subst Not_is_left)
          apply (subst lfilter_ltakeWhile)
          by simp
      qed
    }
    moreover
    {
      assume not_all_right: "ldropWhile is_right t \<noteq> LNil"
      hence finite_rights: "lfinite (ltakeWhile is_right t)"
        by (metis lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lset_ltakeWhileD)
      have ldropWhile_right_LCons: "ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))"
        by (metis (full_types) ldropWhile_rights_not_LNil not_all_right)
      have ?EqLCons
      proof (intro exI conjI)
        show "q = (LCons (Inl (lhd xs')) (lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')),
                   LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'))"
        proof (auto simp add: q_def)
          show "lfilter is_left (xs' \<triangleright> t \<triangleleft> ys')
              = LCons (Inl (lhd xs')) (lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'))"
            apply (subst lfilter_left_traj1[OF not_all_right])
            apply (subst ldropWhile_right_LCons)
            apply (subst interleave_def)
            apply (subst unfold_llist.code)
            apply simp_all
            by (simp add: interleave_def[symmetric])
          show "interleave (lfilter is_left t) xs' ys'
              = LCons (Inl (lhd xs')) (ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')"
            apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right])
            apply (subst Not_is_left)
            apply (subst lfilter_lappend_lfinite)
            apply (simp add: finite_rights)
            apply (subst lfilter_ltakeWhile)
            apply simp
            apply (subst only_left_traj[where ys' = "ldrop (llength (ltakeWhile is_right t)) ys'"])
            apply (subgoal_tac "\<exists>z zs. ldropWhile is_right t = LCons (Inl z) zs")
            apply auto
            apply (subst interleave_def)
            apply (subst unfold_llist.code)
            apply simp_all         
            apply (simp only: interleave_def[symmetric])
            apply (rule sum_list_cases)
            apply (insert not_all_right)
            apply simp
            apply simp
            apply simp
            by (metis Inr_not_Inl ldropWhile_right_LCons lhd_LCons)
        qed
        have "(lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'),
               ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')
            \<in> {(lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
          apply auto
          apply (rule_tac x = "ltl (ldropWhile is_right t)" in exI)
          apply (rule_tac x = "ltl xs'" in exI)
          apply (rule_tac x = "ldrop (llength (ltakeWhile is_right t)) ys'" in exI)
          apply auto
          apply (metis ltls.intros(2) xs_tl)
          by (metis (full_types) finite_rights ldrop_ltls lfinite_llength_enat ys_tl)
        thus "(lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'),
               ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys')
            \<in> {(lfilter is_left (interleave t xs' ys'), interleave (lfilter is_left t) xs' ys')|t xs' ys'. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
          \<or> lfilter is_left (ltl xs' \<triangleright> ltl (ldropWhile is_right t) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys') =
             ltl xs' \<triangleright> lfilter is_left (ltl (ldropWhile is_right t)) \<triangleleft> ldrop (llength (ltakeWhile is_right t)) ys'"
          by blast
      qed auto
    }
    ultimately show ?case
      by fast
  qed
qed

lemma interleave_swap: "ys \<triangleright> lmap swap t \<triangleleft> xs = lmap swap (xs \<triangleright> t \<triangleleft> ys)"
proof -
  have "(ys \<triangleright> lmap swap t \<triangleleft> xs, lmap swap (xs \<triangleright> t \<triangleleft> ys)) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
   {
      assume "t = LNil"
      hence ?EqLNil
        by (simp add: q_def)
    }
    moreover
    {
      fix v t' assume t_def: "t = LCons v t'"
      moreover hence "v = Inl () \<or> v = Inr ()"
        by (metis (full_types) sumE unit.exhaust)
      moreover
      {
        assume t_def: "t = LCons (Inl ()) t'"
        have ?EqLCons
        proof (intro exI conjI)
          show "q = (LCons (Inr (lhd xs')) (ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs'), LCons (Inr (lhd xs')) (lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')))"
            by (simp add: q_def t_def, intro conjI) (subst interleave_def, subst unfold_llist.code, simp_all add: interleave_def[symmetric])+
          show "(ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs', lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
              \<or> ys' \<triangleright> lmap swap t' \<triangleleft> ltl xs' = lmap swap (ltl xs' \<triangleright> t' \<triangleleft> ys')"
            apply (intro disjI1)
            apply auto
            by (metis (full_types) ltls.intros(2) xs_tl ys_tl)
        qed auto
      }
      moreover
      {
        assume t_def: "t = LCons (Inr ()) t'"
        have ?EqLCons
        proof (intro exI conjI)
          show "q = (LCons (Inl (lhd ys')) (ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs'), LCons (Inl (lhd ys')) (lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')))"
            by (simp add: q_def t_def, intro conjI) (subst interleave_def, subst unfold_llist.code, simp_all add: interleave_def[symmetric])+
          show "(ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs', lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')) \<in> {(ys' \<triangleright> lmap swap t \<triangleleft> xs', lmap swap (xs' \<triangleright> t \<triangleleft> ys'))|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}
              \<or> ltl ys' \<triangleright> lmap swap t' \<triangleleft> xs' = lmap swap (xs' \<triangleright> t' \<triangleleft> ltl ys')"
            apply (intro disjI1)
            apply auto
            by (metis (full_types) ltls.intros(2) xs_tl ys_tl)
        qed auto
      }
      ultimately have ?EqLCons
        by (cases v) auto
    }
    ultimately show ?case
      apply (simp add: q_def)
      apply (cases t)
      by auto
  qed
qed

lemma [simp]: "swap (swap x) = x"
  by (cases x) auto

lemma [simp]: "swap \<circ> swap = id"
  by auto

lemma lfilter_right_interleave: "lfilter is_right (xs \<triangleright> t \<triangleleft> ys) = xs \<triangleright> lfilter is_right t \<triangleleft> ys" (is "?lhs = ?rhs")
proof -
  have "?lhs = lmap swap (lfilter is_left (lmap swap (xs \<triangleright> t \<triangleleft> ys)))"
    by (simp add: lfilter_lmap)
  also have "... = lmap swap (lfilter is_left (ys \<triangleright> lmap swap t \<triangleleft> xs))"
    by (simp add: interleave_swap[symmetric])
  also have "... = lmap swap (ys \<triangleright> lfilter is_left (lmap swap t) \<triangleleft> xs)"
    by (metis lfilter_left_interleave)
  also have "... = xs \<triangleright> lmap swap (lfilter is_left (lmap swap t)) \<triangleleft> ys"
    by (simp add: interleave_swap[symmetric])
  also have "... = ?rhs"
    by (simp add: lfilter_lmap)
  finally show ?thesis .
qed

lemma [simp]: "is_left (\<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> x) = is_left x"
  by (cases x) auto

lemma [simp]: "is_left \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> = is_left"
  by (simp add: o_def)

lemma [simp]: "is_left \<circ> \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> = is_left"
  by (simp add: o_def)

lemma [simp]: "is_right (\<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> x) = is_right x"
  by (cases x) auto

lemma [simp]: "is_right \<circ> \<langle>\<lambda>x. Inl (f x),\<lambda>x. Inr (g x)\<rangle> = is_right"
  by (simp add: o_def)

lemma [simp]: "is_right \<circ> \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> = is_right"
  by (simp add: o_def)

lemma lmap_override [simp]: "lmap (\<lambda>x. y) (lmap f xs) = lmap (\<lambda>x. y) xs"
  by (simp add: o_def)

lemma lmap_lfilter_left: "lmap \<langle>f,g\<rangle> (lfilter is_left zs) = lmap (\<lambda>x. f x) (lmap unl (lfilter is_left zs))"
  by (auto intro: lmap_lfilter_left_eq)

lemma lmap_lfilter_right: "lmap \<langle>f,g\<rangle> (lfilter is_right zs) = lmap (\<lambda>x. g x) (lmap unr (lfilter is_right zs))"
  by (auto intro: lmap_lfilter_right_eq)

lemma traj_lfilter_lefts: "\<ll> zs = lmap f xs \<Longrightarrow> lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs"
  by (simp add: lefts_def traj_def lfilter_lmap lmap_lfilter_left)

lemma lmap_const_llength [iff]: "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys \<longleftrightarrow> llength xs = llength ys"
proof
  assume "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys" thus "llength xs = llength ys"
    by (metis llength_lmap)
next
  assume "llength xs = llength ys"
  hence "(lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys) \<in> {(lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys) |(xs::'b llist) (ys::'c llist). llength xs = llength ys}"
    by auto
  thus "lmap (\<lambda>x. c) xs = lmap (\<lambda>x. c) ys"
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain xs :: "'b llist" and ys :: "'c llist"
    where q_def: "q = (lmap (\<lambda>x. c) xs, lmap (\<lambda>x. c) ys)" and same_llength: "llength xs = llength ys" by blast
    {
      assume "xs = LNil"
      moreover hence "ys = LNil"
        by (metis llcp_LNil2 llcp_same_conv_length llist.exhaust lstrict_prefix_code(2) lstrict_prefix_llength_less not_iless0 same_llength)
      ultimately have ?EqLNil using q_def
        by simp
      hence ?case by blast
    }
    moreover
    {
      fix x' xs'
      assume xs_def: "xs = LCons x' xs'"
      then obtain y' and ys' where ys_def: "ys = LCons y' ys'"
        by (metis llength_eq_0 not_lnull_conv same_llength)
      have ?EqLCons
        apply (rule_tac x = "lmap (\<lambda>x. c) xs'" in exI)
        apply (rule_tac x = "lmap (\<lambda>x. c) ys'" in exI)
        apply (rule_tac x = c in exI)+
        apply (intro conjI)
        apply (auto simp add: q_def xs_def ys_def)
        by (metis eSuc_inject llength_LCons same_llength xs_def ys_def)
      hence ?case by blast
    }
    ultimately show ?case
      by (cases xs) auto
  qed
qed

lemma traj_lfilter_lefts_var: "llength (\<ll> zs) = llength xs \<Longrightarrow> lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs"
  by (simp add: lefts_def traj_def lfilter_lmap lmap_lfilter_left)

lemma traj_lfilter_rights_var: "llength (\<rr> zs) = llength ys \<Longrightarrow> lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) ys"
  by (simp add: rights_def traj_def lfilter_lmap lmap_lfilter_right)

lemma lefts_interleave [simp]:
  assumes "\<ll> zs = lmap f xs"
  shows "\<ll> (interleave (traj zs) xs ys) = xs"
proof -
  have "\<ll> (interleave (traj zs) xs ys) = lmap unl (interleave (lfilter is_left (traj zs)) xs ys)"
    by (metis comp_apply lefts_def lfilter_left_interleave)
  also have "... = lmap unl (interleave (lmap (\<lambda>x. Inl ()) xs) xs ys)"
    by (simp only: traj_lfilter_lefts[OF assms(1)])
  also have "... = xs"
    by (metis interleave_only_left lmap2_id unl.simps(1))
  finally show ?thesis .
qed

lemma [simp]: "llength (\<ll> (traj zs)) = llength (\<ll> zs)"
  apply (simp add: traj_def)
  by (metis interleave_only_left lfilter_left_interleave llength_lmap reinterleave traj_def traj_lfilter_lefts_var)

lemma [simp]: "llength (\<rr> (traj zs)) = llength (\<rr> zs)"
  apply (simp add: traj_def)
  by (metis interleave_only_right lfilter_right_interleave llength_lmap reinterleave traj_def traj_lfilter_rights_var)

lemma lefts_interleave_llength [simp]:
  assumes "llength (\<ll> (traj zs)) = llength xs"
  shows "\<ll> (xs \<triangleright> traj zs \<triangleleft> ys) = xs"
proof -
  have "\<ll> (xs \<triangleright> traj zs \<triangleleft> ys) = lmap unl (xs \<triangleright> lfilter is_left (traj zs) \<triangleleft> ys)"
    by (metis comp_apply lefts_def lfilter_left_interleave)
  also have "... = lmap unl (xs \<triangleright> lmap (\<lambda>x. Inl ()) xs \<triangleleft> ys)" using assms
    by (subst traj_lfilter_lefts_var[where xs = xs]) simp_all
  also have "... = xs"
    by (metis interleave_only_left lmap2_id unl.simps(1))
  finally show ?thesis .
qed    

lemma traj_lfilter_rights: "\<rr> zs = lmap f xs \<Longrightarrow> lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) xs"
  by (simp add: rights_def traj_def lfilter_lmap lmap_lfilter_right)

lemma rights_interleave [simp]:
  assumes "\<rr> zs = lmap g ys"
  shows "\<rr> (interleave (traj zs) xs ys) = ys"
proof -
  have "\<rr> (interleave (traj zs) xs ys) = lmap unr (interleave (lfilter is_right (traj zs)) xs ys)"
    by (metis comp_apply rights_def lfilter_right_interleave)
  also have "... = lmap unr (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys)"
    by (simp only: traj_lfilter_rights[OF assms(1)])
  also have "... = ys"
    by (metis interleave_only_right lmap2_id unr.simps(1))
  finally show ?thesis .
qed

lemma rights_interleave_llength [simp]:
  assumes "llength (\<rr> (traj zs)) = llength ys"
  shows "\<rr> (interleave (traj zs) xs ys) = ys"
proof -
  have "\<rr> (interleave (traj zs) xs ys) = lmap unr (interleave (lfilter is_right (traj zs)) xs ys)"
    by (metis comp_apply rights_def lfilter_right_interleave)
  also have "... = lmap unr (interleave (lmap (\<lambda>x. Inr ()) ys) xs ys)" using assms
    by (subst traj_lfilter_rights_var) simp_all
  also have "... = ys"
    by (metis interleave_only_right lmap2_id unr.simps(1))
  finally show ?thesis .
qed


lemma lefts_def_var: "lmap unl (lfilter is_left xs) = \<ll> xs"
  by (auto simp add: lefts_def)

lemma rights_def_var: "lmap unr (lfilter is_right xs) = \<rr> xs"
  by (auto simp add: rights_def)

lemma traj_interleave [simp]: "traj (xs \<triangleright> t \<triangleleft> ys) = t"
proof -
  have "(traj (xs \<triangleright> t \<triangleleft> ys), t) \<in> {(traj (xs' \<triangleright> t \<triangleleft> ys'), t)|xs' ys' t. xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    by auto (metis ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain t xs' ys' where q_def: "q = (traj (xs' \<triangleright> t \<triangleleft> ys'), t)"
    and xs_tl: "xs' \<in> ltls xs"
    and ys_tl: "ys' \<in> ltls ys"
      by auto
    {
      assume "t = LNil"
      hence ?EqLNil
        by (simp add: q_def traj_def)
    }
    moreover
    {
      fix v t' assume t_def: "t = LCons v t'"
      have ?EqLCons
        apply (simp add: q_def t_def)
        apply (cases v)
        apply simp_all
        apply (subst interleave_def)
        apply (subst unfold_llist.code)
        apply simp_all
        apply (subst interleave_def[symmetric])
        apply (auto simp add: traj_def)
        apply (metis ltls.intros(2) xs_tl ys_tl)
        apply (subst interleave_def)
        apply (subst unfold_llist.code)
        apply simp_all
        apply (subst interleave_def[symmetric])
        apply (auto simp add: traj_def)
        by (metis ltls.intros(2) xs_tl ys_tl)
    }
    ultimately show ?case
      apply (simp add: q_def)
      apply (cases t)
      by auto
  qed
qed

lemma [simp]: "unl (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (Inl x)) = f x"
  by simp

lemma [simp]: "unl \<circ> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> \<circ> Inl) = f"
  by auto 

lemma [simp]: "unr (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (Inr x)) = g x"
  by simp

lemma [simp]: "unr \<circ> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> \<circ> Inr) = g"
  by auto 

lemma [simp]: "\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> x"
  by (cases x) auto

lemma [simp]: "\<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> \<circ> \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> = \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle>"
  by auto

lemma lmap_interleave: "\<ll> zs = lmap f xs \<Longrightarrow> \<rr> zs = lmap g ys \<Longrightarrow> lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (xs \<triangleright> traj zs \<triangleleft> ys) = lmap f xs \<triangleright> traj zs \<triangleleft> lmap g ys"
  apply (rule traj_equality)
  defer
  apply (simp (no_asm) add: lefts_def)
  apply (simp add: lfilter_lmap)
  apply (subst lefts_def_var)+
  apply (subst lefts_interleave[where f = id])
  apply simp
  apply (subst lfilter_left_interleave)
  apply (subgoal_tac "lfilter is_left (traj zs) = lmap (\<lambda>x. Inl ()) xs")
  apply (rotate_tac 2)
  apply (erule ssubst)
  apply (subst interleave_only_left)
  apply simp
  apply (metis traj_lfilter_lefts)
  apply (simp (no_asm) add: rights_def)
  apply (simp add: lfilter_lmap)
  apply (subst rights_def_var)+
  apply (subst rights_interleave[where g = id])
  apply simp
  apply (subst lfilter_right_interleave)
  apply (subgoal_tac "lfilter is_right (traj zs) = lmap (\<lambda>x. Inr ()) ys")
  apply (rotate_tac 2)
  apply (erule ssubst)
  apply (subst interleave_only_right)
  apply simp
  apply (metis traj_lfilter_rights)
  apply (simp add: traj_def)
  apply simp
  by (simp add: traj_def [symmetric])

lemma [simp]: "\<ll> zs = lmap f xs \<Longrightarrow> \<rr> zs = lmap g ys \<Longrightarrow> lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> (interleave (traj zs) xs ys) = zs"
  by (subst reinterleave[symmetric, where t = zs], simp add: lmap_interleave)

lemma [simp]: "is_left (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = is_left x"
  by (cases x) auto

lemma [simp]: "is_right (\<langle>Inl \<circ> f,Inr \<circ> g\<rangle> x) = is_right x"
  by (cases x) auto

lemma tshuffle_words_map:
  fixes f :: "'a \<Rightarrow> 'b"
  and g :: "'c \<Rightarrow> 'd"
  shows "lmap f xs \<sha> lmap g ys = lmap \<langle>Inl \<circ> f, Inr \<circ> g\<rangle> ` (xs \<sha> ys)"
proof (auto simp add: tshuffle_words_def image_def)
  fix zs
  assume "\<ll> zs = lmap f xs" and "\<rr> zs = lmap g ys"
  thus "\<exists>zs'. \<ll> zs' = xs \<and> \<rr> zs' = ys \<and> zs = lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs'"
    by (rule_tac x = "interleave (traj zs) xs ys" in exI) (auto intro: traj_equality)
next
  fix zs
  show "\<ll> (lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs) = lmap f (\<ll> zs)"
    apply (simp add: lefts_def lfilter_lmap)
    apply (rule lmap_lfilter_eq)
    by (metis is_right.simps(1) not_is_left o_eq_dest_lhs sum.simps(5) sumE unl.simps(1))
  show "\<rr> (lmap \<langle>Inl \<circ> f,Inr \<circ> g\<rangle> zs) = lmap g (\<rr> zs)"
    apply (simp add: rights_def lfilter_lmap)
    apply (rule lmap_lfilter_eq)
    by (metis comp_apply is_left.simps(1) not_is_left sum.simps(6) sumE unr.simps(1))
qed
  
lemma [simp]: "\<langle>id,id\<rangle> \<circ> \<langle>Inl \<circ> \<langle>id,id\<rangle>,Inr\<rangle> = \<langle>\<langle>id,id\<rangle>,id\<rangle>"
proof -
  {
    fix x :: "('a + 'a) + 'a"
    have "(\<langle>id,id\<rangle> \<circ> \<langle>Inl \<circ> \<langle>id,id\<rangle>,Inr\<rangle>) x = \<langle>\<langle>id,id\<rangle>,id\<rangle> x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

lemma [simp]: "\<langle>id,id\<rangle> \<circ> \<langle>Inl,Inr \<circ> \<langle>id,id\<rangle>\<rangle> = \<langle>id,\<langle>id,id\<rangle>\<rangle>"
proof -
  {
    fix x :: "'a + ('a + 'a)"
    have "(\<langle>id,id\<rangle> \<circ> \<langle>Inl,Inr \<circ> \<langle>id,id\<rangle>\<rangle>) x = \<langle>id,\<langle>id,id\<rangle>\<rangle> x"
      by (cases x) auto
  }
  thus ?thesis by auto
qed

lemma lmap_sum_elim_simp1: "lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle>"
proof -
  {
    fix xs :: "(('a + 'a) + 'a) llist"
    have "(lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) xs = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> xs"
      by (subst o_def) simp
  }
  thus ?thesis by auto
qed

lemma lmap_sum_elim_simp2: "lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle>"
proof -
  {
    fix xs :: "('a + ('a + 'a)) llist"
    have "(lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) xs = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> xs"
      by (subst o_def) simp
  }
  thus ?thesis by auto
qed

text {* Now we can prove the associativity of shuffle *}

lemma shuffle_assoc: "(X \<parallel> Y) \<parallel> Z = X \<parallel> (Y \<parallel> Z)"
proof -
  have "(X \<parallel> Y) \<parallel> Z = lmap \<langle>id,id\<rangle> ` ((lmap \<langle>id,id\<rangle> ` (X \<Sha> Y)) \<Sha> Z)"
    by (simp add: shuffle_to_tshuffle)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> y |x y. x \<in> lmap \<langle>id,id\<rangle> ` (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>id,id\<rangle> x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` (x \<sha> y)|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (simp add: tshuffle_words_map[where g = id, simplified])
  also have "... = lmap \<langle>id,id\<rangle> ` lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> (X \<Sha> Y) \<and> y \<in> Z}"
    by (auto simp add: image_def)
  also have "... = (lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl \<circ> \<langle>id,id\<rangle>, Inr\<rangle>) ` ((X \<Sha> Y) \<Sha> Z)"
    by (metis image_comp tshuffle_def)
  also have "... = lmap \<langle>\<langle>id,id\<rangle>,id\<rangle> ` ((X \<Sha> Y) \<Sha> Z)"
    by (simp only: lmap_sum_elim_simp1)
  also have "... = lmap \<langle>id,\<langle>id,id\<rangle>\<rangle> ` (X \<Sha> (Y \<Sha> Z))"
    by (metis tshuffle_assoc)
  also have "... = (lmap \<langle>id,id\<rangle> \<circ> lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle>) ` (X \<Sha> (Y \<Sha> Z))"
    by (simp only: lmap_sum_elim_simp2)
  also have "... = lmap \<langle>id,id\<rangle> ` lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (metis image_comp tshuffle_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{lmap \<langle>Inl, Inr \<circ> \<langle>id,id\<rangle>\<rangle> ` (x \<sha> y)|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> lmap \<langle>id,id\<rangle> y|x y. x \<in> X \<and> y \<in> (Y \<Sha> Z)}"
    by (simp add: tshuffle_words_map[where f = id, simplified])
  also have "... = lmap \<langle>id,id\<rangle> ` \<Union>{x \<sha> y|x y. x \<in> X \<and> y \<in> lmap \<langle>id,id\<rangle> ` (Y \<Sha> Z)}"
    by (auto simp add: image_def)
  also have "... = lmap \<langle>id,id\<rangle> ` (X \<Sha> (lmap \<langle>id,id\<rangle> ` (Y \<Sha> Z)))"
    by (simp add: tshuffle_def)
  also have "... = X \<parallel> (Y \<parallel> Z)"
    by (simp add: shuffle_to_tshuffle)
  finally show ?thesis .
qed

definition preimp :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" (infixr "\<rightharpoondown>" 65) where
  "X \<rightharpoondown> Y \<equiv> \<Union>{Z. X \<cdot> Z \<subseteq> Y}"

definition FIN where "FIN = {xs. lfinite xs}"

lemma is_right_nth_traj: "\<not> lfinite xs \<Longrightarrow> is_right (lnth xs n) \<Longrightarrow> is_right (lnth (lmap \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> xs) n)"
  apply (subst lnth_lmap)
  apply (metis enat_ile llength_eq_enat_lfiniteD not_less)
  apply (cases "lnth xs n")
  by simp_all

lemma is_left_nth_traj: "\<not> lfinite xs \<Longrightarrow> is_left (lnth xs n) \<Longrightarrow> is_left (lnth (lmap \<langle>\<lambda>x. Inl (),\<lambda>x. Inr ()\<rangle> xs) n)"
  apply (subst lnth_lmap)
  apply (metis enat_ile llength_eq_enat_lfiniteD not_less)
  apply (cases "lnth xs n")
  by simp_all

lemma fair_traj: "\<not> lfinite xs \<Longrightarrow> fair xs \<Longrightarrow> fair (traj xs)"
  apply (auto simp add: traj_def fair_def)
  apply (metis is_right_nth_traj)
  apply (metis is_left_nth_traj)
  by (metis (full_types) is_left_nth_traj is_right_nth_traj not_is_right)+

lemma one_elem_llist:
  assumes inf_xs: "\<not> lfinite xs" and inf_ys: "\<not> lfinite ys"
  shows "lmap (\<lambda>x. z) xs = lmap (\<lambda>x. z) ys"
proof -
  have "(lmap (\<lambda>x. z) xs, lmap (\<lambda>x. z) ys) \<in> {(lmap (\<lambda>x. z) xs', lmap (\<lambda>x. z) ys')|xs' ys'. \<not> lfinite xs' \<and> \<not> lfinite ys' \<and> xs' \<in> ltls xs \<and> ys' \<in> ltls ys}"
    apply auto
    by (metis inf_xs inf_ys ltls.intros(1))
  thus ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q) note q = this[simplified]
    then obtain xs' and ys' where q_def: "q = (lmap (\<lambda>x. z) xs', lmap (\<lambda>x. z) ys')"
    and inf_xs': "\<not> lfinite xs'" and inf_ys': "\<not> lfinite ys'" and xs'_tl: "xs' \<in> ltls xs" and ys'_tl: "ys' \<in> ltls ys"
      by auto
    have ?EqLCons
      apply (rule_tac x = "lmap (\<lambda>x. z) (ltl xs')" in exI)
      apply (rule_tac x = "lmap (\<lambda>x. z) (ltl ys')" in exI)
      apply (rule_tac x = z in exI)+
      apply (auto simp add: q_def)
      apply (metis inf_xs' llist.collapse(2) llist.simps(13) lnull_imp_lfinite)
      apply (metis inf_ys' llist.collapse(2) llist.simps(13) lnull_imp_lfinite)
      apply (rule_tac x = "ltl xs'" in exI)
      apply auto
      apply (rule_tac x = "ltl ys'" in exI)
      by (metis (full_types) inf_xs' inf_ys' lfinite_ltl ltls.intros(2) xs'_tl ys'_tl)
    thus ?case
      by auto
  qed
qed

lemma infinite_fair_shuffle:
  assumes inf_xs: "\<not> lfinite xs" and inf_ys: "\<not> lfinite ys"
  shows "(xs \<sha> ys) \<subseteq> {xs \<triangleright> t \<triangleleft> ys|t. fair t}"
proof (auto simp add: FIN_def)
  fix zs
  assume "zs \<in> xs \<sha> ys"
  hence "zs = xs \<triangleright> traj zs \<triangleleft> ys" and "fair (traj zs)"
    by - (metis (lifting, full_types) mem_Collect_eq reinterleave tshuffle_words_def, metis fair_non_empty fair_traj inf_xs inf_ys shuffle_fair)
  thus "\<exists>t. zs = xs \<triangleright> t \<triangleleft> ys \<and> fair t"
    by blast
qed

lemma interleave_left: "xs \<triangleright> LCons (Inl ()) ts \<triangleleft> ys = LCons (Inl (lhd xs)) (ltl xs \<triangleright> ts \<triangleleft> ys)"
  by (auto simp add: interleave_def)

lemma interleave_right: "xs \<triangleright> LCons (Inr ()) ts \<triangleleft> ys = LCons (Inr (lhd ys)) (xs \<triangleright> ts \<triangleleft> ltl ys)"
  by (auto simp add: interleave_def)

lemma lfinite_lefts: "lfinite xs \<Longrightarrow> lfinite (\<ll> xs)"
  by (simp add: lefts_def)

lemma lfinite_rights: "lfinite xs \<Longrightarrow> lfinite (\<rr> xs)"
  by (simp add: rights_def)

lemma lfinite_traj': "lfinite zs \<Longrightarrow> zs = xs \<triangleright> t \<triangleleft> ys \<Longrightarrow> lfinite t"
proof (induct zs arbitrary: t xs ys rule: lfinite_induct)
  fix t and xs :: "'a llist" and ys :: "'b llist"
  case Nil thus ?case
    by (metis lfinite_code(1) traj_LNil traj_interleave)
next
  fix t xs ys
  case (Cons z zs)
  thus ?case
    by (auto intro: sum_list_cases simp add: interleave_left interleave_right)
qed

lemma lfinite_traj: "lfinite (xs \<triangleright> t \<triangleleft> ys) \<Longrightarrow> lfinite t"
  by (metis lfinite_traj')

lemma shuffle_dist [simp]: "X \<parallel> (Y \<union> Z) = X \<parallel> Y \<union> X \<parallel> Z"
  by (simp only: shuffle_def Union_Un_distrib[symmetric]) (rule arg_cong, fast)

lemma lfilter_right_left: "lfilter is_right x = LNil \<Longrightarrow> lfilter is_left x = x"
  by (metis lfilter_empty_conv lfilter_id_conv not_is_right)

lemma lfilter_left_right: "lfilter is_left x = LNil \<Longrightarrow> lfilter is_right x = x"
  by (metis lfilter_empty_conv lfilter_id_conv not_is_right)

lemma lmap2_id_var: "(\<And>x. x \<in> lset xs \<Longrightarrow> f (g x) = x) \<Longrightarrow> lmap f (lmap g xs) = xs"
  by simp

lemma [simp]: "lmap \<langle>id,id\<rangle> (lmap Inl xs) = xs"
  by (metis all_lefts id_def lefts_def_var lefts_mapl lmap.id lmap_lfilter_left)

lemma [simp]: "lmap \<langle>id,id\<rangle> (lmap Inr xs) = xs"
  by (metis all_rights id_def lmap.id lmap_lfilter_right rights_def_var rights_mapr)

lemma lmap3_id_var: "(\<And>x. x \<in> lset xs \<Longrightarrow> f (g x) = x) \<Longrightarrow> lmap (\<lambda>x. f (g x)) xs = xs"
  by simp

lemma tshuffle_LNil [simp]: "xs \<sha> LNil = {lmap Inl xs}"
  apply (simp add: tshuffle_words_def)
  apply (auto simp add: lefts_def rights_def lmap_eq_LNil)
  apply (rule sym)
  apply (subst lmap3_id_var[where f = Inl, simplified])
  apply auto
  apply (metis (full_types) is_left.simps(2) sumE unl.simps(1))
  by (metis lfilter_right_left)

lemma tshuffle_LNil_sym [simp]: "LNil \<sha> ys = {lmap Inr ys}"
  apply (simp add: tshuffle_words_def)
  apply (auto simp add: lefts_def rights_def)
  apply (rule sym)
  apply (subst lmap2_id_var[where f = id, simplified])
  apply (rename_tac xs x)
  apply (metis is_right.simps(2) lfilter_empty_conv lfilter_left_right lmap_eq_LNil not_is_right sumE unr.simps(1))
  by (metis LNil_eq_lmap lfilter_left_right)

lemma shuffle_one: "X \<parallel> {LNil} = X"
  by (auto simp add: shuffle_def)

interpretation par!: dioid_one_zero "op \<union>" "op \<parallel>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>"
  apply default
  apply (rule Un_assoc)
  apply (rule Un_commute)
  apply (rule shuffle_assoc)
  apply (metis shuffle_dist shuffle_comm)
  apply (metis shuffle_comm shuffle_one)
  apply (metis shuffle_one)
  apply simp
  apply (simp add: shuffle_def)
  apply (simp add: shuffle_def)
  apply (metis Un_upper1 sup_absorb1 sup_commute)
  apply (metis psubset_eq)
  apply simp
  by (rule shuffle_dist)

interpretation seq!: dioid_one_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>"
  apply default
  apply (metis l_prod_assoc)
  apply (metis l_prod_distr)
  apply (metis l_prod_one(1))
  apply (metis l_prod_one(2))
  apply simp
  apply (metis l_prod_zero)
  apply (metis par.add_idem')
  by (metis l_prod_distl)

no_notation
  Signatures.star_op_class.star ("_\<^sup>\<star>" [101] 100) and
  Signatures.omega_op_class.omega ("_\<^sup>\<omega>" [101] 100)

definition omega :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<omega>" [101] 100) where
  "X\<^sup>\<omega> = (\<nu> Y. X\<cdot>Y)"

definition star :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<star>" [101] 100) where
  "X\<^sup>\<star> = (\<mu> Y. {LNil} \<union> X\<cdot>Y)"

definition loop :: "'a lan \<Rightarrow> 'a lan" ("_\<^sup>\<infinity>" [101] 100) where
  "X\<^sup>\<infinity> = X\<^sup>\<star> \<union> X\<^sup>\<omega>"

lemma [simp,intro!]: "mono (op \<cdot> x)"
  by (metis mono_def seq.mult_isol)

lemma iso_Un1 [intro!]: "mono (\<lambda>Y. f Y) \<Longrightarrow> mono (\<lambda>Y. X \<union> f Y)"
  by (auto simp add: mono_def)

lemma iso_Un2 [intro!]: "mono (\<lambda>Y. f Y) \<Longrightarrow> mono (\<lambda>Y. f Y \<union> X)"
  by (auto simp add: mono_def)

interpretation seq!: left_kleene_algebra_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>" star
proof
  fix X Y Z :: "'a lan"
  show "{LNil} \<union> X \<cdot> X\<^sup>\<star> \<subseteq> X\<^sup>\<star>"
    unfolding star_def
    by (subst fp_compute[symmetric], metis order_refl par.add_iso_var seq.mult_isol, blast)

  show "Z \<union> X \<cdot> Y \<subseteq> Y \<longrightarrow> X\<^sup>\<star> \<cdot> Z \<subseteq> Y"
  proof
    assume "Z \<union> X \<cdot> Y \<subseteq> Y"
    hence "(\<mu> Y. Z \<union> X \<cdot> Y) \<subseteq> Y"
      by (rule fp_induct[rotated 1]) (metis (lifting) l_prod_isor subset_refl sup_mono)
    moreover have "X\<^sup>\<star> \<cdot> Z = (\<mu> Y. Z \<union> X \<cdot> Y)"
      unfolding star_def
      by (rule fixpoint_fusion) (auto simp only: lower_is_jp join_preserving_def l_prod_inf_distr o_def l_prod_distr l_prod_one l_prod_assoc)
    ultimately show "X\<^sup>\<star> \<cdot> Z \<subseteq> Y"
      by simp
  qed
qed

interpretation seq!: left_omega_algebra_zerol "op \<union>" "op \<cdot>" "{LNil}" "{}" "op \<subseteq>" "op \<subset>" star omega
proof
  fix X Y Z :: "'a lan"
  show omega_unfold: "X \<cdot> X\<^sup>\<omega> = X\<^sup>\<omega>"
    unfolding omega_def by (subst gfp_compute[symmetric]) (auto simp: seq.mult_isol)

  have omega_coinduct: "\<And>X Y Z. Y \<subseteq> X\<cdot>Y \<Longrightarrow> Y \<subseteq> X\<^sup>\<omega>"
    unfolding omega_def by (rule gfp_induct) (auto simp: seq.mult_isol)

  have omega_star_fuse: "X\<^sup>\<omega> \<union> X\<^sup>\<star>\<cdot>Z = (\<nu> Y. Z \<union> X \<cdot> Y)" unfolding omega_def
  proof (rule greatest_fixpoint_fusion, auto simp add: o_def)
    show "upper_adjoint (\<lambda>Y. Y \<union> X\<^sup>\<star> \<cdot> Z)"
      apply (simp add: upper_adjoint_def galois_connection_def)
      apply (subst Un_commute)
      apply (subst Diff_subset_conv[symmetric])
      apply (rule_tac x = "\<lambda>x. x - X\<^sup>\<star> \<cdot> Z" in exI)
      by simp
  next
    show "(\<lambda>Y. X \<cdot> Y \<union> X\<^sup>\<star> \<cdot> Z) = (\<lambda>Y. Z \<union> (X \<cdot> Y \<union> X \<cdot> (X\<^sup>\<star> \<cdot> Z)))"
      apply (rule ext)
      apply (subst seq.star_unfoldl_eq[symmetric])
      apply (subst l_prod_distr)
      apply simp
      by (simp only: l_prod_assoc Un_assoc[symmetric])
  qed

  assume "Y \<subseteq> Z \<union> X\<cdot>Y" thus "Y \<subseteq> X\<^sup>\<omega> \<union> X\<^sup>\<star>\<cdot>Z"
    by - (simp only: omega_star_fuse, rule gfp_induct, auto, metis set_mp seq.mult_isol)
qed

lemma sumlist_cases [case_names LConsl LConsr LNil]:
  assumes c1: "(\<And>z zs. xs = LCons (Inl z) zs \<Longrightarrow> P)"
  and c2: "(\<And>z zs. xs = LCons (Inr z) zs \<Longrightarrow> P)"
  and c3: "xs = LNil \<Longrightarrow> P"
  shows "P"
proof (cases xs)
  case LNil from this and c3 show P by blast
next
  case (LCons x xs) from this and c1 c2 show P by (cases x) auto
qed

lemma llength_lr: "llength xs = llength (lfilter is_left xs) + llength (lfilter is_right xs)"
proof -
  have "(llength xs, llength (lfilter is_left xs) + llength (lfilter is_right xs)) \<in>
        {(llength xs, llength (lfilter is_left xs) + llength (lfilter is_right xs)) |xs::('a + 'b) llist. True}"
    by auto
  thus ?thesis
  proof(coinduct rule: enat_equalityI)
    case (Eq_enat n m)
    from this[simplified] obtain xs :: "('a + 'b) llist"
    where [simp]: "n = llength xs"
    and [simp]: "m = llength (lfilter is_left xs) + llength (lfilter is_right xs)"
      by blast
    show ?case
      by (rule sumlist_cases[of xs]) (auto simp add: eSuc_plus iadd_Suc_right)
  qed
qed

lemma lfinite_lr: "lfinite (\<ll> zs) \<Longrightarrow> lfinite (\<rr> zs) \<Longrightarrow> lfinite zs"
  apply (drule lfinite_llength_enat)+
  apply (erule exE)+
  apply (rename_tac n m)
  apply (rule_tac n = "n + m" in llength_eq_enat_lfiniteD)
  apply (subst llength_lr)
  by (simp add: rights_def lefts_def)

lemma lfinite_shuffle: "lfinite xs \<Longrightarrow> lfinite ys \<Longrightarrow> zs \<in> xs \<sha> ys \<Longrightarrow> lfinite zs"
  by (auto intro: lfinite_lr simp add: tshuffle_words_def)

lemma LCons_tshuffle: "LCons x xs \<sha> LCons y ys = LCons (Inl x) ` (xs \<sha> LCons y ys) \<union> LCons (Inr y) ` (LCons x xs \<sha> ys)"
proof (auto simp add: tshuffle_words_def image_def)
  fix zs 
  assume zs_not_r: "\<forall>xa. \<rr> xa = ys \<longrightarrow>  \<ll> xa = LCons x xs \<longrightarrow> zs \<noteq> LCons (Inr y) xa"
  and zsl: "\<ll> zs = LCons x xs" and zsr: "\<rr> zs = LCons y ys"
  let ?goal = "\<exists>ws. \<ll> ws = xs \<and> \<rr> ws = LCons y ys \<and> zs = LCons (Inl x) ws"
  show ?goal
  proof (cases zs rule: sumlist_cases)
    case LNil
    from this and zsl
    have False
      by (subgoal_tac "\<ll> zs = LNil") auto
    thus ?goal by blast
  next
    case (LConsl z' zs')
    from this and zsl zsr
    show ?goal
      by simp
  next
    case (LConsr z' zs')
    from this and zsl zsr zs_not_r
    have False
      by auto
    thus ?goal by blast
  qed
qed

lemma [simp]: "lmap \<langle>id,id\<rangle> ` LCons (Inl x) ` X = LCons x ` lmap \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> ` LCons (Inr x) ` X = LCons x ` lmap \<langle>id,id\<rangle> ` X"
  by (auto simp add: image_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> ` (LCons (Inl x) ` (xs \<sha> LCons y ys) \<union> LCons (Inr y) ` (LCons x xs \<sha> ys))
              = (LCons x ` lmap \<langle>id,id\<rangle> ` (xs \<sha> LCons y ys) \<union> LCons y ` lmap \<langle>id,id\<rangle> ` (LCons x xs \<sha> ys))"
  by (simp add: image_Un)

lemma lfinite_lappend_shuffle: "lfinite xs \<Longrightarrow> xs \<frown> ys \<in> lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)"
proof (induct xs arbitrary: ys rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs) note ih_xs = this
  show ?case
  proof (cases ys, simp)
    fix z zs assume [simp]: "ys = LCons z zs"
    show "?case" using ih_xs
      by (simp add: LCons_tshuffle)
  qed
qed

lemma fin_l_prod: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y = {xs \<frown> ys|xs ys. xs \<in> X \<and> ys \<in> Y}"
  by (auto simp add: FIN_def l_prod_def)

lemma fin_l_prod_le_shuffle: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y \<subseteq> X \<parallel> Y"
  by (auto simp add: fin_l_prod shuffle_def FIN_def) (metis lfinite_lappend_shuffle mem_Collect_eq set_mp)

lemma fin_shuffle: "X \<subseteq> FIN \<Longrightarrow> Y \<subseteq> FIN \<Longrightarrow> X \<parallel> Y \<subseteq> FIN"
  by (auto simp add: shuffle_def FIN_def) (metis in_mono lfinite_shuffle mem_Collect_eq)

lemma word_exchange:
  assumes "lfinite a" and "lfinite b"
  shows "(lmap \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (lmap \<langle>id,id\<rangle> ` (c \<sha> d)) \<subseteq> lmap \<langle>id, id\<rangle> ` ((b \<frown> c) \<sha> (a \<frown> d))"
proof -
  have a: "lmap \<langle>id,id\<rangle> ` (a \<sha> b) \<subseteq> FIN"
    by (auto intro!: lfinite_shuffle assms simp add: FIN_def)
  have b: "\<And>z. {y. \<exists>x. \<ll> x = \<ll> z \<and> \<rr> x = \<rr> z \<and> y = lmap \<langle>id,id\<rangle> x} \<subseteq> FIN \<Longrightarrow> lfinite z"
    by (auto simp add: FIN_def)
  from a show ?thesis
    apply (auto dest!: b simp add: fin_l_prod tshuffle_words_def image_def)
    apply (rule_tac x = "lmap swap xa \<frown> xb" in exI)
    by (simp_all add: lefts_append rights_append lmap_lappend_distrib)
qed

lemma set_comp_mono4:
  assumes fg: "\<And>a b c d. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c \<in> C \<Longrightarrow> d \<in> D \<Longrightarrow> f a b c d \<subseteq> g a b c d"
  shows "\<Union>{f a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D} \<subseteq> \<Union>{g a b c d|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
  using assms by blast

lemma exchange:
  assumes "A \<subseteq> FIN" and "B \<subseteq> FIN"
  shows "(A \<parallel> B) \<cdot> (C \<parallel> D) \<subseteq> (B \<cdot> C) \<parallel> (A \<cdot> D)"
proof -
  have "(A \<parallel> B) \<cdot> (C \<parallel> D) = {x \<frown> y|x y. x \<in> lmap \<langle>id, id\<rangle> ` (A \<Sha> B) \<and> y \<in> lmap \<langle>id, id\<rangle> ` (C \<Sha> D)}"
    by (simp add: fin_l_prod[OF fin_shuffle[OF assms(1) assms(2)]]) (simp add: shuffle_to_tshuffle)
  also have "... = {lmap \<langle>id,id\<rangle> x \<frown> lmap \<langle>id,id\<rangle> y|x y. x \<in> (A \<Sha> B) \<and> y \<in> (C \<Sha> D)}"
    by blast
  also have "... = \<Union>{{lmap \<langle>id,id\<rangle> x \<frown> lmap \<langle>id,id\<rangle> y|x y. x \<in> (a \<sha> b) \<and> y \<in> (c \<sha> d)}|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    by (simp add: tshuffle_def) blast
  also have "... \<subseteq> \<Union>{(lmap \<langle>id,id\<rangle> ` (a \<sha> b)) \<cdot> (lmap \<langle>id,id\<rangle> ` (c \<sha> d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
    apply (rule set_comp_mono4)
    apply (subst fin_l_prod)
    apply (auto simp add: FIN_def)
    by (metis FIN_def assms(1) assms(2) lfinite_shuffle mem_Collect_eq set_mp)
  also have "... \<subseteq> \<Union>{lmap \<langle>id, id\<rangle> ` ((b \<frown> c) \<sha> (a \<frown> d))|a b c d. a \<in> A \<and> b \<in> B \<and> c \<in> C \<and> d \<in> D}"
     apply (rule set_comp_mono4)
     apply (rule word_exchange)
     apply (metis FIN_def assms(1) mem_Collect_eq set_mp)
     by (metis (full_types) FIN_def assms(2) mem_Collect_eq set_mp)
  also have "... = \<Union>{lmap \<langle>id, id\<rangle> ` (bc \<sha> ad)|bc ad. bc \<in> (B \<cdot> C) \<and> ad \<in> (A \<cdot> D)}"
    by (simp add: fin_l_prod[OF assms(2)] fin_l_prod[OF assms(1)]) blast
  also have "... = (B \<cdot> C) \<parallel> (A \<cdot> D)"
    by (simp add: shuffle_def)
  finally show ?thesis .
qed

lemma shuffle_inf_dist: "X \<parallel> (\<Union>\<YY>) = \<Union>{X \<parallel> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: shuffle_def)

primrec power :: "'a lan \<Rightarrow> nat \<Rightarrow> 'a lan" where
  "power x 0 = {LNil}"
| "power x (Suc n) = x \<cdot> power x n"

definition powers :: "'a lan \<Rightarrow> 'a lan set" where
  "powers x  = {y. (\<exists>i. y = power x i)}"

lemma l_prod_inf_distl: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> \<Union>\<YY> = \<Union>{X \<cdot> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: l_prod_def FIN_def)

lemma l_prod_inf_distl': "\<YY> \<noteq> {} \<or> X \<subseteq> FIN \<longleftrightarrow> X \<cdot> \<Union>\<YY> = \<Union>{X \<cdot> Y |Y. Y \<in> \<YY>}"
  by (auto simp add: l_prod_def FIN_def)

lemma preimp_galois: "X \<subseteq> FIN \<Longrightarrow> galois_connection (\<lambda>Y. X\<cdot>Y) (\<lambda>Y. X \<rightharpoondown> Y)"
  apply (simp add: suprema_galois join_preserving_def)
  apply auto
  apply (metis Sup_upper UnCI l_prod_distl sup.absorb1)
  apply (erule rev_mp) back
  apply (subst l_prod_inf_distl)
  apply simp_all
  apply metis
  apply (erule rev_mp) back back
  apply (subst fin_l_prod)
  apply simp_all
  apply (subst preimp_def)
  apply (subst fin_l_prod)
  apply auto
  apply (subst fin_l_prod)
  apply simp
  apply (erule rev_mp) back
  apply (subst preimp_def)
  apply (subst fin_l_prod)
  by auto

lemma "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> X \<rightharpoondown> Z"
  by (drule preimp_galois) (simp add: galois_connection_def)

lemma preimp_elem: "z \<in> X \<rightharpoondown> Y \<longleftrightarrow> (\<exists>Z. X \<cdot> Z \<subseteq> Y \<and> z \<in> Z)"
  by (simp add: preimp_def)

lemma preimp_elem_var: "z \<in> X \<rightharpoondown> Y \<longleftrightarrow> (X \<cdot> {z} \<subseteq> Y)"
  apply (auto simp add: preimp_def)
  by (auto simp add: l_prod_def)

lemma shuffle_elemE: "z \<in> X \<parallel> Y \<Longrightarrow> (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> z \<in> lmap \<langle>id,id\<rangle> ` (x \<sha> y))"
  by (auto simp add: shuffle_def)

lemma double_singleton_shuffle: "{x} \<parallel> {y} = lmap \<langle>id,id\<rangle> ` (x \<sha> y)"
  by (simp add: shuffle_def)

lemma preimp_exchange:
  assumes "X \<subseteq> FIN"
  and "Y \<subseteq> FIN"
  shows "(X \<rightharpoondown> Z) \<parallel> (Y \<rightharpoondown> W) \<subseteq> (X \<parallel> Y) \<rightharpoondown> (W \<parallel> Z)"
  apply (auto simp add: preimp_elem_var)
  apply (drule shuffle_elemE)
  apply (erule exE)+
  apply (simp only: preimp_elem_var)
  apply (rename_tac z z' x y)
  apply (subgoal_tac "z' \<in> (X \<cdot> {x}) \<parallel> (Y \<cdot> {y})")
  apply (metis par.mult_isor shuffle_comm subsetCE)
  apply (subgoal_tac "z' \<in> (X \<parallel> Y) \<cdot> ({x} \<parallel> {y})")
  apply (metis assms(1) assms(2) exchange shuffle_comm subsetCE)
  apply (simp add: double_singleton_shuffle)
  by (metis insert_absorb insert_subset l_prod_isor par.zero_least)

lemma preimp_antitone: "X \<subseteq> Y \<Longrightarrow> Y \<rightharpoondown> Z \<subseteq> X \<rightharpoondown> Z"
  by (auto simp add: preimp_def) (metis l_prod_isol order_trans)

lemma preimp_iso: "X \<subseteq> Y \<Longrightarrow> Z \<rightharpoondown> X \<subseteq> Z \<rightharpoondown> Y"
  by (auto simp add: preimp_def)

definition powers_up_to :: "nat \<Rightarrow> 'a lan \<Rightarrow> 'a lan set" where
  "powers_up_to n x \<equiv> {power x i |i. Suc i \<le> n}"

text {* We now show that $x^*$ can be defined as the sum of the powers of $x$. *}

lemma star_power_fin: assumes finite_x: "x \<subseteq> FIN" shows "x\<^sup>\<star> = \<Union>(powers x)"
proof -
  let ?STAR_FUN = "\<lambda>y. {LNil} \<union> x\<cdot>y"
  have "\<mu> ?STAR_FUN = \<Union>{iter ?STAR_FUN n {} |n. True}"
  proof (rule kleene_lfp)
    fix X :: "'a lan set"
    assume "directed X"
    thus "\<Union>((\<lambda>y. {LNil} \<union> x \<cdot> y) ` X) = {LNil} \<union> x \<cdot> \<Union>X"
      by (subst l_prod_inf_distl) (auto intro!: finite_x simp add: directed_def)
  qed
 
  moreover have "\<forall>n. iter ?STAR_FUN n {} = \<Union>(powers_up_to n x)"
  proof
    fix n show "iter ?STAR_FUN n {} = \<Union>(powers_up_to n x)"
    proof (induct n)
      case 0 show ?case
        by (simp add: iter_def powers_up_to_def)
      case (Suc n)
      have "iter ?STAR_FUN (Suc n) {} = {LNil} \<union> x \<cdot> iter ?STAR_FUN n {}"
        by simp
      moreover have "... = {LNil} \<union> x \<cdot> \<Union>(powers_up_to n x)"
        by (metis Suc)
      moreover have "... = {LNil} \<union> x \<cdot> \<Union>{power x i |i. Suc i \<le> n}"
        by (simp add: powers_up_to_def)
      moreover have "... = {LNil} \<union> \<Union>{x \<cdot> power x i |i. Suc i \<le> n}"
        by (subst l_prod_inf_distl) (auto intro!: finite_x)
      moreover have "... = {LNil} \<union> \<Union>{power x (Suc i) |i. Suc i \<le> n}"
        by simp
      moreover have "... = \<Union>{{LNil}} \<union> \<Union>{power x (Suc i) |i. Suc i \<le> n}"
        by auto
      moreover have "... = \<Union>({{LNil}} \<union> {power x (Suc i) |i. Suc i \<le> n})"
        by auto
      moreover have "... = \<Union>(powers_up_to (Suc n) x)"
        apply (simp only: powers_up_to_def)
        apply (rule arg_cong) back
        apply auto
        prefer 3
        apply (erule_tac x = "i - 1" in allE)
        apply simp
        apply (subgoal_tac "i = 0 \<or> (\<exists>j. i = Suc j)")
        apply (erule disjE)
        apply simp
        apply (erule exE)
        apply simp
        apply (metis not0_implies_Suc)
        apply (metis Language.power.simps(1) le0)
        apply (metis Language.power.simps(2))
        apply (erule_tac x = "i - 1" in allE)
        apply simp
        apply (subgoal_tac "i = 0 \<or> (\<exists>j. i = Suc j)")
        apply (erule disjE)
        apply simp
        apply (erule exE)
        apply simp
        by (metis not0_implies_Suc)
      ultimately show ?case by metis
    qed
  qed

  ultimately have "\<mu> ?STAR_FUN = \<Union>{z. \<exists>i. z = \<Union>(powers_up_to i x)}"
    by auto
  moreover have "... = \<Union>(\<Union> {z. \<exists>i. z = powers_up_to i x})"
    by auto
  moreover have "... = \<Union>(powers x)"
    apply (rule arg_cong) back
    apply safe
    apply (simp_all add: powers_up_to_def powers_def)
    apply metis
    by (metis (lifting, full_types) le_add2 mem_Collect_eq)
  ultimately show ?thesis
    by (metis star_def)
qed

lemma strict_inf_star: "x \<cdot> {} = x \<Longrightarrow> x\<^sup>\<star> = {LNil} \<union> x"
  apply (rule antisym)
  apply (rule seq.star_inductl_one[rule_format])
  apply (metis l_prod_zero seq.mult_assoc set_eq_subset)
  by (metis par.add_lub_var seq.star_ext seq.star_ref)

lemma infinite_power: "X \<cdot> {} = X \<Longrightarrow> xs \<in> Language.power X i \<Longrightarrow> xs \<notin> X \<Longrightarrow> xs = LNil"
  apply (induct i arbitrary: xs)
  apply simp
  apply auto
  by (metis l_prod_zero seq.mult_assoc)

lemma star_power_inf: "x \<cdot> {} = x \<Longrightarrow> x\<^sup>\<star> = \<Union>(powers x)"
  apply (subst strict_inf_star)
  apply assumption
  apply (simp add: powers_def)
  apply safe
  apply simp_all
  apply (rule_tac x = "power x 0" in exI)
  apply simp
  apply (rule_tac x = 0 in exI)
  apply simp
  apply (metis Language.power.simps(2) l_prod_zero seq.mult_assoc)
  by (metis infinite_power)

lemma [simp]: "X \<subseteq> FIN \<Longrightarrow> (X \<parallel> Y \<cdot> {}) = (X \<parallel> Y) \<cdot> {}"
  apply (auto simp add: l_prod_def shuffle_def FIN_def)
  apply (metis (mono_tags) lfinite_rights mem_Collect_eq tshuffle_words_def)  
  apply (rename_tac xs ys zs)
  apply (rule_tac x = "lmap \<langle>id,id\<rangle> ` (xs \<sha> ys)" in exI)
  apply auto
  apply (rule_tac x = xs in exI)
  apply (rule_tac x = ys in exI)
  apply auto
  by (metis in_mono lfinite_shuffle mem_Collect_eq)

lemma zero_mid [simp]: "X \<cdot> {} \<cdot> Z = X \<cdot> {}"
  by (metis l_prod_zero seq.mult_assoc)

lemma power_leq_star: "power x i \<subseteq> x\<^sup>\<star>"
  apply (induct i)
  apply (metis Language.power.simps(1) par.zero_least seq.star_iso seq.star_zero)
  apply simp
  by (metis seq.prod_star_closure seq.star_ext)

lemma star_power1: "\<Union>powers x \<subseteq> x\<^sup>\<star>"
  apply (subst Sup_le_iff)
  apply (rule ballI)
  apply (simp only: powers_def)
  apply simp
  apply (erule exE)
  apply simp
  by (metis power_leq_star)

lemma powers_refl: "x \<in> powers x"
  apply (auto simp add: powers_def)
  apply (rule_tac x = 1 in exI)
  by auto

lemma star_power2: "x\<^sup>\<star> \<subseteq> \<Union>powers x"
proof (rule seq.star_inductl_one[rule_format])
  have "x \<cdot> \<Union>powers x \<subseteq> \<Union>powers x"
    apply (auto simp add: l_prod_def)
    apply (rule_tac x = x in bexI)
    apply simp
    apply (metis powers_refl)
    apply (rule_tac x = "x \<cdot> xa" in bexI)
    apply (simp add: l_prod_def)
    apply (intro disjI2)
    apply (rule_tac x = xs in exI)
    apply (rule_tac x = ys in exI)
    apply auto
    apply (simp add: powers_def)
    apply (erule exE)
    apply (rule_tac x = "Suc i" in exI)
    by simp
  moreover have "{LNil} \<subseteq> \<Union>powers x"
    apply (simp add: powers_def)
    apply (rule_tac x = "{LNil}" in exI)
    apply auto
    apply (rule_tac x = 0 in exI)
    by auto
  ultimately show "{LNil} \<union> x \<cdot> \<Union>powers x \<subseteq> \<Union>powers x"
    by (metis par.add_lub)
qed

lemma star_power: "x\<^sup>\<star> = \<Union>powers x"
  by (metis star_power1 star_power2 subset_antisym)

lemma l_prod_FIN_simp1 [simp]: "((x \<inter> FIN) \<cdot> y) \<inter> FIN = (x \<cdot> y) \<inter> FIN"
  by (auto simp add: l_prod_def FIN_def)

lemma l_prod_FIN_simp2 [simp]: "(x \<cdot> (y \<inter> FIN)) \<inter> FIN = (x \<cdot> y) \<inter> FIN"
  by (auto simp add: l_prod_def FIN_def)

lemma shuffle_FIN_simp1 [simp]: "((x \<inter> FIN) \<parallel> y) \<inter> FIN = (x \<parallel> y) \<inter> FIN"
  apply (auto simp add: FIN_def shuffle_def)
  by (metis (lifting, full_types) imageI lfinite_lefts mem_Collect_eq tshuffle_words_def)

lemma shuffle_FIN_simp2 [simp]: "(x \<parallel> (y \<inter> FIN)) \<inter> FIN = (x \<parallel> y) \<inter> FIN"
  apply (auto simp add: FIN_def shuffle_def)
  by (metis (lifting, full_types) imageI lfinite_rights mem_Collect_eq tshuffle_words_def)

lemma [simp]: "(x \<union> y) \<inter> FIN = (x \<inter> FIN) \<union> (y \<inter> FIN)"
  by auto

lemma star_FIN: "x\<^sup>\<star> \<inter> FIN = (x \<inter> FIN)\<^sup>\<star>"
  apply (simp add: star_def)
  apply (rule fixpoint_fusion)
  apply (subst lower_is_jp)
  apply (simp add: join_preserving_def)
  apply (metis (erased, lifting) Set.insert_mono monoI seq.mult_isol)
  apply (simp add: mono_def)
  apply (metis l_prod_isor subset_insertI2)
  apply (simp add: mono_def o_def)
  apply (rule ext)
  apply auto
  apply (metis Int_iff l_prod_FIN_simp1 l_prod_FIN_simp2)
  apply (metis FIN_def lfinite_LNil mem_Collect_eq)
  apply (metis Int_iff l_prod_distr par.order_prop seq.mult_isol subsetCE subsetI)
  by (metis Int_lower1 fin_l_prod_le_shuffle fin_shuffle inf_sup_aci(1) subset_eq)

lemma interleave_append:
  assumes "zs \<in> xs \<sha> ys"
  and "t \<frown> t' = traj zs"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown> (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)"
proof -
  {
    assume "\<not> lfinite t"
    moreover have "\<And>xs ys. \<not> lfinite (xs \<triangleright> t \<triangleleft> ys)"
      by (metis calculation lfinite_traj)
    ultimately have ?thesis using assms
      apply (auto simp add: lappend_inf)
      apply (subst lappend_inf)
      apply (simp add: traj_def)
      apply blast
      by (metis (lifting, full_types) dual_order.refl ltake_all mem_Collect_eq tshuffle_words_def)
  }
  moreover
  {
    assume "lfinite t"
    hence "?thesis" using assms
    proof (induct t arbitrary: xs ys zs rule: lfinite_induct)
      case Nil thus ?case by simp
    next
      case (Cons w ws)
      thus ?case
        apply (cases w)
        apply (simp add: interleave_left)
        apply (subgoal_tac "ltl zs \<in> ltl xs \<sha> ys")
        apply (subgoal_tac "ws \<frown> t' = traj (ltl zs)")
        apply (metis (hide_lams, no_types) interleave_left ldrop_ltl ltake_ltl)
        apply (metis interleave_left ltl_simps(2) reinterleave traj_interleave)
        apply (simp add: tshuffle_words_def)
        apply (metis interleave_left lefts_LConsl ltl_simps(2) reinterleave rights_LConsl)
        apply (simp add: interleave_right)
        apply (subgoal_tac "ltl zs \<in> xs \<sha> ltl ys")
        apply (subgoal_tac "ws \<frown> t' = traj (ltl zs)")
        apply (metis (hide_lams, no_types) interleave_right ldrop_ltl ltake_ltl)
        apply (metis interleave_right ltl_simps(2) reinterleave traj_interleave)
        apply (simp add: tshuffle_words_def)
        by (metis interleave_right lefts_LConsr ltl_simps(2) reinterleave rights_LConsr)
    qed
  }
  ultimately show ?thesis by auto
qed

lemma traj_to_shuffle:
  assumes "llength (\<ll> t) = llength xs"
  and "llength (\<rr> t) = llength ys"
  shows "\<exists>zs. t = traj zs \<and> zs \<in> xs \<sha> ys"
  using assms
  apply (auto simp add: tshuffle_words_def)
  apply (rule_tac x = "xs \<triangleright> t \<triangleleft> ys" in exI)
  apply auto
  apply (metis lefts_interleave_llength traj_interleave)
  by (metis rights_interleave_llength traj_interleave)

lemma interleave_append_llength:
  assumes "llength (\<ll> (t \<frown> t')) = llength xs"
  and "llength (\<rr> (t \<frown> t')) = llength ys"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown> (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)"
  by (metis (hide_lams, no_types) assms(1) assms(2) interleave_append traj_to_shuffle)

coinductive env :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" for "R" where
  EqNil [intro!,simp]: "env R LNil"
| EqSingle [intro!,simp]: "env R (LCons \<sigma> LNil)"
| EqPair [intro!]: "(snd \<sigma>, fst \<sigma>') \<in> R \<Longrightarrow> env R (LCons \<sigma>' t) \<Longrightarrow> env R (LCons \<sigma> (LCons \<sigma>' t))"

lemma env_tl [dest]: "env R (LCons \<sigma> t) \<Longrightarrow> env R t"
  by (erule env.cases) auto

lemma env_LConsD [dest]: "env R (LCons \<sigma> (LCons \<sigma>' t)) \<Longrightarrow> (snd \<sigma>, fst \<sigma>') \<in> R"
  by (erule env.cases) auto

lemma env_iso: "R \<subseteq> S \<Longrightarrow> env R xs \<Longrightarrow> env S xs"
proof -
  assume "R \<subseteq> S" and "env R xs"
  hence "R \<subseteq> S \<and> env R xs"
    by auto
  thus ?thesis
  proof coinduct
    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'" 
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          by auto
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed  

(* Can this be moved up? *)
no_notation Cons (infixr "#" 65)
notation LCons (infixr "#" 65)

definition Env :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<Colon>" 52) where
  "R \<Colon> X \<equiv> X \<inter> Collect (env (R\<^sup>*))"

lemma env_interE1 [elim]: "env (R \<inter> S) x \<Longrightarrow> env S x"
proof -
  assume "env (R \<inter> S) x"
  thus ?thesis
  proof coinduct
    case (env t)
    show ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          by auto
        thus "?EqSingle \<or> ?EqPair" by simp
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_interE2 [elim]: "env (R \<inter> S) x \<Longrightarrow> env R x"
  by (metis env_interE1 inf_commute)

lemma env_InterE: "env (\<Inter>\<RR>) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env R x"
proof -
  assume "env (\<Inter>\<RR>) x" and "R \<in> \<RR>"
  hence "env (\<Inter>\<RR>) x \<and> R \<in> \<RR>" by simp
  thus "env R x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_InterE_star: "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<Longrightarrow> R \<in> \<RR> \<Longrightarrow> env (R\<^sup>*) x"
proof -
  assume "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x" and "R \<in> \<RR>"
  hence "env ((\<Inter>{R\<^sup>* |R. R \<in> \<RR>})\<^sup>*) x \<and> R \<in> \<RR>" by simp
  thus "env (R\<^sup>*) x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "?EqPair"
          apply auto
          apply (drule env_LConsD)
          apply (erule set_rev_mp)
          apply (subst rtrancl_idemp[symmetric]) back back
          apply (rule rtrancl_mono)
          by auto
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_interI [intro]: "env R t \<Longrightarrow> env S t \<Longrightarrow> env (R \<inter> S) t"
proof -
  assume "env R t" and "env S t"
  hence "env R t \<and> env S t"
    by auto
  thus "env (R \<inter> S) t"
  proof (coinduct)
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        show "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma env_InterI [intro]: "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t) \<Longrightarrow> env (\<Inter>\<RR>) t"
proof -
  assume "(\<And>R. R \<in> \<RR> \<Longrightarrow> env R t)"
  hence "(\<forall>R. R \<in> \<RR> \<longrightarrow> env R t)"
    by auto
  thus "env (\<Inter>\<RR>) t"
  proof (coinduct)
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        show "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma Env_continuous: "R \<Colon> (\<Union>\<XX>) = \<Union>{R \<Colon> X |X. X \<in> \<XX>}"
  by (auto simp add: Env_def)

lemma Env_inter [simp]: "R \<Colon> X \<inter> Y = (R \<Colon> X) \<inter> (R \<Colon> Y)"
  by (metis Env_def Int_assoc inf_commute inf_left_idem)

lemma Env_union [simp]: "R \<Colon> (X \<union> Y) = (R \<Colon> X) \<union> (R \<Colon> Y)"
  by (auto simp add: Env_def)

lemma Env_coextensive [intro!]: "R \<Colon> X \<subseteq> X"
  by (auto simp add: Env_def)

lemma Env_iso [intro]: "X \<subseteq> Y \<Longrightarrow> R \<Colon> X \<subseteq> R \<Colon> Y"
  by (auto simp add: Env_def)

lemma Env_idem [simp]: "R \<inter> S \<Colon> X \<subseteq> R \<Colon> S \<Colon> X"
  apply (auto simp add: Env_def)
  apply (metis env_interE1 inf_absorb1 inf_sup_ord(2) rtrancl_mono)
  by (metis env_interE2 inf_absorb2 inf_sup_ord(1) rtrancl_mono)

lemma Env_inter2: "R\<^sup>* \<inter> S\<^sup>* \<Colon> X = (R \<Colon> X) \<inter> (S \<Colon> X)"
  apply (auto simp add: Env_def)
  apply (metis env_interE2 inf.cobounded1 inf_absorb2 rtrancl_subset_rtrancl)
  apply (erule rev_mp)+
  apply (subst Int_commute)
  apply (intro impI)
  apply (metis env_interE2 inf.cobounded1 inf_absorb2 rtrancl_subset_rtrancl)
  by (metis env_interE1 env_interI le_iff_inf r_into_rtrancl subsetI)

lemma Env_set: "R \<Colon> X = {x. x \<in> X \<and> env (R\<^sup>*) x}"
  by (auto simp add: Env_def)

definition EnvUp :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<leadsto>" 52) where
  "R \<leadsto> X \<equiv> {x. x \<in> X \<or> \<not> env (R\<^sup>*) x}"

definition rely :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rely R x y \<equiv> (\<exists>z \<sigma> \<sigma>' \<tau> \<tau>' \<tau>'' x' y'. x = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x')
                                       \<and> y = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>'') # y')
                                       \<and> (\<sigma>',\<tau>) \<notin> (R\<^sup>*)
                                       \<and> lfinite z
                                       \<and> env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))) \<or> x = y"

definition rely' ::  "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rely' R x y \<equiv> (\<exists>z \<sigma> \<sigma>' \<tau> \<tau>' \<tau>'' x' y'. x = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x')
                                        \<and> y = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>'') # y')
                                        \<and> (\<sigma>',\<tau>) \<notin> (R\<^sup>*)
                                        \<and> lfinite z
                                        \<and> env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil)))"

lemma rely_def_var: "rely R x y \<longleftrightarrow> rely' R x y \<or> x = y"
  by (simp only: rely_def rely'_def)

lemma rely_refl: "rely R x x"
  by (auto simp add: rely_def)

lemma rely_sym': "rely' R x y \<Longrightarrow> rely' R y x"
  apply (simp add: rely'_def)
  apply (erule exE)+
  apply (rule_tac x = z in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  by auto

lemma rely_sym: "rely R x y \<longleftrightarrow> rely R y x"
  by (simp add: rely_def_var) (auto intro: rely_sym')

lemma rely_trans': "rely' R x y \<Longrightarrow> rely' R y z \<Longrightarrow> rely' R x z"
  apply (simp add: rely'_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (subgoal_tac "za = zaa")
  apply (metis (no_types, hide_lams) lappend_eq_lappend_conv llist.inject prod.sel(1))
  sorry

lemma rely_trans: "rely R x y \<Longrightarrow> rely R y z \<Longrightarrow> rely R x z"
  apply (auto simp add: rely_def_var)
  by (metis rely_trans')

definition Rely :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<rhd>" 52) where
  "R \<rhd> X \<equiv> {y. \<exists>x\<in>X. rely R x y}"

lemma env_LCons [simp]: "env R ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x) \<longleftrightarrow> (\<sigma>',\<tau>) \<in> R \<and> env R ((\<tau>,\<tau>') # x)"
  by (metis EqPair env_LConsD env_tl prod.collapse prod.sel(1) swap_simp)

lemma env_split [simp]: "lfinite x \<Longrightarrow> env R (x \<frown> (y # y' # ys)) \<longleftrightarrow> env R (x \<frown> (y # LNil)) \<and> env R (y # y' # ys)"
  apply (induct rule: lfinite_induct_pair)
  apply simp
  apply simp
  apply (subgoal_tac "x' = LNil \<or> (\<exists>\<gamma> \<gamma>' z. x' = (\<gamma>,\<gamma>') # z)")
  apply (erule disjE)+
  apply simp
  apply (cases y)
  apply simp
  apply (erule exE)+
  apply simp
  by (metis llist.exhaust prod.collapse)

lemma Rely_EnvUp: "R \<rhd> X \<le> R \<leadsto> X"
  by (auto simp add: EnvUp_def Rely_def rely_def)

lemma Env_galois: "R \<Colon> X \<le> Y \<longleftrightarrow> X \<le> (R \<leadsto> Y)"
  by (auto simp add: Env_set EnvUp_def)

lemma Rely_Env: "X \<le> R \<rhd> Y \<Longrightarrow> R \<Colon> X \<le> Y"
  by (metis Env_galois Rely_EnvUp Un_subset_iff sup.absorb1)

lemma EnvUp_extensive: "X \<subseteq> R \<leadsto> X"
  by (metis Env_coextensive Env_galois)

lemma [simp]: "UNIV\<^sup>* = UNIV"
  by (metis UNIV_I UNIV_eq_I r_into_rtrancl)

lemma env_UNIV [simp]: "env UNIV x"
proof -
  have True by auto
  thus ?thesis
    apply coinduct
    apply auto
    by (metis llist.exhaust prod.collapse)
qed

lemma UNIV_EnvUp [simp]: "UNIV \<leadsto> X = X"
  by (simp add: EnvUp_def)

definition "guar G \<equiv> insert LNil {x. \<forall>x' \<sigma> \<sigma>' x''. x = x' \<frown> ((\<sigma>,\<sigma>') # x'') \<longrightarrow> (\<sigma>,\<sigma>') \<in> G\<^sup>*}"

definition "atomic R \<equiv> {LCons r LNil|r. r \<in> R}"

lemma star_omega_unfold: "X\<^sup>\<star> \<union> X\<^sup>\<omega> = {LNil} \<union> X \<cdot> (X\<^sup>\<star> \<union> X\<^sup>\<omega>)"
  apply (subst seq.star_unfoldl_eq[symmetric])
  apply (subst seq.omega_unfold_eq[symmetric])
  apply (subst l_prod_distl)
  by simp

lemma loop_unfold: "X\<^sup>\<infinity> = {LNil} \<union> X \<cdot> X\<^sup>\<infinity>"
  by (metis loop_def star_omega_unfold)

lemma "t \<in> X \<longleftrightarrow> (\<exists>t'\<in>X. t = t')"
  by metis

lemma guar_hd: "(\<sigma>,\<sigma>') # x \<in> guar G \<Longrightarrow> (\<sigma>,\<sigma>') \<in> G\<^sup>*"
  apply (simp add: guar_def)
  apply (erule_tac x = LNil in allE)
  by auto

lemma guar_tl: "(\<sigma>,\<sigma>') # x \<in> guar G \<Longrightarrow> x \<in> guar G"
  apply (simp add: guar_def)
  apply (rule disjI2)
  apply (intro allI)
  apply (rename_tac x' \<tau> \<tau>')
  apply (erule_tac x = "(\<sigma>, \<sigma>') # x'" in allE)
  by simp

lemma guar_LCons: "(\<sigma>,\<sigma>') \<in> G\<^sup>* \<Longrightarrow> x \<in> guar G \<Longrightarrow> (\<sigma>,\<sigma>') # x \<in> guar G"
  apply (simp add: guar_def)
  apply (erule disjE)
  apply simp
  apply (intro allI impI)
  apply (rename_tac x' \<tau> \<tau>')
  apply (subgoal_tac "x' = LNil \<or> (\<exists>\<gamma> \<gamma>' y. x' = (\<gamma>,\<gamma>') # y)")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  apply (metis LNil_eq_lappend_iff llist.distinct(1))
  apply (metis neq_LNil_conv prod.collapse)
  by (metis eq_LConsD lappend_lnull1 ltl_lappend)

lemma guar_LCons_eq [simp]: "(\<sigma>,\<sigma>') # x \<in> guar G \<longleftrightarrow> ((\<sigma>,\<sigma>') \<in> G\<^sup>* \<and> x \<in> guar G)"
  by (metis guar_LCons guar_hd guar_tl)

lemma guar_UNIV': "UNIV \<subseteq> guar UNIV"
  by (auto simp add: guar_def)

lemma guar_UNIV [simp]: "guar UNIV = UNIV"
  by (metis guar_UNIV' top.extremum_uniqueI)

lemma guar_LNil [simp]: "LNil \<in> guar G"
  by (auto simp add: guar_def)

lemma guar_lappend [simp]: "lfinite x \<Longrightarrow> x \<frown> y \<in> guar G \<longleftrightarrow> (x \<in> guar G \<and> y \<in> guar G)"
  by (induct rule: lfinite_induct_pair) simp_all

lemma guar_lappend1: "x \<frown> y \<in> guar G \<Longrightarrow> x \<in> guar G"
  by (metis guar_lappend lappend_inf)

lemma guar_lappend2: "lfinite x \<Longrightarrow> x \<frown> y \<in> guar G \<Longrightarrow> y \<in> guar G"
  by (metis guar_lappend)

lemma guar_lappend3: "x \<in> guar G \<Longrightarrow> y \<in> guar G \<Longrightarrow> x \<frown> y \<in> guar G"
  by (metis guar_lappend lappend_inf)

lemma guar_inter1: "guar (G \<inter> R) \<subseteq> guar G"
  by (auto simp add: guar_def) (metis contra_subsetD inf_le1 rtrancl_mono)

lemma guar_star: "guar (G\<^sup>*) = guar G"
  by (auto simp add: guar_def)

lemma guar_inter2: "guar G \<inter> guar R \<subseteq> guar (G\<^sup>* \<inter> R\<^sup>*)"
  apply auto
  apply (auto simp add: guar_def)
  by (metis IntI r_into_rtrancl)

lemma guar_inter: "guar G \<inter> guar R = guar (G\<^sup>* \<inter> R\<^sup>*)"
  by (metis Int_commute guar_inter1 guar_inter2 guar_star inf.absorb2 le_inf_iff)

lemma guar_lprod: "(X \<cdot> Y) \<inter> guar G = (X \<inter> guar G) \<cdot> (Y \<inter> guar G)"
  by (auto simp add: l_prod_def)

lemma rg_lem1: "(X \<union> Y) \<parallel> (Z \<union> W) = (X \<parallel> Z) \<union> (X \<parallel> W) \<union> (Y \<parallel> Z) \<union> (Y \<parallel> W)"
  by (metis par.add_assoc' par.distrib_right shuffle_dist)

lemma rg_lem2: "(\<forall>z. z \<in> Y \<parallel> Z \<longrightarrow> P z) \<Longrightarrow> (\<forall>z. z \<in> (X \<inter> Y) \<parallel> Z \<longrightarrow> P z)"
  by auto (metis UnCI inf_commute inf_le1 shuffle_comm shuffle_dist sup.absorb1)

lemma rg_lem3: "z \<in> X \<parallel> Y \<Longrightarrow> (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> z \<in> lmap \<langle>id,id\<rangle> ` (x \<sha> y))"
  by (auto simp add: shuffle_def)

lemma rg_lem4: "\<not> (\<exists>x' \<sigma> \<sigma>' \<tau> \<tau>' x''. x = x' \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x'') \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite x') \<Longrightarrow> env R x"
proof -
  assume "\<not> (\<exists>x' \<sigma> \<sigma>' \<tau> \<tau>' x''. x = x' \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x'') \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite x')"
  thus "env R x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        show "?EqSingle \<or> ?EqPair"
          apply auto
          apply (metis lappend_code(1) lfinite_LNil prod.collapse)
          by (metis lappend_code(2) lfinite_LCons)
      qed
      thus ?case by simp
    qed
  qed
qed

lemma rg_lem4': "\<not> env R x \<Longrightarrow> \<exists>x' \<sigma> \<sigma>' \<tau> \<tau>' x''. x = x' \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x'') \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite x'"
  by (metis (mono_tags, hide_lams) rg_lem4)


lemma env_lem1:
      "lfinite xs' \<Longrightarrow>
       (snd \<sigma>, fst \<sigma>') \<in> R \<Longrightarrow>
       env R (xs' \<frown> ((\<sigma>'', \<sigma>''') # LNil)) \<Longrightarrow>
       (\<sigma>''', \<tau>) \<notin> R \<Longrightarrow>
       \<sigma>' # t'' = xs' \<frown> ((\<sigma>'', \<sigma>''') # (\<tau>, \<tau>') # xs'') \<Longrightarrow>
       env R (\<sigma> # xs' \<frown> ((\<sigma>'', \<sigma>''') # LNil))"
proof (induct xs' rule: lfinite_induct)
  case Nil
  thus ?case
    by simp (metis EqPair EqSingle Nil.prems(1))
next
  case (Cons x xs)
  thus ?case
    by (metis env.simps lappend_code(2) llist.inject)
qed

lemma env_lem2: "\<not> (\<exists>xs' \<sigma> \<sigma>' \<tau> \<tau>' xs''. xs = xs' \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<tau>,\<tau>') xs'') \<and> env R (xs' \<frown> LCons (\<sigma>,\<sigma>') LNil) \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite xs') \<Longrightarrow> env R xs"
proof -
  assume "\<not> (\<exists>xs' \<sigma> \<sigma>' \<tau> \<tau>' xs''. xs = xs' \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<tau>,\<tau>') xs'') \<and> env R (xs' \<frown> LCons (\<sigma>,\<sigma>') LNil) \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite xs')"
  thus "env R xs"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        have "(snd \<sigma>, fst \<sigma>') \<in> R"
          by auto (metis EqSingle lappend_code(1) lfinite.simps prod.collapse)
        from env
        have "?EqPair"
          apply auto
          apply (metis EqSingle lappend_code(1) lfinite.simps prod.collapse)
          apply (erule_tac x = "\<sigma> # xs'" in allE)
          apply (erule_tac x = \<sigma>'' in allE)
          apply (erule_tac x = \<sigma>''' in allE)
          apply (erule impE)
          apply simp
          prefer 2
          apply (erule_tac x = \<tau> in allE)
          apply (erule disjE)
          apply (erule_tac x = \<tau>' in allE)
          apply (erule_tac x = xs'' in allE)
          apply simp
          apply (metis lfinite_LCons)
          by (metis `(snd \<sigma>, fst \<sigma>') \<in> R` env_lem1)
        thus "?EqSingle \<or> ?EqPair"
          by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma first_failure': "\<not> env R xs \<Longrightarrow> (\<exists>xs' \<sigma> \<sigma>' \<tau> \<tau>' xs''. xs = xs' \<frown> LCons (\<sigma>,\<sigma>') (LCons (\<tau>,\<tau>') xs'') \<and> env R (xs' \<frown> LCons (\<sigma>,\<sigma>') LNil) \<and> (\<sigma>',\<tau>) \<notin> R \<and> lfinite xs')"
  using env_lem2 by blast

(* If a word contains any environment steps not in R, then there must exist a first such step *)
lemma first_failure: "\<not> env (R\<^sup>*) x \<Longrightarrow> \<exists>x\<^sub>p \<sigma> \<sigma>' \<tau> \<tau>' x\<^sub>t. x = x\<^sub>p \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x\<^sub>t) \<and> (\<sigma>',\<tau>) \<notin> R\<^sup>* \<and> lfinite x\<^sub>p \<and> env (R\<^sup>*) (x\<^sub>p \<frown> ((\<sigma>,\<sigma>') # LNil))"
  apply (drule first_failure')
  apply (erule exE)+ 
  apply (rule_tac x = xs' in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply (rule_tac x = \<tau>' in exI)
  apply (rule_tac x = xs'' in exI)
  apply (erule conjE)+
  apply (intro conjI)
  by simp_all

definition rely'' ::  "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rely'' R x y \<equiv> (\<exists>z \<sigma> \<sigma>' \<tau> \<tau>' \<tau>'' x' y'. x = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x')
                                         \<and> y = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>'') # y')
                                         \<and> (\<sigma>',\<tau>) \<notin> (R\<^sup>*)
                                         \<and> lfinite z)"

lemma llength_lprefix: "llength x < llength y \<Longrightarrow> z = x \<frown> w \<Longrightarrow> z = y \<frown> w \<Longrightarrow> lprefix x y"
  by (metis lprefix_lappend lprefix_lappendD lprefix_llength_le not_less)

lemma rely_trans2: "rely' R x y \<Longrightarrow> rely' G y z \<Longrightarrow> rely'' (R \<inter> G) x z"
  apply (simp add: rely'_def rely''_def)
  apply (erule exE)+
  apply (rename_tac w w' \<sigma> \<gamma> \<sigma>' \<gamma>' \<tau> \<phi>)
  apply (subgoal_tac "(llength w < llength w') \<or> (llength w = llength w') \<or> (llength w' < llength w)")
  prefer 2
  apply (metis antisym_conv2 not_less)
  apply (erule disjE)
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = w in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply (intro conjI)
  apply blast
  apply (subgoal_tac "(\<exists>\<sigma> \<sigma>' w\<^sub>t. w' = w \<frown> ((\<sigma>,\<sigma>') # w\<^sub>t))")
  apply (erule exE)+
  prefer 2
  apply (metis lappend_LNil2 lprefix_conv_lappend lprefix_lappendD lprefix_llength_le neq_LNil_conv not_less prod.collapse)
  apply simp
  sorry

lemma end_pair_lem: "lfinite z\<^sub>p \<Longrightarrow> z \<frown> ((\<sigma>, \<sigma>') # LNil) = z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # LNil) \<Longrightarrow> z = z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # LNil)"
proof (induct arbitrary: z rule: lfinite_induct_pair)
  case Nil
  thus ?case
    apply simp
    apply (cases z)
    apply simp_all
    by (metis LNil_eq_lappend_iff eq_LConsD llist.collapse(1) ltl_lappend)
next
  case (Cons \<tau> \<tau>' z')

  thus ?case
    apply (cases z)
    apply simp
    apply (metis LNil_eq_lappend_iff llist.distinct(1))
    by simp
qed

lemma rely_no_env: "rely'' R x y \<Longrightarrow> rely' R x y"
proof (auto simp add: rely''_def)
  fix z \<sigma> \<sigma>' \<tau> \<tau>' x' \<tau>'' y'
  assume "lfinite z"  
  and "x = z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>') # x')"
  and "y = z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>'') # y')"
  and "(\<sigma>', \<tau>) \<notin> R\<^sup>*"

  show "rely' R (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>') # x')) (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>'') # y'))"
  proof (cases "env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))")
    assume "env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))"
    thus "rely' R (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>') # x')) (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>'') # y'))"
      by (auto simp add: rely'_def) (metis `(\<sigma>', \<tau>) \<notin> R\<^sup>*` `lfinite z`)
  next
    assume "\<not> env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))"
    from first_failure[OF this]
    obtain z\<^sub>p \<gamma> \<gamma>' \<phi> \<phi>' z\<^sub>t
    where "z \<frown> ((\<sigma>, \<sigma>') # LNil) = z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # z\<^sub>t)"
    and [simp]: "(\<gamma>', \<phi>) \<notin> R\<^sup>*" and [simp]: "lfinite z\<^sub>p" and [simp]: "env (R\<^sup>*) (z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # LNil))"
      by auto
    show "rely' R (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>') # x')) (z \<frown> ((\<sigma>, \<sigma>') # (\<tau>, \<tau>'') # y'))"
      apply (auto simp add: rely'_def)
      apply (rule_tac x = z\<^sub>p in exI)
      apply (rule_tac x = \<gamma> in exI)
      apply (rule_tac x = \<gamma>' in exI)
      apply (rule_tac x = \<phi> in exI)
      apply (intro conjI)
      apply simp_all
      apply (rule_tac x = \<phi>' in exI)
      apply (rule_tac x = "z\<^sub>t \<frown> ((\<tau>, \<tau>') # x')" in exI)
      apply (metis `z \<frown> ((\<sigma>, \<sigma>') # LNil) = z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # z\<^sub>t)` lappend_assoc lappend_code(1) lappend_code(2))
      apply (rule_tac x = \<phi>' in exI)
      apply (rule_tac x = "z\<^sub>t \<frown> ((\<tau>, \<tau>'') # y')" in exI)
      by (metis `z \<frown> ((\<sigma>, \<sigma>') # LNil) = z\<^sub>p \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # z\<^sub>t)` lappend_assoc lappend_code(1) lappend_code(2))
  qed
qed

lemma lmap_unl_lfilter [simp]: "lmap unl (lfilter is_left t) = t' \<longleftrightarrow> lfilter is_left t = lmap Inl t'"
proof
  assume "lmap unl (lfilter is_left t) = t'"
  hence "lmap unl (lfilter is_left t) = lmap unl (lmap Inl t')"
    by (metis all_lefts lefts_def_var lefts_mapl)
  thus "lfilter is_left t = lmap Inl t'"
  proof -
    have f1: "\<And>x\<^sub>1. (lmap unl (lfilter is_left x\<^sub>1)\<Colon>'a llist) \<triangleright> traj x\<^sub>1 \<triangleleft> (\<rr> x\<^sub>1\<Colon>'b llist) = x\<^sub>1"
      by (simp add: lefts_def_var reinterleave)
    have f2: "\<And>x\<^sub>2 x\<^sub>1 x\<^sub>3. lmap (\<lambda>Q. Inl ()) (x\<^sub>2\<Colon>('a + 'b) llist) = lfilter is_left (traj (x\<^sub>1\<Colon>('a + 'b) llist)) \<or> lmap unl (lfilter is_left x\<^sub>1) \<noteq> lmap x\<^sub>3 x\<^sub>2"
      by (metis (no_types) lefts_def_var traj_lfilter_lefts)
    have "\<And>x\<^sub>1. lmap unl (lmap Inl x\<^sub>1\<Colon>('a + 'b) llist) \<triangleright> traj (lmap Inl x\<^sub>1\<Colon>(_ + 'b) llist) \<triangleleft> (\<rr> (lmap Inl x\<^sub>1)\<Colon>'b llist) = lmap Inl x\<^sub>1" using f1
      by (metis all_lefts)
    hence f3: "lmap unl (lfilter is_left t) \<triangleright> traj (lmap Inl t'\<Colon>('a + 'b) llist) \<triangleleft> (\<rr> (lmap Inl t')\<Colon>'b llist) = lmap Inl t'"
      by (metis `lmap unl (lfilter is_left t) = lmap unl (lmap Inl t')`)
    have "\<And>x\<^sub>1. lmap (\<lambda>Q. Inl ()) (lmap Inl x\<^sub>1\<Colon>('a + 'b) llist) = lfilter is_left (traj (lmap Inl x\<^sub>1\<Colon>(_ + 'b) llist))" using f2
      by (metis all_lefts)
    hence "\<And>x\<^sub>1. lfilter is_left (traj (lmap Inl t'\<Colon>('a + 'b) llist)) = lfilter is_left (traj (x\<^sub>1\<Colon>('a + 'b) llist)) \<or> lmap unl (lfilter is_left x\<^sub>1) \<noteq> lmap unl (lfilter is_left t)" using f2
      by (metis `lmap unl (lfilter is_left t) = lmap unl (lmap Inl t')`)
    thus "lfilter is_left t = lmap Inl t'" using f1 f3 by (metis (no_types) all_lefts lfilter_left_interleave only_left_traj)
  qed
next
  assume "lfilter is_left t = lmap Inl t'"
  thus "lmap unl (lfilter is_left t) = t'"
    by (metis lefts_def_var lefts_mapl lfilter_idem)
qed

lemma lmap_swap_swap: "lmap swap (lmap swap x) = x"
  by simp

lemma lmap_swap_eq[simp]: "lmap swap x = lmap swap y \<longleftrightarrow> x = y"
  by (metis lmap_swap_swap)

lemma lmap_unr_lfilter [simp]: "lmap unr (lfilter is_right t) = t' \<longleftrightarrow> lfilter is_right t = lmap Inr t'"
proof
  assume "lmap unr (lfilter is_right t) = t'"

  have "lmap unr (lfilter is_right t) = lmap unr (lfilter is_right (lmap swap (lmap swap t)))"
    by simp
  also have "... = lmap unr (lmap swap (lfilter is_left (lmap swap t)))"
    by (metis is_right_swap lfilter_lmap)
  also have "... = lmap unl (lfilter is_left (lmap swap t))"
    by simp
  finally have "lmap unr (lfilter is_right t) = lmap unl (lfilter is_left (lmap swap t))" .
  hence "... = t'"
    by (metis `lmap unr (lfilter is_right t) = t'`)
  hence "lfilter is_left (lmap swap t) = lmap Inl t'"
    by (metis lmap_unl_lfilter)
  thus "lfilter is_right t = lmap Inr t'"
    apply (simp add: lfilter_lmap)
    apply (erule rev_mp)
    apply (subst lmap_swap_swap[symmetric]) back back back
    apply (subst lmap_swap_eq)
    by simp
next
  assume "lfilter is_right t = lmap Inr t'"
  thus "lmap unr (lfilter is_right t) = t'"
    by (metis lfilter_idem rights_def_var rights_mapr)
qed 

lemma lfilter_left_lappend [simp]: "lfilter is_left (lmap Inl x \<frown> lmap Inr y) = lmap Inl x"
  apply (cases "lfinite x")
  apply simp
  by (metis all_lefts lappend_inf lfinite_lmap)

lemma lfilter_right_lappend [simp]: "lfilter is_right (lmap Inr x \<frown> lmap Inl y) = lmap Inr x"
  apply (cases "lfinite x")
  apply simp
  by (metis all_rights lappend_inf lfinite_lmap)

lemma some_fun: "(\<forall>x\<in>X. f x = y) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> f (SOME x. x \<in> X) = y"
  by (metis all_not_in_conv someI_ex)

lemma "x \<sha> y \<noteq> {} \<Longrightarrow> lfilter is_left (SOME z. z \<in> x \<sha> y) = lmap Inl x"
  apply (rule some_fun)
  by (auto simp add: tshuffle_words_def lefts_def rights_def)

lemma [simp]: "x \<sha> y \<subseteq> FIN \<longleftrightarrow> lfinite x \<and> lfinite y"
  sorry

lemma rg_lem5: "(\<And>x y. Q x y \<Longrightarrow> F x y = G x y) \<Longrightarrow> \<Union>{F x y|x y. Q x y} = \<Union>{G x y|x y. Q x y}"
  by auto

lemma [simp]: "X \<subseteq> {x. lfinite x} \<longleftrightarrow> (\<forall>x\<in>X. lfinite x)"
  by auto

lemma rg_lem6: "env R (x \<frown> y) \<Longrightarrow> lfinite x \<Longrightarrow> env R y"
  apply (rotate_tac 1)
  apply (induct rule: lfinite_induct)
  apply simp_all
  by (metis env_tl)

lemma rg_lem7: "env R (x \<frown> y) \<Longrightarrow> env R x"
proof -
  assume "env R (x \<frown> y)"
  thus "env R x"
  proof coinduct
    case (env t)
    thus ?case
    proof (cases t)
      assume "t = LNil"
      thus ?case
        by simp
    next
      fix \<sigma> t'
      assume [simp]: "t = LCons \<sigma> t'"
      hence "?EqSingle \<or> ?EqPair"
      proof (cases t')
        assume "t' = LNil"
        thus "?EqSingle \<or> ?EqPair" by simp
      next
        fix \<sigma>' t''
        assume [simp]: "t' = LCons \<sigma>' t''"
        from env
        show "?EqSingle \<or> ?EqPair" by auto
      qed
      thus ?case by simp
    qed
  qed
qed

lemma rg_lem8: "X \<subseteq> FIN \<Longrightarrow> z \<in> X \<cdot> {z'} \<cdot> Y \<Longrightarrow> env R z \<Longrightarrow> env R z'"
  apply (auto simp add: l_prod_def FIN_def)
  apply (rename_tac x)
  apply (erule_tac x = x in ballE)
  prefer 2
  apply simp
  apply (metis rg_lem6)
  apply (rename_tac x y)
  apply (erule_tac x = y in ballE)
  prefer 2
  apply simp
  by (metis rg_lem6 rg_lem7)

lemma [simp]: "lmap f ` X \<subseteq> FIN \<longleftrightarrow> X \<subseteq> FIN"
  by (auto simp add: FIN_def)

lemma env_simp: "env R (\<sigma> # \<sigma>' # t) \<longleftrightarrow> (snd \<sigma>, fst \<sigma>') \<in> R \<and> env R (\<sigma>' # t)"
  by (metis EqPair env_LConsD env_tl)

lemma atomic_LCons: "x # xs \<in> atomic G \<cdot> X \<Longrightarrow> x \<in> G"
  apply (simp add: atomic_def l_prod_def)
  by (metis lappend_code(2) llist.inject)

lemma atomic_LCons2: "x # xs \<in> atomic G \<cdot> X \<Longrightarrow> xs \<in> X"
  apply (simp add: atomic_def l_prod_def)
  by (metis lappend_code(1) lappend_code(2) lfinite_code(1) llist.inject)

lemma LCons_in_l_prod: "x # LNil \<in> X \<Longrightarrow> xs \<in> Y \<Longrightarrow> x # xs \<in> X \<cdot> Y"
  apply (auto simp add: l_prod_def)
  apply (metis lappend_code(1) lappend_code(2) lfinite_LCons lfinite_LNil)
  by (metis lappend_code(1) lappend_code(2) lfinite_LCons lfinite_code(1))

lemma [simp]: "x # xs \<in> guar G \<longleftrightarrow> x \<in> G\<^sup>* \<and> xs \<in> guar G"
  by (metis guar_LCons_eq prod.collapse)

lemma rg_lem10: "lfinite xs \<Longrightarrow> xs \<in> guar G \<Longrightarrow> env (R\<^sup>*) (((\<sigma>,\<sigma>') # LNil) \<frown> xs \<frown> ((\<tau>,\<tau>') # LNil)) \<Longrightarrow> (\<sigma>',\<tau>) \<in> (R \<union> G)\<^sup>*"
proof (induct arbitrary: \<sigma> \<sigma>' rule: lfinite_induct)
  case Nil
  thus ?case
    by (simp add: env_simp) (metis in_rtrancl_UnI)
next
  case (Cons x xs)
  thus ?case
    apply (cases x)
    apply (simp add: env_simp)
    apply (erule conjE)+
    by (metis in_rtrancl_UnI rtrancl_trans)
qed

lemma rg_lem11: "(\<And>x y z. Q x y z \<Longrightarrow> F x y z = G x y z) \<Longrightarrow> \<Union>{F x y z |x y z. Q x y z} = \<Union>{G x y z |x y z. Q x y z}"
  by auto metis+

lemma rg_lem12: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> \<Union>{F x y |x y. P x y} = \<Union>{X \<cdot> F x y |x y. P x y}"
  by (subst l_prod_inf_distl) auto

lemma [simp]: "{xs \<in> X. \<not> lfinite xs} \<subseteq> FIN \<longleftrightarrow> (\<forall>xs\<in>X. lfinite xs)"
  by (auto simp add: FIN_def)

lemma [simp]: "{xs \<frown> ys |xs ys. xs \<in> X \<and> lfinite xs \<and> ys \<in> Y} \<subseteq> FIN \<longleftrightarrow> ((\<exists>xs\<in>X. lfinite xs) \<longrightarrow> (\<forall>ys\<in>Y. lfinite ys))"
  by (auto simp add: FIN_def) (metis lfinite_lappend)

lemma FIN_l_prod [simp]: "X \<cdot> Y \<subseteq> FIN \<longleftrightarrow> X \<subseteq> FIN \<and> (X \<noteq> {} \<longrightarrow> Y \<subseteq> FIN)"
  apply (simp add: l_prod_def)
  by (metis (no_types, hide_lams) FIN_def all_not_in_conv contra_subsetD mem_Collect_eq subsetI)

lemma rg_lem13: "\<Union>{\<Union>{F x y z w v |x y. P x y} |z w v. Q z w v} = \<Union>{F x y z w v |x y z w v. P x y \<and> Q z w v}"
  by auto metis

lemma rg_lem14: "\<Union>{F x y z w |x y z w. P x y z w} = \<Union>{F x y z w |z w x y. P x y z w}"
  by auto metis+

lemma rg_lem15: "(\<And>x y z w. P x y z w = Q x y z w) \<Longrightarrow> \<Union>{F x y z w |x y z w. P x y z w} = \<Union>{F x y z w |x y z w. Q x y z w}"
  by auto

lemma rg_lem16: "f ` \<Union>{F x y z w |x y z w. P x y z w} = \<Union>{f ` (F x y z w) |x y z w. P x y z w}"
  apply auto
  apply (metis imageI)
  by blast

lemma rg_lem17: "(\<And>x y z w. Q x y z w \<Longrightarrow> F x y z w = G x y z w) \<Longrightarrow> \<Union>{F x y z w |x y z w. Q x y z w} = \<Union>{G x y z w |x y z w. Q x y z w}"
  by auto metis+

lemma lmap_l_prod_distrib: "lmap f ` (X \<cdot> Y) = lmap f ` X \<cdot> lmap f ` Y"
  apply (auto simp add: l_prod_def)
  apply (metis imageI lfinite_lmap lmap_lappend_distrib)
  apply (metis imageI lfinite_lmap lmap_lappend_distrib)
  apply (auto simp add: image_def)
  apply (rename_tac xs ys)
  apply (rule_tac x = "xs \<frown> ys" in bexI)
  apply auto
  by (metis lmap_lappend_distrib)

lemma l_prod_singleton: "{xs} \<cdot> {ys} = {xs \<frown> ys}"
  by (auto simp add: l_prod_def) (metis lappend_inf)+

lemma rg_lem18: "z \<in> f ` (A \<union> B \<union> C \<union> D \<union> E \<union> F) \<longleftrightarrow> z \<in> f ` A \<or> z \<in> f ` B \<or> z \<in> f ` C \<or> z \<in> f ` D \<or> z \<in> f ` E \<or> z \<in> f ` F"
  by auto

lemma env_split2: "lfinite x \<Longrightarrow> env R (x \<frown> y) \<Longrightarrow> env R x \<and> env R y"
  by (metis rg_lem6 rg_lem7)

lemma guar_par: "guar G\<^sub>1 \<parallel> guar G\<^sub>2 \<subseteq> guar (G\<^sub>1 \<union> G\<^sub>2)"
  sorry

lemma Rely_continuous: "R \<rhd> \<Union>\<XX> = \<Union>{R \<rhd> X |X. X \<in> \<XX>}"
  by (auto simp add: Rely_def)

lemma Rely_ext: "X \<le> R \<rhd> X"
  apply (auto simp add: Rely_def)
  apply (rule_tac x = x in bexI)
  by (auto simp add: rely_refl)

lemma shuffle_elem: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> z \<in> x \<sha> y\<Longrightarrow> lmap \<langle>id,id\<rangle> z \<in> X \<parallel> Y"
  by (auto simp add: shuffle_def)

axiomatization
  alternate :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a + 'b) llist"
where
  alternate_left [simp]: "\<ll> (alternate x y) = x" and
  alternate_right [simp]: "\<rr> (alternate x y) = y"

lemma rg_lefts_rights: "\<ll> z \<in> X \<Longrightarrow> \<rr> z \<in> Y \<Longrightarrow> lmap \<langle>id,id\<rangle> z \<in> X \<parallel> Y"
  by (auto simp add: shuffle_def tshuffle_words_def)

lemma [simp]: "lfinite (xs \<triangleright> t \<triangleleft> ys) \<longleftrightarrow> lfinite t"
  apply auto
  apply (metis lfinite_traj)
  by (metis lfinite_lmap traj_def traj_interleave)

lemma lefts_lmap_Inr [simp]: "\<ll> (lmap Inr x) = LNil"
  by (simp add: lefts_def)

lemma lefts_interleave_Valid [simp]: "Valid x t y \<Longrightarrow> \<ll> (x \<triangleright> t \<triangleleft> y) = x"
  by (smt Valid_def lefts_interleave_llength traj_interleave)

lemma rights_interleave_Valid [simp]: "Valid x t y \<Longrightarrow> \<rr> (x \<triangleright> t \<triangleleft> y) = y"
  by (smt Valid_def rights_interleave_llength traj_interleave)

lemma prime_rely: "rely'' R x y \<Longrightarrow> rely R x y"
  by (metis rely_def_var rely_no_env)

lemma shuffle_elem_ex: "z \<in> x \<sha> y \<Longrightarrow> (\<exists>t. z = x \<triangleright> t \<triangleleft> y \<and> Valid x t y)"
  apply (rule_tac x = "traj z" in exI)
  apply (auto simp add: tshuffle_words_def)
  apply (metis reinterleave)
  by (simp add: Valid_def)

abbreviation sng :: "'a \<Rightarrow> 'a llist" where
  "sng x \<equiv> LCons x LNil" 

find_theorems LCons "op \<sha>"

lemma LCons_tshuffle_1: "{sng (Inl \<sigma>)} \<cdot> (x \<sha> y) \<subseteq> (\<sigma> # x) \<sha> y"
  apply (auto simp add: l_prod_def)
  apply (cases y)
  apply simp
  apply (rename_tac \<tau> z)
  apply simp
  by (metis LCons_tshuffle UnCI image_eqI)

lemma LCons_tshuffle_2: "{sng (Inr \<tau>)} \<cdot> (x \<sha> y) \<subseteq> x \<sha> (\<tau> # y)"
  apply (auto simp add: l_prod_def)
  apply (cases x)
  apply simp
  apply (rename_tac \<sigma> z)
  apply simp
  by (metis LCons_tshuffle UnCI image_eqI)

lemma set_LCons_to_l_prod: "{x # xs} = {sng x} \<cdot> {xs}"
  by (auto simp add: l_prod_def)

lemma l_prod_tshuffle_sub_1: "lfinite x \<Longrightarrow> {lmap Inl x} \<cdot> (x' \<sha> y) \<subseteq> (x \<frown> x') \<sha> y"
proof (induct rule: lfinite_induct)
  case Nil
  show ?case
    by simp
next
  case (Cons x\<^sub>p x\<^sub>t)
  thus ?case
    apply simp
    apply (rule dual_order.trans[OF LCons_tshuffle_1])
    by (metis set_LCons_to_l_prod l_prod_assoc l_prod_isor)
qed

notation ltake ("\<up>")
  and ldrop ("\<down>")

lemma [simp]: "traj LNil = LNil"
  by (metis traj_LNil traj_interleave)

lemma [simp]: "traj (LCons (Inl x) xs) = LCons (Inl ()) (traj xs)"
  by (simp add: traj_def)

lemma [simp]: "traj (LCons (Inr x) xs) = LCons (Inr ()) (traj xs)"
  by (simp add: traj_def)

lemma LConsl_in_shuffle [dest]: "LCons (Inl x) (xs \<frown> ys) \<in> xs' \<sha> ys' \<Longrightarrow> xs \<frown> ys \<in> ltl xs' \<sha> ys'"
  by (auto simp add: tshuffle_words_def)

lemma LConsr_in_shuffle [dest]: "LCons (Inr y) (xs \<frown> ys) \<in> xs' \<sha> ys' \<Longrightarrow> xs \<frown> ys \<in> xs' \<sha> ltl ys'"
  by (auto simp add: tshuffle_words_def)

lemma traj_lappend [simp]: "traj (xs \<frown> ys) = traj xs \<frown> traj ys"
  by (auto simp add: traj_def lmap_lappend_distrib)

lemma traj_id [simp]:
  fixes t :: "(unit + unit) llist"
  shows "traj t = t"
  apply (auto simp add: traj_def)
  apply (subst llist.map_id[symmetric]) back
  apply (rule lmap2_id)
  apply simp
proof -
  fix x :: "(unit + unit)"
  show "(case x of Inl x \<Rightarrow> Inl x | Inr x \<Rightarrow> Inr x) = x"
    by (cases x) auto
qed

lemma intro_traj: "xs \<triangleright> t \<triangleleft> ys = xs \<triangleright> traj t \<triangleleft> ys"
  by simp

lemma [simp]: "lfilter is_right (ltl (ldropWhile is_right t)) = lfilter is_right (ldropWhile is_right t)"
  apply (cases "\<exists>t'\<in>lset t. \<exists>a. t' = Inl a")
  apply (metis is_right.simps(2) lfilter_LCons lhd_ldropWhile llist.collapse ltl_simps(1))
  apply auto
  apply (subgoal_tac "ldropWhile is_right t = LNil")
  apply simp_all
  by (metis is_right.simps(1) ldropWhile_eq_LNil_iff sumE)

lemma ldropWhile_LConsD [dest]: "ldropWhile P xs = LCons y ys \<Longrightarrow> \<exists>zs. xs = zs \<frown> LCons y ys \<and> \<not> P y \<and> (\<forall>z\<in>lset zs. P z) \<and> lfinite zs"
  by (metis lappend_ltakeWhile_ldropWhile ldropWhile_eq_LNil_iff lfinite_ltakeWhile lhd_LCons lhd_ldropWhile llist.distinct(1) lset_ltakeWhileD)

lemma iaV_lem: "(x::enat) + y = z \<Longrightarrow> x = min x z"
  by (metis enat_le_plus_same(1) min_def)

lemma enat_galois_1: "x \<noteq> \<infinity> \<Longrightarrow> (x::enat) + y = z \<Longrightarrow> y = z - x"
  by (metis enat_add_sub_same)

lemma interleave_append_Valid:
  assumes "lfinite t"
  and "Valid xs (t \<frown> t') ys"
  shows "xs \<triangleright> t \<frown> t' \<triangleleft> ys = (\<up> (llength (\<ll> t)) xs \<triangleright> t \<triangleleft> \<up> (llength (\<rr> t)) ys) \<frown> (\<down> (llength (\<ll> t)) xs \<triangleright> t' \<triangleleft> \<down> (llength (\<rr> t)) ys)" (is ?A)
  and "Valid (\<up> (llength (\<ll> t)) xs) t (\<up> (llength (\<rr> t)) ys)" (is "?B")
  and "Valid (\<down> (llength (\<ll> t)) xs) t' (\<down> (llength (\<rr> t)) ys)" (is "?C")
proof -
  from assms Valid_def interleave_append_llength
  show ?A by blast
next
  from assms
  show ?B
    apply (auto simp add: Valid_def)
    apply (simp add: lefts_append)
    apply (rule iaV_lem)
    apply simp
    apply (simp add: rights_append)
    apply (rule iaV_lem)
    by simp
next
  from assms
  show ?C
    apply (auto simp add: Valid_def)
    apply (simp add: lefts_append rights_append llength_ldrop)
    apply auto
    apply (metis lfinite_lefts llength_eq_infty_conv_lfinite)
    apply (rule enat_galois_1)
    apply simp_all
    apply (simp add: lefts_append rights_append llength_ldrop)
    apply auto
    apply (metis lfinite_rights llength_eq_infty_conv_lfinite)
    apply (rule enat_galois_1)
    by simp_all
qed

abbreviation "TL \<equiv> ltakeWhile is_left"
abbreviation "DL \<equiv> ldropWhile is_left"

lemma lefts_take_lefts_llength [simp]: "llength (\<ll> (TL t)) = llength (TL t)"
  apply (simp add: lefts_def)
  by (metis Not_is_right lfilter_ltakeWhile lfilter_right_left)

lemma interleave_only_left_var: "llength t = llength xs \<Longrightarrow> xs \<triangleright> lmap (\<lambda>x. Inl ()) t \<triangleleft> zs = lmap Inl xs"
  by (metis (full_types) interleave_only_left lmap_const_llength)

lemma rights_take_lefts [simp]: "\<rr> (TL t) = LNil"
  apply (simp add: rights_def)
  by (metis Not_is_right lfilter_ltakeWhile)

lemma TL_traj_only_left:
  fixes t :: "(unit + unit) llist"
  shows "TL t = lmap (\<lambda>x. Inl ()) (TL t)"
proof -
  have "\<And>x\<^sub>1. lfilter is_left (TL (x\<^sub>1\<Colon>(unit + unit) llist)) = TL x\<^sub>1" by (metis Not_is_right lfilter_ltakeWhile lfilter_right_left)
  thus "TL t = lmap (\<lambda>x. Inl ()) (TL t)"
    sledgehammer

by (metis interleave_only_left_var lefts_def_var lefts_take_lefts_llength lmap_unl_lfilter traj_id traj_interleave)
qed

lemma interleave_only_left_TL:
  assumes "Valid (\<up> (llength (\<ll> (TL t))) x) (TL t) (\<up> (llength (\<rr> (TL t))) y)"
  shows "\<up> (llength (\<ll> (TL t))) x \<triangleright> TL t \<triangleleft> \<up> (llength (\<rr> (TL t))) y = lmap Inl (\<up> (llength (\<ll> (TL t))) x)"
  using assms
  apply auto
  apply (subst TL_traj_only_left)
  apply (subst interleave_only_left_var)
  by (auto simp add: Valid_def)

lemma ldropWhile_right_LCons [dest!]: "ldropWhile is_right t = LCons x xs \<Longrightarrow> \<exists>x'. ldropWhile is_right t = LCons (Inl x') xs"
  apply (drule ldropWhile_LConsD)
  apply (cases x)
  apply auto
  by (metis is_right.simps(2) ldropWhile_LCons ldropWhile_lappend)

lemma ldropWhile_left_LCons [dest!]: "ldropWhile is_left t = LCons x xs \<Longrightarrow> \<exists>x'. ldropWhile is_left t = LCons (Inr x') xs"
  apply (drule ldropWhile_LConsD)
  apply (cases x)
  apply auto
  by (metis is_left.simps(2) ldropWhile_LCons ldropWhile_lappend)

lemma ldropWhile_left_traj: "DL t \<noteq> LNil \<Longrightarrow> \<exists>t'. DL t = LCons (Inr ()) t'"
  apply (subgoal_tac "\<exists>x xs. DL t = LCons x xs")
  apply (erule exE)+
  apply (drule ldropWhile_left_LCons)
  by auto

lemma interleave_right_Valid:
  assumes "Valid xs (Inr () # t) (y # ys)"
  shows "xs \<triangleright> Inr () # t \<triangleleft> (y # ys) = Inr y # (xs \<triangleright> t \<triangleleft> ys)"
  and "Valid xs t ys"
  using assms
  apply -
  apply (metis interleave_right lhd_LCons ltl_simps(2))
  by (simp add: Valid_def)

lemma lappend_in_l_prod: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<frown> y \<in> X \<cdot> Y"
  by (auto simp add: l_prod_def)  (metis lappend_inf)

lemma interleave_in_shuffle: "Valid x t y \<Longrightarrow> x \<triangleright> t \<triangleleft> y \<in> x \<sha> y"
  by (auto simp add: tshuffle_words_def)

lemma shuffle_LCons_right: "x \<sha> (\<tau> # y) = \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (z' \<sha> y) |z z'. x = z \<frown> z' \<and> lfinite z}"
proof -
  {
    fix w
    assume "w \<in> x \<sha> (LCons \<tau> y)"

   then obtain t
    where va: "Valid x t (\<tau> # y)" and ia: "w = x \<triangleright> t \<triangleleft> (\<tau> # y)"
      by (metis shuffle_elem_ex)

    have ib: "w  = x \<triangleright> TL t \<frown> DL t \<triangleleft> (\<tau> # y)"
      by (metis lappend_ltakeWhile_ldropWhile ia)

    from va have "DL t \<noteq> LNil"
      apply (simp add: Valid_def)
      by (metis lappend_LNil2 lappend_ltakeWhile_ldropWhile llength_LNil rights_take_lefts zero_ne_eSuc)

    from va have "lfinite (TL t)"
      apply (simp add: Valid_def)
      by (metis lfinite_ltakeWhile llength_LNil llength_eq_infty_conv_lfinite llength_ltakeWhile_all rights_take_lefts zero_ne_eSuc)

    have vb: "Valid x (TL t \<frown> DL t) (\<tau> # y)"
      by (metis `Valid x t (\<tau> # y)` lappend_ltakeWhile_ldropWhile)

    have ic: "w = (\<up> (llength (\<ll> (TL t))) x \<triangleright> TL t \<triangleleft> \<up> (llength (\<rr> (TL t))) (\<tau> # y)) \<frown> (\<down> (llength (\<ll> (TL t))) x \<triangleright> DL t \<triangleleft> \<down> (llength (\<rr> (TL t))) (\<tau> # y))"
    and vc1: "Valid (\<up> (llength (\<ll> (TL t))) x) (TL t) (\<up> (llength (\<rr> (TL t))) (\<tau> # y))"
    and vc2: "Valid (\<down> (llength (\<ll> (TL t))) x) (DL t) (\<down> (llength (\<rr> (TL t))) (\<tau> # y))"
      using interleave_append_Valid[OF `lfinite (TL t)` vb] ib
      by - blast+

    have ic': "w = lmap Inl (\<up> (llength (\<ll> (TL t))) x) \<frown> (\<down> (llength (\<ll> (TL t))) x \<triangleright> DL t \<triangleleft> \<down> (llength (\<rr> (TL t))) (\<tau> # y))"
      using ic by (simp only: interleave_only_left_TL[OF vc1])

    hence ic'': "w = lmap Inl (\<up> (llength (\<ll> (TL t))) x) \<frown> (\<down> (llength (\<ll> (TL t))) x \<triangleright> DL t \<triangleleft> \<tau> # y)"
      by simp

    from this and ldropWhile_left_traj[OF `DL t \<noteq> LNil`] obtain t'
    where id: "w = lmap Inl (\<up> (llength (\<ll> (TL t))) x) \<frown> (\<down> (llength (\<ll> (TL t))) x \<triangleright> Inr () # t'  \<triangleleft> \<tau> # y)" and [simp]: "DL t = Inr () # t'"
      apply -
      apply (erule exE)+
      by simp

    from vc2 have vd: "Valid (\<down> (llength (\<ll> (TL t))) x) (Inr () # t')  (\<tau> # y)"
      by simp

    from id and vd
    have ie: "w = lmap Inl (\<up> (llength (\<ll> (TL t))) x) \<frown> (Inr \<tau> # (\<down> (llength (\<ll> (TL t))) x \<triangleright> t' \<triangleleft> y))"
    and ve: "Valid (\<down> (llength (\<ll> (TL t))) x) t' y"
      using interleave_right_Valid[OF vd] by simp_all

    have "w \<in> {lmap Inl (\<up> (llength (\<ll> (TL t))) x)} \<cdot> {sng (Inr \<tau>)} \<cdot> (\<down> (llength (\<ll> (TL t))) x \<sha> y)"
      apply (subst ie)
      apply (subst l_prod_assoc)
      apply (rule lappend_in_l_prod)
      apply simp
      apply (rule LCons_in_l_prod)
      apply simp
      by (rule interleave_in_shuffle[OF ve])

    also have "... \<subseteq> {lmap Inl (\<up> (llength (\<ll> (TL t))) x) \<frown> sng (Inr \<tau>)} \<cdot> (\<down> (llength (\<ll> (TL t))) x \<sha> y)"
      by (metis l_prod_singleton order_refl)

    also have "... \<subseteq> \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (z' \<sha> y) |z z'. x = z \<frown> z' \<and> lfinite z}"
      apply auto
      apply (rule_tac x = "{lmap Inl (\<up> (llength (TL t)) x) \<frown> sng (Inr \<tau>)} \<cdot> (\<down> (llength (TL t)) x \<sha> y)" in exI)
      apply simp
      apply (rule_tac x = "\<up> (llength (TL t)) x" in exI)
      apply (rule_tac x = "\<down> (llength (TL t)) x" in exI)
      apply (intro conjI)
      apply simp_all
      apply (metis lappend_ltake_ldrop)
      by (metis `lfinite (TL t)` lfinite_conv_llength_enat)

    finally have "w \<in> \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (z' \<sha> y) |z z'. x = z \<frown> z' \<and> lfinite z}" .
  }
  moreover
  {
    fix w
    assume "w \<in> \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (z' \<sha> y) |z z'. x = z \<frown> z' \<and> lfinite z}"
    hence "w \<in> x \<sha> (LCons \<tau> y)"
    proof auto
      fix z z'
      assume "lfinite z" and "w \<in> {lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (z' \<sha> y)"
      thus "w \<in> (z \<frown> z') \<sha> (\<tau> # y)"
        apply (simp add: tshuffle_words_def l_prod_def)
        apply (erule disjE)
        apply (metis lappend_LNil2 lfinite_LCons lfinite_lappend lfinite_lmap)
        apply (erule exE)+
        apply (simp add: lefts_append rights_append)
        by (simp add: rights_def)
    qed
  }
  ultimately show ?thesis
    apply -
    apply (rule antisym)
    apply (simp_all only: subset_iff)
    by blast+
qed

lemma l_prod_inf_distr_comp2: "\<Union>{f x y |x y. P x y} \<cdot> Y = \<Union>{f x y \<cdot> Y|x y. P x y}"
  apply (subst l_prod_inf_distr)
  by auto

lemmas l_prod_inf_distl_comp2 = rg_lem12

lemma slr_lem: "(\<And>x y z. P x y z = Q x y z) \<Longrightarrow> \<Union>{f x y z |x y z. P x y z} = \<Union>{f x y z |x y z. Q x y z}"
  by auto

lemma slr_lem2: "\<Union>{f x y z |x y z. (\<exists>w. P x y w \<and> Q z w)} = \<Union>{\<Union>{f x y z |x y. P x y w} |z w. Q z w}"
  by auto metis

lemma shuffle_lappend_right: "lfinite y \<Longrightarrow> x \<sha> (y \<frown> y') = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> y') |z z'. x = z \<frown> z' \<and> lfinite z}"
proof (induct arbitrary: x rule: lfinite_induct)
  case Nil
  {
    fix w
    assume "w \<in> x \<sha> y'"

    hence "w \<in> \<Union>{{lmap Inl z} \<cdot> (z' \<sha> y') |z z'. x = z \<frown> z' \<and> lfinite z}"
      apply auto
      apply (rule_tac x = "x \<sha> y'" in exI)
      apply auto
      apply (rule_tac x = LNil in exI)
      apply (rule_tac x = x in exI)
      by simp_all
  }
  moreover
  {
    fix w
    assume "w \<in> \<Union>{{lmap Inl z} \<cdot> (z' \<sha> y') |z z'. x = z \<frown> z' \<and> lfinite z}"
    hence "w \<in> x \<sha> y'"
      apply auto
      by (metis (full_types) contra_subsetD l_prod_tshuffle_sub_1 tshuffle_LNil)
  }
  ultimately show ?case
    apply -
    apply (rule antisym)
    apply (simp_all only: subset_iff lappend_code(1) tshuffle_LNil)
    by blast+
next
  case (Cons \<tau> y)
  show ?case
  proof (simp add: shuffle_LCons_right Cons(2))
    have "\<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> \<Union>{(w \<sha> y) \<cdot> (w' \<sha> y') |w w'. z' = w \<frown> w' \<and> lfinite w} |z z'. x = z \<frown> z' \<and> lfinite z} =
          \<Union>{\<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (w \<sha> y) \<cdot> (w' \<sha> y') |w w'. z' = w \<frown> w' \<and> lfinite w} |z z'. x = z \<frown> z' \<and> lfinite z}" (is "?lhs = _")
      apply (rule rg_lem5)
      apply (subst l_prod_inf_distl_comp2)
      by (simp_all add: FIN_def l_prod_assoc)
    also have "... = \<Union>{\<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (w \<sha> y) \<cdot> (w' \<sha> y') |w w' z z'. x = z \<frown> z' \<and> z' = w \<frown> w' \<and> lfinite w \<and> lfinite z}}"
      by auto
    also have "... = \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (w \<sha> y) \<cdot> (w' \<sha> y') |w w' z z'. x = z \<frown> z' \<and> z' = w \<frown> w' \<and> lfinite w \<and> lfinite z}"
      by auto
    also have "... = \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (w \<sha> y) \<cdot> (w' \<sha> y') |w w' z. (\<exists>z'. x = z \<frown> z' \<and> z' = w \<frown> w' \<and> lfinite w \<and> lfinite z)}"
      by auto
    also have "... = \<Union>{{lmap Inl z \<frown> sng (Inr \<tau>)} \<cdot> (w \<sha> y) \<cdot> (w' \<sha> y') |w w' z. x = z \<frown> w \<frown> w' \<and> lfinite w \<and> lfinite z}"
      by (metis (erased, hide_lams) lappend_assoc)
    also have "... = \<Union>{{lmap Inl w \<frown> sng (Inr \<tau>)} \<cdot> (w' \<sha> y) \<cdot> (z' \<sha> y') |w w' z'. x = w \<frown> w' \<frown> z' \<and> lfinite w \<and> lfinite w'}"
      by auto
    also have "... = \<Union>{{lmap Inl w \<frown> sng (Inr \<tau>)} \<cdot> (w' \<sha> y) \<cdot> (z' \<sha> y') |w w' z'. \<exists>z. z = w \<frown> w' \<and> lfinite w \<and> x = z \<frown> z' \<and> lfinite z}"
      by (rule slr_lem) auto
    also have "... = \<Union>{{lmap Inl w \<frown> sng (Inr \<tau>)} \<cdot> (w' \<sha> y) \<cdot> (z' \<sha> y') |w w' z'. \<exists>z. (z = w \<frown> w' \<and> lfinite w) \<and> (x = z \<frown> z' \<and> lfinite z)}"
      by simp
    also have "... = \<Union>{\<Union>{{lmap Inl w \<frown> sng (Inr \<tau>)} \<cdot> (w' \<sha> y) \<cdot> (z' \<sha> y') |w w'. z = w \<frown> w' \<and> lfinite w} |z z'. x = z \<frown> z' \<and> lfinite z}"
      by (subst slr_lem2) auto
    also have "... = \<Union>{\<Union>{{lmap Inl w \<frown> sng (Inr \<tau>)} \<cdot> (w' \<sha> y) |w w'. z = w \<frown> w' \<and> lfinite w} \<cdot> (z' \<sha> y') |z z'. x = z \<frown> z' \<and> lfinite z}" (is "_ = ?rhs")
      apply (rule rg_lem5)
      apply (subst l_prod_inf_distr_comp2)
      by simp
    finally show "?lhs = ?rhs" .
  qed
qed

lemma shuffle_lappend_left: "(x \<frown> x') \<sha> y = \<Union>{(x \<sha> z) \<cdot> (x' \<sha> z') |z z'. y = z \<frown> z' \<and> lfinite z}"
  sorry (* symmetric *)

lemma shuffle_cons_right: "x \<sha> (\<sigma> # y) = \<Union>{{lmap Inl z} \<cdot> {LCons (Inr \<sigma>) LNil} \<cdot> (z' \<sha> y) |z z'. x = z \<frown> z' \<and> lfinite z}"
  apply (subst shuffle_LCons_right)
  apply (rule rg_lem5)
  by (metis l_prod_singleton)

lemma shuffle_cons_left: "(\<sigma> # x) \<sha> y = \<Union>{{lmap Inr z} \<cdot> {LCons (Inl \<sigma>) LNil} \<cdot> (x \<sha> z') |z z'. y = z \<frown> z' \<and> lfinite z}"
  sorry (* symmetric *)

lemma l_prod_all_inf: "(\<forall>x\<in>X. \<not> lfinite x) \<Longrightarrow> X \<cdot> Y = X"
  by (auto simp add: l_prod_def)

lemma LCons_tshuffle_var: "(\<sigma> # x) \<sha> (\<tau> # y) = {sng (Inl \<sigma>)} \<cdot> (x \<sha> (\<tau> # y)) \<union> {sng (Inr \<tau>)} \<cdot> ((\<sigma> # x) \<sha> y)"
  by (subst LCons_tshuffle) (auto simp add: l_prod_def)

lemma lprefix_lappend_2:
  assumes "lfinite x" and "lfinite y"
  and "x \<frown> x' = y \<frown> y'"
  shows "lprefix x y \<or> lprefix y x"
  by (metis assms(3) lprefix_lappend lprefix_lappendD)

lemma lprefix_opts:
  "lfinite x \<Longrightarrow> lfinite y \<Longrightarrow> x \<frown> x' = y \<frown> y' \<Longrightarrow> (\<exists>w w'. y = w \<frown> w' \<and> x = w \<and> x' = w' \<frown> y') \<or> (\<exists>w w'. x = w \<frown> w' \<and> y = w \<and> y' = w' \<frown> x')"
  apply (subgoal_tac "lprefix x y \<or> lprefix y x")
  apply (erule disjE)
  apply (rule disjI1)
  prefer 2
  apply (rule disjI2)
  prefer 3
  apply (rule lprefix_lappend_2)
  apply simp_all
proof -
  assume a1: "lfinite y"
  assume a2: "lprefix y x"
  assume "x \<frown> x' = y \<frown> y'"
  hence f3: "\<And>u. y \<frown> u = x \<frown> x' \<longrightarrow> u = y'" using a1 by (simp add: lappend_eq_lappend_conv)
  have "\<forall>v u. \<exists>uu. lprefix (u\<Colon>'a llist) v \<longrightarrow> u \<frown> uu = v" by (metis (no_types) lprefix_conv_lappend)
  then obtain skf\<^sub>2 :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where "y \<frown> skf\<^sub>2 x y = x" using a2 by (metis (no_types))
  thus "\<exists>w'. x = y \<frown> w' \<and> y' = w' \<frown> x'" using f3 by (metis (no_types) lappend_assoc)
next
  assume a1: "lfinite x"
  assume a2: "lprefix x y"
  assume "x \<frown> x' = y \<frown> y'"
  hence f3: "\<And>u. x \<frown> u = y \<frown> y' \<longrightarrow> u = x'" using a1
    by (metis lappend_eq_lappend_conv)
  have "\<forall>v u. \<exists>uu. lprefix (u\<Colon>'a llist) v \<longrightarrow> u \<frown> uu = v" by (metis (no_types) lprefix_conv_lappend)
  then obtain skf\<^sub>2 :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where "x \<frown> skf\<^sub>2 y x = y" using a2 by (metis (no_types))
  thus "\<exists>w'. y = x \<frown> w' \<and> x' = w' \<frown> y'" using f3 by (metis (no_types) lappend_assoc)
qed

lemma split6_lem1: "(\<And>x y. Q x y \<Longrightarrow> P x y \<longleftrightarrow> R x y) \<Longrightarrow> \<Union>{f x y |x y. P x y \<and> Q x y} = \<Union>{f x y |x y. R x y \<and> Q x y} "
  by auto  metis+

lemma split6_lem2: "(\<And>x y. Q x y \<Longrightarrow> P x y \<Longrightarrow> R x y) \<Longrightarrow> \<Union>{f x y |x y. P x y \<and> (R x y \<and> Q x y)} = \<Union>{f x y |x y. P x y \<and> Q x y} "
  by auto metis

lemma split6_lem3: "(\<And>x y. P x y = Q x y) \<Longrightarrow> \<Union>{f x y |x y. P x y} = \<Union>{f x y |x y. Q x y} "
  by auto

lemma split6_lem4: "\<Union>{f x y |x y. P x y \<or> Q x y} = \<Union>{f x y |x y. P x y} \<union> \<Union>{f x y |x y. Q x y}"
  by auto metis

lemma split6_lem5: "X = Y \<Longrightarrow> X \<union> Z = Y \<union> Z"
  by auto

lemma split6_lem6: "X = Y \<Longrightarrow> Z \<union> X = Z \<union> Y"
  by auto

lemma split6_lem7: "X \<subseteq> Z \<Longrightarrow> X \<union> Y \<union> Z = Y \<union> Z"
  by auto

lemma split6_lem8: "X \<subseteq> Y \<Longrightarrow> X \<union> Y \<union> Z = Y \<union> Z"
  by auto

lemma split6_lem9: "\<Union>{f x y |x y. P x y} = \<Union>{f x y |y x. P x y} "
  by auto

lemma split6_lem10: "X \<subseteq> Z \<Longrightarrow> X \<union> Y \<union> Z \<union> W = Y \<union> Z \<union> W"
  by auto

lemma split6:
  assumes [simp]: "lfinite x" and [simp]: "lfinite y"
  shows
  "(x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (y \<frown> (\<tau> # \<tau>' # y\<^sub>t)) = \<Union>{(x \<sha> y') \<cdot> {sng (Inl \<sigma>) \<frown> lmap Inr y'' \<frown> sng (Inr \<tau>) \<frown> sng (Inr \<tau>') \<frown> lmap Inr y\<^sub>t' \<frown> sng (Inl \<sigma>')} \<cdot> (x\<^sub>t \<sha> y\<^sub>t'') |y' y'' y\<^sub>t' y\<^sub>t''. y = y' \<frown> y'' \<and> y\<^sub>t = y\<^sub>t' \<frown> y\<^sub>t'' \<and> lfinite y' \<and> lfinite y\<^sub>t'}
                                              \<union> \<Union>{(x \<sha> y') \<cdot> {sng (Inl \<sigma>) \<frown> lmap Inr y'' \<frown> sng (Inr \<tau>) \<frown> sng (Inl \<sigma>') \<frown> lmap Inl x\<^sub>t' \<frown> sng (Inr \<tau>')} \<cdot> (x\<^sub>t'' \<sha> y\<^sub>t) |y' y'' x\<^sub>t' x\<^sub>t''. y = y' \<frown> y'' \<and> x\<^sub>t = x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite y' \<and> lfinite x\<^sub>t'}
                                              \<union> \<Union>{(x \<sha> y') \<cdot> {sng (Inl \<sigma>) \<frown> lmap Inr y'' \<frown> sng (Inl \<sigma>')} \<cdot> (x\<^sub>t \<sha> (y''' \<frown> (\<tau> # \<tau>' # y\<^sub>t))) |y' y'' y'''. y = y' \<frown> y'' \<frown> y''' \<and> lfinite y' \<and> lfinite y''}
                                              \<union> \<Union>{(x' \<sha> y) \<cdot> {sng (Inr \<tau>) \<frown> lmap Inl x'' \<frown> sng (Inl \<sigma>) \<frown> sng (Inl \<sigma>') \<frown> lmap Inl x\<^sub>t' \<frown> sng (Inr \<tau>')} \<cdot> (x\<^sub>t'' \<sha> y\<^sub>t) |x' x'' x\<^sub>t' x\<^sub>t''. x = x' \<frown> x'' \<and> x\<^sub>t = x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite x' \<and> lfinite x\<^sub>t'}
                                              \<union> \<Union>{(x' \<sha> y) \<cdot> {sng (Inr \<tau>) \<frown> lmap Inl x'' \<frown> sng (Inl \<sigma>) \<frown> sng (Inr \<tau>') \<frown> lmap Inr y\<^sub>t' \<frown> sng (Inl \<sigma>')} \<cdot> (x\<^sub>t \<sha> y\<^sub>t'') |x' x'' y\<^sub>t' y\<^sub>t''. x = x' \<frown> x'' \<and> y\<^sub>t = y\<^sub>t' \<frown> y\<^sub>t'' \<and> lfinite x' \<and> lfinite y\<^sub>t'}
                                              \<union> \<Union>{(x' \<sha> y) \<cdot> {sng (Inr \<tau>) \<frown> lmap Inl x'' \<frown> sng (Inr \<tau>')} \<cdot> ((x''' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> y\<^sub>t) |x' x'' x'''. x = x' \<frown> x'' \<frown> x''' \<and> lfinite x' \<and> lfinite x''}"
proof -
  have "(x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (y \<frown> (\<tau> # \<tau>' # y\<^sub>t)) = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) = z \<frown> z' \<and> lfinite z}"
    by (subst shuffle_lappend_right[OF assms(2)]) simp
  also have "... = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) = z \<frown> z' \<and> (x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) = z \<frown> z' \<and> lfinite z)}"
    by auto
  also have "... = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. ((\<exists>w w'. z = w \<frown> w' \<and> x = w \<and> \<sigma> # \<sigma>' # x\<^sub>t = w' \<frown> z') \<or> (\<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t))) \<and> (x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) = z \<frown> z' \<and> lfinite z)}"
    apply (rule split6_lem1)
    apply (subst lprefix_opts[where x = x and x' = "(\<sigma> # \<sigma>' # x\<^sub>t)"])
    by simp_all
  also have "... = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. ((\<exists>w w'. z = w \<frown> w' \<and> x = w \<and> \<sigma> # \<sigma>' # x\<^sub>t = w' \<frown> z') \<or> (\<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t))) \<and> lfinite z}"
    apply (rule split6_lem2)
    apply (erule disjE)
    apply (erule exE)+
    apply (erule conjE)+
    apply (simp add: lappend_assoc)
    apply (erule exE)+
    apply (erule conjE)+
    by (simp add: lappend_assoc)
  also have "... = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. (\<exists>w w'. z = w \<frown> w' \<and> x = w \<and> \<sigma> # \<sigma>' # x\<^sub>t = w' \<frown> z' \<and> lfinite z) \<or> (\<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite z)}"
    apply (rule split6_lem3)
    by auto
  also have "... = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. \<exists>w w'. z = w \<frown> w' \<and> x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite z} \<union>
                   \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. \<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite z}"
    by (rule split6_lem4)
  also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w'} \<union>
                   \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. \<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite z}"
  proof (rule split6_lem5)
    let ?lhs = "\<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. \<exists>w w'. z = w \<frown> w' \<and> x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite z}"

    have "?lhs = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z' w w'. z = w \<frown> w' \<and> x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite z}"
      by auto
    also have "... = \<Union>{((w \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z' w w'. z = w \<frown> w' \<and> x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite z}"
      apply auto
      apply metis
      by (metis assms(1) lfinite_lappend)
    also have "... = \<Union>{((w \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z' w w'. z = w \<frown> w' \<and> x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w \<and> lfinite w'}"
      by auto
    also have "... = \<Union>{((w \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w w'. x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w \<and> lfinite w'}"
      by auto
    also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w w'. x = w \<and> (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w \<and> lfinite w'}"
      by auto
    also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w'}" (is "_ = ?rhs")
      by auto
    finally show "?lhs = ?rhs" .
  qed
  also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w'} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
  proof (rule split6_lem6)
    let ?lhs = "\<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z'. \<exists>w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite z}"

    have "?lhs = \<Union>{(z \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z z' w w'. x = w \<frown> w' \<and> z = w \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite z}"
      by auto
    also have "... = \<Union>{(w \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w w'. x = w \<frown> w' \<and> z' = w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t) \<and> lfinite w}"
      by auto
    also have "... = \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}" (is "_ = ?rhs")
      by auto
    finally show "?lhs = ?rhs" .
  qed
  also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. ((\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w' \<and> w' = LNil) \<or> (\<exists>\<gamma> u. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w' \<and> w' = \<gamma> # u)} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)
    apply (rule split6_lem3)
    by (metis lfinite.simps)
  also have "... = \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w' \<and> w' = LNil} \<union>
                   \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. \<exists>\<gamma> u. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w' \<and> w' = \<gamma> # u} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)
    by (rule split6_lem4)
  also have "... = (x \<sha> y) \<cdot> ((\<sigma> # \<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> w') \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' w'. \<exists>\<gamma> u. (\<sigma> # \<sigma>' # x\<^sub>t) = w' \<frown> z' \<and> lfinite w' \<and> w' = \<gamma> # u} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)
    apply (rule split6_lem5)
    by simp
  also have "... = (x \<sha> y) \<cdot> ((\<sigma> # \<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)
    apply (rule split6_lem6)
    apply auto
    apply metis
    by (metis lappend_code(2) lfinite_LCons)
  also have "... = \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem7)
    apply auto
    apply (rule_tac x = "(x \<sha> y) \<cdot> ((\<sigma> # \<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t))" in exI)
    apply simp
    apply (rule_tac x = x in exI) apply (rule_tac x = LNil in exI)
    by simp
  also have "... = \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. ((\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u \<and> u = LNil) \<or> (\<exists>\<gamma> u'. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u \<and> u = (\<gamma> # u'))} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
  proof (rule split6_lem5, rule split6_lem3)
    fix z' u
    show "(\<sigma>' # x\<^sub>t = u \<frown> z' \<and> lfinite u) = (\<sigma>' # x\<^sub>t = u \<frown> z' \<and> lfinite u \<and> u = LNil \<or> (\<exists>\<gamma> u'. \<sigma>' # x\<^sub>t = u \<frown> z' \<and> lfinite u \<and> u = \<gamma> # u'))"
      by (cases u) simp_all
  qed
  also have "... = \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u \<and> u = LNil} \<union>
                   \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. \<exists>\<gamma> u'. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u \<and> u = (\<gamma> # u')} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    by (rule split6_lem5) (rule split6_lem4)
  also have "... = ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> ((\<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # u)) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u. \<exists>\<gamma> u'. (\<sigma>' # x\<^sub>t) = u \<frown> z' \<and> lfinite u \<and> u = (\<gamma> # u')} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)+
    by simp
  also have "... = ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> ((\<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # \<sigma>' # u')) \<sha> y) \<cdot> (z' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |z' u'. x\<^sub>t = u' \<frown> z' \<and> lfinite u'} \<union>
                   \<Union>{(w \<sha> y) \<cdot> ((w' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |w w'. x = w \<frown> w' \<and> lfinite w}"
    apply (rule split6_lem5)
    apply (rule split6_lem6)
    apply auto
    apply metis
    by (metis lappend_code(2) lfinite_LCons)
  also have "... = ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> ((\<sigma>' # x\<^sub>t) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t')) \<sha> y) \<cdot> (x\<^sub>t'' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x\<^sub>t' x\<^sub>t''. x\<^sub>t = x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite x\<^sub>t'} \<union>
                   \<Union>{(x' \<sha> y) \<cdot> ((x'' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x' x''. x = x' \<frown> x'' \<and> lfinite x'}"
    apply (rule split6_lem5)
    apply (rule split6_lem6)
    by (rule split6_lem9)
  also have "... = ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> {sng (Inl \<sigma>')} \<cdot> (x\<^sub>t \<sha> (\<tau> # \<tau>' # y\<^sub>t)) \<union>
                   ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> {sng (Inr \<tau>)} \<cdot> ((\<sigma>' # x\<^sub>t) \<sha> (\<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t')) \<sha> y) \<cdot> (x\<^sub>t'' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x\<^sub>t' x\<^sub>t''. x\<^sub>t = x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite x\<^sub>t'} \<union>
                   \<Union>{(x' \<sha> y) \<cdot> ((x'' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x' x''. x = x' \<frown> x'' \<and> lfinite x'}"
    apply (rule split6_lem5)+
    apply (subst LCons_tshuffle)
    apply (simp add: l_prod_assoc)
    apply (rule arg_cong2[where f = "\<lambda>A B. ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> A \<union> ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> B"])
    by (auto simp add: l_prod_def)
  also have "... = ((x \<frown> sng \<sigma>) \<sha> y) \<cdot> {sng (Inr \<tau>)} \<cdot> ((\<sigma>' # x\<^sub>t) \<sha> (\<tau>' # y\<^sub>t)) \<union>
                   \<Union>{((x \<frown> (\<sigma> # \<sigma>' # x\<^sub>t')) \<sha> y) \<cdot> (x\<^sub>t'' \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x\<^sub>t' x\<^sub>t''. x\<^sub>t = x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite x\<^sub>t'} \<union>
                   \<Union>{(x' \<sha> y) \<cdot> ((x'' \<frown> (\<sigma> # \<sigma>' # x\<^sub>t)) \<sha> (\<tau> # \<tau>' # y\<^sub>t)) |x' x''. x = x' \<frown> x'' \<and> lfinite x'}"
    apply (rule split6_lem10)
    apply auto
    apply (rule_tac x = "((x \<frown> (\<sigma> # \<sigma>' # LNil)) \<sha> y) \<cdot> (x\<^sub>t \<sha> (\<tau> # \<tau>' # y\<^sub>t))" in exI)
    apply (intro conjI)
    apply (rule_tac x = LNil in exI)
    apply (rule_tac x = "x\<^sub>t" in exI)
    apply simp
    apply (erule rev_mp)
    apply (rule in_mono)
    apply (rule l_prod_isol)
    sorry
  show ?thesis
    sorry
qed

lemma l_prod_elem_ex: "X \<subseteq> FIN \<Longrightarrow> z \<in> X \<cdot> Y \<Longrightarrow> (\<exists>z' z''. z = z' \<frown> z'' \<and> z' \<in> X \<and> z'' \<in> Y)"
  apply (auto simp add: l_prod_def)
  by (metis FIN_def contra_subsetD mem_Collect_eq)

lemma lfinite_traj_from_Valid: "lfinite x \<Longrightarrow> lfinite y \<Longrightarrow> Valid x t y \<Longrightarrow> lfinite t"
  apply (auto simp add: Valid_def)
  by (metis lfinite_llength_enat lfinite_lr llength_eq_enat_lfiniteD)

lemma Env_Rely1: "R \<Colon> (R \<rhd> X) \<le> X"
  by (metis Env_galois Rely_EnvUp)

lemma rely_xy_env: "rely R x y \<Longrightarrow> env (R\<^sup>*) x \<Longrightarrow> x = y"
  by (auto simp add: rely_def)

lemma Env_Rely2: "R \<rhd> (R \<Colon> X) \<le> X"
  by (auto simp add: Rely_def Env_def) (metis rely_xy_env)

lemma Env_Rely3: "R \<rhd> (R \<Colon> X) = R \<Colon> X"
  apply (auto simp add: Rely_def Env_def)
  apply (metis rely_xy_env)
  apply (metis rely_xy_env)
  by (metis IntI mem_Collect_eq rely_refl)

lemma Env_Rely4: "R \<Colon> (R \<rhd> X) = R \<Colon> X"
  apply (auto simp add: Rely_def Env_def)
  apply (metis rely_sym rely_xy_env)
  by (metis rely_refl)

lemma failure_point:
  assumes "lfinite x"
  and "x \<in> guar G"
  and "(\<sigma>',\<tau>) \<notin> (R \<union> G)\<^sup>*"
  shows "\<exists>w \<gamma> \<gamma>' \<phi> \<phi>' w'. sng (\<sigma>,\<sigma>') \<frown> x \<frown> sng (\<tau>,\<tau>') = w \<frown> ((\<gamma>,\<gamma>') # (\<phi>,\<phi>') # w') \<and> (\<gamma>',\<phi>) \<notin> R\<^sup>* \<and> env (R\<^sup>*) (w \<frown> ((\<gamma>,\<gamma>') # LNil))"
  using assms
proof (induct arbitrary: \<sigma> \<sigma>' rule: lfinite_induct)
  case Nil
  thus ?case
    apply (rule_tac x = LNil in exI)
    apply (rule_tac x = \<sigma> in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply (rule_tac x = \<tau> in exI)
    apply (rule_tac x = \<tau>' in exI)
    apply (rule_tac x = LNil in exI)
    apply simp
    by (metis in_rtrancl_UnI)
next
  case (Cons x\<^sub>h x\<^sub>t) note ind_hyp = this
  obtain \<sigma>'' \<sigma>''' where x\<^sub>h_split [simp]: "x\<^sub>h = (\<sigma>'',\<sigma>''')"
    by (cases "x\<^sub>h") auto

  from ind_hyp(3)
  have "(\<sigma>'',\<sigma>''') \<in> G\<^sup>*"
    by simp

  have "x\<^sub>t \<in> guar G"
    by (metis guar_lappend ind_hyp(3) lappend_code(1) lappend_code(2) lfinite_LCons lfinite_LNil)

  show ?case
  proof (cases "(\<sigma>',\<sigma>'') \<in> R\<^sup>*")
    assume "(\<sigma>',\<sigma>'') \<in> R\<^sup>*"
    from this and `(\<sigma>'',\<sigma>''') \<in> G\<^sup>*` and ind_hyp(4)
    have "(\<sigma>''', \<tau>) \<notin> (R \<union> G)\<^sup>*"
      apply (cases "(\<sigma>''', \<tau>) \<in> (R \<union> G)\<^sup>*")
      apply simp_all
      apply (subgoal_tac "(\<sigma>'', \<tau>) \<in> (R \<union> G)\<^sup>*")
      apply (metis in_rtrancl_UnI rtrancl_trans)
      by (metis (erased, hide_lams) Un_upper1 contra_subsetD rtrancl_mono rtrancl_trans sup_commute)
    from ind_hyp(2)[OF `x\<^sub>t \<in> guar G` this, of \<sigma>''] obtain w \<gamma> \<gamma>' \<phi> \<phi>' w'
    where ind_hyp_eq: "sng (\<sigma>'', \<sigma>''') \<frown> x\<^sub>t \<frown> sng (\<tau>, \<tau>') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
    and [simp]: "(\<gamma>', \<phi>) \<notin> R\<^sup>*" and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
      by auto

    have [simp]: "w = LNil \<Longrightarrow> \<gamma> = \<sigma>''"
      by (metis ind_hyp_eq lappend_code(1) lappend_code(2) lhd_LCons prod.sel(1))

    show ?case
      apply (rule_tac x = "(\<sigma>,\<sigma>') # w" in exI)
      apply (rule_tac x = \<gamma> in exI)
      apply (rule_tac x = \<gamma>' in exI)
      apply (rule_tac x = \<phi> in exI)
      apply (rule_tac x = \<phi>' in exI)
      apply (rule_tac x = w' in exI)
      apply (intro conjI)
      apply (simp_all add: ind_hyp_eq[simplified])
      apply (cases w)
      apply (simp add: `(\<sigma>',\<sigma>'') \<in> R\<^sup>*`)
      apply (rename_tac w\<^sub>h w\<^sub>t)
      apply (subgoal_tac "w\<^sub>h = (\<sigma>'',\<sigma>''')")
      apply (insert `env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))`)
      apply (simp add: `(\<sigma>',\<sigma>'') \<in> R\<^sup>*`)
      apply (insert ind_hyp_eq)
      by auto
  next
    assume "(\<sigma>', \<sigma>'') \<notin> R\<^sup>*"
    thus ?case
      apply (rule_tac x = LNil in exI)
      apply (rule_tac x = \<sigma> in exI)
      apply (rule_tac x = \<sigma>' in exI)
      apply (rule_tac x = \<sigma>'' in exI)
      apply (rule_tac x = \<sigma>''' in exI)
      by simp
  qed
qed

lemma failure_point2:
  assumes "lfinite x"
  and "x \<in> guar G"
  and "(\<sigma>',\<tau>) \<notin> (R \<union> G)\<^sup>*"
  shows "\<exists>w \<gamma> \<gamma>' \<phi>. (\<forall>\<tau>'. \<exists>\<phi>' w'. sng (\<sigma>,\<sigma>') \<frown> x \<frown> sng (\<tau>,\<tau>') = w \<frown> ((\<gamma>,\<gamma>') # (\<phi>,\<phi>') # w')) \<and> (\<gamma>',\<phi>) \<notin> R\<^sup>* \<and> env (R\<^sup>*) (w \<frown> ((\<gamma>,\<gamma>') # LNil))"
  using assms
proof (induct arbitrary: \<sigma> \<sigma>' rule: lfinite_induct)
  case Nil
  thus ?case
    apply (rule_tac x = LNil in exI)
    apply (rule_tac x = \<sigma> in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply (rule_tac x = \<tau> in exI)
    apply (intro conjI)
    apply (rule_tac allI)
    apply (rule_tac x = \<tau>' in exI)
    apply (rule_tac x = LNil in exI)
    apply simp_all
    by (metis in_rtrancl_UnI)
next
  case (Cons x\<^sub>h x\<^sub>t) note ind_hyp = this
  obtain \<sigma>'' \<sigma>''' where x\<^sub>h_split [simp]: "x\<^sub>h = (\<sigma>'',\<sigma>''')"
    by (cases "x\<^sub>h") auto

  from ind_hyp(3)
  have "(\<sigma>'',\<sigma>''') \<in> G\<^sup>*"
    by simp

  have "x\<^sub>t \<in> guar G"
    by (metis guar_lappend ind_hyp(3) lappend_code(1) lappend_code(2) lfinite_LCons lfinite_LNil)

  show ?case
  proof (cases "(\<sigma>',\<sigma>'') \<in> R\<^sup>*")
    assume "(\<sigma>',\<sigma>'') \<in> R\<^sup>*"
    from this and `(\<sigma>'',\<sigma>''') \<in> G\<^sup>*` and ind_hyp(4)
    have "(\<sigma>''', \<tau>) \<notin> (R \<union> G)\<^sup>*"
      apply (cases "(\<sigma>''', \<tau>) \<in> (R \<union> G)\<^sup>*")
      apply simp_all
      apply (subgoal_tac "(\<sigma>'', \<tau>) \<in> (R \<union> G)\<^sup>*")
      apply (metis in_rtrancl_UnI rtrancl_trans)
      by (metis (erased, hide_lams) Un_upper1 contra_subsetD rtrancl_mono rtrancl_trans sup_commute)
    from ind_hyp(2)[OF `x\<^sub>t \<in> guar G` this, of \<sigma>''] obtain w \<gamma> \<gamma>' \<phi>
    where ind_hyp_eq: "\<forall>\<tau>'. \<exists>\<phi>' w'. sng (\<sigma>'', \<sigma>''') \<frown> x\<^sub>t \<frown> sng (\<tau>, \<tau>') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
    and [simp]: "(\<gamma>', \<phi>) \<notin> R\<^sup>*" and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
      by auto

    have [simp]: "w = LNil \<Longrightarrow> \<gamma> = \<sigma>''"
      by (metis ind_hyp_eq lappend_code(1) lappend_code(2) lhd_LCons prod.sel(1))

    show ?case
      apply (rule_tac x = "(\<sigma>,\<sigma>') # w" in exI)
      apply (rule_tac x = \<gamma> in exI)
      apply (rule_tac x = \<gamma>' in exI)
      apply (rule_tac x = \<phi> in exI)
      apply (intro conjI)
      apply (rule_tac allI)
      apply (simp_all add: ind_hyp_eq[simplified])
      apply (cases w)
      apply (simp add: `(\<sigma>',\<sigma>'') \<in> R\<^sup>*`)
      apply (rename_tac w\<^sub>h w\<^sub>t)
      apply (subgoal_tac "w\<^sub>h = (\<sigma>'',\<sigma>''')")
      apply (insert `env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))`)
      apply (simp add: `(\<sigma>',\<sigma>'') \<in> R\<^sup>*`)
      apply (insert ind_hyp_eq)
      by auto
  next
    assume "(\<sigma>', \<sigma>'') \<notin> R\<^sup>*"
    thus ?case
      apply (rule_tac x = LNil in exI)
      apply (rule_tac x = \<sigma> in exI)
      apply (rule_tac x = \<sigma>' in exI)
      apply (rule_tac x = \<sigma>'' in exI)
      apply (intro conjI)
      by simp_all
  qed
qed

lemma [simp]: "\<rr> (lmap Inl xs) = LNil"
  by (simp add: rights_def)

lemma guar_split_first: "x \<frown> y \<in> guar G \<Longrightarrow> x \<in> guar G"
  by (metis guar_lappend lappend_inf)

lemma second_lappend_eq: "lfinite x \<Longrightarrow> x \<frown> y = x \<frown> z \<longleftrightarrow> y = z"
  by (metis lappend_eq_lappend_conv)

lemma first_lappend_eq: "x = y \<Longrightarrow> x \<frown> z = y \<frown> z"
  by auto

lemma sngify: "w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w' \<frown> w'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w') \<frown> w''"
  by (simp add: lappend_assoc)

lemma guar_singleton: "sng (\<sigma>,\<sigma>') \<in> guar G \<longleftrightarrow> (\<sigma>,\<sigma>') \<in> G\<^sup>*"
  apply (auto simp add: guar_def)
  apply (metis lappend_code(1))
  by (metis LNil_eq_lappend_iff eq_LConsD lappend_lnull1 ltl_lappend)

lemma sng_end_eq: "lfinite x \<Longrightarrow> (x \<frown> sng y = z \<frown> sng w) \<longleftrightarrow> (x = z \<and> y = w)"
proof (induct x arbitrary: z rule: lfinite_induct)
  case Nil
  thus ?case
    apply auto
    apply (cases "z \<noteq> LNil")
    apply (metis LNil_eq_lappend_iff lappend_code(2) llist.distinct(1) llist.exhaust llist.inject)
    apply simp
    apply (cases "z \<noteq> LNil")
    apply (metis LNil_eq_lappend_iff lappend_code(2) llist.distinct(1) llist.exhaust llist.inject)
    by simp
next
  case (Cons x xs)
  thus ?case
    apply auto
    apply (cases "z = LNil")
    apply simp
    apply (metis LNil_eq_lappend_iff neq_LNil_conv)
    apply (subgoal_tac "\<exists>z' z''. z = z' # z''")
    apply (erule exE)+
    apply simp
    apply (metis neq_LNil_conv)
    apply (cases "z = LNil")
    apply simp
    apply (metis LNil_eq_lappend_iff neq_LNil_conv)
    apply (subgoal_tac "\<exists>z' z''. z = z' # z''")
    apply (erule exE)+
    apply simp
    by auto
qed

lemma rely_guarantee':
  assumes "z \<in> x \<sha> y"
  and "x \<in> R \<union> G\<^sub>2 \<rhd> X \<inter> guar G\<^sub>1"
  and "y \<in> R \<union> G\<^sub>1 \<rhd> Y \<inter> guar G\<^sub>2"
  shows "lmap \<langle>id,id\<rangle> z \<in> (R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2))"
proof -
  from assms(2)
  obtain x' where r1: "rely (R \<union> G\<^sub>2) x' x" and x'_in: "x' \<in> X \<inter> guar G\<^sub>1"
    by (auto simp add: Rely_def)

  have x'_in': "x' \<in> guar G\<^sub>1"
    by (metis IntE x'_in)

  from assms(3)
  obtain y' where r2: "rely (R \<union> G\<^sub>1) y' y" and y'_in: "y' \<in> Y \<inter> guar G\<^sub>2"
    by (auto simp add: Rely_def)

  have y'_in': "y' \<in> guar G\<^sub>2"
    by (metis IntE y'_in)

  from r1 and r2
  show ?thesis
    apply -
    apply (simp only: rely_def_var)
    apply (erule disjE)
    apply (erule disjE)
    prefer 3
    apply (erule disjE)
    defer
  proof -
    assume "x' = x" and "y' = y"
    thus "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
      apply (simp add: Rely_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> z" in bexI)
      apply (metis rely_refl)
      apply (rule shuffle_elem[of x _ y])
      apply (metis x'_in)
      apply (metis y'_in)
      by (metis assms(1))
  next
    assume "rely' (R \<union> G\<^sub>2) x' x" and "rely' (R \<union> G\<^sub>1) y' y"

    from `rely' (R \<union> G\<^sub>2) x' x` obtain x\<^sub>p \<sigma>\<^sub>0 \<sigma>\<^sub>0' \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>1'' x\<^sub>t x\<^sub>u
    where x'_def: "x' = x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1') # x\<^sub>t)" and x_def: "x = x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1'') # x\<^sub>u)"
    and "(\<sigma>\<^sub>0',\<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*" and "env ((R \<union> G\<^sub>2)\<^sup>*) (x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # LNil))" and "lfinite x\<^sub>p"
      by (auto simp add: rely'_def)

    have x\<^sub>p_guar [simp]: "x\<^sub>p \<in> guar G\<^sub>1"
      using x'_in'
      apply (simp only: x'_def)
      by (erule guar_split_first)

    have x\<^sub>t_guar [simp]: "x\<^sub>t \<in> guar G\<^sub>1"
      using x'_in'
      by (simp add: x'_def guar_lappend[OF `lfinite x\<^sub>p`])

    have \<sigma>_guar [simp]: "(\<sigma>\<^sub>0,\<sigma>\<^sub>0') \<in> G\<^sub>1\<^sup>*"
      by (metis `lfinite x\<^sub>p` guar_LCons_eq guar_lappend x'_def x'_in')

    have \<sigma>_guar2 [simp]: "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<in> G\<^sub>1\<^sup>*" using x'_in'
      by (simp add: x'_def guar_lappend[OF `lfinite x\<^sub>p`])

    from `rely' (R \<union> G\<^sub>1) y' y` obtain y\<^sub>p \<tau>\<^sub>0 \<tau>\<^sub>0' \<tau>\<^sub>1 \<tau>\<^sub>1' \<tau>\<^sub>1'' y\<^sub>t y\<^sub>u
    where y'_def: "y' = y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1') # y\<^sub>t)" and y_def: "y = y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1'') # y\<^sub>u)"
    and "(\<tau>\<^sub>0',\<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*" and "env ((R \<union> G\<^sub>1)\<^sup>*) (y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # LNil))" and "lfinite y\<^sub>p"
      by (auto simp add: rely'_def)

    have y\<^sub>p_guar [simp]: "y\<^sub>p \<in> guar G\<^sub>2"
      using y'_in'
      apply (simp only: y'_def)
      by (erule guar_split_first)

    have y\<^sub>t_guar [simp]: "y\<^sub>t \<in> guar G\<^sub>2"
      using y'_in'
      by (simp add: y'_def guar_lappend[OF `lfinite y\<^sub>p`])

    have \<tau>_guar [simp]: "(\<tau>\<^sub>0,\<tau>\<^sub>0') \<in> G\<^sub>2\<^sup>*"
      by (metis `lfinite y\<^sub>p` guar_LCons_eq guar_lappend y'_def y'_in')

    have \<tau>_guar2 [simp]: "(\<tau>\<^sub>1,\<tau>\<^sub>1') \<in> G\<^sub>2\<^sup>*" using y'_in'
      by (simp add: y'_def guar_lappend[OF `lfinite y\<^sub>p`])

    from `z \<in> x \<sha> y`
    have "z \<in> (x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1'') # x\<^sub>u)) \<sha> (y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1'') # y\<^sub>u))"
      by (simp only: x_def y_def)

    also have "... = \<Union>{(x\<^sub>p \<sha> y') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>t' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>t'') |y' y'' y\<^sub>t' y\<^sub>t''. y\<^sub>p= y' \<frown> y'' \<and> y\<^sub>u= y\<^sub>t' \<frown> y\<^sub>t'' \<and> lfinite y' \<and> lfinite y\<^sub>t'} \<union>
                     \<Union>{(x\<^sub>p \<sha> y') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>t' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>t'' \<sha> y\<^sub>u) |y' y'' x\<^sub>t' x\<^sub>t''. y\<^sub>p= y' \<frown> y'' \<and> x\<^sub>u= x\<^sub>t' \<frown> x\<^sub>t''\<and> lfinite y' \<and> lfinite x\<^sub>t'} \<union>
                     \<Union>{(x\<^sub>p \<sha> y') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> (y''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u))) | y' y'' y'''. y\<^sub>p= y' \<frown> y'' \<frown> y''' \<and> lfinite y' \<and> lfinite y''} \<union>
                     \<Union>{(x' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>t' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>t'' \<sha> y\<^sub>u) |x' x'' x\<^sub>t' x\<^sub>t''. x\<^sub>p= x' \<frown> x'' \<and> x\<^sub>u= x\<^sub>t' \<frown> x\<^sub>t'' \<and> lfinite x' \<and> lfinite x\<^sub>t'} \<union>
                     \<Union>{(x' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>t' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>t'') |x' x'' y\<^sub>t' y\<^sub>t''. x\<^sub>p= x' \<frown> x'' \<and> y\<^sub>u= y\<^sub>t' \<frown> y\<^sub>t'' \<and> lfinite x' \<and> lfinite y\<^sub>t'} \<union>
                     \<Union>{(x' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> ((x''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u)) \<sha> y\<^sub>u) |x' x'' x'''. x\<^sub>p= x' \<frown> x'' \<frown> x''' \<and> lfinite x' \<and> lfinite x''}"
      (is "_ = ?Z1 \<union> ?Z2 \<union> ?Z3 \<union> ?Z4 \<union> ?Z5 \<union> ?Z6")
      apply (subst split6)
      prefer 3
      apply simp
      apply (metis `lfinite x\<^sub>p`)
      by (metis `lfinite y\<^sub>p`)
    finally have "z \<in> ?Z1 \<union> ?Z2 \<union> ?Z3 \<union> ?Z4 \<union> ?Z5 \<union> ?Z6" .
    hence "z \<in> ?Z1 \<or> z \<in> ?Z2 \<or> z \<in> ?Z3 \<or> z \<in> ?Z4 \<or> z \<in> ?Z5 \<or> z \<in> ?Z6"
      by blast
    hence "((((z \<in> ?Z1 \<or> z \<in> ?Z2) \<or> z \<in> ?Z3) \<or> z \<in> ?Z4) \<or> z \<in> ?Z5) \<or> z \<in> ?Z6"
      by blast
    thus "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)" apply -
    proof (erule disjE)+
      assume "z \<in> ?Z1"

      then obtain y\<^sub>p' y\<^sub>p'' y\<^sub>u' y\<^sub>u''
      where z1: "z \<in> (x\<^sub>p \<sha> y\<^sub>p') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>u'')"
      and "y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''" and "y\<^sub>u = y\<^sub>u' \<frown> y\<^sub>u''"  and [simp]: "lfinite y\<^sub>p'" and [simp]: "lfinite y\<^sub>u'"
        by auto

      hence [simp]: "lfinite y\<^sub>p''"
        by (metis `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''` `lfinite y\<^sub>p` lfinite_lappend)

      have "x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN"
        by auto (metis `lfinite x\<^sub>p`)
      have l1: "{sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 t\<^sub>2
      where z_def: "z = (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u'')"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p t\<^sub>1 y\<^sub>p'" and [simp]: "Valid x\<^sub>u t\<^sub>2 y\<^sub>u''"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p t\<^sub>1 y\<^sub>p'` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite x\<^sub>p` `lfinite y\<^sub>p'` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1')) \<frown> alternate ((\<sigma>\<^sub>1,\<sigma>\<^sub>1') # x\<^sub>t) y\<^sub>t"

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc x'_def[symmetric])
        apply (metis IntE x'_in)
        apply (subst rights_append, simp)+
        apply (simp add: `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''`[symmetric])
        apply (simp add: lappend_assoc y'_def[symmetric])
        by (metis IntE y'_in)

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ((x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'')" in exI)
        apply (rule_tac x = \<tau>\<^sub>0 in exI) apply (rule_tac x = \<tau>\<^sub>0' in exI)
        apply (rule_tac x = \<tau>\<^sub>1 in exI) apply (rule_tac x = \<tau>\<^sub>1' in exI) apply (rule_tac x = \<tau>\<^sub>1'' in exI)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (alternate ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t) y\<^sub>t)" in exI)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u''))" in exI)
        apply (intro conjI)
        apply (smt id_apply lappend_assoc lappend_code(1) lappend_code(2) llist.simps(13) lmap_lappend_distrib old.sum.simps(5) old.sum.simps(6))
        apply (smt all_lefts id_apply lappend_assoc lappend_code(1) lappend_code(2) lefts_def_var lefts_mapl llist.distinct(2) llist.exhaust llist.inject llist.map(2) llist.sel(1) llist.sel(3) lmap_lappend_distrib sum.case(1) sum.case(2) sum.distinct(1) sumE unl.simps(1))
        apply (metis `(\<tau>\<^sub>0', \<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*` in_rtrancl_UnI)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    next
      assume "z \<in> ?Z2"

      then obtain y\<^sub>p' y\<^sub>p'' x\<^sub>u' x\<^sub>u''
      where z1: "z \<in> (x\<^sub>p \<sha> y\<^sub>p') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>u'' \<sha> y\<^sub>u)"
      and "y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''" and "x\<^sub>u = x\<^sub>u' \<frown> x\<^sub>u''" and [simp]: "lfinite y\<^sub>p'" and [simp]: "lfinite x\<^sub>u'"
        by auto

      hence [simp]: "lfinite y\<^sub>p''"
        by (metis `lfinite y\<^sub>p` lfinite_lappend)

      have "x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN"
        by auto (metis `lfinite x\<^sub>p`)
      have l1: "{sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 and t\<^sub>2
      where z_def: "z = (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> (x\<^sub>u'' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p t\<^sub>1 y\<^sub>p'" and [simp]: "Valid x\<^sub>u'' t\<^sub>2 y\<^sub>u"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p t\<^sub>1 y\<^sub>p'` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite x\<^sub>p` `lfinite y\<^sub>p'` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1')) \<frown> alternate x\<^sub>t ((\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t)"

      have "y\<^sub>p'' \<in> guar G\<^sub>2"
        by (metis `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''` `lfinite y\<^sub>p'` guar_lappend y\<^sub>p_guar)
      hence "y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<in> guar G\<^sub>2"
        apply (subst guar_lappend)
        by simp_all

      have "lfinite (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0'))" by simp

      from failure_point2[OF `lfinite (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0'))` `y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<in> guar G\<^sub>2` `(\<sigma>\<^sub>0',\<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*`, of \<sigma>\<^sub>0]
      obtain w \<gamma> \<gamma>' \<phi>
      where fp_all: "\<And>\<sigma>\<^sub>1'. \<exists>\<phi>' w'. sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
      and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
        by auto

      from fp_all[of \<sigma>\<^sub>1']
      obtain \<phi>' w'
      where fp: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
        by auto

      have [simp]: "lfinite w"
      proof -
        have "lfinite (sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'))"
          by simp
        hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
          by (simp only: fp)
        thus "lfinite w"
          by (metis lfinite_lappend)
      qed

      from fp_all[of \<sigma>\<^sub>1'']
      obtain \<phi>\<^sub>2' w\<^sub>2'
      where fp2: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> (y\<^sub>p'' \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
        by auto

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc x'_def[symmetric])
        apply (metis IntE x'_in)
        apply (subst rights_append, simp)+
        apply (simp add: `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p''`[symmetric])
        apply (simp add: lappend_assoc y'_def[symmetric])
        by (metis IntE y'_in)

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> w" in exI)
        apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
        apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
        apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate x\<^sub>t ((\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t))" in exI)
        apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> (lmap Inr x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> (x\<^sub>u'' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u))" in exI)
        apply (intro conjI)
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp lappend_code(1) lappend_code(2))
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp2[simplified] lappend_code(2))
        apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    next
      assume "z \<in> ?Z3"

      then obtain y\<^sub>p' y\<^sub>p'' y\<^sub>p'''
      where z1: "z \<in> (x\<^sub>p \<sha> y\<^sub>p') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u)))"
      and "y\<^sub>p =  y\<^sub>p' \<frown> y\<^sub>p''  \<frown> y\<^sub>p'''" and [simp]: "lfinite y\<^sub>p'" and [simp]: "lfinite y\<^sub>p''"
        by auto

      have "x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN"
        by auto (metis `lfinite x\<^sub>p`)
      have l1: "{sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 and t\<^sub>2
      where z_def: "z = (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u)))"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p t\<^sub>1 y\<^sub>p'" and [simp]: "Valid x\<^sub>u t\<^sub>2 (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u))"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p t\<^sub>1 y\<^sub>p'` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite x\<^sub>p` `lfinite y\<^sub>p'` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1')) \<frown> alternate x\<^sub>t (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t))"

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc x'_def[symmetric])
        apply (metis IntE x'_in)
        apply (subst rights_append, simp)+
        apply (simp add: lappend_assoc[symmetric])
        apply (simp add: `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''`[symmetric])
        apply (simp add: lappend_assoc y'_def[symmetric])
        by (metis IntE y'_in)

      have "y\<^sub>p'' \<in> guar G\<^sub>2"
        by (metis `y\<^sub>p = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''` `lfinite y\<^sub>p'` guar_lappend guar_split_first y\<^sub>p_guar)

      from failure_point2[OF `lfinite y\<^sub>p''` `y\<^sub>p'' \<in> guar G\<^sub>2` `(\<sigma>\<^sub>0',\<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*`, of \<sigma>\<^sub>0]
      obtain w \<gamma> \<gamma>' \<phi>
      where fp_all: "\<And>\<sigma>\<^sub>1'. \<exists>\<phi>' w'. sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
      and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
        by auto

      from fp_all[of \<sigma>\<^sub>1']
      obtain \<phi>' w'
      where fp: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
        by auto

      have [simp]: "lfinite w"
      proof -
        have "lfinite (sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'))"
          by simp
        hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
          by (simp only: fp)
        thus "lfinite w"
          by (metis lfinite_lappend)
      qed

      from fp_all[of \<sigma>\<^sub>1'']
      obtain \<phi>\<^sub>2' w\<^sub>2'
      where fp2: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
        by auto

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> w" in exI)
        apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
        apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
        apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate x\<^sub>t (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t)))" in exI)
        apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> (y\<^sub>p''' \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u)))" in exI)
        apply (intro conjI)
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp lappend_code(1) lappend_code(2))
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply (simp add: fp2[simplified])
        apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    next
      assume "z \<in> ?Z4"

      then obtain x\<^sub>p' x\<^sub>p'' x\<^sub>u' x\<^sub>u''
      where z1: "z \<in> (x\<^sub>p' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>u'' \<sha> y\<^sub>u)"
      and "x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''" and "x\<^sub>u = x\<^sub>u' \<frown> x\<^sub>u''"  and [simp]: "lfinite x\<^sub>p'" and [simp]: "lfinite x\<^sub>u'"
        by auto

      hence [simp]: "lfinite x\<^sub>p''"
        by (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` `lfinite x\<^sub>p` lfinite_lappend)

      have "x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN"
        by auto (metis `lfinite y\<^sub>p`)
      have l1: "{sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 t\<^sub>2
      where z_def: "z = (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> (x\<^sub>u'' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p' t\<^sub>1 y\<^sub>p" and [simp]: "Valid x\<^sub>u'' t\<^sub>2 y\<^sub>u"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p' t\<^sub>1 y\<^sub>p` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite y\<^sub>p` `lfinite x\<^sub>p'` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1')) \<frown> alternate x\<^sub>t ((\<tau>\<^sub>1,\<tau>\<^sub>1') # y\<^sub>t)"

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc)
        apply (intro conjI)
        apply (metis IntE `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` lappend_assoc x'_def x'_in)
        apply (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` guar_split_first x\<^sub>p_guar)
        apply (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` `lfinite x\<^sub>p'` guar_lappend x\<^sub>p_guar)
        apply (subst rights_append, simp)+
        apply (simp add: `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''`[symmetric])
        apply (simp add: lappend_assoc y'_def[symmetric])
        by (metis IntE y'_in)

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ((x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'')" in exI)
        apply (rule_tac x = \<sigma>\<^sub>0 in exI) apply (rule_tac x = \<sigma>\<^sub>0' in exI)
        apply (rule_tac x = \<sigma>\<^sub>1 in exI) apply (rule_tac x = \<sigma>\<^sub>1' in exI) apply (rule_tac x = \<sigma>\<^sub>1'' in exI)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (alternate x\<^sub>t ((\<tau>\<^sub>1,\<tau>\<^sub>1') # y\<^sub>t))" in exI)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (lmap Inl x\<^sub>u' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> (x\<^sub>u'' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u))" in exI)
        apply (intro conjI)
        apply (smt id_apply lappend_assoc lappend_code(1) lappend_code(2) llist.simps(13) lmap_lappend_distrib old.sum.simps(5) old.sum.simps(6))
        apply (simp add: lmap_lappend_distrib lappend_assoc)
        apply (metis `(\<sigma>\<^sub>0', \<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*` in_rtrancl_UnI)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    next
      assume "z \<in> ?Z5"

      then obtain x\<^sub>p' x\<^sub>p'' y\<^sub>u' y\<^sub>u''
      where z1: "z \<in> (x\<^sub>p' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>u'')"
      and "x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''" and "y\<^sub>u = y\<^sub>u' \<frown> y\<^sub>u''" and [simp]: "lfinite x\<^sub>p'" and [simp]: "lfinite y\<^sub>u'"
        by auto

      hence [simp]: "lfinite x\<^sub>p''"
        by (metis `lfinite x\<^sub>p` lfinite_lappend)

      have "x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN"
        by auto (metis `lfinite y\<^sub>p`)
      have l1: "{sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 and t\<^sub>2
      where z_def: "z = (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u'')"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p' t\<^sub>1 y\<^sub>p" and [simp]: "Valid x\<^sub>u t\<^sub>2 y\<^sub>u''"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p' t\<^sub>1 y\<^sub>p` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite x\<^sub>p'` `lfinite y\<^sub>p` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1')) \<frown> alternate ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t) y\<^sub>t"

      have "x\<^sub>p'' \<in> guar G\<^sub>1"
        by (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` `lfinite x\<^sub>p'` guar_lappend x\<^sub>p_guar)
      hence "x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<in> guar G\<^sub>1"
        by (subst guar_lappend) simp_all

      have "lfinite (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))" by simp

      from failure_point2[OF `lfinite (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))` `x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<in> guar G\<^sub>1` `(\<tau>\<^sub>0',\<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*`, of \<tau>\<^sub>0]
      obtain w \<gamma> \<gamma>' \<phi>
      where fp_all: "\<And>\<tau>\<^sub>1'. \<exists>\<phi>' w'. sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
      and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
        by auto

      from fp_all[of \<tau>\<^sub>1']
      obtain \<phi>' w'
      where fp: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
        by auto

      have [simp]: "lfinite w"
      proof -
        have "lfinite (sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'))"
          by simp
        hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
          by (simp only: fp)
        thus "lfinite w"
          by (metis lfinite_lappend)
      qed

      from fp_all[of \<tau>\<^sub>1'']
      obtain \<phi>\<^sub>2' w\<^sub>2'
      where fp2: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> (x\<^sub>p'' \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
        by auto

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc)
        apply (intro conjI)
        apply (metis IntE `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` lappend_assoc x'_def x'_in)
        apply (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` guar_split_first x\<^sub>p_guar)
        apply (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p''` `lfinite x\<^sub>p'` guar_lappend x\<^sub>p_guar)
        apply (subst rights_append, simp)+
        apply simp
        apply (simp add: lappend_assoc y'_def[symmetric])
        by (metis IntE y'_in)

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> w" in exI)
        apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
        apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
        apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate ((\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t) y\<^sub>t)" in exI)
        apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> (lmap Inl y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u''))" in exI)
        apply (intro conjI)
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp lappend_code(1) lappend_code(2))
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp2[simplified] lappend_code(2))
        apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    next
      assume "z \<in> ?Z6"

      then obtain x\<^sub>p' x\<^sub>p'' x\<^sub>p'''
      where z1: "z \<in> (x\<^sub>p' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> ((x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u)) \<sha> y\<^sub>u)"
      and "x\<^sub>p =  x\<^sub>p' \<frown> x\<^sub>p''  \<frown> x\<^sub>p'''" and [simp]: "lfinite x\<^sub>p'" and [simp]: "lfinite x\<^sub>p''"
        by auto

      have "x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN"
        by auto (metis `lfinite y\<^sub>p`)
      have l1: "{sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<subseteq> FIN"
        by (auto simp add: FIN_def)

      from z1 obtain t\<^sub>1 and t\<^sub>2
      where z_def: "z = (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> ((x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u)) \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)"
        (is "_ = ?z")
      and [simp]: "Valid x\<^sub>p' t\<^sub>1 y\<^sub>p" and [simp]: "Valid (x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u)) t\<^sub>2 y\<^sub>u"
        apply -
        apply (simp only: l_prod_assoc)
        apply (drule l_prod_elem_ex[OF `x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN`])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule l_prod_elem_ex[OF l1])
        apply (erule exE)+
        apply (erule conjE)+
        apply (drule shuffle_elem_ex)+
        apply (erule exE)+
        apply (erule conjE)+
        by (metis lappend_assoc singletonD)

      from `Valid x\<^sub>p' t\<^sub>1 y\<^sub>p` have [simp]: "lfinite t\<^sub>1"
        by (metis `lfinite x\<^sub>p'` `lfinite y\<^sub>p` lfinite_traj_from_Valid)

      let ?z' = "(x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1')) \<frown> alternate (x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t)) y\<^sub>t"

      have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (rule rg_lefts_rights)
        apply (subst lefts_append, simp)+
        apply (simp add: lappend_assoc[symmetric] `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p'' \<frown> x\<^sub>p'''`[symmetric] x'_def[symmetric])
        apply (metis IntE x'_in)
        apply (subst rights_append, simp)+
        apply simp
        by (metis IntE lappend_assoc lappend_code(1) lappend_code(2) y'_def y'_in)

      have "x\<^sub>p'' \<in> guar G\<^sub>1"
        by (metis `x\<^sub>p = x\<^sub>p' \<frown> x\<^sub>p'' \<frown> x\<^sub>p'''` `lfinite x\<^sub>p'` guar_lappend guar_split_first x\<^sub>p_guar)

      from failure_point2[OF `lfinite x\<^sub>p''` `x\<^sub>p'' \<in> guar G\<^sub>1` `(\<tau>\<^sub>0',\<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*`, of \<tau>\<^sub>0]
      obtain w \<gamma> \<gamma>' \<phi>
      where fp_all: "\<And>\<tau>\<^sub>1'. \<exists>\<phi>' w'. sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
      and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
        by auto

      from fp_all[of \<tau>\<^sub>1']
      obtain \<phi>' w'
      where fp: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
        by auto

      have [simp]: "lfinite w"
      proof -
        have "lfinite (sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'))"
          by simp
        hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
          by (simp only: fp)
        thus "lfinite w"
          by (metis lfinite_lappend)
      qed

      from fp_all[of \<tau>\<^sub>1'']
      obtain \<phi>\<^sub>2' w\<^sub>2'
      where fp2: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
        by auto

      have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
        apply (rule prime_rely)
        apply (simp only: rely''_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> w" in exI)
        apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
        apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
        apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate (x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t)) y\<^sub>t)" in exI)
        apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> ((x\<^sub>p''' \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u)) \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)" in exI)
        apply (intro conjI)
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply simp
        apply (metis fp lappend_code(1) lappend_code(2))
        apply (simp only: lappend_assoc lmap_lappend_distrib)
        apply (subst second_lappend_eq)
        apply simp
        apply (simp only: lappend_assoc[symmetric] sngify)
        apply (rule first_lappend_eq)
        apply (simp add: fp2[simplified])
        apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
        by simp

      show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
        apply (auto simp only: Rely_def)
        apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
        apply (simp only: z_def)
        apply (rule rely_link)
        by (rule z'_XY)
    qed
  next
    assume "rely' (R \<union> G\<^sub>2) x' x" and "y' = y"

    from `rely' (R \<union> G\<^sub>2) x' x` obtain x\<^sub>p \<sigma>\<^sub>0 \<sigma>\<^sub>0' \<sigma>\<^sub>1 \<sigma>\<^sub>1' \<sigma>\<^sub>1'' x\<^sub>t x\<^sub>u
    where x'_def: "x' = x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1') # x\<^sub>t)" and x_def: "x = x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1'') # x\<^sub>u)"
    and "(\<sigma>\<^sub>0',\<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*" and "env ((R \<union> G\<^sub>2)\<^sup>*) (x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # LNil))" and "lfinite x\<^sub>p"
      by (auto simp add: rely'_def)

    have x\<^sub>p_guar [simp]: "x\<^sub>p \<in> guar G\<^sub>1"
      using x'_in'
      apply (simp only: x'_def)
      by (erule guar_split_first)

    have x\<^sub>t_guar [simp]: "x\<^sub>t \<in> guar G\<^sub>1"
      using x'_in'
      by (simp add: x'_def guar_lappend[OF `lfinite x\<^sub>p`])

    have \<sigma>_guar [simp]: "(\<sigma>\<^sub>0,\<sigma>\<^sub>0') \<in> G\<^sub>1\<^sup>*"
      by (metis `lfinite x\<^sub>p` guar_LCons_eq guar_lappend x'_def x'_in')

    have \<sigma>_guar2 [simp]: "(\<sigma>\<^sub>1,\<sigma>\<^sub>1') \<in> G\<^sub>1\<^sup>*" using x'_in'
      by (simp add: x'_def guar_lappend[OF `lfinite x\<^sub>p`])

    from `z \<in> x \<sha> y`
    have "z \<in> (x\<^sub>p \<frown> ((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1'') # x\<^sub>u)) \<sha> y"
      by (simp only: x_def)

    from this and shuffle_lappend_left[of x\<^sub>p "((\<sigma>\<^sub>0,\<sigma>\<^sub>0') # (\<sigma>\<^sub>1,\<sigma>\<^sub>1'') # x\<^sub>u)" y]
    have z_lhs: "z \<in> \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> (((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u) \<sha> y\<^sub>u) |y\<^sub>p y\<^sub>u. y = y\<^sub>p \<frown> y\<^sub>u \<and> lfinite y\<^sub>p}" (is "_ \<in> ?lhs")
      by auto

    have "?lhs = \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> \<Union>{{lmap Inr y\<^sub>u'} \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))} \<cdot> (((\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u) \<sha> y\<^sub>u'') |y\<^sub>u' y\<^sub>u''. y\<^sub>u = y\<^sub>u' \<frown> y\<^sub>u'' \<and> lfinite y\<^sub>u'} | y\<^sub>p y\<^sub>u. y = y\<^sub>p \<frown> y\<^sub>u \<and> lfinite y\<^sub>p}"
      by (subst shuffle_cons_left) simp
    also have "... = \<Union>{\<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> {lmap Inr y\<^sub>u'} \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))} \<cdot> (((\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u) \<sha> y\<^sub>u'') |y\<^sub>u' y\<^sub>u''. y\<^sub>u = y\<^sub>u' \<frown> y\<^sub>u'' \<and> lfinite y\<^sub>u'} | y\<^sub>p y\<^sub>u. y = y\<^sub>p \<frown> y\<^sub>u \<and> lfinite y\<^sub>p}"
      apply (rule rg_lem5)
      apply (subst l_prod_inf_distl)
      apply (metis FIN_def `lfinite x\<^sub>p` lfinite_shuffle mem_Collect_eq subsetI)
      by (auto simp add: l_prod_assoc)
    also have "... \<subseteq> \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> {lmap Inr y\<^sub>u'} \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))} \<cdot> (((\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>u) \<sha> y\<^sub>u'') |y\<^sub>p  y\<^sub>u' y\<^sub>u''. y = y\<^sub>p \<frown> y\<^sub>u' \<frown> y\<^sub>u'' \<and> lfinite y\<^sub>p \<and> lfinite y\<^sub>u'}"
      apply auto
      by (metis lappend_assoc)
    also have "... \<subseteq> \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))} \<cdot> {lmap Inr y\<^sub>u'} \<cdot> {sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>u'') |y\<^sub>p  y\<^sub>u' y\<^sub>u''. y = y\<^sub>p \<frown> y\<^sub>u' \<frown> y\<^sub>u'' \<and> lfinite y\<^sub>p \<and> lfinite y\<^sub>u'}"
      sorry
    also have "... = \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>u' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>u'') |y\<^sub>p  y\<^sub>u' y\<^sub>u''. y = y\<^sub>p \<frown> y\<^sub>u' \<frown> y\<^sub>u'' \<and> lfinite y\<^sub>p \<and> lfinite y\<^sub>u'}"
      (is "_ = ?rhs")
      by (rule rg_lem11) (metis l_prod_assoc l_prod_singleton)
    finally have "?lhs \<subseteq> ?rhs" .

    from this and z_lhs have "z \<in> ?rhs"
      by blast

    then obtain y\<^sub>p' y\<^sub>p'' y\<^sub>p'''
     where z1: "z \<in> (x\<^sub>p \<sha> y\<^sub>p') \<cdot> {sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<cdot> (x\<^sub>u \<sha> y\<^sub>p''')"
      and "y =  y\<^sub>p' \<frown> y\<^sub>p''  \<frown> y\<^sub>p'''" and [simp]: "lfinite y\<^sub>p'" and [simp]: "lfinite y\<^sub>p''"
        by auto

    have "x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN"
      by auto (metis `lfinite x\<^sub>p`)
    have l1: "{sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1''))} \<subseteq> FIN"
      by (auto simp add: FIN_def)

    from z1 obtain t\<^sub>1 and t\<^sub>2
    where z_def: "z = (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1'')) \<frown> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>p''')"
      (is "_ = ?z")
    and [simp]: "Valid x\<^sub>p t\<^sub>1 y\<^sub>p'" and [simp]: "Valid x\<^sub>u t\<^sub>2 y\<^sub>p'''"
      apply -
      apply (simp only: l_prod_assoc)
      apply (drule l_prod_elem_ex[OF `x\<^sub>p \<sha> y\<^sub>p' \<subseteq> FIN`])
      apply (erule exE)+
      apply (erule conjE)+
      apply (drule l_prod_elem_ex[OF l1])
      apply (erule exE)+
      apply (erule conjE)+
      apply (drule shuffle_elem_ex)+
      apply (erule exE)+
      apply (erule conjE)+
      by (metis lappend_assoc singletonD)

    from `Valid x\<^sub>p t\<^sub>1 y\<^sub>p'` have [simp]: "lfinite t\<^sub>1"
      by (metis `lfinite x\<^sub>p` `lfinite y\<^sub>p'` lfinite_traj_from_Valid)

    let ?z' = "(x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> sng (Inl (\<sigma>\<^sub>0, \<sigma>\<^sub>0')) \<frown> lmap Inr y\<^sub>p'' \<frown> sng (Inl (\<sigma>\<^sub>1, \<sigma>\<^sub>1')) \<frown> alternate x\<^sub>t y\<^sub>p'''"

    have [simp]: "y\<^sub>p'' \<in> guar G\<^sub>2"
      by (metis `y = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''` `y' = y` `lfinite y\<^sub>p'` guar_lappend guar_split_first y'_in')

    have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
      apply (rule rg_lefts_rights)
      apply (subst lefts_append, simp)+
      apply (simp add: lappend_assoc x'_def[symmetric])
      apply (metis IntE x'_in)
      apply (subst rights_append, simp)+
      apply (simp add: lappend_assoc[symmetric])
      apply (simp add: `y = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''`[symmetric])
      apply (intro conjI)
      apply (metis IntE `y' = y` y'_in)
      apply (metis `y = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''` `y' = y` guar_split_first y'_in')
      by (metis `y = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''` `y' = y` `lfinite y\<^sub>p'` `lfinite y\<^sub>p''` guar_lappend lfinite_lappend y'_in')

    have "y\<^sub>p'' \<in> guar G\<^sub>2"
      by (metis `y = y\<^sub>p' \<frown> y\<^sub>p'' \<frown> y\<^sub>p'''` `y' = y` `lfinite y\<^sub>p'` guar_lappend guar_split_first y'_in')

    from failure_point2[OF `lfinite y\<^sub>p''` `y\<^sub>p'' \<in> guar G\<^sub>2` `(\<sigma>\<^sub>0',\<sigma>\<^sub>1) \<notin> (R \<union> G\<^sub>2)\<^sup>*`, of \<sigma>\<^sub>0]
    obtain w \<gamma> \<gamma>' \<phi>
    where fp_all: "\<And>\<sigma>\<^sub>1'. \<exists>\<phi>' w'. sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
    and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
    and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
      by auto

    from fp_all[of \<sigma>\<^sub>1']
    obtain \<phi>' w'
    where fp: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      by auto

    have [simp]: "lfinite w"
    proof -
      have "lfinite (sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'))"
        by simp
      hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
        by (simp only: fp)
      thus "lfinite w"
        by (metis lfinite_lappend)
    qed

    from fp_all[of \<sigma>\<^sub>1'']
    obtain \<phi>\<^sub>2' w\<^sub>2'
    where fp2: "sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0') \<frown> y\<^sub>p'' \<frown> sng (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
      by auto

    have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
      apply (rule prime_rely)
      apply (simp only: rely''_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p') \<frown> w" in exI)
      apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
      apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
      apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate x\<^sub>t y\<^sub>p''')" in exI)
      apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> (x\<^sub>u \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>p''')" in exI)
      apply (intro conjI)
      apply (simp only: lappend_assoc lmap_lappend_distrib)
      apply (subst second_lappend_eq)
      apply simp
      apply (simp only: lappend_assoc[symmetric] sngify)
      apply (rule first_lappend_eq)
      apply simp
      apply (metis fp lappend_code(1) lappend_code(2))
      apply (simp only: lappend_assoc lmap_lappend_distrib)
      apply (subst second_lappend_eq)
      apply simp
      apply (simp only: lappend_assoc[symmetric] sngify)
      apply (rule first_lappend_eq)
      apply (simp add: fp2[simplified])
      apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
      by simp

    show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
      apply (auto simp only: Rely_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
      apply (simp only: z_def)
      apply (rule rely_link)
      by (rule z'_XY)
  next
    assume "x' = x" and "rely' (R \<union> G\<^sub>1) y' y"

    from `rely' (R \<union> G\<^sub>1) y' y` obtain y\<^sub>p \<tau>\<^sub>0 \<tau>\<^sub>0' \<tau>\<^sub>1 \<tau>\<^sub>1' \<tau>\<^sub>1'' y\<^sub>t y\<^sub>u
    where y'_def: "y' = y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1') # y\<^sub>t)" and y_def: "y = y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1'') # y\<^sub>u)"
    and "(\<tau>\<^sub>0',\<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*" and "env ((R \<union> G\<^sub>1)\<^sup>*) (y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # LNil))" and "lfinite y\<^sub>p"
      by (auto simp add: rely'_def)

    have y\<^sub>p_guar [simp]: "y\<^sub>p \<in> guar G\<^sub>2"
      using y'_in'
      apply (simp only: y'_def)
      by (erule guar_split_first)

    have y\<^sub>t_guar [simp]: "y\<^sub>t \<in> guar G\<^sub>2"
      using y'_in'
      by (simp add: y'_def guar_lappend[OF `lfinite y\<^sub>p`])

    have \<tau>_guar [simp]: "(\<tau>\<^sub>0,\<tau>\<^sub>0') \<in> G\<^sub>2\<^sup>*"
      by (metis `lfinite y\<^sub>p` guar_LCons_eq guar_lappend y'_def y'_in')

    have \<tau>_guar2 [simp]: "(\<tau>\<^sub>1,\<tau>\<^sub>1') \<in> G\<^sub>2\<^sup>*" using y'_in'
      by (simp add: y'_def guar_lappend[OF `lfinite y\<^sub>p`])

    from `z \<in> x \<sha> y`
    have "z \<in> x \<sha> (y\<^sub>p \<frown> ((\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1'') # y\<^sub>u))"
      by (simp only: y_def)

    from this and shuffle_lappend_right[of y\<^sub>p x "(\<tau>\<^sub>0,\<tau>\<^sub>0') # (\<tau>\<^sub>1,\<tau>\<^sub>1'') # y\<^sub>u"]
    have z_lhs: "z \<in> \<Union>{(x\<^sub>p \<sha> y\<^sub>p) \<cdot> (x\<^sub>u \<sha> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>u)) |x\<^sub>p x\<^sub>u. x = x\<^sub>p \<frown> x\<^sub>u \<and> lfinite x\<^sub>p}" (is "_ \<in> ?lhs")
      by (smt `lfinite y\<^sub>p`)

    have "... \<subseteq> \<Union>{(x\<^sub>p' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>p''' \<sha> y\<^sub>u) |x\<^sub>p'  x\<^sub>p'' x\<^sub>p'''. x = x\<^sub>p' \<frown> x\<^sub>p'' \<frown> x\<^sub>p''' \<and> lfinite x\<^sub>p' \<and> lfinite x\<^sub>p''}"
      (is "_ \<subseteq> ?rhs")
      sorry

    from this and z_lhs have "z \<in> ?rhs"
      by blast

    then obtain x\<^sub>p' x\<^sub>p'' x\<^sub>p'''
    where z1: "z \<in> (x\<^sub>p' \<sha> y\<^sub>p) \<cdot> {sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<cdot> (x\<^sub>p''' \<sha> y\<^sub>u)"
    and "x =  x\<^sub>p' \<frown> x\<^sub>p''  \<frown> x\<^sub>p'''" and [simp]: "lfinite x\<^sub>p'" and [simp]: "lfinite x\<^sub>p''"
      by auto

    have "x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN"
      by auto (metis `lfinite y\<^sub>p`)
    have l1: "{sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1''))} \<subseteq> FIN"
      by (auto simp add: FIN_def)

    from z1 obtain t\<^sub>1 and t\<^sub>2
    where z_def: "z = (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1'')) \<frown> (x\<^sub>p''' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)"
      (is "_ = ?z")
    and [simp]: "Valid x\<^sub>p' t\<^sub>1 y\<^sub>p" and [simp]: "Valid x\<^sub>p''' t\<^sub>2 y\<^sub>u"
      apply -
      apply (simp only: l_prod_assoc)
      apply (drule l_prod_elem_ex[OF `x\<^sub>p' \<sha> y\<^sub>p \<subseteq> FIN`])
      apply (erule exE)+
      apply (erule conjE)+
      apply (drule l_prod_elem_ex[OF l1])
      apply (erule exE)+
      apply (erule conjE)+
      apply (drule shuffle_elem_ex)+
      apply (erule exE)+
      apply (erule conjE)+
      by (metis lappend_assoc singletonD)

    from `Valid x\<^sub>p' t\<^sub>1 y\<^sub>p` have [simp]: "lfinite t\<^sub>1"
      by (metis `lfinite x\<^sub>p'` `lfinite y\<^sub>p` lfinite_traj_from_Valid)

    let ?z' = "(x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> sng (Inr (\<tau>\<^sub>0, \<tau>\<^sub>0')) \<frown> lmap Inl x\<^sub>p'' \<frown> sng (Inr (\<tau>\<^sub>1, \<tau>\<^sub>1')) \<frown> alternate x\<^sub>p''' y\<^sub>t"

    have z'_XY: "lmap \<langle>id,id\<rangle> ?z' \<in> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
      apply (rule rg_lefts_rights)
      apply (subst lefts_append, simp)+
      apply (simp add: lappend_assoc[symmetric] `x = x\<^sub>p' \<frown> x\<^sub>p'' \<frown> x\<^sub>p'''`[symmetric])
      apply (metis IntE `x' = x` x'_in)
      apply (subst rights_append, simp)+
      apply simp
      by (metis IntE lappend_assoc lappend_code(1) lappend_code(2) y'_def y'_in)

    have "x\<^sub>p'' \<in> guar G\<^sub>1"
      by (metis `x = x\<^sub>p' \<frown> x\<^sub>p'' \<frown> x\<^sub>p'''` `x' = x` `lfinite x\<^sub>p'` guar_lappend guar_split_first x'_in')

    from failure_point2[OF `lfinite x\<^sub>p''` `x\<^sub>p'' \<in> guar G\<^sub>1` `(\<tau>\<^sub>0',\<tau>\<^sub>1) \<notin> (R \<union> G\<^sub>1)\<^sup>*`, of \<tau>\<^sub>0]
    obtain w \<gamma> \<gamma>' \<phi>
    where fp_all: "\<And>\<tau>\<^sub>1'. \<exists>\<phi>' w'. sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
    and "(\<gamma>', \<phi>) \<notin> R\<^sup>*"
    and "env (R\<^sup>*) (w \<frown> sng (\<gamma>, \<gamma>'))"
      by auto

    from fp_all[of \<tau>\<^sub>1']
    obtain \<phi>' w'
    where fp: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w')"
      by auto

    have [simp]: "lfinite w"
    proof -
      have "lfinite (sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'))"
        by simp
      hence "lfinite (w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>') # w'))"
        by (simp only: fp)
      thus "lfinite w"
        by (metis lfinite_lappend)
    qed

    from fp_all[of \<tau>\<^sub>1'']
    obtain \<phi>\<^sub>2' w\<^sub>2'
    where fp2: "sng (\<tau>\<^sub>0, \<tau>\<^sub>0') \<frown> x\<^sub>p'' \<frown> sng (\<tau>\<^sub>1, \<tau>\<^sub>1'') = w \<frown> ((\<gamma>, \<gamma>') # (\<phi>, \<phi>\<^sub>2') # w\<^sub>2')"
      by auto

    have rely_link: "rely R (lmap \<langle>id,id\<rangle> ?z') (lmap \<langle>id,id\<rangle> ?z)"
      apply (rule prime_rely)
      apply (simp only: rely''_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> (x\<^sub>p' \<triangleright> t\<^sub>1 \<triangleleft> y\<^sub>p) \<frown> w" in exI)
      apply (rule_tac x = \<gamma> in exI) apply (rule_tac x = \<gamma>' in exI)
      apply (rule_tac x = \<phi> in exI) apply (rule_tac x = \<phi>' in exI) apply (rule_tac x = \<phi>\<^sub>2' in exI)
      apply (rule_tac x = "w' \<frown> lmap \<langle>id,id\<rangle> (alternate x\<^sub>p''' y\<^sub>t)" in exI)
      apply (rule_tac x = "w\<^sub>2' \<frown> lmap \<langle>id,id\<rangle> (x\<^sub>p''' \<triangleright> t\<^sub>2 \<triangleleft> y\<^sub>u)" in exI)
      apply (intro conjI)
      apply (simp only: lappend_assoc lmap_lappend_distrib)
      apply (subst second_lappend_eq)
      apply simp
      apply (simp only: lappend_assoc[symmetric] sngify)
      apply (rule first_lappend_eq)
      apply simp
      apply (metis fp lappend_code(1) lappend_code(2))
      apply (simp only: lappend_assoc lmap_lappend_distrib)
      apply (subst second_lappend_eq)
      apply simp
      apply (simp only: lappend_assoc[symmetric] sngify)
      apply (rule first_lappend_eq)
      apply (simp add: fp2[simplified])
      apply (metis `(\<gamma>', \<phi>) \<notin> R\<^sup>*`)
       by simp

    show "lmap \<langle>id,id\<rangle> z \<in> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
      apply (auto simp only: Rely_def)
      apply (rule_tac x = "lmap \<langle>id,id\<rangle> ?z'" in bexI)
      apply (simp only: z_def)
      apply (rule rely_link)
      by (rule z'_XY)
  qed
qed

theorem rely_guarantee: "(R \<union> G\<^sub>2 \<rhd> X \<inter> guar G\<^sub>1) \<parallel> (R \<union> G\<^sub>1 \<rhd> Y \<inter> guar G\<^sub>2) \<subseteq> R \<rhd> (X \<inter> guar G\<^sub>1) \<parallel> (Y \<inter> guar G\<^sub>2)"
  apply (subst shuffle_def)
  apply (simp add: subset_iff Rely_continuous)
  apply auto
  by (metis rely_guarantee')

lemma [simp]: "UNIV \<rhd> X = X"
  by (simp add: Rely_def rely_def)

lemma rely_antitone: "G\<^sup>* \<subseteq> R\<^sup>* \<Longrightarrow> rely R x y \<Longrightarrow> rely G x y"
  apply (erule rev_mp) back
  apply (subst rely_def)
  apply (intro impI)
  apply (erule disjE)
  apply (simp only: rely_def_var)
  apply (intro disjI1)
  apply (rule rely_no_env)
  apply (simp add: rely''_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = z in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply (intro conjI)
  apply metis
  apply metis
  apply (metis contra_subsetD)
  apply simp
  by (simp add: rely_def)

lemma "R \<union> G \<rhd> X \<subseteq> R \<rhd> G \<rhd> X"
  apply (simp add: Rely_def)
  apply auto
  apply (rename_tac y x)
  apply (rule_tac x = y in exI)
  apply (simp add: rely_refl)
  apply (rule_tac x = x in bexI)
  apply (metis Un_upper1 rely_antitone rtrancl_mono sup_commute)
  by simp

definition test :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) lan" where
  "test P \<equiv> {sng (\<sigma>, \<sigma>) |\<sigma>. P \<sigma>}"

lemma tests_finite: "test P \<subseteq> FIN"
  by (auto simp add: test_def FIN_def)

lemma preimp_galois_2: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> X \<rightharpoondown> Z"
  by (drule preimp_galois[of X]) (simp add: galois_connection_def)

lemma preimp_galois_3: "X \<subseteq> FIN \<Longrightarrow> X \<cdot> (X \<rightharpoondown> Y) \<subseteq> Y"
  by (metis order_refl preimp_galois_2)

lemma test_preimp: "test P \<cdot> (test P \<rightharpoondown> X) \<subseteq> X"
  by (metis preimp_galois_3 tests_finite)

lemma test_in_guar: "test P \<subseteq> guar G"
  by (auto simp add: test_def)

lemma test_inter_guar [simp]: "test P \<inter> guar G = test P"
  by (metis inf.absorb2 inf_commute test_in_guar)

lemma l_prod_elem_cases: "z \<in> X \<cdot> Y \<Longrightarrow> (\<not> lfinite z \<and> z \<in> X) \<or> (\<exists>x y. lfinite x \<and> z = x \<frown> y \<and> x \<in> X \<and> y \<in> Y)"
  by (auto simp add: l_prod_def)

lemma Rely_zero [simp]: "(R \<rhd> {}) = {}"
  by (metis Env_Rely1 Env_Rely3 bot.extremum_uniqueI)

lemma non_empty_elemD: "Y \<noteq> {} \<Longrightarrow> \<exists>y. y \<in> Y"
  by auto

lemma rely_l_prod1: "Y \<noteq> {} \<Longrightarrow> \<not> lfinite t \<Longrightarrow> t \<in> R \<rhd> X \<Longrightarrow> t \<in> R \<rhd> X \<cdot> Y"
  apply (simp add: Rely_def)
  apply (drule non_empty_elemD)
  apply (erule bexE)
  apply (erule exE)
  apply (rule_tac x = "x \<frown> y" in bexI)
  prefer 2
  apply (simp add: lappend_in_l_prod)
  apply (simp add: rely_def)
  apply (erule disjE)
  apply (rule disjI1)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = z in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply simp
  apply (intro conjI)
  apply (rule_tac x = \<tau>' in exI)
  apply (rule_tac x = "x' \<frown> y" in exI)
  apply (simp add: sngify)
  apply (rule_tac x = \<tau>'' in exI)
  apply (rule_tac x = y' in exI)
  apply simp
  apply (rule disjI2)
  apply simp
  using lappend_inf by blast

lemma rely_l_prod2'':
  assumes "\<exists>x\<^sub>p \<sigma>\<^sub>0 \<sigma>\<^sub>0' \<sigma>\<^sub>1.
    (\<exists>\<sigma>\<^sub>1' x\<^sub>t. x = x\<^sub>p \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t)) \<and>
    (\<exists>\<sigma>\<^sub>1'' x\<^sub>t'. x' = x\<^sub>p \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>t')) \<and>
    (\<sigma>\<^sub>0', \<sigma>\<^sub>1) \<notin> R\<^sup>* \<and> lfinite x\<^sub>p \<and> env (R\<^sup>*) (x\<^sub>p \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))"
  and "\<exists>y\<^sub>p \<tau>\<^sub>0 \<tau>\<^sub>0' \<tau>\<^sub>1.
    (\<exists>\<tau>\<^sub>1' y\<^sub>t. y = y\<^sub>p \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t)) \<and>
    (\<exists>\<tau>\<^sub>1'' y\<^sub>t'. y' = y\<^sub>p \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>t')) \<and>
    (\<tau>\<^sub>0', \<tau>\<^sub>1) \<notin> R\<^sup>* \<and> lfinite y\<^sub>p \<and> env (R\<^sup>*) (y\<^sub>p \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0'))"
  shows "rely R (x \<frown> y) (x' \<frown> y')"
  using assms
  apply -
  apply (rule prime_rely)
  apply (simp add: rely''_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = x\<^sub>p in exI)
  apply (rule_tac x = \<sigma>\<^sub>0 in exI)
  apply (rule_tac x = \<sigma>\<^sub>0' in exI)
  apply (rule_tac x = \<sigma>\<^sub>1 in exI)
  apply (intro conjI)
  defer defer
  apply simp
  apply simp
  apply (rule_tac x = \<sigma>\<^sub>1' in exI)
  apply (rule_tac x = "x\<^sub>t \<frown> y" in exI)
  apply (simp add: lappend_assoc)
  apply (rule_tac x = \<sigma>\<^sub>1'' in exI)
  apply (rule_tac x = "x\<^sub>t' \<frown> y'" in exI)
  by (simp add: lappend_assoc)

lemma rely_l_prod2_1a'':
  assumes "\<exists>x\<^sub>p \<sigma>\<^sub>0 \<sigma>\<^sub>0' \<sigma>\<^sub>1.
    (\<exists>\<sigma>\<^sub>1' x\<^sub>t. x = x\<^sub>p \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1') # x\<^sub>t)) \<and>
    (\<exists>\<sigma>\<^sub>1'' x\<^sub>t'. x' = x\<^sub>p \<frown> ((\<sigma>\<^sub>0, \<sigma>\<^sub>0') # (\<sigma>\<^sub>1, \<sigma>\<^sub>1'') # x\<^sub>t')) \<and>
    (\<sigma>\<^sub>0', \<sigma>\<^sub>1) \<notin> R\<^sup>* \<and> lfinite x\<^sub>p \<and> env (R\<^sup>*) (x\<^sub>p \<frown> sng (\<sigma>\<^sub>0, \<sigma>\<^sub>0'))"
  shows "rely R (x \<frown> y) (x' \<frown> y)"
  using assms
  apply -
  apply (rule prime_rely)
  apply (simp add: rely''_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = x\<^sub>p in exI)
  apply (rule_tac x = \<sigma>\<^sub>0 in exI)
  apply (rule_tac x = \<sigma>\<^sub>0' in exI)
  apply (rule_tac x = \<sigma>\<^sub>1 in exI)
  apply (intro conjI)
  defer defer
  apply simp
  apply simp
  apply (rule_tac x = \<sigma>\<^sub>1' in exI)
  apply (rule_tac x = "x\<^sub>t \<frown> y" in exI)
  apply (simp add: lappend_assoc)
  apply (rule_tac x = \<sigma>\<^sub>1'' in exI)
  apply (rule_tac x = "x\<^sub>t' \<frown> y" in exI)
  by (simp add: lappend_assoc)

lemma rely_l_prod2_1b'':
  assumes "lfinite x"
  and "\<exists>y\<^sub>p \<tau>\<^sub>0 \<tau>\<^sub>0' \<tau>\<^sub>1.
    (\<exists>\<tau>\<^sub>1' y\<^sub>t. y = y\<^sub>p \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1') # y\<^sub>t)) \<and>
    (\<exists>\<tau>\<^sub>1'' y\<^sub>t'. y' = y\<^sub>p \<frown> ((\<tau>\<^sub>0, \<tau>\<^sub>0') # (\<tau>\<^sub>1, \<tau>\<^sub>1'') # y\<^sub>t')) \<and>
    (\<tau>\<^sub>0', \<tau>\<^sub>1) \<notin> R\<^sup>* \<and> lfinite y\<^sub>p \<and> env (R\<^sup>*) (y\<^sub>p \<frown> sng (\<tau>\<^sub>0, \<tau>\<^sub>0'))"
  shows "rely R (x \<frown> y) (x \<frown> y')"
  using assms
  apply -
  apply (rule prime_rely)
  apply (simp add: rely''_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = "x \<frown> y\<^sub>p" in exI)
  apply (rule_tac x = \<tau>\<^sub>0 in exI)
  apply (rule_tac x = \<tau>\<^sub>0' in exI)
  apply (rule_tac x = \<tau>\<^sub>1 in exI)
  apply (intro conjI)
  defer defer
  apply simp
  apply simp
  apply (rule_tac x = \<tau>\<^sub>1' in exI)
  apply (rule_tac x = y\<^sub>t in exI)
  apply (simp add: lappend_assoc)
  apply (rule_tac x = \<tau>\<^sub>1'' in exI)
  apply (rule_tac x = y\<^sub>t' in exI)
  by (simp add: lappend_assoc)

lemma rely_l_prod2: "lfinite x' \<Longrightarrow> rely R x x'\<Longrightarrow> rely R y y' \<Longrightarrow> rely R (x \<frown> y) (x' \<frown> y')"
  apply (erule rev_mp)+
  apply (subst rely_def)
  apply (subst rely_def)
  apply (intro impI)
  apply (erule disjE)+
  prefer 3
  apply (erule disjE)+
  apply simp_all
  prefer 2
  using rely_refl apply blast
  prefer 2
  apply (rule rely_l_prod2'')
  apply simp
  apply simp
  apply (simp add: rely_l_prod2_1a'')
  by (simp add: rely_l_prod2_1b'')

lemma rely_l_prod_nz: "Y \<noteq> {} \<Longrightarrow> (R \<rhd> X) \<cdot> (R \<rhd> Y) \<subseteq> R \<rhd> (X \<cdot> Y)"
  apply (simp add: subset_iff)
  apply (intro impI allI)
  apply (drule l_prod_elem_cases)
  apply (erule disjE)
  apply (erule conjE)+
  apply (rule rely_l_prod1)
  apply simp_all
  apply (erule exE)
  apply (erule conjE)+
  apply (erule exE)
  apply (erule conjE)+
  apply (simp add: Rely_def)
  apply (erule bexE)+
  apply (rename_tac t x' y' x y)
  apply (rule_tac x = "x \<frown> y" in bexI)
  apply (simp add: rely_l_prod2)
  using lappend_in_l_prod by blast

definition rely_abort :: "'a rel \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) llist \<Rightarrow> bool" where
  "rely_abort R x y \<equiv> (\<exists>z \<sigma> \<sigma>' \<tau> \<tau>' \<tau>'' x' y'. x = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x')
                                             \<and> y = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>'') # y')
                                             \<and> (\<sigma>',\<tau>) \<notin> (R\<^sup>*)
                                             \<and> lfinite z
                                             \<and> env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))
                                             \<and> (lfinite x' \<longleftrightarrow> lfinite y')) \<or> x = y"

lemma ra1: "rely_abort R x y \<Longrightarrow> lfinite x \<longleftrightarrow> lfinite y"
  apply (simp add: rely_abort_def)
  apply (erule disjE)+
  by auto

lemma ra2: "rely_abort R x y \<Longrightarrow> rely R x y"
  by (auto simp add: rely_abort_def rely_def) blast+

lemma ra3: "lfinite x \<longleftrightarrow> lfinite y \<Longrightarrow> rely R x y \<Longrightarrow> rely_abort R x y"
  apply (simp add: rely_def)
  apply (erule disjE)
  apply (simp add: rely_abort_def)
  apply (rule disjI1)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (rule_tac x = z in exI)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply (rule_tac x = \<tau>' in exI)
  apply (rule_tac x = \<tau>'' in exI)
  apply (rule_tac x = x' in exI)
  apply (intro conjI)
  apply simp
  apply (rule_tac x = y' in exI)
  apply simp
  apply simp
  by (simp add: rely_abort_def)

lemma rely_abort_prop: "rely_abort R x y \<longleftrightarrow> (rely R x y \<and> (lfinite x \<longleftrightarrow> lfinite y))"
  using ra1 ra2 ra3 by blast

definition Rely_abort :: "'a rel \<Rightarrow> ('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" (infixr "\<box>" 52) where
  "R \<box> X \<equiv> {y. \<exists>x\<in>X. rely_abort R x y}"

lemma mult_zero_inf: "X \<cdot> {} = {x\<in>X. \<not> lfinite x}"
  by (auto simp add: l_prod_def)

lemma "(R \<box> X) \<cdot> {} \<subseteq> R \<box> X \<cdot> {}"
  by (auto simp add: Rely_abort_def mult_zero_inf rely_abort_prop)

lemma rely_abort_leq: "R \<box> X \<subseteq> R \<rhd> X"
  by (auto simp add: Rely_abort_def Rely_def rely_abort_prop)

lemma rely_abort_l_prod: "(R \<box> X) \<cdot> (R \<box> Y) \<subseteq> R \<box> (X \<cdot> Y)"
  apply (auto simp add: subset_iff)
  apply (drule l_prod_elem_cases)
  apply (erule disjE)
  apply (simp add: Rely_abort_def)
  apply (metis (mono_tags, lifting) UnCI l_prod_def mem_Collect_eq ra1)
  apply (auto simp add: Rely_abort_def rely_abort_prop)
  apply (rule_tac x = "xa \<frown> xb" in bexI)
  using lfinite_lappend rely_l_prod2 apply blast
  using lappend_in_l_prod apply blast
  apply (rule_tac x = "xa \<frown> xb" in bexI)
  using lfinite_lappend rely_l_prod2 apply blast
  using lappend_in_l_prod apply blast
  done

lemma rely_l_prod: "(R \<rhd> X) \<cdot> (R \<rhd> Y) \<subseteq> R \<rhd> (X \<cdot> Y)"
  sorry (* FIXME *)

lemma Box1: "x \<in> R \<box> X \<Longrightarrow> lfinite x \<Longrightarrow> x \<in> R \<rhd> (X \<inter> FIN)"
  by (auto simp add: Rely_abort_def rely_abort_prop Rely_def FIN_def)

lemma Box2: "x \<in> R \<box> X \<Longrightarrow> \<not> lfinite x \<Longrightarrow> x \<in> R \<rhd> (X \<cdot> {})"
  by (auto simp add: Rely_abort_def rely_abort_prop Rely_def mult_zero_inf)

lemma Box3: "(lfinite x \<longrightarrow> x \<in> R \<rhd> (X \<inter> FIN)) \<and> (\<not> lfinite x \<longrightarrow> x \<in> R \<rhd> (X \<cdot> {})) \<Longrightarrow> x \<in> R \<box> X"
  apply (cases "lfinite x")
  apply auto
  by (auto simp add: Rely_abort_def rely_abort_prop Rely_def FIN_def mult_zero_inf)

lemma rely_abort_elem: "x \<in> R \<box> X \<longleftrightarrow> (lfinite x \<longrightarrow> x \<in> R \<rhd> (X \<inter> FIN)) \<and> (\<not> lfinite x \<longrightarrow> x \<in> R \<rhd> (X \<cdot> {}))"
  using Box1 Box2 Box3 by blast

lemma rely_l_prod_var: "(R \<rhd> X) \<cdot> Y \<subseteq> R \<rhd> (X \<cdot> Y)"
  by (metis Rely_ext l_prod_isor order_trans rely_l_prod)

lemma rely_l_prod_var2: "X \<cdot> (R \<rhd> Y) \<subseteq> R \<rhd> (X \<cdot> Y)"
  by (metis Rely_ext l_prod_isol order_trans rely_l_prod)

lemma prog_rely_iso: "X \<subseteq> Y \<Longrightarrow> R \<rhd> X \<subseteq> R \<rhd> Y"
  by (auto simp add: Rely_def)

lemma rely_idem: "R \<rhd> R \<rhd> X \<subseteq> R \<rhd> X"
  by (auto simp add: Rely_def) (metis rely_trans)

lemma inter_isol: "X \<subseteq> Y \<Longrightarrow> X \<inter> Z \<subseteq> Y \<inter> Z"
  by (metis inf_mono order_refl)

lemma FIN_FIN: "FIN \<cdot> FIN \<subseteq> FIN"
  by auto

end
