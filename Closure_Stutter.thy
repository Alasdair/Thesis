theory Closure_Stutter
  imports Language
begin

inductive_set stutter :: "('a \<times> 'a) llist \<Rightarrow> ('a \<times> 'a) lan" for xs where
  self [simp, intro!]: "xs \<in> stutter xs"
| stutter_left [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') zs) \<in> stutter xs"
| stutter_right [dest]: "ys \<frown> LCons (\<sigma>, \<sigma>') zs \<in> stutter xs \<Longrightarrow> ys \<frown> LCons (\<sigma>, \<sigma>') (LCons (\<sigma>', \<sigma>') zs) \<in> stutter xs"

definition Stutter :: "('a \<times> 'a) lan \<Rightarrow> ('a \<times> 'a) lan" ("_\<^sup>\<dagger>" [1000] 1000) where
  "X\<^sup>\<dagger> = \<Union>{stutter xs |xs. xs \<in> X}"

lemma env_stutter1: "lfinite xs \<Longrightarrow> env (R\<^sup>*) (xs \<frown> ((\<sigma>, \<sigma>') # xs')) \<Longrightarrow> env (R\<^sup>*) (xs \<frown> ((\<sigma>, \<sigma>) # (\<sigma>, \<sigma>') # xs'))"
proof (induct xs rule: lfinite_induct)
  case Nil thus ?case
    by (metis EqPair lappend_code(1) prod.sel(1) prod.sel(2) rtrancl.rtrancl_refl)
next
  case (Cons x xs)
  thus ?case
    apply simp
    apply (cases xs)
    by auto
qed

lemma env_stutter2: "lfinite xs \<Longrightarrow> env (R\<^sup>*) (xs \<frown> ((\<sigma>, \<sigma>') # xs')) \<Longrightarrow> env (R\<^sup>*) (xs \<frown> ((\<sigma>, \<sigma>') # (\<sigma>', \<sigma>') # xs'))"
proof (induct xs rule: lfinite_induct)
  case Nil thus ?case
    apply simp
    apply (rule EqPair)
    apply auto
    by (metis env.simps env_LConsD llist.inject lnull_def not_lnull_conv prod.sel(2))
next
  case (Cons x xs)
  thus ?case
    apply simp
    apply (cases xs)
    by auto
qed

lemma env_stuter3: "lfinite xs \<Longrightarrow> env R (xs \<frown> ((\<sigma>, \<sigma>) # (\<sigma>, \<sigma>') # xs')) \<Longrightarrow> env R (xs \<frown> ((\<sigma>, \<sigma>') # xs'))"
proof (induct xs rule: lfinite_induct)
  case Nil thus ?case
    by (metis env_tl lappend_code(1))
next
  case (Cons x xs)
  thus ?case
    apply simp
    apply (cases xs)
    by auto
qed

lemma env_stuter4: "lfinite xs \<Longrightarrow> env R (xs \<frown> ((\<sigma>, \<sigma>') # (\<sigma>', \<sigma>') # xs')) \<Longrightarrow> env R (xs \<frown> ((\<sigma>, \<sigma>') # xs'))"
proof (induct xs rule: lfinite_induct)
  case Nil thus ?case
    by (metis EqPair EqSingle env_LConsD env_tl lappend_code(1) neq_LNil_conv snd_conv)
next
  case (Cons x xs)
  thus ?case
    apply simp
    apply (cases xs)
    by auto
qed

lemma stutter_preserves_env1: "xs \<in> stutter ys \<Longrightarrow> env (R\<^sup>*) ys \<Longrightarrow> env (R\<^sup>*) xs"
proof (induct xs rule: stutter.induct)
  case self thus ?case by simp
next
  case (stutter_left xs \<sigma> \<sigma>' xs')
  thus ?case
    by (metis env_stutter1 lappend_inf)
next
  case (stutter_right xs \<sigma> \<sigma>' xs')
  thus ?case
    by (metis env_stutter2 lappend_inf)
qed

lemma stutter_preserves_env2: "xs \<in> stutter ys \<Longrightarrow> env (R\<^sup>*) xs \<Longrightarrow> env (R\<^sup>*) ys"
proof (induct xs rule: stutter.induct)
  case self thus ?case by simp
next
  case (stutter_left xs \<sigma> \<sigma>' xs')
  thus ?case
    by (metis env_stuter3 lappend_inf)
next
  case (stutter_right xs \<sigma> \<sigma>' xs')
  thus ?case
    by (metis env_stuter4 lappend_inf)
qed

lemma stutter_preserves_env: "xs \<in> stutter ys \<Longrightarrow> env (R\<^sup>*) xs \<longleftrightarrow> env (R\<^sup>*) ys"
  by (metis stutter_preserves_env1 stutter_preserves_env2)

lemma stutter_self_eq: "xs = ys \<Longrightarrow> xs \<in> stutter ys"
  by (metis stutter.self)

lemma stutter_trans: "xs \<in> stutter ys \<Longrightarrow> ys \<in> stutter zs \<Longrightarrow> xs \<in> stutter zs"
proof (induct xs rule: stutter.induct)
  case self
  thus ?case .
next
  case (stutter_left ys \<sigma> \<sigma>' zs)
  from stutter_left(2)[OF stutter_left(3)]
  show ?case
    by (rule stutter.stutter_left)
next
  case (stutter_right ys \<sigma> \<sigma>' zs)
  from stutter_right(2)[OF stutter_right(3)]
  show ?case
    by (rule stutter.stutter_right)
qed

lemma stutter_lappend: "xs \<in> stutter xs' \<Longrightarrow> ys \<in> stutter ys' \<Longrightarrow> (xs \<frown> ys) \<in> stutter (xs' \<frown> ys')"
proof (induct xs rule: stutter.induct)
  case self
  thus ?case
  proof (induct ys rule: stutter.induct)
    case self
    show ?case
      by (metis stutter.self)
  next
    case (stutter_left ws \<sigma> \<sigma>' vs)
    thus ?case
      by (metis lappend_assoc stutter.stutter_left)
  next
    case (stutter_right ws \<sigma> \<sigma>' vs)
    thus ?case
      by (metis lappend_assoc stutter.stutter_right)      
  qed
next
  case (stutter_left ws \<sigma> \<sigma>' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.stutter_left)
next
  case (stutter_right ws \<sigma> \<sigma>' vs)
  thus ?case
    by (metis lappend_assoc lappend_code(2) stutter.stutter_right)
qed

lemma Stutter_iso: "X \<subseteq> Y \<Longrightarrow> X\<^sup>\<dagger> \<subseteq> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_ext: "X \<subseteq> X\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_idem [simp]: "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> \<subseteq> X\<^sup>\<dagger>\<^sup>\<dagger>"
    by (metis Stutter_ext)
  thus "X\<^sup>\<dagger>\<^sup>\<dagger> = X\<^sup>\<dagger>"
    by (auto dest: stutter_trans simp add: Stutter_def)
qed

lemma Stutter_union [simp]: "(X \<union> Y)\<^sup>\<dagger> = X\<^sup>\<dagger> \<union> Y\<^sup>\<dagger>"
  by (auto simp add: Stutter_def)

lemma Stutter_continuous: "(\<Union>\<XX>)\<^sup>\<dagger> = \<Union>{X\<^sup>\<dagger> |X. X \<in> \<XX>}"
  by (auto simp add: Stutter_def)

lemma Stutter_meet [simp]: "(X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>)\<^sup>\<dagger> = X\<^sup>\<dagger> \<inter> Y\<^sup>\<dagger>"
  by (auto dest: stutter_trans simp add: Stutter_def)

lemma stutter_infinite [dest]: "ys \<in> stutter xs \<Longrightarrow> \<not> lfinite xs \<Longrightarrow> \<not> lfinite ys"
  by (induct ys rule: stutter.induct) auto

lemma stutter_l_prod: "stutter xs \<cdot> stutter ys \<subseteq> stutter (xs \<frown> ys)"
  apply (auto simp add: l_prod_def)
  apply (metis lappend_inf stutter.self stutter_lappend)
  by (metis stutter_lappend)

lemma stutter_LNil: "xs \<in> stutter LNil \<Longrightarrow> xs = LNil"
  apply (induct rule: stutter.induct)
  apply auto
  apply (metis lappend_eq_LNil_iff llist.distinct(1))
  by (metis lappend_eq_LNil_iff llist.distinct(1))

lemma Stutter_empty [simp]: "{}\<^sup>\<dagger> = {}"
  by (auto simp add: Stutter_def)

lemma llength_lefts_lappend1: "lfinite xs \<Longrightarrow> llength (\<ll> (xs \<frown> LCons (Inl y) ys)) = eSuc (llength (\<ll> (xs \<frown> ys)))"
proof (induct rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases x) simp_all
qed

lemma llength_lefts_lappend2: "lfinite xs \<Longrightarrow> llength (\<ll> (xs \<frown> LCons (Inr y) ys)) = llength (\<ll> (xs \<frown> ys))"
proof (induct rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases x) simp_all
qed

lemma llength_rights_lappend1: "lfinite xs \<Longrightarrow> llength (\<rr> (xs \<frown> LCons (Inr y) ys)) = eSuc (llength (\<rr> (xs \<frown> ys)))"
proof (induct rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases x) simp_all
qed

lemma llength_rights_lappend2: "lfinite xs \<Longrightarrow> llength (\<rr> (xs \<frown> LCons (Inl y) ys)) = llength (\<rr> (xs \<frown> ys))"
proof (induct rule: lfinite_induct)
  case Nil show ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases x) simp_all
qed

lemma traj_lappend [simp]: "traj (xs \<frown> ys) = traj xs \<frown> traj ys"
  by (auto simp add: traj_def lmap_lappend_distrib)

lemma [simp]: "traj (ltakeWhile is_right t) \<frown> traj (ldropWhile is_right t) = traj t"
  by (metis lappend_ltakeWhile_ldropWhile traj_lappend)

lemma ltakeWhile_traj_commute1: "traj (ltakeWhile is_right t) = ltakeWhile is_right (traj t)"
  by (simp add: ltakeWhile_lmap traj_def)

lemma ltakeWhile_traj_commute2: "traj (ltakeWhile is_left t) = ltakeWhile is_left (traj t)"
  by (simp add: ltakeWhile_lmap traj_def)

lemma ldropWhile_traj_commute1: "traj (ldropWhile is_right t) = ldropWhile is_right (traj t)"
  by (simp add: ldropWhile_lmap traj_def)

lemma ldropWhile_traj_commute2: "traj (ldropWhile is_left t) = ldropWhile is_left (traj t)"
  by (simp add: ldropWhile_lmap traj_def)

lemma llength_lefts_traj: "llength (\<ll> (traj t)) = llength (\<ll> t)"
  by (simp add: lefts_def traj_def lfilter_lmap)

lemma llength_rights_traj: "llength (\<rr> (traj t)) = llength (\<rr> t)"
  by (simp add: rights_def traj_def lfilter_lmap)

lemma [simp]: "llength (\<rr> (ltakeWhile is_right (traj t))) = llength (\<rr> (ltakeWhile is_right t))"
  by (metis llength_rights_traj ltakeWhile_traj_commute1)

lemma [simp]: "LCons x xs \<triangleright> LCons (Inl ()) t \<triangleleft> zs = LCons (Inl x) (xs \<triangleright> t \<triangleleft> zs)"
  by (metis interleave_left lhd_LCons ltl_simps(2))

lemma "x \<in> lset t \<Longrightarrow> (\<exists>t' t''. t = t' \<frown> LCons x t'')"
  by (metis split_llist_first)

lemma is_leftD: "is_left x \<Longrightarrow> (\<exists>x'. x = Inl x')"
  by (metis is_left.simps(2) swap.cases)

lemma ldropWhile_LNil_lappend: "lfinite xs \<Longrightarrow> ldropWhile is_right xs = LNil \<Longrightarrow> ldropWhile is_right (xs \<frown> ys) = ldropWhile is_right ys"
  apply (induct rule: lfinite_induct)
  apply simp_all
  by (metis ldropWhile_eq_LNil_iff llist.distinct(1) not_is_right)

lemma no_lefts_ldropWhile_is_right: "lfinite xs \<Longrightarrow> Inl () \<notin> lset xs \<Longrightarrow> ldropWhile is_right xs = LNil"
  apply (induct rule: lfinite_induct)
  apply simp_all
  by (metis (full_types) is_leftD not_is_left unit.exhaust)

lemma ldropWhile_is_right: "\<ll> t \<noteq> LNil \<Longrightarrow> ldropWhile is_right t = LCons (Inl ()) (ltl (ldropWhile is_right t))"
  sorry

lemma l_prod_fin: "(\<forall>xs\<in>X. lfinite xs) \<Longrightarrow> X \<cdot> Y = {xs \<frown> ys |xs ys. xs \<in> X \<and> ys \<in> Y}"
  by (auto simp add: l_prod_def)

lemma ltake_llength_rights:
  assumes "lfinite (ltakeWhile is_right t)"
  shows "lmap Inr (\<up> (llength (ltakeWhile is_right t)) (\<rr> t)) = \<up> (llength (ltakeWhile is_right t)) t"
proof -
  {
    fix x xs and t :: "('a + 'b) llist"
    have "LCons x xs = ltakeWhile is_right t \<Longrightarrow> xs = ltakeWhile is_right (ltl t)"
      by (metis llist.distinct(1) ltakeWhile_eq_LNil_iff ltl_ltakeWhile ltl_simps(2))
  } note helper = this

  {
    fix xs
    have "lfinite xs \<Longrightarrow> xs = ltakeWhile is_right t \<Longrightarrow> lmap Inr (\<up> (llength xs) (\<rr> t)) = \<up> (llength xs) t"
    proof (induct xs arbitrary: t rule: lfinite_induct)
      case (Nil t)
      thus ?case
        by simp
    next
      case (Cons x xs t)
      then obtain r and t' where [simp]: "t = LCons (Inr r) t'"
        by (metis is_right.simps(2) llist.discI ltakeWhile_LCons ltakeWhile_LNil sumlist_cases)
      hence [simp]: "ltl t = t'"
        by auto
      thus ?case
        by (simp add: Cons(2)[OF helper[OF Cons(3)], simplified])
    qed
  }
  from this and assms show ?thesis
    by metis
qed

lemma lefts_ldrop_rights: "\<ll> (\<down> (llength (ltakeWhile is_right t)) t) = \<ll> t"
  by (metis lappend_code(1) lappend_inf lappend_ltakeWhile_ldropWhile ldropWhile_eq_ldrop ldrop_eq_LNil lefts_LNil lefts_append lefts_ltake_right order_refl)

lemma lefts_ldrop_rights_var: "\<ll> t = LCons x (xs \<frown> LCons (\<sigma>, \<sigma>') ys) \<Longrightarrow> \<ll> (ltl (\<down> (llength (ltakeWhile is_right t)) t)) = xs \<frown> LCons (\<sigma>, \<sigma>') ys"
proof -
  assume "\<ll> t = LCons x (xs \<frown> LCons (\<sigma>, \<sigma>') ys)" 
  moreover have "\<ll> (ltl (\<down> (llength (ltakeWhile is_right t)) t)) = ltl (\<ll> (\<down> (llength (ltakeWhile is_right t)) t))"
    apply (simp add: lefts_def)
    apply (subst ltl_lfilter)
    by (metis Not_is_left ldropWhile_eq_ldrop lefts_def_var lefts_ldrop_rights ltl_lfilter ltl_lmap)
  ultimately show ?thesis
    by (metis lefts_ldrop_rights ltl_simps(2))
qed

lemma lfilter_is_right_ltl_ltakeWhile:
  assumes "lfinite (ltakeWhile is_right t)"
  shows "lfilter is_right (ltl (\<down> (llength (ltakeWhile is_right t)) t)) = \<down> (llength (ltakeWhile is_right t)) (lfilter is_right t)" 
proof -
  {
    fix x xs and t :: "('a + 'b) llist"
    have "LCons x xs = ltakeWhile is_right t \<Longrightarrow> xs = ltakeWhile is_right (ltl t)"
      by (metis llist.distinct(1) ltakeWhile_eq_LNil_iff ltl_ltakeWhile ltl_simps(2))
  } note helper = this

  {
    fix xs
    have "lfinite xs \<Longrightarrow> xs = ltakeWhile is_right t \<Longrightarrow> lfilter is_right (ltl (\<down> (llength xs) t)) = \<down> (llength xs) (lfilter is_right t)"
    proof (induct arbitrary: t rule: lfinite_induct)
      case (Nil t)
      thus ?case
        by simp (metis lfilter_LCons llist.sel_exhaust ltakeWhile_eq_LNil_iff ltl_simps(1))
    next
      case (Cons x xs t)
      then obtain r and t' where [simp]: "t = LCons (Inr r) t'"
        by (metis is_right.simps(2) llist.discI ltakeWhile_LCons ltakeWhile_LNil sumlist_cases)
      hence [simp]: "ltl t = t'"
        by auto
      thus ?case
        by (simp add: Cons(2)[OF helper[OF Cons(3)], simplified])
    qed
  }
  from this and assms show ?thesis
    by metis
qed

lemmas ldrop_to_ldropWhile[simp] = ldropWhile_eq_ldrop[symmetric]

lemma "xs \<noteq> LNil \<Longrightarrow> xs = LCons (lhd xs) (ltl xs)"
  by (metis llist.collapse)

lemma lmap_unl_to_Inl [simp]: "lmap unl (lfilter is_left xs) = ys \<longleftrightarrow> lfilter is_left xs = lmap Inl ys"
  apply (rule antisym)
  apply auto
  apply (subst lmap_lfilter_eq[where g = id])
  apply (metis DEADID.map_id is_leftD unl.simps(1))
  by simp

lemma drop_rights: "\<ll> t = LCons x xs \<Longrightarrow> ldropWhile is_right t = LCons (Inl x) (ltl (ldropWhile is_right t))"
  apply (simp add: lefts_def)
  apply (subgoal_tac "lhd (lfilter is_left t) = Inl x")
  apply simp
  apply (subst llist.collapse[symmetric])
  apply simp_all
  apply (rule_tac x = "Inl x" in bexI)
  apply auto
  apply (metis (erased, lifting) lset_intros(1) lset_lfilter mem_Collect_eq)
  by (metis Not_is_left lhd_LCons lhd_lfilter)  

lemma drop_rights_var: "\<ll> t = LCons x xs \<Longrightarrow> \<down> (llength (ltakeWhile is_right t)) t = LCons (Inl x) (ltl (\<down> (llength (ltakeWhile is_right t)) t))"
  apply simp
  by (metis drop_rights)

lemma singleton_lappend_Inr: "lfinite xs \<Longrightarrow> t \<in> {lmap Inr xs} \<cdot> ys \<Longrightarrow> \<down> (llength xs) t \<in> ys"
  apply (induct arbitrary: t rule: lfinite_induct)
  apply simp
  apply (auto simp add: l_prod_def)
  by metis

lemma ldrop_eq_LCons: "\<down> n xs = LCons y ys \<Longrightarrow> \<down> (eSuc n) xs = ys"
  by (metis ldrop_ltl ltl_ldrop ltl_simps(2))

lemma [simp]: "llength (\<rr> (ltakeWhile is_right t)) = llength (ltakeWhile is_right t)"
  by (auto simp add: rights_def) (metis lfilter_empty_conv lfilter_left_right lset_ltakeWhileD not_is_right)

lemma [simp]: "ltakeWhile is_right (traj t) = traj (ltakeWhile is_right t)"
  by (metis ltakeWhile_traj_commute1)

lemma [simp]: "(LNil \<triangleright> traj (ltakeWhile is_right t) \<triangleleft> \<up> (llength (ltakeWhile is_right t)) ys) = lmap Inr (\<up> (llength (ltakeWhile is_right t)) ys)"
  sorry

lemma [simp]: "lfinite (ltakeWhile is_right xs) \<Longrightarrow> llength (\<ll> (traj (ltakeWhile is_right xs) \<frown> ys)) = llength (\<ll> ys)"
  sorry

lemma length_ge_0_lfinite_ltakeWhile: "0 < llength (\<ll> xs) \<Longrightarrow> lfinite (ltakeWhile is_right xs)"
  by (simp add: lefts_def) (metis lfinite_ltakeWhile not_is_right)

lemma length_ge_e0_lfinite_ltakeWhile: "enat 0 < llength (\<ll> xs) \<Longrightarrow> lfinite (ltakeWhile is_right xs)"
  by (simp add: lefts_def enat_0) (metis lfinite_ltakeWhile not_is_right)

(*
lemma "enat n < llength (\<ll> xs) \<Longrightarrow> llength (\<ll> (linsertLeft_nat n x xs)) = eSuc (llength (\<ll> xs))"
proof (induct n)
  case 0
  hence "llength (\<ll> (ltakeWhile is_right xs \<frown> LCons (Inl x) (ldropWhile is_right xs))) = llength (\<ll> (LCons (Inl x) (ltakeWhile is_right xs \<frown> ldropWhile is_right xs)))"
    by (metis lefts_LConsl length_ge_0_lfinite_ltakeWhile llength_LCons llength_lefts_lappend1 zero_enat_def)
  also have "... = eSuc (llength (\<ll> xs))"
    by (metis lappend_ltakeWhile_ldropWhile lefts_LConsl llength_LCons)
  finally show ?case
    by simp
next

*)

lemma stutter_left_in_left:
  assumes "t \<in> (xs \<frown> LCons (\<sigma>,\<sigma>') ys) \<sha> zs"
  shows "lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>) (LCons (\<sigma>,\<sigma>') ys) \<triangleright> linsertLeft (llength xs) () (traj t) \<triangleleft> zs) \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>,\<sigma>') ys \<triangleright> traj t \<triangleleft> zs))"
proof (cases "llength xs")
  assume "llength xs = \<infinity>"
  from this and assms
  show ?thesis
    by (auto intro: sumlist_cases[of t] simp add: traj_def interleave_left interleave_right)
next
  fix n
  assume "llength xs = enat n"
  hence xs_fin: "lfinite xs"
    by (metis lfinite_conv_llength_enat)
  from this and assms
  show ?thesis
  proof (induct xs arbitrary: t zs rule: lfinite_induct)
    case (Nil t zs)

    have t_lefts [simp]: "\<ll> t = LCons (\<sigma>, \<sigma>') ys"
      by (metis (lifting, full_types) Nil.prems lappend_code(1) mem_Collect_eq tshuffle_words_def)

    have t_rights[simp]: "\<rr> t = zs"
      by (metis (lifting, full_types) Nil.prems mem_Collect_eq tshuffle_words_def)

    have lem: "ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))"
      apply (rule ldropWhile_is_right)
      by (metis co.enat.discI llength_LCons llength_LNil llength_lefts_traj t_lefts)

    have "lfinite (ltakeWhile is_right (traj t))"
      apply (subst lfinite_ltakeWhile)
      apply (intro disjI2)
      apply auto
      apply (rule_tac x = "Inl ()" in bexI)
      apply simp_all
      by (metis (full_types) in_lset_ldropWhileD lem lset_intros(1))

    show ?case
      apply (simp add: enat_0[symmetric])
      apply (subst interleave_append_llength)
      apply (metis `lfinite (ltakeWhile is_right (traj t))` lappend_code(1) ldrop_to_ldropWhile lefts_LConsl lefts_append lefts_ldrop_rights lefts_ltake_right llength_LCons llength_lefts_traj ltakeWhile_traj_commute1 t_lefts)
      apply (metis `lfinite (ltakeWhile is_right (traj t))` lappend_ltakeWhile_ldropWhile llength_rights_lappend2 llength_rights_traj ltakeWhile_traj_commute1 t_rights)
      apply (simp add: llength_rights_lappend2[OF `lfinite (ltakeWhile is_right (traj t))`])
      apply simp
      apply (subst lappend_ltakeWhile_ldropWhile[symmetric, of t is_right]) back back back
      apply (simp only: traj_lappend)
      apply (subst interleave_append_llength)
      apply simp
      apply simp
      apply simp
      apply (subst lmap_lappend_distrib)
      apply (subst lmap_lappend_distrib)
      apply (rule stutter_lappend)
      apply (rule stutter_self_eq)
      apply (metis ltakeWhile_traj_commute1)
      apply (subst lem)
      apply (subst ldropWhile_traj_commute1)
      apply (subst lem) back
      apply simp
      apply (rule stutter_left[where ys = LNil, simplified])
      by (rule stutter.self)
  next
    case (Cons x xs t zs)

    have [simp]: "lfinite (ltakeWhile is_right t)"
      sorry

    have "t \<in> LCons x (xs \<frown> LCons (\<sigma>, \<sigma>') ys) \<sha> zs"
      by (metis Cons.prems lappend_code(2))
    hence "t \<in> {lmap Inr (\<up> (llength (ltakeWhile is_right t)) zs)} \<cdot> (LCons (Inl x) ` ((xs \<frown> LCons (\<sigma>, \<sigma>') ys) \<sha> (\<down> (llength (ltakeWhile is_right t)) zs)))"
      apply (auto simp add: tshuffle_words_def image_def)
      apply (subst l_prod_fin)
      apply simp
      apply (intro disjI2)
      apply (metis (hide_lams, no_types) lappend_inf lappend_ltakeWhile_ldropWhile lefts_ltake_right lfinite_llength_enat neq_LNil_conv)
      apply auto
      apply (subst ltake_llength_rights)
      apply (metis lappend_inf lappend_ltakeWhile_ldropWhile lefts_ltake_right neq_LNil_conv)
      apply (rule_tac x = "\<down> (llength (ltakeWhile is_right t)) t" in exI)
      apply (intro conjI)
      apply (metis lappend_ltake_ldrop)
      apply (rule_tac x = "ltl (\<down> (llength (ltakeWhile is_right t)) t)" in exI)
      apply (intro conjI)
      apply (metis lefts_ldrop_rights_var)
      apply (simp del: ldrop_to_ldropWhile add: rights_def)
      apply (rule arg_cong) back
      apply (rule lfilter_is_right_ltl_ltakeWhile)
      apply (metis lappend_inf lappend_ltakeWhile_ldropWhile lefts_ltake_right neq_LNil_conv)
      by (metis drop_rights_var)
    moreover from Cons(3) have "lfinite (\<up> (llength (ltakeWhile is_right t)) zs)"
      by (auto simp add: tshuffle_words_def) (metis lefts_ltake_right llength_ltakeWhile_eq_infinity neq_LNil_conv)
    ultimately obtain zs' zs''
    where "t \<in> {lmap Inr zs'} \<cdot> (LCons (Inl x) ` ((xs \<frown> LCons (\<sigma>, \<sigma>') ys) \<sha> zs''))"
    and zs'_def: "zs' = \<up> (llength (ltakeWhile is_right t)) zs"
    and zs''_def: "zs'' = \<down> (llength (ltakeWhile is_right t)) zs"
    and "lfinite zs'"
      by auto
    hence "\<down> (eSuc (llength zs')) t \<in> (xs \<frown> LCons (\<sigma>, \<sigma>') ys) \<sha> zs''"
      apply -
      apply (drule singleton_lappend_Inr[where xs = zs', OF `lfinite zs'`])
      apply (auto simp add: image_def)
      apply (metis (mono_tags) zs''_def ldrop_eq_LCons)
      by (metis (full_types) ldrop_eq_LCons)
    from Cons(2)[OF this]
    have "lmap \<langle>id,id\<rangle> (xs \<frown>  LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys) \<triangleright> linsertLeft (llength xs) () (traj (\<down> (eSuc (llength zs')) t)) \<triangleleft> zs'')
          \<in> stutter (lmap \<langle>id,id\<rangle> (xs \<frown> LCons (\<sigma>, \<sigma>') ys \<triangleright> traj (\<down> (eSuc (llength zs')) t) \<triangleleft> zs''))"
      by simp
    have "lmap \<langle>id,id\<rangle> (LCons x xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys) \<triangleright> linsertLeft (llength (LCons x xs)) () (traj t) \<triangleleft> zs)
          = lmap \<langle>id,id\<rangle> (LCons x (xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys)) \<triangleright> linsertLeft (llength (LCons x xs)) () (traj t) \<triangleleft> zs)"
      by (metis lappend_code(2))
    also have "... = lmap \<langle>id,id\<rangle> (LCons x (xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys)) \<triangleright> linsertLeft (eSuc (llength xs)) () (traj t) \<triangleleft> zs)"
      by simp
    also have "... = lmap \<langle>id,id\<rangle> (LCons x (xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys)) \<triangleright> ltakeWhile is_right (traj t) \<frown> LCons (Inl ()) (linsertLeft (llength xs) () (ltl (ldropWhile is_right (traj t)))) \<triangleleft> zs)"
      apply (simp add: linsertLeft_eSuc llist_Case_def)
      apply (subgoal_tac "ldropWhile is_right (traj t) = LCons (Inl ()) (ltl (ldropWhile is_right (traj t)))")
      apply (erule ssubst)
      apply simp
      sorry
    also have "... = lmap \<langle>id,id\<rangle> (lmap Inr (\<up> (llength (ltakeWhile is_right t)) zs) \<frown> LCons (Inl x) (xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys) \<triangleright> linsertLeft (llength xs) () (ltl (ldropWhile is_right (traj t))) \<triangleleft> \<down> (llength (\<rr> (ltakeWhile is_right t))) zs))"
      apply (subst interleave_append_llength)
      apply simp_all
      sorry
      

    show "lmap \<langle>id,id\<rangle> (LCons x xs \<frown> LCons (\<sigma>, \<sigma>) (LCons (\<sigma>, \<sigma>') ys) \<triangleright> linsertLeft (llength (LCons x xs)) () (traj t) \<triangleleft> zs)
          \<in> stutter (lmap \<langle>id,id\<rangle> (LCons x xs \<frown> LCons (\<sigma>, \<sigma>') ys \<triangleright> traj t \<triangleleft> zs))"
      sorry
  qed
qed

(*
lemma shuffle_stutter1: "X\<^sup>\<dagger> \<parallel> Y \<subseteq> (X \<parallel> Y)\<^sup>\<dagger>"
proof -
  have "X\<^sup>\<dagger> \<parallel> Y = \<Union>(stutter ` X) \<parallel> Y"
    by (rule arg_cong, auto simp add: Stutter_def image_def)
  also have "... = \<Union>{stutter xs \<parallel> Y |xs. xs \<in> X}"
    by (subst trans[OF shuffle_comm shuffle_inf_dist], subst shuffle_comm, auto)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs' ys. xs' \<in> stutter xs \<and> ys \<in> Y} |xs. xs \<in> X}"
    by (simp add: shuffle_def)
  also have "... = \<Union>{\<Union>{lmap \<langle>id,id\<rangle> ` (xs' \<sha> ys) |xs'. xs' \<in> stutter xs} |xs ys. xs \<in> X \<and> ys \<in> Y}"
    by blast
  also have "... \<subseteq> \<Union>{(lmap \<langle>id,id\<rangle> ` (xs \<sha> ys))\<^sup>\<dagger> |xs ys. xs \<in> X \<and> ys \<in> Y}"
    sorry
*)

end