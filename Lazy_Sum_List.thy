theory Lazy_Sum_List
  imports "$AFP/Coinductive/Coinductive" Sum_Type
begin

section {* Lazy Sum Lists *}

notation case_sum ("\<langle>_,_\<rangle>" [0,0] 1000)

primrec is_left :: "('a + 'b) \<Rightarrow> bool" where
  "is_left (Inl x) = True"
| "is_left (Inr x) = False"

primrec is_right :: "('a + 'b) \<Rightarrow> bool" where
  "is_right (Inr x) = True"
| "is_right (Inl x) = False"

primrec unl :: "('a, 'b) sum \<Rightarrow> 'a" where
  "unl (Inl x) = x"
| "unl (Inr x) = undefined"

primrec unr :: "('a, 'b) sum \<Rightarrow> 'b" where
  "unr (Inr x) = x"
| "unr (Inl x) = undefined"

lemma not_is_left [simp]: "\<not> is_left x \<longleftrightarrow> is_right x"
  by (cases x) auto

lemma Not_is_left: "is_right = Not \<circ> is_left"
  by (simp add: o_def)

lemma not_is_right [simp]: "\<not> is_right x \<longleftrightarrow> is_left x"
  by (cases x) auto

lemma Not_is_right: "is_left = Not \<circ> is_right"
  by (simp add: o_def)

definition lefts :: "('a + 'b) llist \<Rightarrow> 'a llist" ("\<ll>") where
  "lefts = lmap unl \<circ> lfilter is_left"

definition rights :: "('a + 'b) llist \<Rightarrow> 'b llist" ("\<rr>") where
  "rights = lmap unr \<circ> lfilter is_right"

lemma [dest!]: "xs \<noteq> LNil \<Longrightarrow> \<exists>y ys. xs = LCons y ys"
  by (metis llist.exhaust)

lemma all_rights [simp]: "lfilter is_right (lmap Inr xs) = lmap Inr xs"
  by (simp add: lfilter_lmap)

lemma all_lefts [simp]: "lfilter is_left (lmap Inl xs) = lmap Inl xs"
  by (simp add: lfilter_lmap)

lemma lmap2_id: "(\<And>x. f (g x) = x) \<Longrightarrow> lmap f (lmap g xs) = xs"
  by (simp add: llist.map_comp)

lemma rights_mapr [simp]: "\<rr> (lmap Inr xs) = xs"
  by (auto simp add: rights_def, rule lmap2_id, simp)

lemma lefts_mapl [simp]: "\<ll> (lmap Inl xs) = xs"
  by (auto simp add: lefts_def, rule lmap2_id, simp)

lemma rights_LConsr [simp]: "\<rr> (LCons (Inr x) xs) = LCons x (\<rr> xs)"
  by (auto simp add: rights_def)

lemma rights_LConsl [simp]: "\<rr> (LCons (Inl x) xs) = \<rr> xs"
  by (auto simp add: rights_def)

lemma lefts_LConsl [simp]: "\<ll> (LCons (Inl x) xs) = LCons x (\<ll> xs)"
  by (auto simp add: lefts_def)

lemma lefts_LConsr [simp]: "\<ll> (LCons (Inr x) xs) = \<ll> xs"
  by (auto simp add: lefts_def)

lemma rights_LNil [simp]: "\<rr> LNil = LNil"
  by (auto simp add: rights_def)

lemma lefts_LNil [simp]: "\<ll> LNil = LNil"
  by (auto simp add: lefts_def)

fun swap :: "('a + 'b) \<Rightarrow> ('b, 'a) sum" where
  "swap (Inl x) = Inr x"
| "swap (Inr x) = Inl x"

definition fair :: "('a + 'b) llist \<Rightarrow> bool" where
  "fair l \<equiv> (\<exists>n. is_right (lnth l n)) \<and> (\<exists>n. is_left (lnth l n))
          \<and> (\<forall>n. is_right (lnth l n) \<longrightarrow> (\<exists>m>n. is_right (lnth l m)))
          \<and> (\<forall>n. is_left (lnth l n) \<longrightarrow> (\<exists>m>n. is_left (lnth l m)))
          \<and> (\<not> lfinite l)"

lemma fair_right_ex: "fair l \<Longrightarrow> \<exists>n. is_right (lnth l n)"
  by (simp add: fair_def)

lemma fair_left_ex: "fair l \<Longrightarrow> \<exists>n. is_left (lnth l n)"
  by (simp add: fair_def)

lemma fair_morer: "fair l \<Longrightarrow> is_right (lnth l n) \<Longrightarrow> \<exists>m>n. is_right (lnth l m)"
  by (simp add: fair_def)

lemma fair_morel: "fair l \<Longrightarrow> is_left (lnth l n) \<Longrightarrow> \<exists>m>n. is_left (lnth l m)"
  by (simp add: fair_def)

definition first_left :: "('a + 'b) llist \<Rightarrow> 'a" where
  "first_left = Sum_Type.Suml id \<circ> lhd \<circ> ldropWhile is_right"

lemma lefts_append: "lfinite xs \<Longrightarrow> \<ll> (lappend xs ys) = lappend (\<ll> xs) (\<ll> ys)"
  apply (auto simp add: lefts_def)
  by (metis lmap_lappend_distrib)

lemma rights_append: "lfinite xs \<Longrightarrow> \<rr> (lappend xs ys) = lappend (\<rr> xs) (\<rr> ys)"
  apply (auto simp add: rights_def)
  by (metis lmap_lappend_distrib)

declare in_lset_conv_lnth[iff]
declare lfinite_conv_llength_enat[iff]

lemma lnth_in_lset: "\<not> lfinite xs \<Longrightarrow> lnth xs n \<in> lset xs"
  by auto

lemma fair_ltakel: "fair xs \<Longrightarrow> lfinite (ltakeWhile is_left xs)"
  apply (subst lfinite_ltakeWhile)
  apply (rule disjI2)
  apply (auto simp add: fair_def)
  apply (rule_tac x = "lnth xs n" in bexI)
  apply assumption
  by (metis llength_eq_infty_conv_lfinite lnth_in_lset)

lemma fair_ltaker: "fair xs \<Longrightarrow> lfinite (ltakeWhile is_right xs)"
  apply (subst lfinite_ltakeWhile)
  apply (rule disjI2)
  apply (auto simp add: fair_def)
  apply (rule_tac x = "lnth xs na" in bexI)
  apply assumption
  by (metis llength_eq_infty_conv_lfinite lnth_in_lset)

lemma lefts_Nil: "lfinite xs \<Longrightarrow> \<forall>x\<in>lset xs. is_right x \<Longrightarrow> \<ll> xs = LNil"
  by (auto simp add: lefts_def)

lemma lefts_ltaker: "fair xs \<Longrightarrow> \<ll> (ltakeWhile is_right xs) = LNil"
  apply (rule lefts_Nil)
  apply (erule fair_ltaker)
  by (metis lset_ltakeWhileD)

lemma lefts_ldropr:
  assumes xs_fair: "fair xs" shows "\<ll> xs = \<ll> (ldropWhile is_right xs)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<ll> (lappend (ltakeWhile is_right xs) (ldropWhile is_right xs))"
    by (metis lappend_ltakeWhile_ldropWhile)
  also have "... = lappend (\<ll> (ltakeWhile is_right xs)) (\<ll> (ldropWhile is_right xs))"
    by (metis fair_ltaker lefts_append xs_fair)
  also have "... = lappend LNil (\<ll> (ldropWhile is_right xs))"
    by (metis lefts_ltaker xs_fair)
  also have "... = ?rhs"
    by (metis lappend_code(1))
  finally show ?thesis .
qed

lemma fairI:
  assumes "\<exists>n. is_right (lnth l n)" and "\<exists>n. is_left (lnth l n)"
  and "\<And>n. is_right (lnth l n) \<Longrightarrow> \<exists>m>n. is_right (lnth l m)"
  and "\<And>n. is_left (lnth l n) \<Longrightarrow> \<exists>m>n. is_left (lnth l m)"
  and "\<not> lfinite l"
  shows "fair l"
  by (insert assms) (simp add: fair_def)

lemma fair_non_empty: "fair l \<Longrightarrow> \<not> lfinite l"
  by (auto simp add: fair_def)

lemma [simp]: "is_right (swap x) = is_left x"
  by (cases x) auto

lemma [simp]: "is_left (swap x) = is_right x"
  by (cases x) auto

lemma is_right_swap [simp]: "is_right \<circ> swap = is_left"
  by (rule ext) (simp  add: o_def)

lemma is_left_swap [simp]: "is_left \<circ> swap = is_right"
  by (rule ext) (simp  add: o_def)

lemma [simp]: "unr (swap x) = unl x"
  by (cases x) auto

lemma [simp]: "unl (swap x) = unr x"
  by (cases x) auto

lemma unr_swap [simp]: "unr \<circ> swap = unl"
  by (rule ext) (simp  add: o_def)

lemma unl_swap [simp]: "unl \<circ> swap = unr"
  by (rule ext) (simp  add: o_def)

lemma [simp]: "\<langle>id,id\<rangle> (swap x) = \<langle>id,id\<rangle> x"
  by (cases x) auto

declare lmap.compositionality[simp]

lemma [simp]: "\<rr> (lmap swap xs) = \<ll> xs"
  by (simp add: rights_def lfilter_lmap lefts_def)

lemma [simp]: "\<ll> (lmap swap xs) = \<rr> xs"
  by (simp add: rights_def lfilter_lmap lefts_def)

lemma [simp]: "lmap \<langle>id,id\<rangle> (lmap swap xs) = lmap \<langle>id,id\<rangle> xs"
  by (simp add: o_def)

fun rbr1 :: "'a + ('b + 'c) \<Rightarrow> ('a + 'b) + 'c" where
  "rbr1 (Inl x) = Inl (Inl x)"
| "rbr1 (Inr (Inl x)) = Inl (Inr x)"
| "rbr1 (Inr (Inr x)) = Inr x"

fun rbr2 :: "('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)" where
  "rbr2 (Inr x) = Inr (Inr x)"
| "rbr2 (Inl (Inr x)) = Inr (Inl x)"
| "rbr2 (Inl (Inl x)) = Inl x"

lemma sum3_cases1: "(\<And>x. P (Inl x)) \<Longrightarrow> (\<And>x. P (Inr (Inl x))) \<Longrightarrow> (\<And>x. P (Inr (Inr x))) \<Longrightarrow> P x"
  by (metis sumE)

lemma sum3_cases2: "(\<And>x. P (Inr x)) \<Longrightarrow> (\<And>x. P (Inl (Inl x))) \<Longrightarrow> (\<And>x. P (Inl (Inr x))) \<Longrightarrow> P x"
  by (metis sumE)

lemma [simp]: "is_left (unl (rbr1 x)) \<and> is_left (rbr1 x) \<longleftrightarrow> is_left x"
  by (rule sum3_cases1) auto

lemma [simp]: "is_left x \<Longrightarrow> unl (unl (rbr1 x)) = unl x"
  by (cases x) auto

lemma [simp]: "is_right (unl (rbr1 x)) \<and> is_left (rbr1 x) \<longleftrightarrow> is_left (unr x) \<and> is_right x"
  by (rule sum3_cases1) auto

lemma [simp]: "is_left (unr x) \<and> is_right x \<Longrightarrow> unr (unl (rbr1 x)) = unl (unr x)"
  apply (cases x)
  apply auto
  by (metis is_right.simps(1) not_is_right rbr1.simps(2) sum.exhaust unl.simps(1) unr.simps(1))

lemma [simp]: "is_right (rbr1 x) \<longleftrightarrow> is_right (unr x) \<and> is_right x"
  by (rule sum3_cases1) auto

lemma [simp]: "is_right (unr x) \<and> is_right x \<Longrightarrow> unr (rbr1 x) = unr (unr x)"
  apply (cases x)
  apply auto
  by (metis is_left.simps(1) not_is_left rbr1.simps(3) swap.cases unr.simps(1))

lemma [simp]: "is_right (unr (rbr2 x)) \<and> is_right (rbr2 x) \<longleftrightarrow> is_right x"
  by (rule sum3_cases2) auto

lemma [simp]: "is_right x \<Longrightarrow> unr (unr (rbr2 x)) = unr x"
  by (cases x) auto

lemma [simp]: "is_left (unr (rbr2 x)) \<and> is_right (rbr2 x) \<longleftrightarrow> is_right (unl x) \<and> is_left x"
  by (rule sum3_cases2) auto

lemma [simp]: "is_right (unl x) \<and> is_left x \<Longrightarrow> unl (unr (rbr2 x)) = unr (unl x)"
  apply (cases x)
  apply auto
  by (metis is_left.simps(1) not_is_right rbr2.simps(2) sum.exhaust unl.simps(1) unr.simps(1))

lemma [simp]: "is_left (rbr2 x) \<longleftrightarrow> is_left (unl x) \<and> is_left x"
  by (rule sum3_cases2) auto

lemma [simp]: "is_left (unl x) \<and> is_left x \<Longrightarrow> unl (rbr2 x) = unl (unl x)"
  apply (cases x)
  apply auto
  by (metis is_left.simps(2) rbr2.simps(3) sum.exhaust unl.simps(1))

lemma lmap_lfilter_eq [intro]: "(\<And>x. P x \<Longrightarrow> f x = g x) \<Longrightarrow> lmap f (lfilter P xs) = lmap g (lfilter P xs)"
  by (rule llist.map_cong0) simp

lemma lmap_lfilter_left_eq: "(\<And>x. f (Inl x) = g (Inl x)) \<Longrightarrow> lmap f (lfilter is_left xs) = lmap g (lfilter is_left xs)"
  by (rule lmap_lfilter_eq) (metis (full_types) is_left.simps(2) swap.cases)

lemma lmap_lfilter_right_eq: "(\<And>x. f (Inr x) = g (Inr x)) \<Longrightarrow> lmap f (lfilter is_right xs) = lmap g (lfilter is_right xs)"
  by (rule lmap_lfilter_eq) (metis (full_types) is_right.simps(2) swap.cases)

lemma [simp]: "\<ll> (\<ll> (lmap rbr1 xs)) = \<ll> xs"
  by (auto simp add: lefts_def lfilter_lmap  lfilter_lfilter o_def)

lemma [simp]: "\<rr> (\<ll> (lmap rbr1 xs)) = \<ll> (\<rr> xs)"
  by (auto simp add: rights_def lefts_def lfilter_lmap lfilter_lfilter o_def)

lemma [simp]: "\<rr> (lmap rbr1 xs) = \<rr> (\<rr> xs)"
  by (auto simp add: rights_def lfilter_lmap  lfilter_lfilter o_def)

lemma [simp]: "\<rr> (\<rr> (lmap rbr2 xs)) = \<rr> xs"
  by (auto simp add: rights_def lfilter_lmap  lfilter_lfilter o_def)

lemma [simp]: "\<ll> (\<rr> (lmap rbr2 xs)) = \<rr> (\<ll> xs)"
  by (auto simp add: rights_def lefts_def lfilter_lmap lfilter_lfilter o_def)

lemma [simp]: "\<ll> (lmap rbr2 xs) = \<ll> (\<ll> xs)"
  by (auto simp add: lefts_def lfilter_lmap lfilter_lfilter o_def)

lemma [simp]: "\<langle>id,\<langle>id,id\<rangle>\<rangle> (rbr2 x) = \<langle>\<langle>id,id\<rangle>,id\<rangle> x"
  by (rule sum3_cases2) auto

lemma [simp]: "\<langle>\<langle>id,id\<rangle>,id\<rangle> (rbr1 x) = \<langle>id,\<langle>id,id\<rangle>\<rangle> x"
  by (rule sum3_cases1) auto

lemma lfilter_ltakeWhile [simp]: "lfilter P (ltakeWhile (Not \<circ> P) xs) = LNil"
  by auto (metis lfilter_empty_conv lset_ltakeWhileD)

lemma lset_ex_lnth: "(\<exists>x\<in>lset xs. P x) \<Longrightarrow> \<exists>n. P (lnth xs n)"
  by auto

lemma infinite_lfilter: "\<not> lfinite (lfilter P xs) \<Longrightarrow> \<exists>n. P (lnth xs n)"
proof -
  assume "\<not> lfinite (lfilter P xs)"
  hence assm1: "\<not> lfinite (lfilter P (lappend (ltakeWhile (Not \<circ> P) xs) (ldropWhile (Not \<circ> P) xs)))"
    by (metis lappend_ltakeWhile_ldropWhile)
  {
    assume assm2: "lfinite (ltakeWhile (Not \<circ> P) xs)"
    then obtain n where n_def: "llength (ltakeWhile (Not \<circ> P) xs) = enat n"
      by (metis lfinite_conv_llength_enat)
    from assm1 and assm2
    have "\<not> lfinite (lappend (lfilter P (ltakeWhile (Not \<circ> P) xs)) (lfilter P (ldropWhile (Not \<circ> P) xs)))"
      by (metis lfilter_lappend_lfinite)
    hence "\<not> lfinite (lfilter P (ldropWhile (Not \<circ> P) xs))"
      by (simp only: lfilter_ltakeWhile, simp)
    hence "P (lhd (ldropWhile (Not \<circ> P) xs))"
      by (metis assm2 lappend_ltakeWhile_ldropWhile lfilter_eq_LConsD lfilter_lappend_lfinite lhd_LCons_ltl lhd_lfilter lnull_imp_lfinite lnull_lappend)
    hence "\<exists>x\<in>lset xs. P x"
      apply (rule_tac x = "lhd (ldropWhile (Not \<circ> P) xs)" in bexI)
      apply simp
      by (metis `\<not> lfinite (lfilter P xs)` assm2 lfinite_lfilterI lfinite_ltakeWhile lhd_ldropWhile_in_lset)
    hence "\<exists>n. P (lnth xs n)"
      by (rule lset_ex_lnth)
  }
  moreover
  {
    assume assm2: "\<not> lfinite (ltakeWhile (Not \<circ> P) xs)"
    from assm1 and assm2
    have "\<not> lfinite (lfilter P (ltakeWhile (Not \<circ> P) xs))"
      by (metis lappend_inf)
    hence "\<not> lfinite LNil"
      by (simp only: lfilter_ltakeWhile, simp)
    from this and lfinite_LNil have "False" by blast
  }
  ultimately show "\<exists>n. P (lnth xs n)"
    by metis
qed

declare in_lset_conv_lnth[iff del]
declare lfinite_conv_llength_enat[iff del]

definition "llist_Case \<equiv> case_llist"

primrec ldeleteLeft_nat :: "nat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft_nat 0 xs = lappend (ltakeWhile is_right xs) (ltl (ldropWhile is_right xs))"
| "ldeleteLeft_nat (Suc n) xs = lappend (ltakeWhile is_right xs) (llist_Case LNil (\<lambda>x' xs'. LCons x' (ldeleteLeft_nat n xs')) (ldropWhile is_right xs))"

primrec ldeleteLeft :: "enat \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "ldeleteLeft (enat n) xs = ldeleteLeft_nat n xs"
| "ldeleteLeft \<infinity> xs = xs"

primrec linsertLeft_nat :: "nat \<Rightarrow> 'a \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "linsertLeft_nat 0 x xs = lappend (ltakeWhile is_right xs) (LCons (Inl x) (ldropWhile is_right xs))"
| "linsertLeft_nat (Suc n) x xs = lappend (ltakeWhile is_right xs) (llist_Case LNil (\<lambda>x' xs'. LCons x' (linsertLeft_nat n x xs')) (ldropWhile is_right xs))"

primrec linsertLeft :: "enat \<Rightarrow> 'a \<Rightarrow> ('a + 'b) llist \<Rightarrow> ('a + 'b) llist" where
  "linsertLeft (enat n) x xs = linsertLeft_nat n x xs"
| "linsertLeft \<infinity> x xs = xs"

lemma [simp]: "(case xs of LNil \<Rightarrow> LNil | LCons x' xs' \<Rightarrow> LCons x' xs') = xs"
  by (cases xs) auto

lemma linsertLeft_eSuc: "linsertLeft (eSuc n) x xs = lappend (ltakeWhile is_right xs) (llist_Case LNil (\<lambda>x' xs'. LCons x' (linsertLeft n x xs')) (ldropWhile is_right xs))"
  by (cases n) (simp_all add: eSuc_enat llist_Case_def)

primrec linsert_nat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "linsert_nat 0 x xs = LCons x xs"
| "linsert_nat (Suc n) x xs = llist_Case LNil (\<lambda>x' xs'. LCons x' (linsert_nat n x xs')) xs"

primrec linsert :: "enat \<Rightarrow> 'a \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "linsert (enat n) x xs = linsert_nat n x xs"
| "linsert \<infinity> x xs = xs"

lemma [simp]: "llength xs = \<infinity> \<Longrightarrow> lappend xs ys = xs"
  by (metis lappend_inf llength_eq_infty_conv_lfinite)

notation ltake ("\<up>")
  and ldrop ("\<down>")

lemma [simp]: "\<up> (llength xs) xs = xs"
  by (metis ltake_all order_refl)

lemma lefts_ltake_right [simp]: "\<ll> (ltakeWhile is_right xs) = LNil"
  by (metis Not_is_left comp_apply lefts_def lfilter_ltakeWhile llist.simps(12))

lemma [simp]: "lmap f xs \<noteq> LNil \<longleftrightarrow> xs \<noteq> LNil"
  by (metis lmap_eq_LNil)

end
