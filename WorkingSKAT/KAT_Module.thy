theory KAT_Module
  imports KAT
begin

context complete_boolean_lattice
begin

  lemma double_neg: "x \<in> carrier A \<Longrightarrow> !(!x) = x"
    by (metis (lifting) ccompl_bot ccompl_closed ccompl_top ccompl_uniq join_comm meet_comm)

end

locale kat_module' =
  fixes K :: "'a test_algebra"
  and A :: "('b, 'c) ord_scheme"
  and scalar_product :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes kat_subalg: "kat K"
  and cbl_subalg: "complete_boolean_lattice A"
  and mk_type: "scalar_product : carrier A \<rightarrow> carrier K \<rightarrow> carrier A"

sublocale kat_module' \<subseteq> kat K using kat_subalg .
sublocale kat_module' \<subseteq> A: complete_boolean_lattice A using cbl_subalg .

no_notation
  Groups.plus_class.plus (infixl "+" 65) and
  Groups.zero_class.zero ("0") and
  Dioid.plus (infixl "+\<index>" 70) and
  Dioid.mult (infixl "\<cdot>\<index>" 80) and
  Dioid.one ("1\<index>") and
  Dioid.zero ("0") and
  Kleene_Algebra.star ("_\<^sup>\<star>\<index>" [101] 100) and
  KAT.kat.complement ("!")

context kat_module'
begin

  abbreviation plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 70) where
    "p + q \<equiv> dioid.plus K p q"

  abbreviation mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>" 80) where
     "p\<cdot>q \<equiv> dioid.mult K p q"

  abbreviation one :: "'a" ("1") where "1 \<equiv> Dioid.one K"

  abbreviation zero :: "'a" ("0") where "0 \<equiv> Dioid.zero K"

  abbreviation module :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<Colon>" 75) where
    "m \<Colon> p \<equiv> scalar_product m p"

  abbreviation star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100) where
    "x\<^sup>\<star> \<equiv> Kleene_Algebra.star K x"

  notation
    nat_order (infixl "\<preceq>" 50)

  notation
    complement ("!")

end

locale kat_module = kat_module' +
  assumes mod_plus: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> (p + q) = m \<Colon> p \<squnion> m \<Colon> q"
  and mod_mult: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> (p\<cdot>q) = m \<Colon> p \<Colon> q"
  and mod_join: "\<lbrakk>p \<in> carrier K; P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> (P \<squnion> Q) \<Colon> p = P \<Colon> p \<squnion> Q \<Colon> p"
  and mod_zero: "m \<in> carrier A \<Longrightarrow> m \<Colon> 0 = complete_join_semilattice.bot A"
  and mod_star: "\<lbrakk>m \<in> carrier A; n \<in> carrier A; p \<in> carrier K\<rbrakk> \<Longrightarrow> m \<squnion> n \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> n \<Longrightarrow> m \<Colon> p\<^sup>\<star> \<sqsubseteq>\<^bsub>A\<^esub> n"
  and mod_one: "m \<in> carrier A \<Longrightarrow> m \<Colon> 1 = m"
  and mod_test: "\<lbrakk>a \<in> tests K; m \<in> carrier A\<rbrakk> \<Longrightarrow> m \<Colon> a = m \<sqinter> \<top> \<Colon> a"

begin

  lemma one_element: "\<lbrakk>m \<in> carrier A; \<And>a m. \<lbrakk>a \<in> tests K; m \<in> carrier A\<rbrakk> \<Longrightarrow> !(m \<Colon> a) = m \<Colon> !a\<rbrakk> \<Longrightarrow> m = \<top>"
  proof -
    assume mc: "m \<in> carrier A" and mod_not: "\<And>a m. \<lbrakk>a \<in> tests K; m \<in> carrier A\<rbrakk> \<Longrightarrow> !(m \<Colon> a) = m \<Colon> !a"
    have "m = !(!m)"
      by (metis double_neg mc)
    also have "... = !(!(m \<Colon> 1))"
      by (metis (lifting) mc mod_one)
    also have "... = !(m \<Colon> !1)"
      by (metis mc mod_not test.top_closed)
    also have "... = !(m \<Colon> 0)"
      by (metis test_not_one)
    also have "... = !\<bottom>"
      by (metis mc mod_zero)
    also have "... = \<top>"
      by (metis A.bot_closed bot_onel ccompl_closed ccompl_top)
    finally show ?thesis .
  qed

  lemma mod_bot: "p \<in> carrier K \<Longrightarrow> \<bottom> \<Colon> p = \<bottom>"
  proof -
    assume pc: "p \<in> carrier K"
    have "\<bottom> \<Colon> p = \<bottom> \<Colon> 0 \<Colon> p"
      by (metis A.bot_closed mod_zero)
    also have "... = \<bottom> \<Colon> 0"
      by (metis A.bot_closed mod_mult mult_zerol pc zero_closed)
    also have "... = \<bottom>"
      by (metis A.bot_closed mod_zero)
    finally show ?thesis .
  qed

  lemma mod_closed [intro]: "\<lbrakk>p \<in> carrier K; P \<in> carrier A\<rbrakk> \<Longrightarrow> P \<Colon> p \<in> carrier A"
    by (metis mk_type typed_application)

  lemma mod_A_iso: "\<lbrakk>p \<in> carrier K; P \<in> carrier A; Q \<in> carrier A\<rbrakk> \<Longrightarrow> P \<sqsubseteq>\<^bsub>A\<^esub> Q \<Longrightarrow> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> Q \<Colon> p"
    by (metis A.leq_def A.leq_def_left mod_closed mod_join)

  lemma mod_K_iso: "\<lbrakk>p \<in> carrier K; q \<in> carrier K; P \<in> carrier A\<rbrakk> \<Longrightarrow> p \<preceq> q \<Longrightarrow> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> P \<Colon> q"
    by (metis A.leq_def mod_closed mod_plus nat_order_def)

  declare A.order_refl [intro]
  declare A.bot_closed [intro]

  lemma mod_zero_bot: "\<lbrakk>p \<in> carrier K; M \<in> carrier A; p \<preceq> 0\<rbrakk> \<Longrightarrow> M \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> \<bottom>"
    by (subgoal_tac "p = 0", auto simp add: mod_zero) (metis add_zeror nat_order_def)

  definition hoare_triple :: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [54,54,54] 53) where
    "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace> \<equiv> P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> Q"

  lemma hoare_composition:
    assumes pc: "p \<in> carrier K" and qc: "q \<in> carrier K"
    and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A" and Rc: "R \<in> carrier A"
    and p_triple: "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>" and q_triple: "\<lbrace>Q\<rbrace> q \<lbrace>R\<rbrace>"
    shows "\<lbrace>P\<rbrace> p \<cdot> q \<lbrace>R\<rbrace>"
    by (smt A.join_assoc A.leq_def Pc Qc Rc hoare_triple_def mod_closed mod_join mod_mult p_triple pc q_triple qc)

  lemma hoare_skip: shows "P \<in> carrier A \<Longrightarrow> \<lbrace>P\<rbrace> 1 \<lbrace>P\<rbrace>"
    by (metis A.order_refl hoare_triple_def mod_one)

  lemma hoare_weakening:
    assumes Pc[intro]: "P \<in> carrier A" and P'c[intro]: "P' \<in> carrier A"
    and Qc[intro]: "Q \<in> carrier A" and Q'c[intro]: "Q' \<in> carrier A"
    and pc[intro]: "p \<in> carrier K"
    shows "\<lbrakk>\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>; P' \<sqsubseteq>\<^bsub>A\<^esub> P; Q \<sqsubseteq>\<^bsub>A\<^esub> Q'\<rbrakk> \<Longrightarrow> \<lbrace>P'\<rbrace> p \<lbrace>Q'\<rbrace>"
  proof -
    assume "Q \<sqsubseteq>\<^bsub>A\<^esub> Q'"
    hence a: "\<lbrace>Q\<rbrace> 1 \<lbrace>Q'\<rbrace>"
      by (metis Qc hoare_triple_def mod_one)
    assume "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>" and "P' \<sqsubseteq>\<^bsub>A\<^esub> P"
    hence b: "\<lbrace>P'\<rbrace> p \<lbrace>Q\<rbrace>"
      by (simp add: hoare_triple_def, rule_tac y = "P \<Colon> p" in A.order_trans) (metis P'c Pc mod_A_iso pc, auto)
    have "\<lbrace>P'\<rbrace> p \<cdot> 1 \<lbrace>Q'\<rbrace>"
      by (metis (lifting) P'c Q'c Qc a b hoare_composition one_closed pc)
    thus ?thesis
      by (metis mult_oner pc)
  qed

  declare mod_closed[intro]

  lemma hoare_plus:
    assumes pc [intro]: "p \<in> carrier K" and qc [intro]: "q \<in> carrier K"
    and Pc [intro]: "P \<in> carrier A" and Qc [intro]: "Q \<in> carrier A"
    and then_branch: "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
    and else_branch: "\<lbrace>P\<rbrace> q \<lbrace>Q\<rbrace>"
    shows "\<lbrace>P\<rbrace> p + q \<lbrace>Q\<rbrace>"
  proof -
    have "P \<Colon> p \<sqsubseteq>\<^bsub>A\<^esub> Q" and "P \<Colon> q \<sqsubseteq>\<^bsub>A\<^esub> Q"
      by (insert then_branch else_branch) (simp add: hoare_triple_def)+
    hence "P \<Colon> (p + q) \<sqsubseteq>\<^bsub>A\<^esub> Q"
      by (simp add: mod_plus[OF pc qc Pc], subst A.bin_lub_var, auto)
    thus ?thesis
      by (simp add: hoare_triple_def)
  qed

  (* by (metis A.bin_lub_var Pc Qc else_branch hoare_triple_def mod_closed mod_plus pc qc then_branch) *)

  lemma hoare_if:
    assumes b_test: "b \<in> tests K"
    and pc: "p \<in> carrier K" and qc: "q \<in> carrier K"
    and Pc: "P \<in> carrier A" and Qc: "Q \<in> carrier A"
    and then_branch: "\<lbrace>P \<sqinter> (\<top> \<Colon> b)\<rbrace> p \<lbrace>Q\<rbrace>"
    and else_branch: "\<lbrace>P \<sqinter> (\<top> \<Colon> !b)\<rbrace> q \<lbrace>Q\<rbrace>"
    shows "\<lbrace>P\<rbrace> b\<cdot>p + !b\<cdot>q \<lbrace>Q\<rbrace>"
    apply (rule hoare_plus)
    apply (metis (lifting) b_test mult_closed pc test_subset_var)
    apply (metis b_test local.complement_closed mult_closed qc test_subset_var)
    apply (metis Pc)
    apply (metis Qc)
    apply (rule_tac Q = "P \<sqinter> (\<top> \<Colon> b)" in hoare_composition)
    apply (metis b_test test_subset_var)
    apply (metis pc)
    apply (metis Pc)
    apply (metis A.meet_closed A.top_closed Pc b_test mod_closed test_subset_var)
    apply (metis (lifting) Qc)
    apply (metis A.eq_refl Pc b_test hoare_triple_def mod_closed mod_test test_subset_var)
    apply (metis then_branch)
    apply (rule_tac Q = "P \<sqinter> \<top> \<Colon> !b" in hoare_composition)
    apply (metis b_test local.complement_closed test_subset_var)
    apply (metis (lifting) qc)
    apply (metis (lifting) Pc)
    apply (metis (lifting) A.meet_closed A.top_closed Pc b_test local.complement_closed mod_closed test_subset_var)
    apply (metis (lifting) Qc)
    apply (metis A.eq_refl Pc b_test hoare_triple_def kat.complement_closed kat_subalg mod_closed mod_test test_subset_var)
    by (metis (lifting) else_branch)

  lemma hoare_star:
    assumes pc: "p \<in> carrier K"
    and Pc: "P \<in> carrier A"
    and p_triple: "\<lbrace>P\<rbrace> p \<lbrace>P\<rbrace>"
    shows "\<lbrace>P\<rbrace> p\<^sup>\<star> \<lbrace>P\<rbrace>"
    by (metis (lifting) A.bin_lub_var A.order_refl Pc hoare_triple_def mod_closed mod_star p_triple pc)

  declare star_closed [intro]
  declare mult_closed [intro]
  declare test_subset_var [intro]
  declare complement_closed [intro]
  declare meet_closed [intro!]
  declare top_closed [intro]

  lemma [intro]: "\<lbrakk>b \<in> tests K; P \<in> carrier A\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> b \<lbrace>P \<sqinter>\<^bsub>A\<^esub> \<top> \<Colon> b\<rbrace>"
    by (metis A.eq_refl hoare_triple_def mod_closed mod_test test_subset_var)

  lemma hoare_while:
    assumes b_test [intro]: "b \<in> tests K" and pc [intro]: "p \<in> carrier K"
    and Pc [intro]: "P \<in> carrier A"
    and loop_condition [intro]: "\<lbrace>P \<sqinter> (\<top> \<Colon> b)\<rbrace> p \<lbrace>P\<rbrace>"
    shows "\<lbrace>P\<rbrace> (b\<cdot>p)\<^sup>\<star>\<cdot>!b \<lbrace>P \<sqinter> (\<top> \<Colon> !b)\<rbrace>"
  proof (rule hoare_composition[where ?Q = P], auto)
    show "\<lbrace>P\<rbrace> (b \<cdot> p)\<^sup>\<star> \<lbrace>P\<rbrace>"
      by (blast intro: hoare_star hoare_composition[where ?Q = "P \<sqinter> \<top> \<Colon> b"])
  qed

lemma derived_rule1:
  assumes p: "{P1,P2,Q1,Q2} \<subseteq> carrier A" and q: "p \<in> carrier K"
  and "\<lbrace>P1\<rbrace> p \<lbrace>Q1\<rbrace>" and "\<lbrace>P2\<rbrace> p \<lbrace>Q2\<rbrace>"
  shows "\<lbrace>P1 \<sqinter> P2\<rbrace> p \<lbrace>Q1 \<sqinter> Q2\<rbrace>"
  using assms
  apply (auto intro: simp add: hoare_triple_def assms, subst A.bin_glb_var)
  by (metis A.absorb1 A.bin_lub_var A.meet_closed A.meet_comm mod_closed mod_join)+

lemma derived_rule2:
  assumes "P \<in> carrier A" and "p \<in> carrier K" and "P \<Colon> p = (\<top> \<Colon> p) \<sqinter> P"
  shows "\<lbrace>P\<rbrace> p \<lbrace>P\<rbrace>"
  using assms
  by (metis (lifting) A.bin_glb_var A.eq_refl A.top_closed hoare_triple_def mod_closed)

lemma derived_rule3:
  assumes "{P,Q,R} \<subseteq> carrier A" and "p \<in> carrier K" and "P \<Colon> p = (\<top> \<Colon> p) \<sqinter> P"
  and "\<lbrace>Q\<rbrace> p \<lbrace>R\<rbrace>"
  shows "\<lbrace>P \<sqinter> Q\<rbrace> p \<lbrace>P \<sqinter> R\<rbrace>"
  by (insert assms) (smt derived_rule1 derived_rule2 insert_subset)

end

lemma "range f = (\<Union>x. {f x})" and "(\<Union>x. {f x}) = {f i|i. True}" by auto

end

