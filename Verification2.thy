theory Verification2
  imports Language2
begin

record store =
  s_f\<^sub>A :: nat
  s_f\<^sub>B :: nat
  s_i\<^sub>A :: nat
  s_i\<^sub>B :: nat
  s_fmax :: nat
  s_A :: "nat list"

type_synonym program = "(store \<times> store) llist set"

datatype var = f\<^sub>A | f\<^sub>B | i\<^sub>A | i\<^sub>B | fmax

primrec deref :: "var \<Rightarrow> store \<Rightarrow> nat" where
  "deref f\<^sub>A s = s_f\<^sub>A s"
| "deref f\<^sub>B s = s_f\<^sub>B s"
| "deref i\<^sub>A s = s_i\<^sub>A s"
| "deref i\<^sub>B s = s_i\<^sub>B s"
| "deref fmax s = s_fmax s"

datatype expr = Const nat
              | Var var
              | ALen
              | Lookup expr
              | BinOp "nat \<Rightarrow> nat \<Rightarrow> nat" expr expr
              | Fun "nat \<Rightarrow> nat" expr

primrec eval_expr :: "expr \<Rightarrow> store \<Rightarrow> nat" where
  "eval_expr (Const c) s = c"
| "eval_expr (Var v) s = deref v s"
| "eval_expr ALen s = length (s_A s)"
| "eval_expr (Lookup x) s = s_A s ! eval_expr x s"
| "eval_expr (BinOp f x y) s = f (eval_expr x s) (eval_expr y s)"
| "eval_expr (Fun f x) s = f (eval_expr x s)"

datatype bool_expr = BTrue ("\<one>")
                   | BFalse ("\<zero>")
                   | BDisj bool_expr bool_expr (infixl "\<oplus>" 65)
                   | BConj bool_expr bool_expr (infixl "\<otimes>" 70)
                   | BImpl bool_expr bool_expr (infixl "\<rightharpoonup>" 60)
                   | BIff bool_expr bool_expr
                   | BNot bool_expr
                   | BExpr1 "nat \<Rightarrow> bool" expr
                   | BExpr2 "nat \<Rightarrow> nat \<Rightarrow> bool" expr expr
                   | BArray "nat \<Rightarrow> nat list \<Rightarrow> bool" expr

primrec eval_bool_expr :: "bool_expr \<Rightarrow> store \<Rightarrow> bool" where
  "eval_bool_expr BTrue s = True"
| "eval_bool_expr BFalse s = False"
| "eval_bool_expr (BDisj x y) s = (eval_bool_expr x s \<or> eval_bool_expr y s)"
| "eval_bool_expr (BConj x y) s = (eval_bool_expr x s \<and> eval_bool_expr y s)"
| "eval_bool_expr (BImpl x y) s = (eval_bool_expr x s \<longrightarrow> eval_bool_expr y s)"
| "eval_bool_expr (BIff x y) s = (eval_bool_expr x s \<longleftrightarrow> eval_bool_expr y s)"
| "eval_bool_expr (BNot x) s = (\<not> eval_bool_expr x s)"
| "eval_bool_expr (BExpr1 f x) s = f (eval_expr x s)"
| "eval_bool_expr (BExpr2 f x y) s = f (eval_expr x s) (eval_expr y s)"
| "eval_bool_expr (BArray p x) s = p (eval_expr x s) (s_A s)"

(* no_notation residual_l (infixl "\<leftarrow>" 60) *)

primrec assign :: "var \<Rightarrow> expr \<Rightarrow> store \<Rightarrow> store" (infix "\<leftarrow>" 67) where
  "(f\<^sub>A \<leftarrow> e) s = store.make (eval_expr e s) (s_f\<^sub>B s) (s_i\<^sub>A s) (s_i\<^sub>B s) (s_fmax s) (s_A s)"
| "(f\<^sub>B \<leftarrow> e) s = store.make (s_f\<^sub>A s) (eval_expr e s) (s_i\<^sub>A s) (s_i\<^sub>B s) (s_fmax s) (s_A s)"
| "(i\<^sub>A \<leftarrow> e) s = store.make (s_f\<^sub>A s) (s_f\<^sub>B s) (eval_expr e s) (s_i\<^sub>B s) (s_fmax s) (s_A s)"
| "(i\<^sub>B \<leftarrow> e) s = store.make (s_f\<^sub>A s) (s_f\<^sub>B s) (s_i\<^sub>A s) (eval_expr e s) (s_fmax s) (s_A s)"
| "(fmax \<leftarrow> e) s = store.make (s_f\<^sub>A s) (s_f\<^sub>B s) (s_i\<^sub>A s) (s_i\<^sub>B s) (eval_expr e s) (s_A s)"

primrec e_subst :: "expr \<Rightarrow> expr \<Rightarrow> var \<Rightarrow> expr" where
  "e_subst (Const c) e v = Const c"
| "e_subst (Var v') e v = (if v = v' then e else Var v')"
| "e_subst ALen e v = ALen"
| "e_subst (Lookup x) e v = Lookup (e_subst x e v)"
| "e_subst (BinOp f x y) e v = BinOp f (e_subst x e v) (e_subst y e v)"
| "e_subst (Fun f x) e v = Fun f (e_subst x e v)"

primrec be_subst :: "bool_expr \<Rightarrow> expr \<Rightarrow> var \<Rightarrow> bool_expr" ("_[_\<bar>_]") where
  "be_subst BTrue e v = BTrue"
| "be_subst BFalse e v = BFalse"
| "be_subst (BDisj x y) e v = BDisj (x[e\<bar>v]) (y[e\<bar>v])"
| "be_subst (BConj x y) e v = BConj (x[e\<bar>v]) (y[e\<bar>v])"
| "be_subst (BImpl x y) e v = BImpl (x[e\<bar>v]) (y[e\<bar>v])"
| "be_subst (BIff x y) e v = BIff (x[e\<bar>v]) (y[e\<bar>v])"
| "be_subst (BNot x) e v = BNot (x[e\<bar>v])"
| "be_subst (BExpr1 f x) e v = BExpr1 f (e_subst x e v)"
| "be_subst (BExpr2 f x y) e v = BExpr2 f (e_subst x e v) (e_subst y e v)"
| "be_subst (BArray p x) e v = BArray p (e_subst x e v)"

lemma [simp]: "s_A ((x\<^sub>v \<leftarrow> E) s) = s_A s"
  by (cases "x\<^sub>v") (simp_all add: store.defs)

lemma [simp]: "eval_expr e ((x\<^sub>v \<leftarrow> E) s) = eval_expr (e_subst e E x\<^sub>v) s"
proof (induct e)
  case (Const c)
  show ?case by simp
next
  case (Var v)
  show ?case
    apply (cases x\<^sub>v)
    apply (simp_all add: store.defs)
    apply (cases v, simp_all)
    apply (cases v, simp_all)
    apply (cases v, simp_all)
    apply (cases v, simp_all)
    by (cases v, simp_all)
next
  case ALen
  thus ?case
    by simp
next
  case (Lookup x)
  thus ?case
    by simp
next
  case (BinOp f x y)
  thus ?case
    by simp
next
  case (Fun f x)
  thus ?case
    by simp
qed

lemma assign_eval_bool: "eval_bool_expr (Q[E\<bar>x\<^sub>v]) s \<longleftrightarrow> eval_bool_expr Q ((x\<^sub>v \<leftarrow> E) s)"
proof (induct Q)
  case BTrue
  thus ?case
    by simp
next
  case BFalse
  thus ?case
    by simp
next
  case (BDisj Q1 Q2)
  thus ?case
    by auto
next
  case (BConj Q1 Q2)
  thus ?case
    by simp
next
  case (BImpl Q1 Q2)
  thus ?case
    by simp
next
  case (BIff Q1 Q2)
  thus ?case
    by simp
next
  case (BNot Q)
  thus ?case
    by simp
next
  case (BExpr1 f x)
  thus ?case
    by simp
next
  case (BExpr2 f x y)
  thus ?case
    by simp
next
  case (BArray p x)
  thus ?case
    by auto
qed

definition test :: "bool_expr \<Rightarrow> program" where
  "test P \<equiv> Language2.test (eval_bool_expr P)"

definition sequential_composition :: "program \<Rightarrow> program \<Rightarrow> program" (infixr ";" 52) where
  "X; Y \<equiv> X\<cdot>Y"

definition parallel_composition :: "program \<Rightarrow> program \<Rightarrow> program"
  ("parallel { _ } meanwhile { _ }" [51,51] 55) where
  "parallel { X } meanwhile { Y } \<equiv> X \<parallel> Y"

definition while_loop :: "bool_expr \<Rightarrow> program \<Rightarrow> program" ("while _ { _ }" [51] 55) where
  "while B { P } \<equiv> (test B ; P)\<^sup>\<star>; test (BNot B)"

definition quintuple :: "store rel \<Rightarrow> store rel \<Rightarrow> bool_expr \<Rightarrow> program \<Rightarrow> bool_expr \<Rightarrow> bool"
  ("_, //_ //\<turnstile> \<lbrace>_\<rbrace>// _// \<lbrace>_\<rbrace>" [20,20,20,20,20] 1000) where
  "R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>Q\<rbrace> \<equiv> (X \<subseteq> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G))"

definition preserve :: "bool_expr \<Rightarrow> store rel" where
  "preserve P = {(\<sigma>, \<sigma>'). eval_bool_expr P \<sigma>  \<longrightarrow> eval_bool_expr P \<sigma>'}"

lemma relcomp_elem: "(\<sigma>,\<tau>) \<in> R O S \<longleftrightarrow> (\<exists>\<gamma>. (\<sigma>,\<gamma>) \<in> R \<and> (\<gamma>,\<tau>) \<in> S)"
  by auto

lemma preservation': "eval_bool_expr P \<sigma> \<Longrightarrow> (\<sigma>, \<tau>) \<in> {(\<sigma>, \<sigma>'). eval_bool_expr P \<sigma> \<longrightarrow> eval_bool_expr P \<sigma>'} ^^ n \<Longrightarrow> eval_bool_expr P \<tau>"
proof (induct n arbitrary: \<tau>)
  case 0 thus ?case by simp
next
  case (Suc n)
  from Suc(2) and Suc(3) show ?case
    apply (simp add: relcomp_elem)
    apply (erule exE)
    apply (erule conjE)
    by (metis Suc.hyps)
qed 

lemma preservation: "eval_bool_expr P \<sigma> \<Longrightarrow> (\<sigma>, \<tau>) \<in> (preserve P)\<^sup>* \<Longrightarrow> eval_bool_expr P \<tau>"
  apply (simp add: preserve_def)
  apply (drule rtrancl_imp_relpow)
  apply (erule exE)+
  apply (rule preservation')
  by simp_all

lemma test_guar: "test P \<subseteq> guar G"
  by (metis test_def test_in_guar)

lemma preimp_mono: "G \<subseteq> R \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> R \<rightharpoondown> X \<subseteq> G \<rightharpoondown> Y"
  by (metis order_trans preimp_antitone preimp_iso)

lemma Rely_antitone: "G\<^sup>* \<subseteq> R\<^sup>* \<Longrightarrow> R \<rhd> X \<subseteq> G \<rhd> X"
  apply (auto simp add: Rely_def)
  apply (rename_tac x y)
  apply (rule_tac x = y in bexI)
  apply simp_all
  by (metis rely_antitone)

lemma Rely_mono: "G\<^sup>* \<subseteq> R\<^sup>* \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> R \<rhd> X \<subseteq> G \<rhd> Y"
  apply (rule order_trans[where y = "G \<rhd> X"])
  apply (rule Rely_antitone)
  apply simp
  apply (rule prog_rely_iso)
  by auto

lemma l_prod_mono: "X \<subseteq> Y \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> X \<cdot> Z \<subseteq> Y \<cdot> W"
  by (metis seq.mult_isol_var)

lemma guar_mono: "G\<^sup>* \<subseteq> G'\<^sup>* \<Longrightarrow> guar G \<subseteq> guar G'"
  by (auto simp add: guar_def) (metis contra_subsetD)

lemma evaluate_tests [simp]: "test P \<subseteq> test Q \<longleftrightarrow> (\<forall>s. eval_bool_expr P s \<longrightarrow> eval_bool_expr Q s)"
  by (auto simp add: test_def Language2.test_def)

lemma preimp_zero [simp]: "({} \<rightharpoondown> x) = UNIV"
  by (simp add: preimp_def)

lemma preimp_zero_right: "X \<noteq> {} \<Longrightarrow> X \<rightharpoondown> {} = {}"
  by (auto simp add: preimp_def l_prod_def)

abbreviation "\<T> \<equiv> test"

abbreviation "\<P> \<equiv> preserve"

abbreviation "\<F> \<equiv> FIN"

(* ------------------------------------------------------------------------
   Assignment
   ------------------------------------------------------------------------ *)

definition assign_prog :: "var \<Rightarrow> expr \<Rightarrow> (store \<times> store) llist set" (infix ":=" 67) where
  "v := E \<equiv> {(\<sigma>,\<sigma>') # sng (\<sigma>',\<sigma>') |\<sigma> \<sigma>'. \<sigma>' = (v \<leftarrow> E) \<sigma>}"

lemma FIN_test1: "xs \<in> FIN \<cdot> t \<Longrightarrow> x # xs \<in> FIN \<cdot> t"
  by (auto simp add: FIN_def l_prod_def) (metis lappend_code(2) lfinite_LCons)

lemma FIN_test2: "x # xs \<in> t \<Longrightarrow> x # xs \<in> FIN \<cdot> t"
  by (auto simp add: FIN_def l_prod_def) (metis lappend_code(1) lfinite_code(1))

lemma rely_elem1: "env (R\<^sup>*) x \<and> x \<in> X \<Longrightarrow> x \<in> R \<rhd> X"
  by (auto simp add: Rely_def rely_def)

lemma refine_assignment:
  "v := E \<subseteq> \<T> (Q[E\<bar>v]) \<rightharpoondown> (\<P> (Q[E\<bar>v]) \<rhd> \<F> \<cdot> \<T> Q \<inter> guar {(\<sigma>, (v \<leftarrow> E) \<sigma>)|\<sigma>. eval_bool_expr (Q[E\<bar>v]) \<sigma>})"
proof (simp only: subset_iff, clarify)
  let ?G = "{(\<sigma>, (v \<leftarrow> E) \<sigma>)|\<sigma>. eval_bool_expr (Q[E\<bar>v]) \<sigma>}"

  fix w
  assume "w \<in> v := E"

  then obtain \<sigma> \<sigma>'
  where w_def: "w = (\<sigma>, \<sigma>') # sng (\<sigma>', \<sigma>')" and \<sigma>'_assign: "\<sigma>' = (v \<leftarrow> E) \<sigma>"
    by (auto simp add: assign_prog_def)

  have "{(\<tau>, \<tau>) # (\<sigma>, \<sigma>') # sng (\<sigma>', \<sigma>') |\<tau>. eval_bool_expr (Q[E\<bar>v]) \<tau>} \<subseteq> preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G"
  proof (simp only: subset_iff, clarify)
    fix \<tau> assume "eval_bool_expr (Q[E\<bar>v]) \<tau>"

    have "test Q \<noteq> {}"
      by (auto simp add: test_def Language2.test_def) (metis `eval_bool_expr (Q[E\<bar>v]) \<tau>` assign_eval_bool)
    then obtain Q_inhab where "Q_inhab \<in> test Q"
      by (metis all_not_in_conv)

    hence "lfinite Q_inhab"
      by (auto simp add: test_def Language2.test_def)

    show "(\<tau>, \<tau>) # (\<sigma>, \<sigma>') # sng (\<sigma>', \<sigma>') \<in> preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G"
    proof (cases "(\<tau>, \<sigma>) \<in> (preserve (Q[E\<bar>v]))\<^sup>*")
      assume [simp]: "(\<tau>, \<sigma>) \<in> (preserve (Q[E\<bar>v]))\<^sup>*"
      hence "eval_bool_expr (Q[E\<bar>v]) \<sigma>"
        by (metis `eval_bool_expr (Q[E\<bar>v]) \<tau>` preservation)

      show "(\<tau>, \<tau>) # (\<sigma>, \<sigma>') # sng (\<sigma>', \<sigma>') \<in> preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G"
        apply (rule rely_elem1)
        apply auto
        apply (rule FIN_test1)
        apply (rule FIN_test1)
        apply (rule FIN_test2)
        apply (simp add: test_def Language2.test_def)
        apply (metis \<sigma>'_assign `eval_bool_expr (Q[E\<bar>v]) \<sigma>` assign_eval_bool)
        apply (rule r_into_rtrancl )
        by (simp add: \<sigma>'_assign `eval_bool_expr (Q[E\<bar>v]) \<sigma>`)
    next
      assume \<tau>\<sigma>: "(\<tau>, \<sigma>) \<notin> (preserve (Q[E\<bar>v]))\<^sup>*"

      show "(\<tau>, \<tau>) # (\<sigma>, \<sigma>') # sng (\<sigma>', \<sigma>') \<in> preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G"
        apply (auto simp add: Rely_def)
        apply (rule_tac x = "(\<tau>, \<tau>) # (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # Q_inhab" in bexI)
        apply (simp add: rely_def)
        apply (rule disjI1)
        apply (rule_tac x = "LNil" in exI)
        apply (rule_tac x = \<tau> in exI)
        apply (rule_tac x = \<tau> in exI)
        apply (rule_tac x = \<sigma> in exI)
        apply (simp_all add: \<tau>\<sigma>)
        apply auto
        apply (simp add: \<open>lfinite Q_inhab\<close>)
        apply (metis FIN_def FIN_test1 LCons_in_l_prod `Q_inhab \<in> test Q` lfinite_LCons lfinite_code(1) mem_Collect_eq)
        apply (rule subsetD[of "test Q"])
        by (simp_all add: test_guar `Q_inhab \<in> test Q`)
    qed
  qed
  hence "{sng (\<sigma>, \<sigma>) |\<sigma>. eval_bool_expr (Q[E\<bar>v]) \<sigma>} \<cdot> {w} \<subseteq> preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G"
    apply (simp add: w_def)
    apply (subst fin_l_prod)
    by (auto simp add: fin_l_prod FIN_def)
  thus "w \<in> test (Q[E\<bar>v]) \<rightharpoondown> (preserve (Q[E\<bar>v]) \<rhd> FIN \<cdot> test Q \<inter> guar ?G)"
    by (simp only: preimp_elem_var test_def Language2.test_def)
qed

lemma assignment_rule:
  assumes "R\<^sup>* \<subseteq> (\<P> (Q[E\<bar>v]))\<^sup>*"
  and "{(\<sigma>, (v \<leftarrow> E) \<sigma>)|\<sigma>. eval_bool_expr (Q[E\<bar>v]) \<sigma>}\<^sup>* \<subseteq> G\<^sup>*"
  and "test P \<subseteq> test (Q[E\<bar>v])"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> v := E \<lbrace>Q\<rbrace>"
  apply (simp add: quintuple_def)
  apply (rule subset_trans[OF refine_assignment[where Q = Q]])
  apply (rule preimp_mono[OF assms(3)])
  apply (rule Rely_mono[OF assms(1)])
  apply (rule Int_mono[OF order_refl])
  by (rule guar_mono[OF assms(2)])

(* ------------------------------------------------------------------------
   Sequential Composition
   ------------------------------------------------------------------------ *)

lemma tests_finite: "test P \<subseteq> \<F>"
  by (simp add: test_def tests_finite)

lemma test_preimp: "test P \<cdot> (test P \<rightharpoondown> X) \<subseteq> X"
  by (metis preimp_galois_3 tests_finite)

lemma test_inter_guar [simp]: "test P \<inter> guar G = test P"
  by (simp add: test_def)

lemma refine_sequential: "(test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test S \<inter> guar G)) \<cdot> (test S \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)) \<le> (test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G))"
  apply (subst preimp_galois_2[symmetric, OF tests_finite])
  apply (simp only: l_prod_assoc[symmetric])
  apply (rule subset_trans[OF l_prod_isol[OF test_preimp]])
  apply (simp only: guar_lprod test_inter_guar)
  apply (rule subset_trans[OF rely_l_prod_var])
  defer
  apply (simp only: l_prod_assoc)
  apply (rule subset_trans[OF prog_rely_iso[OF l_prod_isor[OF test_preimp]]])
  apply (rule subset_trans[OF prog_rely_iso[OF rely_l_prod_var2]])
  defer
  apply (rule subset_trans[OF rely_idem])
  apply (simp only: l_prod_assoc[symmetric] guar_lprod[symmetric])
  apply (rule subset_trans[OF prog_rely_iso[OF l_prod_isol[OF inter_isol[OF FIN_FIN]]]])
  by (rule order_refl)

lemma sequential_rule: "R, G \<turnstile> \<lbrace>P\<rbrace> x \<lbrace>S\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>S\<rbrace> y \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> x \<cdot> y \<lbrace>Q\<rbrace>"
  apply (simp add: quintuple_def)
  apply (subst subset_trans[where B = "(test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test S \<inter> guar G)) \<cdot> (test S \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G))"])
  apply (rule l_prod_mono)
  apply simp_all
  by (rule refine_sequential)

(* ------------------------------------------------------------------------
   If Statement
   ------------------------------------------------------------------------ *)

lemma one_test_pre: "test P \<cdot> X = {(\<sigma>,\<sigma>) # x |\<sigma> x. eval_bool_expr P \<sigma> \<and> x \<in> X}"
  apply (subst fin_l_prod)
  apply (metis tests_finite)
  apply (simp add: test_def)
  apply (auto simp add: Language2.test_def)
  by (metis lappend_code(1) lappend_code(2))

lemma two_tests_pre: "test P \<cdot> test S \<cdot> X = {(\<sigma>,\<sigma>) # (\<sigma>',\<sigma>') # x |\<sigma> \<sigma>' x. eval_bool_expr P \<sigma> \<and> eval_bool_expr S \<sigma>' \<and> x \<in> X}"
  apply (subst fin_l_prod)
  apply (metis tests_finite)
  apply (subst fin_l_prod)
  apply (simp add: test_def Language2.test_def FIN_def)
  apply (metis lfinite_LCons lfinite_code(1) lfinite_lappend)
  apply (auto simp add: test_def Language2.test_def)
  by (metis lappend_code(1) lappend_code(2))

lemma rely_cons_eq: "rely R (x # xs) (y # ys) \<Longrightarrow> x = y"
  apply (auto simp add: rely_def)
  apply (metis (erased, hide_lams) lappend_code(1) lappend_code(2) lhd_LCons llist.exhaust)
  by (metis (erased, hide_lams) lappend_code(1) lappend_code(2) lhd_LCons llist.exhaust)

definition fpres :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "fpres x y \<equiv> lfinite x = lfinite y"

lemma rely_fpres_def: "rely R x y \<equiv> (\<exists>z \<sigma> \<sigma>' \<tau> \<tau>' \<tau>'' x' y'. x = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>') # x')
                                       \<and> y = z \<frown> ((\<sigma>,\<sigma>') # (\<tau>,\<tau>'') # y')
                                       \<and> (\<sigma>',\<tau>) \<notin> (R\<^sup>*)
                                       \<and> lfinite z
                                       \<and> fpres x' y'
                                       \<and> env (R\<^sup>*) (z \<frown> ((\<sigma>,\<sigma>') # LNil))) \<or> x = y"
  by (simp add: fpres_def rely_def)

lemma rely_cons_lem: "rely R ((\<gamma>', \<gamma>') # x) ((\<gamma>', \<gamma>') # y) \<Longrightarrow> rely R ((\<gamma>, \<gamma>) # (\<gamma>', \<gamma>') # x) ((\<gamma>, \<gamma>) # (\<gamma>', \<gamma>') # y)"
  apply (cases "(\<gamma>, \<gamma>') \<in> R\<^sup>*")
  apply (auto simp add: rely_fpres_def)
  apply (rule_tac x = "(\<gamma>, \<gamma>) # z" in exI)
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
  apply (metis env_lem1 prod.sel(1) prod.sel(2))
  apply (rule_tac x = LNil in exI)
  apply (rule_tac x = \<gamma> in exI)
  apply (rule_tac x = \<gamma> in exI)
  apply (rule_tac x = \<gamma>' in exI)
  apply (rule_tac x = \<gamma>' in exI)
  apply (rule_tac x = \<gamma>' in exI)
  apply (rule_tac x = x in exI)
  apply simp_all
  apply (rule_tac x = y in exI)
  apply simp
  apply (simp add: fpres_def)
  by (metis lfinite_code(2) lfinite_lappend)

lemma stutter_1: "x \<in> FIN \<cdot> test Q \<inter> guar G \<Longrightarrow> rely R x ((\<sigma>', \<sigma>') # t') \<Longrightarrow> rely R ((\<sigma>, \<sigma>) # x) ((\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t')"
  apply (cases x)
  apply simp
  defer
  apply simp
  apply (frule rely_cons_eq)
  apply simp
  apply (metis rely_cons_lem)
proof -
  assume "rely R LNil ((\<sigma>', \<sigma>') # t')"
  hence False by (simp add: LNil_eq_lappend_iff rely_def)
  thus "rely R (sng (\<sigma>, \<sigma>)) ((\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t')" by meson
qed

lemma double_test1:
  assumes "\<And>t. t \<in> test P \<cdot> x \<Longrightarrow> t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
  and "t \<in> test S \<cdot> test P \<cdot> x"
  shows "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
proof -
  from assms(2)
  obtain \<sigma> \<sigma>' t'
  where "t = (\<sigma>,\<sigma>) # (\<sigma>',\<sigma>') # t'" and "t' \<in> x" and "eval_bool_expr S \<sigma>" and "eval_bool_expr P \<sigma>'"
    by (simp add: two_tests_pre) metis

  hence "(\<sigma>',\<sigma>') # t' \<in> test P \<cdot> x"
    by (simp add: one_test_pre)

  hence "(\<sigma>',\<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    by (metis assms(1))

  hence "(\<sigma>,\<sigma>) # (\<sigma>',\<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    apply (simp add: Rely_def)
    apply (erule bexE)
    apply (rule_tac x = "(\<sigma>,\<sigma>) # x" in bexI)
    apply (rule stutter_1)
    apply simp_all
    by (metis FIN_test1)

  thus ?thesis
    by (metis `t = (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t'`)
qed

lemma double_test2: "test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) \<le> test S \<cdot> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  apply (auto simp add: subset_iff preimp_def)
  apply (rule_tac x = x in exI)
  apply auto
  by (metis double_test1)

lemma mumble_lem1': "(\<sigma>',\<sigma>) \<in> R\<^sup>* \<Longrightarrow> rely R ((\<sigma>', \<sigma>') # x) ((\<sigma>', \<sigma>') # (\<sigma>, \<sigma>) # y) \<Longrightarrow> rely R x ((\<sigma>, \<sigma>) # y)"
  apply (simp add: rely_fpres_def)
  apply auto
  apply (subgoal_tac "\<exists>z'. z = (\<sigma>', \<sigma>') # z'")
  apply (erule exE)+
  apply simp
  apply (rule_tac x = z' in exI)
  apply (rule_tac x = \<sigma>'' in exI)
  apply (rule_tac x = \<sigma>''' in exI)
  apply (rule_tac x = \<tau> in exI)
  apply (rule_tac x = \<tau>' in exI)
  apply (rule_tac x = \<tau>'' in exI)
  apply (rule_tac x = x' in exI)
  apply simp
  apply (rule_tac x = y' in exI)
  apply simp
  apply (metis env_tl)
  apply (subgoal_tac "z = LNil \<or> (\<exists>\<gamma> \<gamma>' z''. z = (\<gamma>, \<gamma>') # z'')")
  apply (erule disjE)
  apply simp
  apply (erule exE)+
  apply simp
  by (metis llist.exhaust prod.collapse)

lemma mumble_lem1: "(\<sigma>',\<sigma>) \<in> R\<^sup>*  \<Longrightarrow> x \<in> FIN \<cdot> test Q \<inter> guar G \<Longrightarrow> rely R x ((\<sigma>', \<sigma>') # (\<sigma>, \<sigma>) # t') \<Longrightarrow> rely R (ltl x) ((\<sigma>, \<sigma>) # t')"
  apply (cases x)
  apply simp
  defer
  apply simp
  apply (frule rely_cons_eq)
  apply simp
  apply (metis mumble_lem1')
  by (smt LNil_eq_lappend_iff llist.distinct(1) rely_def)

lemma double_tests: "test P \<cdot> test Q = {(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # LNil |\<sigma> \<sigma>'. eval_bool_expr P \<sigma> \<and> eval_bool_expr Q \<sigma>'}"
  apply (auto simp add: test_def Language2.test_def l_prod_def)
  apply (metis lappend_code(1) lappend_code(2) lfinite_LCons lfinite_code(1))
  by (metis lappend_code(1) lappend_code(2) lfinite_LCons lfinite_code(1))

lemma triple_tests: "test P \<cdot> test Q \<cdot> test S = {(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # (\<sigma>'', \<sigma>'') # LNil |\<sigma> \<sigma>' \<sigma>''. eval_bool_expr P \<sigma> \<and> eval_bool_expr Q \<sigma>' \<and> eval_bool_expr S \<sigma>''}"
  apply (auto simp add: test_def Language2.test_def l_prod_def)
  by (metis lappend_code(1) lappend_code(2) lfinite_LCons lfinite_code(1))+

lemma preimp_2_l_prod: "Z \<subseteq> FIN \<Longrightarrow> Y \<subseteq> FIN \<Longrightarrow> X \<le> Y \<rightharpoondown> Z \<rightharpoondown> W \<longleftrightarrow> X \<le> Z \<cdot> Y \<rightharpoondown> W"
proof -
  assume a1: "Y \<subseteq> FIN"
  assume a2: "Z \<subseteq> FIN"
  hence "\<And>x\<^sub>1. FIN \<rightharpoondown> x\<^sub>1 \<subseteq> Z \<rightharpoondown> x\<^sub>1" by (simp add: preimp_antitone)
  hence "Z \<cdot> Y \<subseteq> FIN" using a1 a2 by (metis (no_types) FIN_FIN order_refl order_trans preimp_galois_2)
  thus "(X \<subseteq> Y \<rightharpoondown> Z \<rightharpoondown> W) = (X \<subseteq> Z \<cdot> Y \<rightharpoondown> W)" using a1 a2 by (metis (no_types) l_prod_assoc preimp_galois_2)
qed

lemma test2_conj':
  assumes "\<And>t. t \<in> test (P \<otimes> B) \<cdot> X \<Longrightarrow> t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
  and "t \<in> test P \<cdot> test B \<cdot> X"
  and "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  shows "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
proof -
  from `t \<in> test P \<cdot> test B \<cdot> X`
  obtain \<sigma> \<sigma>' t'
  where t_def: "t = (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t'" and "eval_bool_expr P \<sigma>" and "eval_bool_expr B \<sigma>'" and "t' \<in> X"
    by (simp add: two_tests_pre) metis

  from `test Q \<noteq> {}`
  obtain \<sigma>''
  where "eval_bool_expr Q \<sigma>''"
    by (auto simp add: test_def Language2.test_def)
  hence "sng (\<sigma>'', \<sigma>'') \<in> test Q"
    by (auto simp add: test_def Language2.test_def)

  {
    assume "(\<sigma>, \<sigma>') \<notin> (preserve P)\<^sup>*"

    hence "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      apply (auto simp add: Rely_def)
      apply (rule_tac x = "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # sng (\<sigma>'', \<sigma>'')" in bexI)
      apply (rule rely_antitone[OF `R\<^sup>* \<subseteq> (preserve P)\<^sup>*`])
      apply (simp add: rely_def)
      apply (rule disjI1)
      apply (rule_tac x = LNil in exI)
      apply (rule_tac x = \<sigma> in exI) apply (rule_tac x = \<sigma> in exI)
      apply (rule_tac x = \<sigma>' in exI)
      apply simp
      prefer 2
      apply (metis FIN_test1 FIN_test2 Int_iff `sng (\<sigma>'', \<sigma>'') \<in> test Q` guar_LCons_eq guar_singleton rtrancl.rtrancl_refl)
      sorry

    hence "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis t_def)
  }
  moreover
  {
    assume "(\<sigma>, \<sigma>') \<in> (preserve P)\<^sup>*"

    from preservation[OF `eval_bool_expr P \<sigma>` this] and `eval_bool_expr B \<sigma>'`
    have "sng (\<sigma>', \<sigma>') \<in> test (P \<otimes> B)"
      by (simp add: test_def Language2.test_def)

    hence "(\<sigma>', \<sigma>') # t' \<in> test (P \<otimes> B) \<cdot> X"
      by (metis LCons_in_l_prod `t' \<in> X`)

    hence "(\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis assms(1))

    hence "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      apply (simp add: Rely_def)
      apply (erule bexE)
      apply (rule_tac x = "(\<sigma>, \<sigma>) # x" in bexI)
      apply (metis stutter_1)
      apply auto
      by (metis FIN_test1)

    hence "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis t_def)
  }
  ultimately show ?thesis by blast
qed

lemma llength_ge_1: "llength x > 1 \<Longrightarrow> \<exists>x1 x2 x3. x = x1 # x2 # x3"
  by (metis eSuc_enat iless_Suc_eq less_imp_le llength_LCons llength_eq_0 llist.collapse(2) neq_iff one_eSuc zero_enat_def)

lemma post_ltl: "llength x > 1 \<Longrightarrow> x \<in> \<F> \<cdot> \<T> Q \<Longrightarrow> ltl x \<in> \<F> \<cdot> \<T> Q"
  apply (drule llength_ge_1)
  apply (erule exE)+
  apply simp
  apply (auto simp add: FIN_def l_prod_def test_def Language2.test_def)
  by (metis lappend_code(1) lfinite.simps llist.distinct(1) llist.sel(3) ltl_lappend)

lemma [simp]: "xa = x21 # x22 \<frown> ((\<sigma>', \<sigma>'') # (\<tau>, \<tau>') # x') \<Longrightarrow> z = x21 # x22 \<Longrightarrow> llength x22 + eSuc (eSuc (llength x')) \<noteq> 0"
  apply (cases x22)
  apply simp_all
  by (simp add: plus_enat_eq_0_conv)

lemma eSuc_0_llength_lem: "xa = z \<frown> ((\<sigma>', \<sigma>'') # (\<tau>, \<tau>') # x') \<Longrightarrow> eSuc 0 < llength xa"
  apply (cases z)
  by simp_all

lemma guar_ltl: "x \<in> guar G \<Longrightarrow> ltl x \<in> guar G"
  by (cases x) simp_all

lemma test2_conj'_opp_lem:
  "(\<sigma>, \<sigma>) # (\<sigma>, \<sigma>) # x \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G \<Longrightarrow> (\<sigma>, \<sigma>) # x \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
  apply (auto simp add: Rely_def)
  apply (rule_tac x = "ltl xa" in bexI)
  apply (meson Int_iff mumble_lem1 rtrancl.rtrancl_refl)
  apply auto
  apply (rule post_ltl)
  apply simp_all
  apply (simp add: rely_def)
  apply (erule disjE)
  prefer 2
  apply (simp_all add: one_eSuc)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (meson eSuc_0_llength_lem)
  by (metis guar_ltl)

lemma test2_conj'_opp:
  assumes "\<And>t. t \<in> test P \<cdot> test B \<cdot> X \<Longrightarrow> t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
  and "t \<in> test (P \<otimes> B) \<cdot> X"
  and "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  shows "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
proof -
  from `t \<in> test (P \<otimes> B) \<cdot> X`
  obtain \<sigma> t'
  where t_def: "t = (\<sigma>, \<sigma>) # t'" and "eval_bool_expr P \<sigma>" and "eval_bool_expr B \<sigma>" and "t' \<in> X"
    by (auto simp add: test_def Language2.test_def l_prod_def)

  from `test Q \<noteq> {}`
  obtain \<sigma>'
  where "eval_bool_expr Q \<sigma>'"
    by (auto simp add: test_def Language2.test_def)
  hence "sng (\<sigma>', \<sigma>') \<in> test Q"
    by (auto simp add: test_def Language2.test_def)

  from `eval_bool_expr P \<sigma>` and `eval_bool_expr B \<sigma>` and `t' \<in> X`
  have "(\<sigma>, \<sigma>) # (\<sigma>, \<sigma>) # t' \<in> test P \<cdot> test B \<cdot> X"
    apply (simp only: l_prod_assoc)
    apply (rule LCons_in_l_prod)
    apply (simp add: test_def Language2.test_def)
    apply (rule LCons_in_l_prod)
    apply (simp add: test_def Language2.test_def)
    by simp

  hence "(\<sigma>, \<sigma>) # (\<sigma>, \<sigma>) # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    using assms(1) by blast

  hence "(\<sigma>, \<sigma>) # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    using test2_conj'_opp_lem by blast

  then show ?thesis
    using t_def by blast
qed

lemma [simp]: "\<F> \<cdot> {} = {}"
  by (auto simp add: l_prod_def FIN_def)

lemma [simp]: "\<T> P \<cdot> {} = {}"
  by (auto simp add: l_prod_def test_def Language2.test_def)

lemma [simp]: "R \<rhd> {} = {}"
  by (auto simp add: Rely_def)

lemma test2_conj_var:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test (P \<otimes> B) \<noteq> {}"
  shows "test (P \<otimes> B) \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) \<subseteq> test P \<cdot> test B \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  apply (cases "test Q = {}")
  apply simp
  apply (cases "test P = {}")
  apply simp
  apply (cases "test B = {}")
  apply simp
  apply (subst preimp_zero_right)
  apply (rule assms(2))
  apply (subst preimp_zero_right)
  apply (metis FIN_l_prod empty_subsetI preimp_galois_2 preimp_zero_right subset_antisym)
  apply simp
  apply (simp add: preimp_def subset_iff)
  apply (intro allI impI)
  apply (erule exE)+
  apply (rule_tac x = x in exI)
  apply auto
  by (metis (mono_tags, hide_lams) all_not_in_conv assms(1) test2_conj')

lemma test2_conj:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  shows "test (P \<otimes> B) \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) \<subseteq> test P \<cdot> test B \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  apply (simp add: preimp_def subset_iff)
  apply (intro allI impI)
  apply (erule exE)+
  apply (rule_tac x = x in exI)
  apply auto
  apply (rule test2_conj')
  apply auto
  apply (metis assms(1) contra_subsetD)
  by (metis assms(2))

lemma test2_conj_opp:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  shows "test P \<cdot> test B \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) \<subseteq> test (P \<otimes> B) \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  apply (simp add: preimp_def subset_iff)
  apply (intro allI impI)
  apply (erule exE)+
  apply (rule_tac x = x in exI)
  apply auto
  apply (rule test2_conj'_opp)
  apply auto
  apply (metis assms(1) contra_subsetD)
  by (metis assms(2))

lemma test2_conj_eq:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  shows "test P \<cdot> test B \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) = test (P \<otimes> B) \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  by (simp add: assms(1) assms(2) subset_antisym test2_conj test2_conj_opp)

lemma empty_test_pair:
  assumes "test (P \<otimes> B) = {}"
  and "test Q \<noteq> {}"
  and "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  shows "test P \<cdot> test B \<cdot> X \<subseteq> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
proof (auto simp add: subset_iff)
  fix t
  assume "t \<in> test P \<cdot> test B \<cdot> X"

  then obtain \<sigma> \<sigma>' t'
  where "t = (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t'" and "eval_bool_expr P \<sigma>" and "eval_bool_expr B \<sigma>'" and "t' \<in> X"
    by (simp add: two_tests_pre) metis

  from `eval_bool_expr B \<sigma>'` and assms(1) have "\<not> eval_bool_expr P \<sigma>'"
    by (auto simp add: Language2.test_def test_def)

  from `test Q \<noteq> {}`
  obtain \<sigma>''
  where "eval_bool_expr Q \<sigma>''"
    by (auto simp add: Language2.test_def test_def)
  hence "sng (\<sigma>'', \<sigma>'') \<in> test Q"
    by (auto simp add: Language2.test_def test_def)

  hence "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    apply (auto simp add: Rely_def)
    apply (rule_tac x = "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # sng (\<sigma>'', \<sigma>'')" in bexI)
    apply (rule rely_antitone[OF assms(3)])
    apply (auto simp add: rely_def)
    apply (rule_tac x = LNil in exI)
    apply (rule_tac x = \<sigma> in exI) apply (rule_tac x = \<sigma> in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply (rule_tac x = "sng (\<sigma>'', \<sigma>'')" in exI)
    apply (intro conjI)
    apply simp
    apply (rule_tac x = "t'" in exI)
    apply simp_all
    apply (intro conjI)
    apply (metis `\<not> eval_bool_expr P \<sigma>'` `eval_bool_expr P \<sigma>` preservation)
    prefer 2
    apply (metis FIN_test1 FIN_test2)
    sorry

  thus "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    by (metis `t = (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t'`)
qed

lemma "test P = {} \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>Q\<rbrace>"
  by (auto simp add: quintuple_def)

lemma zero_rule: "R, G \<turnstile> \<lbrace>P\<rbrace> {} \<lbrace>Q\<rbrace>"
  by (simp add: quintuple_def)

lemma conj_empty: "test (P \<otimes> B) = {} \<Longrightarrow> test (P \<otimes> (BNot B)) = test P"
  by (auto simp add: test_def Language2.test_def)

lemma conj_empty2: "test (P \<otimes> BNot B) = {} \<Longrightarrow> test (P \<otimes> B) = test P"
  by (auto simp add: test_def Language2.test_def)

lemma test_to_precondition_var: "test (P \<otimes> B) \<noteq> {} \<Longrightarrow> R\<^sup>* \<subseteq> (preserve P)\<^sup>* \<Longrightarrow> R, G \<turnstile> \<lbrace>P \<otimes> B\<rbrace> X \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> test B \<cdot> X \<lbrace>Q\<rbrace>"
  apply (simp add: quintuple_def)
  apply (subst preimp_galois_2[symmetric])
  apply (simp add: tests_finite)
  apply (simp only: l_prod_assoc[symmetric])
  apply (subst preimp_galois_2)
  apply (simp add: tests_finite)
  apply (rule subset_trans[OF _ test2_conj_var])
  by simp_all

lemma test_to_precondition: "test Q \<noteq> {} \<Longrightarrow> R\<^sup>* \<subseteq> (preserve P)\<^sup>* \<Longrightarrow> R, G \<turnstile> \<lbrace>P \<otimes> B\<rbrace> X \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> test B \<cdot> X \<lbrace>Q\<rbrace>"
  apply (simp add: quintuple_def)
  apply (subst preimp_galois_2[symmetric])
  apply (simp add: tests_finite)
  apply (simp only: l_prod_assoc[symmetric])
  apply (subst preimp_galois_2)
  apply (simp add: tests_finite)
  apply (rule subset_trans[OF _ test2_conj])
  by simp_all

lemma FIN_l_prod_ex: "z \<in> FIN \<cdot> X \<Longrightarrow> \<exists>z'. z' \<in> X"
  by (auto simp add: FIN_def l_prod_def)

lemma test_conj_leq1: "test (P \<otimes> B) \<subseteq> test P"
  by (auto simp add: test_def Language2.test_def)

lemma test_conj_leq2: "test (B \<otimes> P) \<subseteq> test P"
  by (auto simp add: test_def Language2.test_def)

lemma test_conj_2:
  assumes "\<And>t. t \<in> test P \<cdot> X \<Longrightarrow> t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
  and "t \<in> test P \<cdot> test B \<cdot> X"
  and "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  shows "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
proof -
  from assms(2)
  obtain \<sigma> \<sigma>' t'
  where t_def: "t = (\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t'" and "eval_bool_expr P \<sigma>" and "eval_bool_expr B \<sigma>'" and "t' \<in> X"
    by (simp add: two_tests_pre) metis

  hence "(\<sigma>, \<sigma>) # t' \<in> test P \<cdot> X"
    apply -
    apply (rule LCons_in_l_prod)
    by (auto simp add: test_def Language2.test_def)

  hence "(\<sigma>, \<sigma>) # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
    by (metis assms(1))

  then obtain \<sigma>'' where "sng (\<sigma>'', \<sigma>'')  \<in> test Q"
    apply (auto simp add: Rely_def)
    apply (drule FIN_l_prod_ex)
    by (auto simp add: Language2.test_def test_def)

  {
    assume "(\<sigma>, \<sigma>') \<notin> (preserve P)\<^sup>*"

    hence "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      apply (auto simp add: Rely_def)
      apply (rule_tac x = "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # sng (\<sigma>'', \<sigma>'')" in bexI)
      apply (rule rely_antitone[OF `R\<^sup>* \<subseteq> (preserve P)\<^sup>*`])
      apply (simp add: rely_def)
      apply (rule disjI1)
      apply (rule_tac x = LNil in exI)
      apply (rule_tac x = \<sigma> in exI) apply (rule_tac x = \<sigma> in exI)
      apply (rule_tac x = \<sigma>' in exI)
      apply simp
      prefer 2
      apply (metis FIN_test1 FIN_test2 Int_iff `sng (\<sigma>'', \<sigma>'') \<in> test Q` guar_LCons_eq guar_singleton rtrancl.rtrancl_refl)
      sorry

    hence "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis t_def)
  }
  moreover
  {
    assume "(\<sigma>, \<sigma>') \<in> (preserve P)\<^sup>*"

    from preservation[OF `eval_bool_expr P \<sigma>` this] and `eval_bool_expr B \<sigma>'`
    have "sng (\<sigma>', \<sigma>') \<in> test (P \<otimes> B)"
      by (simp add: test_def Language2.test_def)

    hence "(\<sigma>', \<sigma>') # t' \<in> test (P \<otimes> B) \<cdot> X"
      by (metis LCons_in_l_prod `t' \<in> X`)

    also have "... \<subseteq> test P \<cdot> X"
      by (metis l_prod_isol test_conj_leq1)

    finally have "(\<sigma>', \<sigma>') # t' \<in> test P \<cdot> X" .

    hence "(\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis assms(1))

    hence "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # t' \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      apply (simp add: Rely_def)
      apply (erule bexE)
      apply (rule_tac x = "(\<sigma>, \<sigma>) # x" in bexI)
      apply (metis stutter_1)
      apply auto
      by (metis FIN_test1)

    hence "t \<in> R \<rhd> FIN \<cdot> test Q \<inter> guar G"
      by (metis t_def)
  }
  ultimately show ?thesis by blast
qed 

lemma test_conj_3:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  shows "test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G) \<subseteq> test P \<cdot> test B \<rightharpoondown> (R \<rhd> FIN \<cdot> test Q \<inter> guar G)"
  apply (simp add: subset_iff)
  apply (simp add: preimp_def)
  apply auto
  apply (rule_tac x = x in exI)
  apply (simp add: subset_iff)
  apply (intro allI impI)
  apply (rule test_conj_2)
  apply auto
  by (metis assms contra_subsetD)

lemma choice_rule:
  assumes "R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>Q\<rbrace>"
  and "R, G \<turnstile> \<lbrace>P\<rbrace> Y \<lbrace>Q\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> X \<union> Y \<lbrace>Q\<rbrace>"
  using assms
  by (simp add: quintuple_def)

lemma if_rule:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test Q \<noteq> {}"
  and "R, G \<turnstile> \<lbrace>P \<otimes> B\<rbrace> X \<lbrace>Q\<rbrace>"
  and "R, G \<turnstile> \<lbrace>P \<otimes> (BNot B)\<rbrace> Y \<lbrace>Q\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> test B \<cdot> X \<union> test (BNot B) \<cdot> Y \<lbrace>Q\<rbrace>"
  apply (rule choice_rule)
  apply (rule test_to_precondition)
  apply (simp_all add: assms)
  apply (rule test_to_precondition)
  by (simp_all add: assms)

lemma if_rule_var:
  assumes "R\<^sup>* \<subseteq> (preserve P)\<^sup>*"
  and "test (P \<otimes> B) \<noteq> {}"
  and "test (P \<otimes> BNot B) \<noteq> {}"
  and "R, G \<turnstile> \<lbrace>P \<otimes> B\<rbrace> X \<lbrace>Q\<rbrace>"
  and "R, G \<turnstile> \<lbrace>P \<otimes> (BNot B)\<rbrace> Y \<lbrace>Q\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> test B \<cdot> X \<union> test (BNot B) \<cdot> Y \<lbrace>Q\<rbrace>"
  apply (rule choice_rule)
  apply (rule test_to_precondition_var)
  apply (simp_all add: assms)
  apply (rule test_to_precondition_var)
  by (simp_all add: assms)

definition "skip \<equiv> {LNil}"

lemma remove_Rely: "X \<subseteq> Y \<Longrightarrow> X \<subseteq> R \<rhd> Y"
  by (metis Rely_ext Un_subset_iff sup.absorb1)

lemma skip_rule: "R, G \<turnstile> \<lbrace>P\<rbrace> skip \<lbrace>P\<rbrace>"
  apply (simp add: quintuple_def)
  apply (subst preimp_galois_2[symmetric])
  apply (simp add: tests_finite)
  apply (rule remove_Rely)
  apply (simp add: skip_def)
  apply auto
  apply (metis (erased, hide_lams) FIN_def contra_subsetD empty_subsetI insert_subset l_prod_isol lfinite_LNil mem_Collect_eq seq.mult.left_neutral)
  by (metis contra_subsetD test_def test_in_guar)

lemma star_inductl_one_skip: "skip \<union> x \<cdot> y \<subseteq> y \<Longrightarrow> x\<^sup>\<star> \<subseteq> y"
  apply (rule seq.star_inductl_one[rule_format])
  by (simp add: skip_def)

lemma refine_skip [simp]: "skip \<subseteq> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test P \<inter> guar G)"
  using skip_rule
  by (simp add: quintuple_def)

lemma star_rule:
  assumes "R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>P\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> X\<^sup>\<star> \<lbrace>P\<rbrace>"
  using assms
proof (simp add: quintuple_def)
  assume "X \<subseteq> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test P \<inter> guar G)"

  moreover have "(test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test P \<inter> guar G))\<^sup>\<star> \<subseteq> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test P \<inter> guar G)"
    by (rule star_inductl_one_skip[rule_format]) (simp add: refine_sequential)

  ultimately show "X\<^sup>\<star> \<subseteq> test P \<rightharpoondown> (R \<rhd> FIN \<cdot> test P \<inter> guar G)"
    by (metis (erased, hide_lams) inf.absorb2 inf_commute seq.star_ext seq.star_iso)
qed

lemma while_lem1:
  assumes "R\<^sup>* \<subseteq> (preserve I)\<^sup>*"
  and "test (BNot P \<otimes> I) \<noteq> {}"
  shows "test I \<cdot> test (BNot P) \<subseteq> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G"
proof -
  from assms(2) obtain \<sigma>''
  where "sng (\<sigma>'', \<sigma>'') \<in> test (BNot P \<otimes> I)"
    by (smt Collect_empty_eq mem_Collect_eq test_def Language2.test_def)

  {
    fix t
    assume "t \<in> test I \<cdot> test (BNot P)"

    then obtain \<sigma> \<sigma>'
    where t_def: "t = (\<sigma>, \<sigma>) # sng (\<sigma>', \<sigma>')" and "eval_bool_expr I \<sigma>" and "eval_bool_expr (BNot P) \<sigma>'"
      by (simp add: double_tests) blast

    {
      assume "(\<sigma>, \<sigma>') \<in> (preserve I)\<^sup>*"

      hence "eval_bool_expr I \<sigma>'"
        by (metis `eval_bool_expr I \<sigma>` preservation)

      hence "eval_bool_expr (BNot P \<otimes> I) \<sigma>'"
        by (metis `eval_bool_expr (BNot P) \<sigma>'` eval_bool_expr.simps(4))

      hence "sng (\<sigma>', \<sigma>') \<in> test (BNot P \<otimes> I)"
        by (simp add: test_def Language2.test_def)

      hence "(\<sigma>, \<sigma>) # sng (\<sigma>', \<sigma>') \<in> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G"
        apply (auto simp add: Rely_def)
        apply (rule_tac x = "(\<sigma>, \<sigma>) # sng (\<sigma>', \<sigma>')" in bexI)
        apply (rule rely_refl)
        apply auto
        by (metis FIN_test1 FIN_test2)

      hence "t \<in> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G"
        by (simp add: t_def)
    }
    moreover
    {
      assume "(\<sigma>, \<sigma>') \<notin> (preserve I)\<^sup>*"

      hence "(\<sigma>, \<sigma>) # sng (\<sigma>', \<sigma>') \<in> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G"
        apply (auto simp add: Rely_def)
        apply (rule_tac x = "(\<sigma>, \<sigma>) # (\<sigma>', \<sigma>') # sng (\<sigma>'',\<sigma>'')" in bexI)
        apply (simp add: rely_def)
        apply (rule_tac x = LNil in exI)
        apply (rule_tac x = \<sigma> in exI) apply (rule_tac x = \<sigma> in exI)
        apply (rule_tac x = \<sigma>' in exI)
        apply simp_all
        apply (metis assms(1) contra_subsetD)
        by (metis FIN_test1 FIN_test2 `sng (\<sigma>'', \<sigma>'') \<in> test (BNot P \<otimes> I)`)

      hence "t \<in> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G"
        by (simp add: t_def)
    }
    ultimately have "t \<in> R \<rhd> FIN \<cdot> test (BNot P \<otimes> I) \<inter> guar G" by blast
  }
  thus ?thesis
    by blast
qed

lemma "test P \<noteq> {} \<longleftrightarrow> (\<exists>\<sigma>. eval_bool_expr P \<sigma>)"
  by (auto simp add: test_def Language2.test_def)

lemma while_rule:
  assumes "R\<^sup>* \<subseteq> (preserve I)\<^sup>*"
  and "test (BNot P \<otimes> I) \<noteq> {}"
  and "test (I \<otimes> P) \<noteq> {}"
  and "R, G \<turnstile> \<lbrace>I \<otimes> P\<rbrace> X \<lbrace>I\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>I\<rbrace> (test P \<cdot> X)\<^sup>\<star> \<cdot> test (BNot P) \<lbrace>(BNot P) \<otimes> I\<rbrace>"
  apply (simp add: quintuple_def)
  apply (rule seq.star_inductl[rule_format])
  apply simp
  apply (intro conjI)
  apply (subst preimp_galois_2[symmetric])
  apply (simp add: tests_finite)
  apply (rule while_lem1[OF assms(1) assms(2)])
  using assms(4)
  apply (simp add: quintuple_def)
  apply (subst preimp_galois_2[symmetric])
  apply (simp add: tests_finite)
  apply (subst l_prod_assoc)
  apply (subst l_prod_assoc[symmetric])
  apply (subst preimp_galois_2)
  apply (simp add: tests_finite)
  apply (rule subset_trans[OF _ test2_conj_var[OF assms(1) assms(3)]])
  apply (rule subset_trans)
  prefer 2
  apply (rule refine_sequential[where S = "I"])
  by (metis l_prod_isol)

(* ------------------------------------------------------------------------
   Parallel Rule
   ------------------------------------------------------------------------ *)

lemma weakening:
  assumes "test P' \<subseteq> test P"
  and "test Q \<subseteq> test Q'"
  and "R'\<^sup>* \<subseteq> R\<^sup>*"
  and "G\<^sup>* \<subseteq> G'\<^sup>*"
  and "R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>Q\<rbrace>"
  shows "R', G' \<turnstile> \<lbrace>P'\<rbrace> X \<lbrace>Q'\<rbrace>"
  using assms
  apply (simp only: quintuple_def)
  apply (erule_tac subset_trans)
  apply (rule preimp_mono)
  apply simp
  apply (rule Rely_mono)
  apply simp
  by (metis guar_mono inf_mono l_prod_isor)

(* ------------------------------------------------------------------------
   Parallel Rule
   ------------------------------------------------------------------------ *)


lemma parallel_rule:
  assumes "(R \<union> G\<^sub>1)\<^sup>* \<subseteq> (R\<^sub>2)\<^sup>*"
  and "(R \<union> G\<^sub>2)\<^sup>* \<subseteq> R\<^sub>1\<^sup>*"
  and "(G\<^sub>1 \<union> G\<^sub>2)\<^sup>* \<subseteq> G\<^sup>*"
  and "R\<^sub>1, G\<^sub>1 \<turnstile> \<lbrace>P\<^sub>1\<rbrace> X \<lbrace>Q\<^sub>1\<rbrace>"
  and "R\<^sub>2, G\<^sub>2 \<turnstile> \<lbrace>P\<^sub>2\<rbrace> Y \<lbrace>Q\<^sub>2\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<^sub>1 \<otimes> P\<^sub>2\<rbrace> X \<parallel> Y \<lbrace>Q\<^sub>1 \<otimes> Q\<^sub>2\<rbrace>"
  sorry

lemma parallel_statement_rule:
  assumes "(R \<union> G\<^sub>1)\<^sup>* \<subseteq> (R\<^sub>2)\<^sup>*"
  and "(R \<union> G\<^sub>2)\<^sup>* \<subseteq> R\<^sub>1\<^sup>*"
  and "(G\<^sub>1 \<union> G\<^sub>2)\<^sup>* \<subseteq> G\<^sup>*"
  and "test P \<subseteq> test (P\<^sub>1 \<otimes> P\<^sub>2)"
  and "test (Q\<^sub>1 \<otimes> Q\<^sub>2) \<subseteq> test Q"
  and "R\<^sub>1, G\<^sub>1 \<turnstile> \<lbrace>P\<^sub>1\<rbrace> X \<lbrace>Q\<^sub>1\<rbrace>"
  and "R\<^sub>2, G\<^sub>2 \<turnstile> \<lbrace>P\<^sub>2\<rbrace> Y \<lbrace>Q\<^sub>2\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> parallel { X } meanwhile { Y } \<lbrace>Q\<rbrace>"
  sorry

lemma preimp_dist: "(X \<union> Y) \<rightharpoondown> Z \<le> (X \<rightharpoondown> Z) \<union> (Y \<rightharpoondown> Z)"
  by (auto simp add: preimp_def)

lemma preimp_dist_var: "(X \<rightharpoondown> Z) \<inter> (Y \<rightharpoondown> Z) \<le> (X \<union> Y) \<rightharpoondown> Z"
 apply (auto simp add: preimp_def)
 apply (rule_tac x = "Xa \<inter> Xaa" in exI)
  by (meson Int_iff dual_order.trans inf_le1 inf_le2 l_prod_isor)
  
lemma skip_preimp [simp]: "{LNil} \<rightharpoondown> X = X"
  by (auto simp add: preimp_def)

lemma preimp_star1: "X\<^sup>\<star> \<rightharpoondown> Y \<subseteq> X \<rightharpoondown> Y"
  by (rule preimp_mono) (auto simp add: seq.star_ext)

lemma preimp_star2: "X \<subseteq> \<F> \<Longrightarrow> X \<cdot> (X\<^sup>\<star> \<rightharpoondown> Y) \<subseteq> Y"
  by (simp add: preimp_galois_2 preimp_star1)

lemma Rely_preimp: "R \<rhd> (P \<rightharpoondown> Q) \<le> P \<rightharpoondown> (R \<rhd> Q)"
  apply (auto simp add: preimp_def Rely_continuous)
  apply (rule_tac x = "R \<rhd> Xa" in exI)
  apply auto
  by (meson prog_rely_iso rely_l_prod_var2 subsetCE)

end
