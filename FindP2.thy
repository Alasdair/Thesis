theory FindP2                        
  imports Verification2 "~~/src/HOL/Eisbach/Eisbach"
begin                              

definition while_loop :: "bool_expr \<Rightarrow> program \<Rightarrow> program" ("while _ do { _ }" [51] 55) where
  "while B do { P } \<equiv> (test B; P)\<^sup>\<star> ; test (BNot B)"

lemma while_loop_rule:
  assumes "R\<^sup>* \<subseteq> (preserve I)\<^sup>*"
  and "test (BNot B \<otimes> I) \<noteq> {}"
  and "test (I \<otimes> B) \<noteq> {}"
  and "test P \<subseteq> test I" and "test (BNot B \<otimes> I) \<subseteq> test Q"
  and "R, G \<turnstile> \<lbrace>I \<otimes> B\<rbrace> X \<lbrace>I\<rbrace>"
  shows "R, G \<turnstile> \<lbrace>P\<rbrace> while B do { X } \<lbrace>Q\<rbrace>"
  apply (simp add: while_loop_def sequential_composition_def)
  apply (rule_tac P = "I" and Q = "BNot B \<otimes> I" in weakening)  
  apply (rule assms(4))
  apply (rule assms(5))
  apply (rule order.refl)
  apply (rule order.refl)
  apply (rule while_rule)
  apply (simp_all add: assms)
  done

definition if_statement :: "bool_expr \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" ("if _ { _ } else { _ }" [51,51,51] 55) where
  "if P { X } else { Y } \<equiv> (test P; X) \<union> (test (BNot P); Y)"

lemma if_statement_rule:
  "R\<^sup>* \<subseteq> (\<P> P)\<^sup>* \<Longrightarrow> \<T> Q \<noteq> {} \<Longrightarrow> R, G \<turnstile> \<lbrace>P \<otimes> B\<rbrace> X \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P \<otimes> BNot B\<rbrace> Y \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> if B { X } else { Y } \<lbrace>Q\<rbrace>"
  apply (simp only: if_statement_def sequential_composition_def)
  apply (rule if_rule)
  by simp_all

definition lessthan :: "var \<Rightarrow> var \<Rightarrow> bool_expr" (infix "less than" 71) where
  "x less than y \<equiv> BExpr2 (op <) (Var x) (Var y)"

definition par_A :: "(nat \<Rightarrow> bool) \<Rightarrow> program" where
"par_A P \<equiv>
i\<^sub>A := Const 0;
while (i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B) do {
  if BExpr1 P (Lookup (Var i\<^sub>A)) {
    f\<^sub>A := Var i\<^sub>A
  } else {
    i\<^sub>A := BinOp (op +) (Var i\<^sub>A) (Const 2)
  }
}
"

definition par_B :: "(nat \<Rightarrow> bool) \<Rightarrow> program" where
"par_B P \<equiv>
i\<^sub>B := Const 1;
while (i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B) do {
  if BExpr1 P (Lookup (Var i\<^sub>B)) {
    f\<^sub>B := Var i\<^sub>B
  } else {
    i\<^sub>B := BinOp (op +) (Var i\<^sub>B) (Const 2)
  }
}
"

definition findp :: "(nat \<Rightarrow> bool) \<Rightarrow> program" where
"findp P \<equiv>
f\<^sub>A := ALen;
f\<^sub>B := ALen;
parallel {
  i\<^sub>A := Const 0;
  while (i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B) do {
    if BExpr1 P (Lookup (Var i\<^sub>A)) {
      f\<^sub>A := Var i\<^sub>A
    } else {
      i\<^sub>A := BinOp (op +) (Var i\<^sub>A) (Const 2)
    }
  }
} meanwhile {
  i\<^sub>B := Const 1;
  while (i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B) do {
    if BExpr1 P (Lookup (Var i\<^sub>B)) {
      f\<^sub>B := Var i\<^sub>B
    } else {
      i\<^sub>B := BinOp (op +) (Var i\<^sub>B) (Const 2)
    }
  }
};
fmax := BinOp min (Var f\<^sub>A) (Var f\<^sub>B)
"

lemma sequential_rule2: "R, G \<turnstile> \<lbrace>P\<rbrace> x \<lbrace>S\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>S\<rbrace> y \<lbrace>Q\<rbrace> \<Longrightarrow> R, G \<turnstile> \<lbrace>P\<rbrace> x; y \<lbrace>Q\<rbrace>"
  by (metis sequential_composition_def sequential_rule)

lemma [simp]: "Id \<subseteq> X\<^sup>*"
  by (metis empty_subsetI rtrancl_empty rtrancl_mono)

definition "invariant_A P \<equiv>
  BArray (\<lambda>i arr. \<forall>i'. i' < i \<and> even i' \<longrightarrow> \<not> P (arr ! i')) (Var i\<^sub>A)
  \<otimes> BExpr1 even (Var i\<^sub>A)
  \<otimes> BArray (\<lambda>i arr. i < length arr \<longrightarrow> P (arr ! i)) (Var f\<^sub>A)
  \<otimes> BExpr2 (op <) (Var f\<^sub>A) (BinOp (op +) ALen (Const 1))"

definition "invariant_B P \<equiv>
  BArray (\<lambda>i arr. \<forall>i'. i' < i \<and> odd i' \<longrightarrow> \<not> P (arr ! i')) (Var i\<^sub>B)
  \<otimes> BExpr1 odd (Var i\<^sub>B)
  \<otimes> BArray (\<lambda>i arr. i < length arr \<longrightarrow> P (arr ! i)) (Var f\<^sub>B)
  \<otimes> BExpr2 (op <) (Var f\<^sub>B) (BinOp (op +) ALen (Const 1))"

definition "loop_post P \<equiv>
  BExpr2 (op <) (BinOp min (Var f\<^sub>A) (Var f\<^sub>B)) (BinOp (op +) ALen (Const 1))
  \<otimes> BArray (\<lambda>fmax arr. \<forall>i. i < fmax \<longrightarrow> \<not> P (arr ! i)) (BinOp min (Var f\<^sub>A) (Var f\<^sub>B))
  \<otimes> BArray (\<lambda>fmax arr. fmax < length arr \<longrightarrow> P (arr ! fmax)) (BinOp min (Var f\<^sub>A) (Var f\<^sub>B))"

lemma [simp]: "(x::nat) < y \<Longrightarrow> min x y = x"
  by auto

lemma 
  findp_while_res1:
  "test (invariant_A P \<otimes> invariant_B P \<otimes> BNot ((i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B)) \<otimes> BNot ((i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B))) \<subseteq> test (loop_post P)"
  apply (simp add: invariant_A_def invariant_B_def loop_post_def lessthan_def)
  apply clarify
proof -
  fix s :: store

  def A \<equiv> "s_A s"
  def ia \<equiv> "s_i\<^sub>A s"
  def ib \<equiv> "s_i\<^sub>B s"
  def fa \<equiv> "s_f\<^sub>A s"
  def fb \<equiv> "s_f\<^sub>B s"

  thm A_def

  assume "\<forall>i'. i' < s_i\<^sub>A s \<and> even i' \<longrightarrow> \<not> P (s_A s ! i')"
  and "even (s_i\<^sub>A s)"
  and "s_f\<^sub>A s < length (s_A s) \<longrightarrow> P (s_A s ! s_f\<^sub>A s)"
  and "s_f\<^sub>A s < Suc (length (s_A s))"
  and "\<forall>i'. i' < s_i\<^sub>B s \<and> odd i' \<longrightarrow> \<not> P (s_A s ! i')"
  and "odd (s_i\<^sub>B s)"
  and "s_f\<^sub>B s < length (s_A s) \<longrightarrow> P (s_A s ! s_f\<^sub>B s)"
  and "s_f\<^sub>B s < Suc (length (s_A s))"
  and "\<forall>i'. i' < s_i\<^sub>A s \<and> even i' \<longrightarrow> \<not> P (s_A s ! i')"
  and "s_i\<^sub>A s < s_f\<^sub>A s \<longrightarrow> \<not> s_i\<^sub>A s < s_f\<^sub>B s"
  and "s_i\<^sub>B s < s_f\<^sub>A s \<longrightarrow> \<not> s_i\<^sub>B s < s_f\<^sub>B s"
  thus "min (s_f\<^sub>A s) (s_f\<^sub>B s) < Suc (length (s_A s)) \<and>
        (\<forall>i. i < s_f\<^sub>A s \<and> i < s_f\<^sub>B s \<longrightarrow> \<not> P (s_A s ! i)) \<and>
        (min (s_f\<^sub>A s) (s_f\<^sub>B s) < length (s_A s) \<longrightarrow> P (s_A s ! min (s_f\<^sub>A s) (s_f\<^sub>B s)))"
    apply -
    apply (simp only: A_def[symmetric] ia_def[symmetric] ib_def[symmetric] fa_def[symmetric] fb_def[symmetric])
    apply (cases "fa < fb")
    apply simp
    apply (intro conjI allI)
    apply (intro impI allI)
    apply (erule conjE)
    apply (subgoal_tac "even i \<or> odd i")
    prefer 2
    apply metis
    apply (erule disjE)
    apply (metis le_less_trans not_less)
    apply (metis le_less_trans not_less)
    apply (cases "fb < fa")
    apply simp
    apply (intro conjI allI)
    apply (metis min.commute min.strict_coboundedI2)
    apply (intro impI allI)
    apply (erule conjE)
    apply (subgoal_tac "even i \<or> odd i")
    prefer 2
    apply metis
    apply (erule disjE)
    apply (metis le_less_trans not_less)
    apply (metis le_less_trans not_less)
    apply (metis min_def)
    apply (subgoal_tac "fa = fb")
    prefer 2
    apply (metis linorder_neqE_nat)
    apply simp
    apply (intro conjI allI impI)
    by (metis le_less_trans not_less)
qed

lemma
  findp_parallel_postcondition:
  "test ((BNot ((i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B)) \<otimes> invariant_A P) \<otimes> (BNot ((i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B)) \<otimes> invariant_B P)) \<subseteq> test (loop_post P)"
  apply (rule subset_trans)
  prefer 2
  apply (rule findp_while_res1)
  by simp


lemma test_conj_split: "\<T> P \<subseteq> \<T> (Q \<otimes> S) \<longleftrightarrow> \<T> P \<subseteq> \<T> Q \<and> \<T> P \<subseteq> \<T> S"
  apply (auto simp add: test_def Language2.test_def subset_iff)
  apply (metis llast_singleton prod.inject)
  apply (metis llast_singleton prod.inject)
  done

definition "rely_A P \<equiv> {(\<sigma>, \<sigma>') |\<sigma> \<sigma>'.
  s_A \<sigma> = s_A \<sigma>'
\<and> s_f\<^sub>A \<sigma> = s_f\<^sub>A \<sigma>'
\<and> s_i\<^sub>A \<sigma> = s_i\<^sub>A \<sigma>'
\<and> ((P (s_A \<sigma>' ! s_f\<^sub>B \<sigma>') \<and> (\<forall>v<s_f\<^sub>B \<sigma>'. odd v \<longrightarrow> \<not> P (s_A \<sigma>' ! v)) \<and> s_f\<^sub>B \<sigma>' < s_f\<^sub>B \<sigma> \<and> s_f\<^sub>B \<sigma>' = s_i\<^sub>B \<sigma>' \<and> s_i\<^sub>B \<sigma> = s_i\<^sub>B \<sigma>') \<or> (s_i\<^sub>B \<sigma>' < s_i\<^sub>B \<sigma> \<and> s_f\<^sub>B \<sigma> = length (s_A \<sigma>) \<longrightarrow> s_f\<^sub>B \<sigma>' = length (s_A \<sigma>')))}"

definition "rely_B P \<equiv> {(\<sigma>, \<sigma>') |\<sigma> \<sigma>'.
  s_A \<sigma> = s_A \<sigma>'
\<and> s_f\<^sub>B \<sigma> = s_f\<^sub>B \<sigma>'
\<and> s_i\<^sub>B \<sigma> = s_i\<^sub>B \<sigma>'
\<and> ((P (s_A \<sigma>' ! s_f\<^sub>A \<sigma>') \<and> (\<forall>v<s_f\<^sub>A \<sigma>'. even v \<longrightarrow> \<not> P (s_A \<sigma>' ! v)) \<and> s_f\<^sub>A \<sigma>' < s_f\<^sub>A \<sigma> \<and> s_f\<^sub>A \<sigma>' = s_i\<^sub>A \<sigma>' \<and> s_i\<^sub>A \<sigma> = s_i\<^sub>A \<sigma>') \<or> (s_i\<^sub>A \<sigma>' < s_i\<^sub>A \<sigma> \<and> s_f\<^sub>A \<sigma> = length (s_A \<sigma>) \<longrightarrow> s_f\<^sub>A \<sigma>' = length (s_A \<sigma>')))}"

lemma preserve_split: "X \<subseteq> \<P> P \<and> X \<subseteq> \<P> Q \<Longrightarrow> X \<subseteq> \<P> (P \<otimes> Q)"
  by (auto simp add: preserve_def subset_iff)

lemma state_existence: "\<T> X \<noteq> {} \<longleftrightarrow> (\<exists>\<sigma>. eval_bool_expr X \<sigma>)"
  by (auto simp add: test_def Language2.test_def)

lemma par_A_proof:
  shows "rely_A P,
         rely_B P \<turnstile>
         \<lbrace>BExpr2 (op =) (Var f\<^sub>A) ALen\<rbrace>
           par_A P
         \<lbrace>BNot (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) \<otimes> invariant_A P\<rbrace>"
  apply (simp add: par_A_def)
  apply (rule_tac S = "BExpr2 (op =) (Var f\<^sub>A) ALen \<otimes> BExpr2 (op =) (Var i\<^sub>A) (Const 0)" in sequential_rule2)
  apply (rule assignment_rule)
  defer
  apply simp
  apply (rule rtrancl_mono)
  apply (simp add: subset_iff store.defs rely_B_def)
  apply simp
  apply (rule_tac I = "invariant_A P" in while_loop_rule)
  defer
  defer
  defer
  apply (simp add: invariant_A_def)
  defer
  apply (simp add: lessthan_def invariant_A_def)
  apply (rule_tac P = "BArray (\<lambda>i arr. \<forall>i'. i' < i \<and> even i' \<longrightarrow> \<not> P (arr ! i')) (Var i\<^sub>A) \<otimes> BExpr1 even (Var i\<^sub>A) \<otimes>
        BArray (\<lambda>i arr. i < length arr \<longrightarrow> P (arr ! i)) (Var f\<^sub>A) \<otimes>
        BExpr2 op < (Var f\<^sub>A) (BinOp op + ALen (Const (Suc 0))) \<otimes>
        BExpr2 op < (Var i\<^sub>A) (Var f\<^sub>A)" in weakening)
  apply simp
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule if_statement_rule)
  defer
  defer
  apply (rule_tac Q = "invariant_A P \<otimes> BExpr1 P (Lookup (Var i\<^sub>A))" in weakening)
  apply (rule order.refl)
  apply (simp add: invariant_A_def)
  apply (rule order.refl)
  apply (rule order.refl)
  apply (rule assignment_rule)
  defer
  apply (rule rtrancl_mono)
  apply (simp add: store.defs subset_iff lessthan_def invariant_A_def rely_B_def)
  apply (simp add: invariant_A_def)
  apply (rule assignment_rule)
  defer
  apply (rule rtrancl_mono)
  apply (simp add: store.defs subset_iff lessthan_def rely_B_def)
  apply (simp add: invariant_A_def)
  apply (metis even_Suc linorder_neqE_nat not_less_eq)
  prefer 5
  apply simp
  apply (rule rtrancl_mono)
  apply (simp add: rely_A_def preserve_def subset_iff)
  apply (rule rtrancl_mono)
  apply (simp add: rely_A_def preserve_def subset_iff invariant_A_def)
  prefer 3
  apply (rule rtrancl_mono)
  apply (simp add: rely_A_def preserve_def subset_iff)
  prefer 4
  apply (rule rtrancl_mono)
  apply (simp add: rely_A_def preserve_def subset_iff invariant_A_def)
  prefer 4
  apply (rule rtrancl_mono)
  apply (simp add: rely_A_def preserve_def subset_iff)
  apply (simp_all only: state_existence)
  apply (simp add: lessthan_def invariant_A_def)
  apply (rule_tac x = "store.make 0 0 0 0 0 []" in exI)
  apply (simp add: store.defs)
  apply (simp add: lessthan_def invariant_A_def)
  apply (rule_tac x = "store.make 1 1 0 0 0 [1]" in exI)
  apply (simp add: store.defs)
  apply (simp add: lessthan_def invariant_A_def)
  apply (rule_tac x = "store.make 0 0 0 0 0 []" in exI)
  by (simp add: store.defs)

lemma odd_Suc: "odd (Suc x) = even x"
  by (cases x) simp_all

lemma par_B_proof:
  shows "rely_B P,
         rely_A P \<turnstile>
         \<lbrace>BExpr2 (op =) (Var f\<^sub>B) ALen\<rbrace>
           par_B P
         \<lbrace>BNot (i\<^sub>B less than f\<^sub>A \<otimes> i\<^sub>B less than f\<^sub>B) \<otimes> invariant_B P\<rbrace>"
  apply (simp add: par_B_def)
  apply (rule_tac S = "BExpr2 (op =) (Var f\<^sub>B) ALen \<otimes> BExpr2 (op =) (Var i\<^sub>B) (Const 1)" in sequential_rule2)
  apply (rule assignment_rule)
  defer
  apply simp
  apply (rule rtrancl_mono)
  apply (simp add: subset_iff store.defs rely_A_def)
  apply simp
  apply (rule_tac I = "invariant_B P" in while_loop_rule)
  defer
  defer
  defer
  apply (simp add: invariant_B_def)
  defer
  apply (simp add: lessthan_def invariant_B_def)
  apply (rule_tac P = "BArray (\<lambda>i arr. \<forall>i'. i' < i \<and> odd i' \<longrightarrow> \<not> P (arr ! i')) (Var i\<^sub>B) \<otimes> BExpr1 odd (Var i\<^sub>B) \<otimes>
        BArray (\<lambda>i arr. i < length arr \<longrightarrow> P (arr ! i)) (Var f\<^sub>B) \<otimes>
        BExpr2 op < (Var f\<^sub>B) (BinOp op + ALen (Const (Suc 0))) \<otimes>
        BExpr2 op < (Var i\<^sub>B) (Var f\<^sub>B)" in weakening)
  apply (simp add: invariant_B_def lessthan_def)
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule if_statement_rule)
  defer
  defer
  apply (rule_tac Q = "invariant_B P \<otimes> BExpr1 P (Lookup (Var i\<^sub>B))" in weakening)
  apply (rule order.refl)
  apply (simp add: invariant_B_def)
  apply (rule order.refl)
  apply (rule order.refl)
  apply (rule assignment_rule)
  defer
  apply (rule rtrancl_mono)
  apply (simp add: store.defs subset_iff lessthan_def invariant_B_def rely_A_def)
  apply (simp add: invariant_B_def)
  apply (rule assignment_rule)
  defer
  apply (rule rtrancl_mono)
  apply (simp add: store.defs subset_iff lessthan_def rely_A_def)
  apply (simp add: invariant_B_def)
  apply (metis less_antisym odd_Suc)
  prefer 5
  apply simp
  apply (rule rtrancl_mono)
  apply (simp add: rely_B_def preserve_def subset_iff)
  apply (rule rtrancl_mono)
  apply (simp add: rely_B_def preserve_def subset_iff invariant_B_def)
  prefer 3
  apply (rule rtrancl_mono)
  apply (simp add: rely_B_def preserve_def subset_iff)
  prefer 4
  apply (rule rtrancl_mono)
  apply (simp add: rely_B_def preserve_def subset_iff invariant_B_def)
  prefer 4
  apply (rule rtrancl_mono)
  apply (simp add: rely_B_def preserve_def subset_iff)
  apply (simp_all only: state_existence)
  apply (simp add: lessthan_def invariant_B_def)
  apply (rule_tac x = "store.make 1 1 1 1 1 [1]" in exI)
  apply (simp add: store.defs)
  apply (rule_tac x = "store.make 3 3 1 1 3 [1,2,3]" in exI)
  apply (simp only: lessthan_def invariant_B_def store.defs)
  apply (simp add: invariant_B_def)
  apply (rule_tac x = "store.make 3 3 1 1 3 [1,2,3]" in exI)
  by (simp add: store.defs)

find_theorems name: parallel

lemma "
{},
UNIV \<turnstile>
\<lbrace>\<zero>\<rbrace>
  findp P
\<lbrace>BExpr2 (op <) (Var fmax) (BinOp (op +) ALen (Const 1))
 \<otimes> BArray (\<lambda>fmax arr. \<forall>i. i < fmax \<longrightarrow> \<not> P (arr ! i)) (Var fmax)
 \<otimes> BArray (\<lambda>fmax arr. fmax < length arr \<longrightarrow> P (arr ! fmax)) (Var fmax)\<rbrace>"
  apply (simp add: findp_def)
  apply (rule_tac S = "BExpr2 (op =) (Var f\<^sub>A) ALen" in sequential_rule2)
  apply (rule assignment_rule)
  apply simp
  apply simp
  apply simp
  apply (rule_tac S = "BExpr2 (op =) (Var f\<^sub>A) ALen \<otimes> BExpr2 (op =) (Var f\<^sub>B) ALen" in sequential_rule2)
  apply (rule assignment_rule)
  apply simp
  apply simp
  apply simp
  apply (rule_tac S = "loop_post P" in sequential_rule2)
  prefer 2
  apply (rule assignment_rule)
  apply simp
  apply simp
  apply (simp add: loop_post_def)
  apply (rule_tac R\<^sub>1 = "rely_A P" and G\<^sub>1 = "rely_B P" and R\<^sub>2 = "rely_B P" and G\<^sub>2 = "rely_A P" in parallel_statement_rule)
  apply simp
  apply simp
  apply simp
  apply (rule order_refl)
  apply (rule findp_parallel_postcondition)
  apply (simp_all only: par_A_def[symmetric] par_B_def[symmetric,simplified])
  apply (rule par_A_proof)
  apply (rule par_B_proof)
  done

no_notation Fixpoint.pleq (infix "\<sqsubseteq>" 50)

definition refinement_order :: "program \<Rightarrow> program \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<equiv> y \<le> x"

lemma refine: "x \<le> y \<Longrightarrow> y \<sqsubseteq> x"
  by (simp add: refinement_order_def)

lemma refine_refl [simp]: "x \<sqsubseteq> x"
  by (auto intro: refine)

(* no_notation residual_r (infixr "\<rightarrow>" 60) *)
notation preimp (infixr "\<rightarrow>" 65)

lemma tactic_sequential: "\<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<sqsubseteq> (\<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> S \<inter> guar G)) ; (\<T> S \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G))"
  by (simp add: sequential_composition_def) (rule refine[OF refine_sequential])

lemma verify: "R, G \<turnstile> \<lbrace>P\<rbrace> X \<lbrace>Q\<rbrace> \<Longrightarrow> \<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<sqsubseteq> X"
  by (simp add: quintuple_def refinement_order_def)

lemma verify_refine: "R, G \<turnstile> \<lbrace>P\<rbrace> \<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<lbrace>Q\<rbrace>"
  by (simp add: quintuple_def)

lemma tactic_parallel:
  assumes "(R \<union> G\<^sub>1)\<^sup>* \<subseteq> R\<^sub>2\<^sup>*"
  and "(R \<union> G\<^sub>2)\<^sup>* \<subseteq> R\<^sub>1\<^sup>*"
  and "(G\<^sub>1 \<union> G\<^sub>2)\<^sup>* \<subseteq> G\<^sup>*"
  and "\<T> P \<subseteq> \<T> (P\<^sub>1 \<otimes> P\<^sub>2)"
  and "\<T> (Q\<^sub>1 \<otimes> Q\<^sub>2) \<subseteq> \<T> Q"
  shows "\<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<sqsubseteq>
         parallel {
           \<T> P\<^sub>1 \<rightarrow> (R\<^sub>1 \<rhd> \<F> \<cdot> \<T> Q\<^sub>1 \<inter> guar G\<^sub>1)
         } meanwhile {
           \<T> P\<^sub>2 \<rightarrow> (R\<^sub>2 \<rhd> \<F> \<cdot> \<T> Q\<^sub>2 \<inter> guar G\<^sub>2)
         }"
  apply (rule verify)
  apply (rule parallel_statement_rule[OF assms(1) assms(2) assms(3) assms(4) assms(5)])
  by (rule verify_refine)+

lemma tactic_while:
  assumes "\<T> P \<subseteq> \<T> I"
  and "R\<^sup>* \<subseteq> (\<P> I)\<^sup>*"
  and "\<T> (BNot B \<otimes> I) \<noteq> {}"
  and "\<T> (I \<otimes> B) \<noteq> {}"
  shows "\<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> (BNot B \<otimes> I) \<inter> guar G) \<sqsubseteq> while B do { \<T> (I \<otimes> B) \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> I \<inter> guar G) }"
  apply (rule verify)
  apply (rule while_loop_rule[OF assms(2) assms(3) assms(4) assms(1)])
  apply simp
  by (rule verify_refine)

lemma tactic_if:
  assumes "R\<^sup>* \<subseteq> (\<P> P)\<^sup>*"
  and "\<T> Q \<noteq> {}"
  shows "\<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<sqsubseteq>
         if B {
           \<T> (P \<otimes> B) \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G)
         } else {
           \<T> (P \<otimes> BNot B) \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G)
         }"
  apply (rule verify)
  apply (rule if_statement_rule[OF assms(1) assms(2)])
  by (rule verify_refine)+

lemma seq_isol: "X \<sqsubseteq> Z \<Longrightarrow> X; Y \<sqsubseteq> Z; Y"
  by (simp add: refinement_order_def sequential_composition_def) (simp add: l_prod_isol)

lemma seq_isor: "X \<sqsubseteq> Z \<Longrightarrow> Y; X \<sqsubseteq> Y; Z"
  by (simp add: refinement_order_def sequential_composition_def) (simp add: l_prod_isor)

lemma par_isol: "X \<sqsubseteq> Z \<Longrightarrow> parallel { X } meanwhile { Y } \<sqsubseteq> parallel { Z } meanwhile { Y }"
  by (simp add: refinement_order_def parallel_composition_def par.mult_isor)

lemma par_isor: "X \<sqsubseteq> Z \<Longrightarrow> parallel { Y } meanwhile { X } \<sqsubseteq> parallel { Y } meanwhile { Z }"
  by (simp add: refinement_order_def parallel_composition_def par.mult_isol)

lemma if_isol: "X \<sqsubseteq> Z \<Longrightarrow> if B { X } else { Y } \<sqsubseteq> if B { Z } else { Y }"
  apply (simp add: if_statement_def)
  by (metis l_prod_isor par.add_left_idem refinement_order_def sequential_composition_def sup.mono sup_ge2)

lemma if_isor: "X \<sqsubseteq> Z \<Longrightarrow> if B { Y } else { X } \<sqsubseteq> if B { Y } else { Z }"
  apply (simp add: if_statement_def)
  by (metis Un_upper1 l_prod_isor refinement_order_def sequential_composition_def sup.mono sup.right_idem)

lemma while_body_iso: "X \<sqsubseteq> Z \<Longrightarrow> while B do { X } \<sqsubseteq> while B do { Z }"
  apply (simp add: while_loop_def refinement_order_def sequential_composition_def)
  apply (rule l_prod_isol)
  apply (rule seq.star_iso[rule_format])
  apply (rule l_prod_isor)
  by simp

lemma [trans]: "X \<sqsubseteq> Y \<Longrightarrow> Y \<sqsubseteq> Z \<Longrightarrow> X \<sqsubseteq> Z"
  by (simp add: refinement_order_def)

method isotonicity =
  (rule seq_isol | rule seq_isor | rule par_isol | rule par_isor | rule while_body_iso | rule if_isol | rule if_isor)+

method refine uses add =
  isotonicity?;
  ( rule tactic_sequential
  | (rule tactic_parallel; (simp_all only: add)?; simp_all?)
  | rule tactic_while
  | rule tactic_if
  )

method verify uses add =
  isotonicity?;
  (rule verify);
  (rule assignment_rule);
  ((rule rtrancl_mono)?; (simp add: add))+

method verify_no_simp =
  isotonicity?;
  (rule verify);
  (rule assignment_rule);
  (rule rtrancl_mono)?

definition "postcondition P  \<equiv> BExpr2 (op <) (Var fmax) (BinOp (op +) ALen (Const 1)) \<otimes> BArray (\<lambda>fmax arr. \<forall>i. i < fmax \<longrightarrow> \<not> P (arr ! i)) (Var fmax) \<otimes> BArray (\<lambda>fmax arr. fmax < length arr \<longrightarrow> P (arr ! fmax)) (Var fmax)"

abbreviation equality_test (infix "equals" 71) where "x equals y \<equiv> BExpr2 (op =) x y" 

abbreviation "MIN x y \<equiv> BinOp min x y"

abbreviation ADD_function (infix "ADD" 71) where "x ADD y \<equiv> BinOp (op +) x y"

lemma weaken_precondition: "\<T> P' \<le> \<T> P \<Longrightarrow> \<T> P' \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G) \<sqsubseteq> \<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G)"
  by (simp add: preimp_antitone refine)

lemma weaken_postcondition: "\<T> Q \<le> \<T> Q' \<Longrightarrow> \<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q' \<inter> guar G) \<sqsubseteq> \<T> P \<rightarrow> (R \<rhd> \<F> \<cdot> \<T> Q \<inter> guar G)"
  apply (rule refine)
  apply (rule preimp_iso)
  apply (rule Rely_mono)
  apply simp
  by (meson inter_isol l_prod_isor)

method weakening uses add =
  isotonicity?;
  (rule weaken_precondition | rule weaken_postcondition)

lemma findp_refine: "\<T> \<zero> \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV) \<sqsubseteq> findp P"
  (is "?specification \<sqsubseteq> _")
proof -
  have "?specification \<sqsubseteq>
    \<T> \<zero> \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (Var f\<^sub>A equals ALen) \<inter> guar UNIV);
    \<T> (Var f\<^sub>A equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV)"
    by refine
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    \<T> (Var f\<^sub>A equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV)"
    by verify
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    \<T> (Var f\<^sub>A equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (Var f\<^sub>A equals ALen \<otimes> Var f\<^sub>B equals ALen) \<inter> guar UNIV);
    \<T> (Var f\<^sub>A equals ALen \<otimes> Var f\<^sub>B equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV)"
    by refine
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    \<T> (Var f\<^sub>A equals ALen \<otimes> Var f\<^sub>B equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV)"
    by verify
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    \<T> (Var f\<^sub>A equals ALen \<otimes> Var f\<^sub>B equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (loop_post P) \<inter> guar UNIV);
    \<T> (loop_post P) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (postcondition P) \<inter> guar UNIV)"
    by refine
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    \<T> (Var f\<^sub>A equals ALen \<otimes> Var f\<^sub>B equals ALen) \<rightarrow> ({} \<rhd> \<F> \<cdot> \<T> (loop_post P) \<inter> guar UNIV);
    fmax := MIN (Var f\<^sub>A) (Var f\<^sub>B)"
    by (verify add: loop_post_def postcondition_def)
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    parallel {
      \<T> (Var f\<^sub>A equals ALen) \<rightarrow>
        (rely_A P \<rhd> \<F> \<cdot> \<T> (BNot ((i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B)) \<otimes> invariant_A P) \<inter> guar (rely_B P))
    } meanwhile {
      \<T> (Var f\<^sub>B equals ALen) \<rightarrow>
        (rely_B P \<rhd> \<F> \<cdot> \<T> (BNot ((i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B)) \<otimes> invariant_B P) \<inter> guar (rely_A P))
    };
    fmax := MIN (Var f\<^sub>A) (Var f\<^sub>B)"
    (is "_ \<sqsubseteq> _; _; parallel { ?specification_A } meanwhile { ?specification_B }; _")
    by (refine add: findp_parallel_postcondition)
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    parallel {
      par_A P
    } meanwhile {
      \<T> (Var f\<^sub>B equals ALen) \<rightarrow>
        (rely_B P \<rhd> \<F> \<cdot> \<T> (BNot ((i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B)) \<otimes> invariant_B P) \<inter> guar (rely_A P))
    };
    fmax := MIN (Var f\<^sub>A) (Var f\<^sub>B)"
  proof isotonicity
    let ?if_pre = "
        BArray (\<lambda>i arr. \<forall>i'. i' < i \<and> even i' \<longrightarrow> \<not> P (arr ! i')) (Var i\<^sub>A) \<otimes>
        BExpr1 even (Var i\<^sub>A) \<otimes>
        BArray (\<lambda>i arr. i < length arr \<longrightarrow> P (arr ! i)) (Var f\<^sub>A) \<otimes>
        BExpr2 op < (Var f\<^sub>A) (BinOp op + ALen (Const (Suc 0))) \<otimes>
        BExpr2 op < (Var i\<^sub>A) (Var f\<^sub>A)"

    have "?specification_A \<sqsubseteq>
      \<T> (Var f\<^sub>A equals ALen) \<rightarrow>
        (rely_A P \<rhd> \<F> \<cdot> \<T> (Var f\<^sub>A equals ALen \<otimes> Var i\<^sub>A equals Const 0) \<inter> guar (rely_B P));
      \<T> (Var f\<^sub>A equals ALen \<otimes> Var i\<^sub>A equals Const 0) \<rightarrow>
        (rely_A P \<rhd> \<F> \<cdot> \<T> (BNot (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) \<otimes> invariant_A P) \<inter> guar (rely_B P))"
      by refine
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      \<T> (Var f\<^sub>A equals ALen \<otimes> Var i\<^sub>A equals Const 0) \<rightarrow>
        (rely_A P \<rhd> \<F> \<cdot> \<T> (BNot (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) \<otimes> invariant_A P) \<inter> guar (rely_B P))"
      by (verify add: subset_iff preserve_def rely_A_def store.defs rely_B_def test_def Language2.test_def)
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        \<T> (invariant_A P \<otimes> (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B)) \<rightarrow>
          (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
      }"
      apply refine
      apply (simp add: invariant_A_def)
      apply (rule rtrancl_mono)
      apply (simp add: preserve_def invariant_A_def subset_iff rely_A_def)
      apply (simp_all only: state_existence)
      apply (simp add: lessthan_def invariant_A_def)
      apply (rule_tac x = "store.make 0 0 0 0 0 []" in exI)
      apply (simp add: store.defs)
      apply (simp add: lessthan_def invariant_A_def)
      apply (rule_tac x = "store.make 1 1 0 0 0 [1]" in exI)
      by (simp add: store.defs)
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        \<T> ?if_pre \<rightarrow> (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
      }"
      by weakening (simp add: invariant_A_def lessthan_def)
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>A)) {
          \<T> (?if_pre \<otimes> BExpr1 P (Lookup (Var i\<^sub>A))) \<rightarrow>
            (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
        } else {
          \<T> (?if_pre \<otimes> BNot (BExpr1 P (Lookup (Var i\<^sub>A)))) \<rightarrow>
            (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
        }
      }"
      apply refine
      apply (rule rtrancl_mono)
      apply (simp add: rely_A_def preserve_def subset_iff)
      apply (simp add: state_existence invariant_A_def)
      apply (rule_tac x = "store.make 0 0 0 0 0 []" in exI)
      by (simp add: store.defs)
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>A)) {
          \<T> (?if_pre \<otimes> BExpr1 P (Lookup (Var i\<^sub>A))) \<rightarrow>
            (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P \<otimes> BExpr1 P (Lookup (Var i\<^sub>A))) \<inter> guar (rely_B P))
        } else {
          \<T> (?if_pre \<otimes> BNot (BExpr1 P (Lookup (Var i\<^sub>A)))) \<rightarrow>
            (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
        }
      }"
      by weakening simp
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>A)) {
          f\<^sub>A := Var i\<^sub>A
        } else {
          \<T> (?if_pre \<otimes> BNot (BExpr1 P (Lookup (Var i\<^sub>A)))) \<rightarrow>
            (rely_A P \<rhd> \<F> \<cdot> \<T> (invariant_A P) \<inter> guar (rely_B P))
        }
      }"
      apply (verify add: rely_A_def preserve_def subset_iff invariant_A_def
                         test_def Language2.test_def rely_B_def store.defs)
      by auto
    also have "... \<sqsubseteq>
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A \<otimes> i\<^sub>A less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>A)) {
          f\<^sub>A := Var i\<^sub>A
        } else {
          i\<^sub>A := Var i\<^sub>A ADD Const 2 
        }
      }"
      apply (verify add: rely_A_def preserve_def subset_iff invariant_A_def
                         test_def Language2.test_def rely_B_def store.defs)
      using less_Suc_eq by auto
    also have "... \<sqsubseteq> par_A P"
      by (simp add: par_A_def)
    finally show "?specification_A \<sqsubseteq> par_A P" .
  qed
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    parallel {
      par_A P
    } meanwhile {
      par_B P
    };
    fmax := MIN (Var f\<^sub>A) (Var f\<^sub>B)"
    by isotonicity (auto intro: verify par_B_proof)
  also have "... \<sqsubseteq>
    f\<^sub>A := ALen;
    f\<^sub>B := ALen;
    parallel {
      i\<^sub>A := Const 0;
      while (i\<^sub>A less than f\<^sub>A) \<otimes> (i\<^sub>A less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>A)) {
          f\<^sub>A := Var i\<^sub>A
        } else {
          i\<^sub>A := Var i\<^sub>A ADD Const 2
        }
      }
    } meanwhile {
      i\<^sub>B := Const 1;
      while (i\<^sub>B less than f\<^sub>A) \<otimes> (i\<^sub>B less than f\<^sub>B) do {
        if BExpr1 P (Lookup (Var i\<^sub>B)) {
          f\<^sub>B := Var i\<^sub>B
        } else {
          i\<^sub>B := Var i\<^sub>B ADD Const 2
        }
      }
    };
    fmax := MIN (Var f\<^sub>A) (Var f\<^sub>B)"
    by (simp add: par_A_def par_B_def)
  also have "... \<sqsubseteq> findp P"
    by (simp add: findp_def)

  finally show "?specification \<sqsubseteq> findp P" .
qed
   