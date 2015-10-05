theory SKAT_Euclid
  imports SKAT_Eval GCD
begin

datatype alph = mod_alph | plus_alph | mult_alph | minus_alph | nat_alph nat | eq_alph

lemma alph_UNIV: "UNIV = {mod_alph,eq_alph,plus_alph,mult_alph,minus_alph} \<union> (nat_alph ` UNIV)"
  by (auto simp add: image_def, metis alph.exhaust)

instantiation alph :: ranked_alphabet
begin

  fun arity_alph :: "alph \<Rightarrow> nat" where
    "arity_alph mod_alph = 2"
  | "arity_alph plus_alph = 2"
  | "arity_alph mult_alph = 2"
  | "arity_alph minus_alph = 2"
  | "arity_alph eq_alph = 2"
  | "arity_alph is_gcd_alph = 0"
  | "arity_alph (nat_alph _) = 0"

  definition funs_alph :: "alph set" where "funs_alph \<equiv> {mod_alph,plus_alph,mult_alph,minus_alph} \<union> (nat_alph ` UNIV)"

  definition rels_alph :: "alph set" where "rels_alph \<equiv> {eq_alph}"

  definition NULL_alph :: "alph" where "NULL_alph \<equiv> nat_alph 0"

  declare funs_alph_def [alphabet]
    and rels_alph_def [alphabet]
    and NULL_alph_def [alphabet]

  definition output_vars_alph :: "alph itself \<Rightarrow> nat set" where "output_vars_alph x \<equiv> {0}"

  declare output_vars_alph_def [alphabet]

  instance proof
    show "(funs :: alph set) \<inter> rels = {}"
      by (auto simp add: funs_alph_def rels_alph_def)

    show "(funs :: alph set) \<union> rels = UNIV"
      by (auto simp add: funs_alph_def rels_alph_def alph_UNIV)

    show "(funs :: alph set) \<noteq> {}"
      by (simp add: funs_alph_def)

    show "(rels :: alph set) \<noteq> {}"
      by (simp add: rels_alph_def)

    show "NULL \<in> (funs :: alph set)"
      by (simp add: NULL_alph_def funs_alph_def)

    show "arity (NULL::alph) = 0"
      by (simp add: NULL_alph_def)

    show "\<exists>x. x \<in> output_vars TYPE(alph)"
      by (metis (mono_tags) insertI1 output_vars_alph_def)

    show "finite (output_vars TYPE(alph))"
      by (metis (hide_lams, mono_tags) atLeastLessThan0 finite_atLeastLessThan finite_insert output_vars_alph_def)
  qed
end

definition MOD :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "MOD a b \<equiv> (App mod_alph [a, b])"

definition PLUS :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "PLUS a b = (App plus_alph [a, b])"

definition EQ :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph pred" where
  "EQ x y \<equiv> Pred eq_alph [x, y]"

definition NAT :: "nat \<Rightarrow> alph trm" where
  "NAT n \<equiv> App (nat_alph n) []"

definition MULT :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "MULT a b = (App mult_alph [a, b])"

definition MINUS :: "alph trm \<Rightarrow> alph trm \<Rightarrow> alph trm" where
  "MINUS a b = (App minus_alph [a, b])"

fun euclid_funs :: "alph \<Rightarrow> nat list \<Rightarrow> nat" where
  "euclid_funs mod_alph [x, y] = x mod y"
| "euclid_funs plus_alph [x, y] = x + y"
| "euclid_funs mult_alph [x, y] = x * y"
| "euclid_funs minus_alph [x, y] = x - y"
| "euclid_funs (nat_alph n) [] = n"
| "euclid_funs _ _ = 0"

inductive_set euclid_rels :: "alph \<Rightarrow> nat relation" for a :: "alph" where
  "a = eq_alph \<Longrightarrow> [x,x] \<in> euclid_rels a"

lemma [simp]: "[x, y] \<in> euclid_rels eq_alph \<longleftrightarrow> x = y"
  by (metis (lifting) euclid_rels.simps list.inject)

abbreviation EUCLID :: "(alph, nat) interp" where "EUCLID \<equiv> \<lparr>interp_fun = euclid_funs, interp_rel = euclid_rels\<rparr>"

interpretation interp EUCLID done

definition SIMPLE_LOOP :: "alph skat" where
  "SIMPLE_LOOP \<equiv>
   WHILE !(pred (EQ (Var 0) (NAT 5))) DO
     0 := PLUS (Var 0) (NAT 1)
   WEND"

definition GCD :: "alph skat" where
  "GCD \<equiv>
   WHILE !(pred (EQ (Var 1) (NAT 0))) DO
     2 := Var 1;
     1 := MOD (Var 0) (Var 1);
     0 := Var 2
   WEND"

abbreviation hoare_triple_notation :: "nat mems \<Rightarrow> alph skat \<Rightarrow> nat mems \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [54,54,54] 53) where
  "hoare_triple_notation \<equiv> interp.hoare_triple EUCLID"

abbreviation module_notation :: "nat mems \<Rightarrow> alph skat \<Rightarrow> nat mems" (infix "\<Colon>" 75) where
  "module_notation \<Delta> x \<equiv> interp.module EUCLID \<Delta> x"

lemma helper: "\<lbrakk>\<And>x. P x = Q x\<rbrakk> \<Longrightarrow> {x. P x} = {x. Q x}"
  by auto

lemma set_mem_UNIV [simp]: "set_mems x (\<lambda>mem. m) UNIV = {mem. m = mem x}"
  by (auto simp add: set_mems_def image_def set_mem_def) (rule_tac x = xa in exI, auto)

lemma satisfies_assign: "satisfies x (op = m) = UNIV \<Colon> x := NAT m"
  by (simp add: satisfies_def module_def NAT_def, transfer, simp add: assigns_def)

lemma skat_assign3_var: "r = t[x|s] \<Longrightarrow> (x := s \<cdot> x := t) = (x := r)"
  by (metis skat_assign3)

lemma [simp]: "satisfies x P \<subseteq> satisfies x Q \<longleftrightarrow> (\<forall>mem. P (mem x) \<longrightarrow> Q (mem x))"
  by (auto simp add: satisfies_def)

lemma [simp]: "UNIV \<Colon> pred_expr (BLeaf (EQ (Var n) (NAT m))) = satisfies n (op = m)"
  apply (simp add: module_def EQ_def NAT_def satisfies_def)
  apply transfer
  apply auto
  by (metis empty_iff singleton_iff)

lemma [simp]: "UNIV \<Colon> pred_expr (BNot (BLeaf (EQ (Var n) (NAT m)))) = satisfies n (op \<noteq> m)"
  apply (simp add: module_def EQ_def NAT_def satisfies_def)
  apply transfer
  apply auto
  by (metis empty_iff singleton_iff)

declare pred_to_expr [simp]
declare pred_expr_not [simp]

lemma [simp]: "pred_expr (BNot (BNot P)) = pred_expr P"
  apply (subst pred_expr_not[symmetric])+
  by (metis hba.double_neg not_to_not pred_expr_test)

declare pred_expr_closed [simp]

fun initial_mem :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "initial_mem x y 0 = x"
| "initial_mem x y (Suc 0) = y"
| "initial_mem x y _ = 0"

declare pred_to_expr [simp]
declare pred_expr_not [simp]
declare Nat.One_nat_def [simp del]

no_notation
  dioid.one ("1\<index>") and
  dioid.zero ("0\<index>")

ML {*

structure HoareSimpRules = Named_Thms
  (val name = @{binding "hoare_simp"}
   val description = "Simplification rules for the hoare tactic")

structure HoareRules = Named_Thms
  (val name = @{binding "hoare_rule"}
   val description = "Extra Hoare Rules")

fun hoare_step_tac ctxt n =
  rtac @{thm hoare_assignment} n THEN TRY (rtac @{thm subset_refl} n)
  ORELSE (rtac @{thm hoare_while_inv} n THEN asm_full_simp_tac (simpset_of ctxt) 1)
  ORELSE (FIRST' (map (fn thm => rtac thm) (HoareRules.get ctxt)) n)

val hoare_tac = Subgoal.FOCUS (fn {context, ...} =>
  REPEAT (hoare_step_tac context 1)
  THEN auto_tac (map_simpset (fn ss => ss addsimps HoareSimpRules.get context) context))

*}

setup {* HoareSimpRules.setup *}
setup {* HoareRules.setup *}

declare hoare_composition[hoare_rule]
declare hoare_if[hoare_rule]

method_setup hoare_auto = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT (CHANGED (hoare_tac ctxt 1))))
*}

declare assigns_def [hoare_simp]
declare set_mems_def [hoare_simp]
declare image_def [hoare_simp]
declare set_mem_def [hoare_simp]
declare satisfies_def [hoare_simp]
declare MOD_def [hoare_simp]
declare PLUS_def [hoare_simp]
declare MINUS_def [hoare_simp]
declare MULT_def [hoare_simp]

lemma euclids_algorithm:
  "\<lbrace>{mem. mem 0 = x \<and> mem 1 = y}\<rbrace>
  WHILE !(pred (EQ (Var 1) (NAT 0)))
  INVARIANT {mem. gcd (mem 0) (mem 1) = gcd x y}
  DO
    2 := Var 1;
    1 := MOD (Var 0) (Var 1);
    0 := Var 2
  WEND
  \<lbrace>{mem. mem 0 = gcd x y}\<rbrace>"
  by hoare_auto (metis gcd_red_nat)

lemma [simp]: "eval_trm EUCLID mem (NAT x) = x"
  by (simp add: NAT_def)

lemma [simp]: "UNIV \<Colon> pred_expr (BLeaf (EQ (Var n) (Var m))) = {mem. mem n = mem m}"
  by (auto simp add: mod_pred_expr EQ_def) (metis empty_iff singleton_iff)+

lemma [simp]: "UNIV \<Colon> pred_expr (BNot (BLeaf (EQ (Var n) (Var m)))) = {mem. mem n \<noteq> mem m}"
  by (auto simp add: mod_pred_expr EQ_def) (metis empty_iff singleton_iff)+

lemma repeated_addition:
  "\<lbrace>{mem. mem 0 = x \<and> mem 1 = y}\<rbrace>
  2 := NAT 0;
  3 := NAT 0;
  (WHILE !(pred (EQ (Var 2) (Var 0)))
  INVARIANT {mem. mem 3 = mem 2 * mem 1 \<and> mem 0 = x \<and> mem 1 = y}
  DO
    3 := PLUS (Var 3) (Var 1);
    2 := PLUS (Var 2) (NAT 1)
  WEND)
  \<lbrace>{mem. mem 3 = (x * y)}\<rbrace>"
  by hoare_auto smt

lemma factorial:
  "\<lbrace>{mem. mem 0 = x}\<rbrace>
  1 := NAT 1;
  (WHILE !(pred (EQ (Var 0) (NAT 0)))
  INVARIANT {mem. fact x = mem 1 * fact (mem 0)}
  DO
    1 := MULT (Var 1) (Var 0); 0 := MINUS (Var 0) (NAT 1)
  WEND)
  \<lbrace>{mem. mem 1 = fact x}\<rbrace>"
  by hoare_auto (metis fact_reduce_nat)

end
