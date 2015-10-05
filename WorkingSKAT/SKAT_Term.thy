theory SKAT_Term
  imports KAT Boolean_Algebra_Extras
begin

section {* SKAT Terms *}

(* +------------------------------------------------------------------------+ *)
subsection {* Ranked Alphabets *}
(* +------------------------------------------------------------------------+ *)

class ranked_alphabet =
  fixes arity :: "'a \<Rightarrow> nat"
  and funs :: "'a set"
  and rels :: "'a set"
  and NULL :: 'a
  and output_vars :: "'a itself \<Rightarrow> nat set"
  assumes funs_rels_disjoint: "funs \<inter> rels = {}"
  and funs_rels_union: "funs \<union> rels = UNIV"
  and funs_exist: "funs \<noteq> {}"
  and rels_exist: "rels \<noteq> {}"
  and NULL_fun: "NULL \<in> funs"
  and NULL_arity: "arity NULL = 0"
  and output_exists: "\<exists>x. x \<in> output_vars TYPE('a)"
  and output_finite: "finite (output_vars TYPE('a))"

text {* A ranked alphabet consists of a set of disjoint function and
relation symbols. Each symbol in the alphabet has an associated
arity. The set @{const funs} contains all the function symbols, while
@{const rels} contains all the relation symbols. The @{const arity}
function returns the arity of a symbol.

Ranked alphabets are formalised as a typeclass, so a concrete alphabet
is simply a type which supports the above functions and the typeclass
laws. This avoids having to parameterise defintions with alphabets,
which allows things to stay at the type level. *}

(* +------------------------------------------------------------------------+ *)
subsection {* Terms *}
(* +------------------------------------------------------------------------+ *)

datatype 'a trm = App 'a "'a trm list" | Var nat

fun trm_vars :: "'a trm \<Rightarrow> nat set" where
  "trm_vars (App f xs) = \<Union> (set (map trm_vars xs))"
| "trm_vars (Var v) = {v}"

fun trm_subst :: "nat \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" where
  "trm_subst v s (Var v') = (if v' = v then s else Var v')"
| "trm_subst v s (App f xs) = App f (map (trm_subst v s) xs)"

inductive_set wf_trms :: "'a::ranked_alphabet trm set" where
  var: "Var n \<in> wf_trms"
| func: "\<lbrakk>f \<in> funs; arity f = n; xs \<in> lists wf_trms; length xs = n\<rbrakk> \<Longrightarrow> App f xs \<in> wf_trms"

lemma trm_subterms: "App f xs \<in> wf_trms \<Longrightarrow> xs \<in> lists wf_trms"
  by (metis (lifting) trm.simps(1) trm.simps(4) wf_trms.simps)

lemma trm_subterms_var: "App f xs \<in> wf_trms \<Longrightarrow> set xs \<subseteq> wf_trms"
  by (metis in_lists_conv_set subset_code(1) trm_subterms)

lemma map_in_lists: "map f xs \<in> lists X \<longleftrightarrow> f ` set xs \<subseteq> X"
  by (metis in_lists_conv_set in_mono set_map subsetI)

lemma trm_subst_wf: "\<lbrakk>s \<in> wf_trms; x \<in> wf_trms\<rbrakk> \<Longrightarrow> trm_subst v s x \<in> wf_trms"
proof (rule wf_trms.induct[of x "\<lambda>x. trm_subst v s x \<in> wf_trms"], safe)
  fix n assume "s \<in> wf_trms" and "x \<in> wf_trms" thus "trm_subst v s (Var n) \<in> wf_trms"
    by (metis trm_subst.simps(1) wf_trms.var)
next
  fix f :: "'a::ranked_alphabet" and xs :: "'a trm list"
  assume s_trm: "s \<in> wf_trms" and x_trm: "x \<in> wf_trms" and f_fun: "f \<in> funs"
  and xs_len: "length xs = arity f"
  and ind_hyp: "\<forall>x\<in>set xs. x \<in> wf_trms \<inter> {x. trm_subst v s x \<in> wf_trms}"
  show "trm_subst v s (App f xs) \<in> wf_trms"
  proof (simp, rule wf_trms.func[of _ "length xs"])
    show "f \<in> funs" using f_fun .
    show "arity f = length xs" by (simp add: xs_len)
    show "map (trm_subst v s) xs \<in> lists wf_trms"
      by (simp add: map_in_lists image_def, auto, metis Int_Collect ind_hyp)
    show "length (map (trm_subst v s) xs) = length xs"
      by (metis length_map)
  qed
qed

lemma wf_trms_const: "\<lbrakk>f \<in> funs; arity f = 0\<rbrakk> \<Longrightarrow> App f [] \<in> wf_trms"
  by (rule wf_trms.func, simp_all add: lists_def)

(* +------------------------------------------------------------------------+ *)
subsection {* n-tuples *}
(* +------------------------------------------------------------------------+ *)

text {* Given a set, generate all posible $n$-tuples of a specific
length. Here we represent an $n$-tuple as a list. *}

fun ntuples :: "'a set \<Rightarrow> nat \<Rightarrow> ('a list) set" ("_\<^bsup>_\<^esup>") where
  "X\<^bsup>0\<^esup> = {[]}"
| "X\<^bsup>Suc n\<^esup> = {x. \<exists>y\<in>X. \<exists>ys\<in>X\<^bsup>n\<^esup>. x = y#ys}"

lemma ntuples1: "set xs \<subseteq> X \<longleftrightarrow> xs \<in> X\<^bsup>length xs\<^esup>" by (induct xs, simp_all)

lemma ntuples2: "\<lbrakk>set xs \<subseteq> X; length xs = n\<rbrakk> \<Longrightarrow> xs \<in> X\<^bsup>n\<^esup>" by (metis ntuples1)

lemma ntuples3: "xs \<in> X\<^bsup>length xs\<^esup> \<Longrightarrow> set xs \<subseteq> X"
  by (induct xs, simp_all)

lemma ntuples4: "xs \<in> X\<^bsup>n\<^esup> \<Longrightarrow> length xs = n"
  apply (induct X n arbitrary: xs rule: ntuples.induct)
  by (simp_all, metis Suc_length_conv)

lemma ntuples5 [iff]: "xs \<in> X\<^bsup>n\<^esup> \<longleftrightarrow> (set xs \<subseteq> X \<and> length xs = n)"
  by (metis ntuples1 ntuples4)

lemma ntuples6: "(x \<in> X \<and> xs \<in> X\<^bsup>n\<^esup>) \<longleftrightarrow> x#xs \<in> X\<^bsup>Suc n\<^esup>" by simp

lemma ntuples7: "n \<noteq> 0 \<longleftrightarrow> [] \<notin> X\<^bsup>n\<^esup>"
  by (induct n, simp_all)

lemma ntuples_set: "X\<^bsup>n\<^esup> = {xs. set xs \<subseteq> X \<and> length xs = n}" by auto

type_synonym 'a relation = "('a list) set"

(* +------------------------------------------------------------------------+ *)
subsection {* Interpretation and term evaluation *}
(* +------------------------------------------------------------------------+ *)

record ('a, 'b) interp =
  interp_fun :: "'a \<Rightarrow> 'b list \<Rightarrow> 'b"
  interp_rel :: "'a \<Rightarrow> 'b relation"

type_synonym 'a mem = "nat \<Rightarrow> 'a"

fun eval_trm :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> 'a trm \<Rightarrow> 'b" where
  "eval_trm D mem (Var n) = mem n"
| "eval_trm D mem (App f xs) = interp_fun D f (map (eval_trm D mem) xs)"

definition null :: "'a::ranked_alphabet trm" where
  "null \<equiv> App NULL []"

abbreviation trm_subst_notation :: "'a::ranked_alphabet trm \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'a trm"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> trm_subst x t s"

(* +------------------------------------------------------------------------+ *)
subsection {* Predicates *}
(* +------------------------------------------------------------------------+ *)

datatype 'a pred = Pred 'a "'a trm list"

inductive_set wf_preds :: "'a::ranked_alphabet pred set" where
  "\<lbrakk>P \<in> rels; arity P = length xs\<rbrakk> \<Longrightarrow> Pred P xs \<in> wf_preds"

primrec eval_pred :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "eval_pred D mem (Pred P xs) \<longleftrightarrow> map (eval_trm D mem) xs \<in> interp_rel D P"

primrec pred_subst :: "nat \<Rightarrow> 'a::ranked_alphabet trm \<Rightarrow> 'a pred \<Rightarrow> 'a pred" where
  "pred_subst v s (Pred P xs) = Pred P (map (trm_subst v s) xs)"

abbreviation
  pred_subst_notation :: "'a::ranked_alphabet pred \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'a pred"
  ("_[_|_]" [100,100,100] 101) where
  "s[x|t] \<equiv> pred_subst x t s"

(* Simple while programs *)

datatype 'a prog = If "'a pred" "'a prog" "'a prog"
                 | While "'a pred" "'a prog"
                 | Seq "'a prog" "'a prog"
                 | Assign nat "'a trm"
                 | Skip

fun prog_preds :: "'a prog \<Rightarrow> 'a pred set" where
  "prog_preds (If P x y) = {P} \<union> prog_preds x \<union> prog_preds y"
| "prog_preds (While P x) = {P} \<union> prog_preds x"
| "prog_preds (Seq x y) = prog_preds x \<union> prog_preds y"
| "prog_preds (Assign _ _) = {}"
| "prog_preds Skip = {}"

fun prog_whiles :: "'a prog \<Rightarrow> 'a prog set" where
  "prog_whiles (If P x y) = prog_whiles x \<union> prog_whiles y"
| "prog_whiles (While P x) = {While P x} \<union> prog_whiles x"
| "prog_whiles (Seq x y) = prog_whiles x \<union> prog_whiles y"
| "prog_whiles (Assign _ _) = {}"
| "prog_whiles Skip = {}"

fun eval_prog :: "nat \<Rightarrow> ('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'a prog \<Rightarrow> 'b mem option" where
  "eval_prog 0 _ _ _ = None"
| "eval_prog (Suc n) D mem (If P x y) =
     (if eval_pred D mem P
     then eval_prog n D mem x
     else eval_prog n D mem y)"
| "eval_prog (Suc n) D mem (While P x) =
     (if eval_pred D mem P
     then case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem' (While P x)
     | None \<Rightarrow> None
     else Some mem)"
| "eval_prog (Suc n) D mem (Seq x y) =
     (case eval_prog n D mem x of
       Some mem' \<Rightarrow> eval_prog n D mem' y
     | None \<Rightarrow> None)"
| "eval_prog (Suc n) D mem Skip = Some mem"
| "eval_prog (Suc n) D mem (Assign m x) =
     (Some (\<lambda>v. if v = m then eval_trm D mem x else mem v))"

fun FV :: "'a trm \<Rightarrow> nat set" where
  "FV (Var v) = {v}"
| "FV (App f xs) = foldr op \<union> (map FV xs) {}"

lemma app_FV: "v \<notin> FV (App f xs) \<Longrightarrow> \<forall>x\<in>set xs. v \<notin> FV x"
  by (erule contrapos_pp, simp, induct xs, auto)

lemma no_FV [simp]: "v \<notin> FV s \<Longrightarrow> s[v|t] = s"
proof (induct s)
  fix f xs
  assume asm: "\<forall>x\<in>set xs. v \<notin> FV x \<longrightarrow> trm_subst v t x = x"
    and "v \<notin> FV (App f xs)"
  hence "\<forall>x\<in>set xs. v \<notin> FV x"
    by (metis app_FV)
  thus "trm_subst v t (App f xs) = App f xs"
    by (metis (lifting) asm map_idI trm_subst.simps(2))
next
  fix v' assume "v \<notin> FV (Var v')"
  thus "trm_subst v t (Var v') = Var v'" by simp
next
  show "\<forall>x\<in>set []. v \<notin> FV x \<longrightarrow> trm_subst v t x = x" by simp
next
  fix x xs
  assume "v \<notin> FV x \<Longrightarrow> trm_subst v t x = x"
    and "\<forall>y\<in>set xs. v \<notin> FV y \<longrightarrow> trm_subst v t y = y"
  thus "\<forall>y\<in>set (x # xs). v \<notin> FV y \<longrightarrow> trm_subst v t y = y"
    by auto
qed

primrec pred_vars :: "'a::ranked_alphabet pred \<Rightarrow> nat set" where
  "pred_vars (Pred P xs) = \<Union> (set (map FV xs))"

lemma no_pred_vars: "v \<notin> pred_vars \<phi> \<Longrightarrow> \<phi>[v|t] = \<phi>"
proof (induct \<phi>, simp)
  fix xs :: "'a trm list" assume "\<forall>x\<in>set xs. v \<notin> FV x"
  thus "map (trm_subst v t) xs = xs"
    by (induct xs, simp_all)
qed

ML {*
structure AlphabetRules = Named_Thms
  (val name = @{binding "alphabet"}
   val description = "Alphabet rules")
*}

setup {* AlphabetRules.setup *}

lemma trm_simple_induct': "\<lbrakk>\<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs); \<And>n. P (Var n)\<rbrakk> \<Longrightarrow> P s \<and> (\<forall>x\<in>set []. P x)"
  by (rule trm.induct[of "\<lambda>xs. (\<forall>x\<in>set xs. P x)" P], simp_all)

lemma trm_simple_induct: "\<lbrakk>\<And>n. P (Var n); \<And>f xs. (\<forall>x\<in>set xs. P x) \<Longrightarrow> P (App f xs)\<rbrakk> \<Longrightarrow> P s"
  by (metis trm_simple_induct')

lemma foldr_FV: "foldr op \<union> (map FV xs) {} = \<Union> (FV ` set xs)"
  by (induct xs, auto)

lemma eval_trm_eq_mem: "(\<forall>v\<in>FV s. m1 v = m2 v) \<Longrightarrow> eval_trm D m1 s = eval_trm D m2 s"
proof (induct rule: trm_simple_induct, auto)
  fix f :: "'a" and xs :: "'a trm list"
  assume asm1: "\<forall>x\<in>set xs. (\<forall>v\<in>FV x. m1 v = m2 v) \<longrightarrow> eval_trm D m1 x = eval_trm D m2 x"
  and asm2: "\<forall>v\<in>foldr op \<union> (map FV xs) {}. m1 v = m2 v"
  have "foldr op \<union> (map FV xs) {} = \<Union> (FV ` set xs)"
    by (induct xs, auto)
  hence "\<forall>v\<in>\<Union>(FV ` set xs). m1 v = m2 v"
    by (metis asm2)
  hence "\<forall>x\<in>set xs. (\<forall>v\<in>FV x. m1 v = m2 v)"
    by (metis UnionI imageI)
  hence "\<forall>x\<in>set xs. eval_trm D m1 x = eval_trm D m2 x"
    by (metis asm1)
  hence "map (eval_trm D m1) xs = map (eval_trm D m2) xs"
    by (induct xs, auto)
  thus "interp_fun D f (map (eval_trm D m1) xs) = interp_fun D f (map (eval_trm D m2) xs)"
    by metis
qed

definition set_mem :: "nat \<Rightarrow> 'a \<Rightarrow> 'a mem \<Rightarrow> 'a mem" where
  "set_mem x s mem \<equiv> \<lambda>v. if v = x then s else mem v"

definition assign ::
  "('a::ranked_alphabet, 'b) interp \<Rightarrow> nat \<Rightarrow> 'a trm \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "assign D x s mem = set_mem x (eval_trm D mem s) mem"

definition halt_null :: "('a::ranked_alphabet, 'b) interp \<Rightarrow> 'b mem \<Rightarrow> 'b mem"
  where
  "halt_null D mem \<equiv> \<lambda>v. if v \<notin> output_vars TYPE('a) then interp_fun D NULL [] else mem v"

lemma eval_assign1:
  assumes xy: "x \<noteq> y" and ys: "y \<notin> FV s"
  shows "assign D y t (assign D x s mem) = assign D x s (assign D y (trm_subst x s t) mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def set_mem_def)
  apply default
  apply default
  apply default
  apply (smt eval_trm_eq_mem ys)
  apply auto
  apply default
  apply (smt eval_trm.simps(1) eval_trm_eq_mem xy ys)
proof
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D y t (assign D x s mem) =
                      assign D x s (assign D y (trm_subst x s t) mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D x s (assign D y (trm_subst x s t) mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D x s (assign D y (App f (map (trm_subst x s) ts)) mem) v"
    apply (simp add: assign_def set_mem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy ys)
qed

lemma eval_assign2:
  assumes xy: "x \<noteq> y" and xs: "x \<notin> FV s"
  shows "assign D y t (assign D x s mem) =
         assign D y (trm_subst x s t) (assign D x s mem)"
  apply (induct t rule: trm_simple_induct)
  apply (simp add: assign_def set_mem_def)
  apply default
  apply default
  apply default
  apply (smt eval_trm_eq_mem xs)
  apply auto
proof
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D y t (assign D x s mem) =
                      assign D y (trm_subst x s t) (assign D x s mem)"
  hence "\<forall>t\<in>set ts. assign D y t (assign D x s mem) v =
                     assign D y (trm_subst x s t) (assign D x s mem) v"
    by auto
  thus "assign D y (App f ts) (assign D x s mem) v =
        assign D y (App f (map (trm_subst x s) ts)) (assign D x s mem) v"
    apply (simp add: assign_def set_mem_def o_def)
    by (smt eval_trm_eq_mem map_eq_conv xy xs)
qed

lemma eval_assign3: "assign D x t (assign D x s mem) = assign D x (trm_subst x s t) mem"
proof (induct t rule: trm_simple_induct, simp add: assign_def set_mem_def, auto, default)
  fix f ts v
  assume "\<forall>t\<in>set ts. assign D x t (assign D x s mem) = assign D x (trm_subst x s t) mem"
  hence "\<forall>t\<in>set ts. assign D x t (assign D x s mem) v = assign D x (trm_subst x s t) mem v"
    by auto
  hence "v = x \<longrightarrow> map (eval_trm D (\<lambda>v. if v = x then eval_trm D mem s else mem v)) ts =
                  map (eval_trm D mem \<circ> trm_subst x s) ts"
    by (auto simp add: assign_def set_mem_def)
  thus "assign D x (App f ts) (assign D x s mem) v = assign D x (App f (map (trm_subst x s) ts)) mem v"
    by (auto simp add: assign_def set_mem_def o_def, smt map_eq_conv)
qed

lemma eval_halt:
  "x \<notin> output_vars TYPE('a::ranked_alphabet) \<Longrightarrow> halt_null D mem = halt_null D (assign D x (App (NULL::'a) []) mem)"
  by (auto simp add: halt_null_def assign_def set_mem_def)

lemma subst_preds: "P \<in> wf_preds \<Longrightarrow> P[x|s] \<in> wf_preds"
  apply (induct P)
  apply simp
  by (metis SKAT_Term.pred.inject length_map wf_preds.simps)

lemma eval_assign4: "P \<in> preds \<Longrightarrow> eval_pred D (assign D x t mem) P = eval_pred D mem (pred_subst x t P)"
proof (induct P)
  fix P and xs :: "'a trm list" assume "Pred P xs \<in> preds"
  have "\<And>s. s \<in> set xs \<Longrightarrow> eval_trm D (assign D x t mem) s = eval_trm D mem (s[x|t])"
    by (metis eval_assign3 set_mem_def assign_def)
  thus "eval_pred D (assign D x t mem) (Pred P xs) = eval_pred D mem (pred_subst x t (Pred P xs))"
    by (simp add: o_def, metis (lifting) map_ext)
qed

end
