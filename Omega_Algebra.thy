(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Omega Algebras *}

theory Omega_Algebra
imports "$AFP/Kleene_Algebra/Kleene_Algebra"
begin

text {*
\emph{Omega algebras}~\cite{cohen00omega} extend Kleene algebras by an
$\omega$-operation that axiomatizes infinite iteration (just like the
Kleene star axiomatizes finite iteration).
*}

subsection {* Left Omega Algebras *}

text {*
In this section we consider \emph{left omega algebras}, i.e., omega
algebras based on left Kleene algebras. Surprisingly, we are still
looking for statements mentioning~$\omega$ that are true in omega
algebras, but do not already hold in left omega algebras.
*}

class left_omega_algebra_zerol = left_kleene_algebra_zerol + omega_op +
  assumes omega_unfold_eq [simp]: "x \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
  and omega_coinduct: "y \<le> z + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
begin

lemma omega_unfold: "x\<cdot>x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis omega_unfold_eq order_refl)

lemma omega_zeror: "x\<^sup>\<star>\<cdot>0 \<le> x\<^sup>\<omega>"
  apply (rule star_inductl[rule_format])
  by (simp add: omega_unfold)

text {* First we prove some variants of the coinduction axiom. *}

lemma [simp]: "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> 0 = x\<^sup>\<omega>"
  by (metis add_commute less_eq_def omega_zeror)

lemma omega_coinduct_var2: "y \<le> x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
  by (auto intro: omega_coinduct[where z = 0, simplified, rule_format])

lemma omega_coinduct_var1: "y \<le> 1 + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star>"
  by (metis mult_oner omega_coinduct)

lemma omega_coinduct_eq: "y = z + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
  by (metis eq_refl omega_coinduct)

lemma omega_coinduct_eq_var1: "y = 1 + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star>"
  by (metis eq_refl omega_coinduct_var1)

lemma  omega_coinduct_eq_var2: "y = x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
  by (metis eq_refl omega_coinduct_var2)

text {* Next we strengthen the unfold law to an equation. *}

lemma omega_unfold_var: "z + x \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
  by (metis add_lub add_ub1 omega_coinduct omega_unfold_eq)

text {* We now prove subdistributivity and isotonicity of omega. *}

lemma omega_subdist: "x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "x\<^sup>\<omega> \<le> (x + y) \<cdot> x\<^sup>\<omega>"
    by (metis add_ub1 mult_isor omega_unfold_eq)
  thus ?thesis
    by (metis omega_coinduct_var2)
qed

lemma omega_iso: "x \<le> y \<longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (metis less_eq_def omega_subdist)

lemma omega_subdist_var: "x\<^sup>\<omega> + y\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
  by (metis add.commute add_lub omega_subdist)

lemma zero_omega [simp]: "0\<^sup>\<omega> = 0"
  by (metis annil omega_unfold_eq)

text {* The next lemma is another variant of omega unfold *}

lemma star_omega_1 [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
proof (rule antisym)
  have "x \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by (metis eq_refl omega_unfold_eq)
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by (metis star_inductl_var)
  show "x\<^sup>\<omega> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
    by (metis star_ref mult_isor mult_onel)
qed

text {* The next lemma says that~@{term "1\<^sup>\<omega>"} is the maximal element
of omega algebra. We therefore baptise it~$\top$. *}

lemma max_element: "x \<le> 1\<^sup>\<omega>"
  by (metis eq_refl mult_onel omega_coinduct_var2)

definition omega_top ("\<top>")
  where "\<top> = 1\<^sup>\<omega>"

lemma star_omega_3 [simp]: "(x\<^sup>\<star>)\<^sup>\<omega> = \<top>"
proof -
  have "1 \<le> x\<^sup>\<star>"
    by (fact star_ref)
  hence "\<top> \<le> (x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis omega_iso omega_top_def)
  thus ?thesis
    by (metis eq_iff max_element omega_top_def)
qed

text {* The following lemma is strange since it is counterintuitive
that one should be able to append something after an infinite
iteration. *}

lemma omega_1: "x\<^sup>\<omega> \<cdot> y \<le> x\<^sup>\<omega>"
proof -
  have "x\<^sup>\<omega> \<cdot> y \<le> x \<cdot> x\<^sup>\<omega> \<cdot> y"
    by (metis eq_refl omega_unfold_eq)
  thus ?thesis
    by (metis mult.assoc omega_coinduct_var2)
qed

lemma omega_sup_id: "1 \<le> y \<longrightarrow> x\<^sup>\<omega> \<cdot> y = x\<^sup>\<omega>"
  by (metis eq_iff mult_isol mult_oner omega_1)

lemma omega_top [simp]: "x\<^sup>\<omega> \<cdot> \<top> = x\<^sup>\<omega>"
  by (metis max_element omega_sup_id omega_top_def)

lemma supid_omega: "1 \<le> x \<longrightarrow> x\<^sup>\<omega> = \<top>"
  by (metis eq_iff max_element omega_iso omega_top_def)

text {* Next we prove a simulation law for the omega operation *}

lemma omega_simulation: "z \<cdot> x \<le> y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
proof
  assume "z \<cdot> x \<le> y \<cdot> z"
  also have "z \<cdot> x\<^sup>\<omega> = z \<cdot> x \<cdot> x\<^sup>\<omega>"
    by (metis mult.assoc omega_unfold_eq)
  moreover have "... \<le> y \<cdot> z \<cdot> x\<^sup>\<omega>"
    by (metis mult_isor calculation)
  thus "z \<cdot> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
    by (metis calculation(2) mult_assoc omega_coinduct_var2)
qed

text {* Next we prove transitivity of omega elements. *}

lemma omega_trans: "x\<^sup>\<omega> \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (fact omega_1)

lemma omega_omega: "(x\<^sup>\<omega>)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis omega_1 omega_unfold_eq)

text {* The next lemmas are axioms of Wagner's complete axiomatisation
for omega-regular languages~\cite{Wagner77omega}, but in a slightly
different setting.  *}

lemma wagner_1 [simp]: "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> = x\<^sup>\<omega>"
proof (rule antisym)
  have "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> = x \<cdot> x\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult.assoc omega_unfold_eq)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult.assoc star_slide_var)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult.assoc star_trans_eq)
  also have "... = x \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult.assoc omega_unfold_eq)
  thus "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by (metis calculation eq_refl omega_coinduct_var2)
   show "x\<^sup>\<omega> \<le> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult_isol mult_oner omega_iso star_ref)
qed

lemma wagner_2_var: "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
proof -
  have "x \<cdot> y \<cdot> x \<le> x \<cdot> y \<cdot> x"
    by auto
  thus "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
    by (metis mult.assoc omega_simulation)
qed

lemma wagner_2 [simp]: "x \<cdot> (y \<cdot> x)\<^sup>\<omega> = (x \<cdot> y)\<^sup>\<omega>"
proof (rule antisym)
  show "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
    by (rule wagner_2_var)
  have "(x \<cdot> y)\<^sup>\<omega> = x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<omega>"
    by (metis omega_unfold_eq)
  thus "(x \<cdot> y)\<^sup>\<omega> \<le> x \<cdot> (y \<cdot> x)\<^sup>\<omega>"
    by (metis mult.assoc mult_isol wagner_2_var)
qed

text {*
This identity is called~(A8) in Wagner's paper.
*}

lemma wagner_3:
assumes "x \<cdot> (x + y)\<^sup>\<omega> + z = (x + y)\<^sup>\<omega>"
shows "(x + y)\<^sup>\<omega> = x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
proof (rule antisym)
  show  "(x + y)\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
    by (metis add.commute assms omega_coinduct_eq)
  have "x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^sup>\<omega>"
    by (metis add.commute assms star_inductl_eq)
  thus "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^sup>\<omega>"
    by (metis add_lub omega_subdist)
qed

text {*
This identity is called~(R4) in Wagner's paper.
*}

lemma wagner_1_var [simp]: "(x\<^sup>\<star> \<cdot> x)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (metis star_slide_var wagner_1)

lemma star_omega_4 [simp]: "(x\<^sup>\<omega>)\<^sup>\<star> = 1 + x\<^sup>\<omega>"
proof (rule antisym)
  have "(x\<^sup>\<omega>)\<^sup>\<star> = 1 + x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star>"
    by simp
  also have "... \<le> 1 + x\<^sup>\<omega> \<cdot> \<top>"
    by (metis add_iso_var eq_refl omega_1 omega_top)
  thus "(x\<^sup>\<omega>)\<^sup>\<star> \<le> 1 + x\<^sup>\<omega>"
    by (metis calculation omega_top)
  show "1 + x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<star>"
    by (metis star2 star_ext)
qed

lemma star_omega_5 [simp]: "x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star> = x\<^sup>\<omega>"
proof (rule antisym)
  show "x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star> \<le> x\<^sup>\<omega>"
    by (rule omega_1)
  show "x\<^sup>\<omega> \<le> x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star>"
    by (metis mult_oner star_ref mult_isol)
qed

text {* The next law shows how omegas below a sum can be unfolded. *}

lemma omega_sum_unfold: "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<omega> = (x + y)\<^sup>\<omega>"
proof -
  have "(x + y)\<^sup>\<omega> = x \<cdot> (x + y)\<^sup>\<omega> + y \<cdot> (x+y)\<^sup>\<omega>"
    by (metis distrib_right omega_unfold_eq)
  thus ?thesis
    by (metis mult.assoc wagner_3)
qed

text {*
The next two lemmas apply induction and coinduction to this law.
*}

lemma omega_sum_unfold_coind: "(x + y)\<^sup>\<omega> \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
  by (metis omega_coinduct_eq omega_sum_unfold)

lemma omega_sum_unfold_ind: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
  by (metis omega_sum_unfold star_inductl_eq)

lemma wagner_1_gen: "(x \<cdot> y\<^sup>\<star>)\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "(x \<cdot> y\<^sup>\<star>)\<^sup>\<omega> \<le> ((x + y) \<cdot> (x + y)\<^sup>\<star>)\<^sup>\<omega>"
    by (metis add_ub1 add_ub2 mult_isol_var omega_iso star_iso)
  thus ?thesis
    by (metis wagner_1)
qed

lemma wagner_1_var_gen: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis wagner_2)
  also have "... \<le> x\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add.commute mult_isol wagner_1_gen)
  also have "... \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add_ub1 mult_isor star_iso)
  thus ?thesis
    by (metis calculation order_trans star_omega_1)
qed

text {* The next lemma is a variant of the denest law for the star at
the level of omega. *}

lemma omega_denest [simp]: "(x + y)\<^sup>\<omega> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
proof (rule antisym)
  show "(x + y)\<^sup>\<omega> \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
    by (rule omega_sum_unfold_coind)
  have "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> \<le>  (x + y)\<^sup>\<omega>"
    by (rule wagner_1_var_gen)
  hence "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (metis omega_sum_unfold_ind)
  thus "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (metis add_lub wagner_1_var_gen)
qed

text {* The next lemma yields a separation theorem for infinite
iteration in the presence of a quasicommutation property. A
nondeterministic loop over~@{term x} and~@{term y} can be refined into
separate infinite loops over~@{term x} and~@{term y}.  *}

lemma omega_sum_refine:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^sup>\<omega> = x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega>"
proof (rule antisym)
  have "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (metis assms quasicomm_var)
  also have "(x + y)\<^sup>\<omega> = y\<^sup>\<omega> + y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add.commute omega_sum_unfold)
  moreover have "... \<le> x \<cdot> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega> + y\<^sup>\<omega>"
    by (metis add_iso add_lub add_ub2 calculation(1) mult_isor)
  moreover have "... \<le> x \<cdot> (x + y)\<^sup>\<omega> + y\<^sup>\<omega>"
    by (metis mult.assoc order_refl star_omega_1)
  thus "(x + y)\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega>"
    by (metis add.commute calculation mult.assoc omega_coinduct star_omega_1)
  have "x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (rule omega_subdist)
  moreover have "x\<^sup>\<star> \<cdot> y\<^sup>\<omega> \<le> x\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    by (metis calculation add_ub1 mult_isol)
  moreover have"... \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add_ub1 star_iso mult_isor)
  moreover have "... = (x + y)\<^sup>\<omega>"
     by (rule star_omega_1)
   thus "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
     by (metis add.commute add_lub calculation mult_isol omega_subdist order_trans star_omega_1)
qed

text {* The following theorem by Bachmair and
Dershowitz~\cite{bachmair86commutation} is a corollary. *}

lemma bachmair_dershowitz:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega> + y\<^sup>\<omega> = 0"
proof
  assume "(x + y)\<^sup>\<omega> = 0"
  show "x\<^sup>\<omega> + y\<^sup>\<omega> = 0"
    by (metis `(x + y)\<^sup>\<omega> = (0\<Colon>'a)` omega_subdist_var zero_unique)
next
  assume "x\<^sup>\<omega> + y\<^sup>\<omega> = 0"
  show "(x + y)\<^sup>\<omega> = 0"
    by (metis `x\<^sup>\<omega> + y\<^sup>\<omega> = (0\<Colon>'a)` assms no_trivial_inverse omega_sum_refine distrib_left star_omega_1)
qed

text {*
The next lemmas consider an abstract variant of the empty word
property from language theory and match it with the absence of
infinite iteration~\cite{struth12regeq}.
*}

definition (in dioid_one_zerol) ewp
where "ewp x \<equiv> \<not>(\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0)"

lemma ewp_super_id1: "0 \<noteq> 1 \<longrightarrow> 1 \<le> x \<longrightarrow> ewp x"
  by (metis ewp_def mult_1_right)

text {* The next facts relate the absence of the empty word property
with the absence of infinite iteration. *}

lemma ewp_neg_and_omega: "\<not> ewp x \<longleftrightarrow> x\<^sup>\<omega> = 0"
proof
  assume "\<not> ewp x"
  hence a: "\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    by (metis ewp_def)
  thus "x\<^sup>\<omega> = 0"
    by (metis eq_refl omega_unfold_eq)
next
  assume "x\<^sup>\<omega> = 0"
  hence "\<forall> y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    by (metis omega_coinduct_var2 zero_unique)
  thus "\<not> ewp x"
    by (metis ewp_def)
qed

lemma ewp_alt1: "(\<forall>z. x\<^sup>\<omega> \<le> x\<^sup>\<star> \<cdot> z) \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  by (metis add_comm less_eq_def omega_coinduct omega_unfold_eq order_prop)

(*
lemma ewp_alt: "x\<^sup>\<omega> = 0 \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  nitpick [expect = genuine]
oops
*)

text {* So we have obtained a condition for Arden's lemma in omega
algebra.  *}

lemma omega_super_id1: "0 \<noteq> 1 \<longrightarrow> 1 \<le> x \<longrightarrow> x\<^sup>\<omega> \<noteq> 0"
  by (metis eq_iff max_element omega_iso zero_least)

lemma omega_super_id2: "0 \<noteq> 1 \<longrightarrow> x\<^sup>\<omega> = 0 \<longrightarrow> \<not>(1 \<le> x)"
  by (metis omega_super_id1)

text {* The next lemmas are abstract versions of Arden's lemma from
language theory.  *}

lemma ardens_lemma_var:
  assumes "x\<^sup>\<omega> = 0" and  "z + x \<cdot> y = y"
  shows "x\<^sup>\<star> \<cdot> z = y"
proof -
  have "y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
    by (metis assms omega_coinduct order_refl)
  hence "y \<le> x\<^sup>\<star> \<cdot> z"
    by (metis add_zero_l assms)
  thus "x\<^sup>\<star> \<cdot> z = y"
    by (metis assms eq_iff star_inductl_eq)
qed

lemma ardens_lemma: "\<not> ewp x \<longrightarrow> z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y"
  by (metis ardens_lemma_var ewp_neg_and_omega)

lemma ardens_lemma_equiv:
  assumes "\<not> ewp x"
  shows "z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y"
proof
  assume "z + x \<cdot> y = y"
  thus "x\<^sup>\<star> \<cdot> z = y"
    by (metis ardens_lemma assms)
next
  assume "x\<^sup>\<star> \<cdot> z = y"
  also have "z + x \<cdot> y = z + x \<cdot> x\<^sup>\<star> \<cdot> z"
    by (metis calculation mult.assoc)
  moreover have "... = (1 + x \<cdot> x\<^sup>\<star>) \<cdot> z"
    by (metis distrib_right mult_onel)
  moreover have "... = x\<^sup>\<star> \<cdot> z"
    by (metis star_unfoldl_eq)
  thus "z + x \<cdot> y = y"
    by (metis calculation)
qed

lemma ardens_lemma_var_equiv: "x\<^sup>\<omega> = 0 \<longrightarrow> (z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y)"
  by (metis ardens_lemma_equiv ewp_neg_and_omega)

lemma inf_star [simp]: "(x\<cdot>0)\<^sup>\<star> = 1 + x\<cdot>0"
  apply (rule antisym)
  apply (rule star_inductl_one[rule_format])
  apply (metis annil mult_assoc order_refl)
  by (metis add_lub star_ext star_ref)

lemma [simp]: "x \<cdot> 0 \<cdot> y = x \<cdot> 0"
  by (metis annil mult_assoc)

lemma inf_part_star1: "(y + x\<cdot>0)\<^sup>\<star> \<le> y\<^sup>\<star>\<cdot>x\<cdot>0 + y\<^sup>\<star>"
  apply (rule star_inductl_one[rule_format])
  apply (subst star_unfoldl_eq[symmetric]) back back
  apply (subst star_unfoldl_eq[symmetric]) back back back
  apply (simp only: distrib_right distrib_left mult_assoc[symmetric])
  apply (simp add: distrib_left)
  by (metis add_assoc add_commute local.distrib_left local.eq_refl local.mult_1_left local.mult_1_right local.star2 local.star_one local.troeger mult_assoc)

lemma inf_part_star [simp]: "(y + x\<cdot>0)\<^sup>\<star> = y\<^sup>\<star>\<cdot>x\<cdot>0 + y\<^sup>\<star>"
  apply (rule antisym)
  apply (metis inf_part_star1)
  by (metis add_commute add_lub mult_assoc prod_star_closure star_subdist star_subdist_var_1)

(*
lemma arden_conv1: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longrightarrow> \<not> ewp x"
  nitpick [expect = genuine]
oops

lemma arden_conv2: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longrightarrow> x\<^sup>\<omega> = 0"
  nitpick [expect = genuine]
oops

lemma arden_var3: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longleftrightarrow> x\<^sup>\<omega> = 0"
  nitpick [expect = genuine]
oops
*)

end

end
