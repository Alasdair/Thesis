theory Fixpoint
  imports Main
begin

context order
begin

definition endo_galois_connection :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "endo_galois_connection f g \<equiv> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"

definition endo_lower_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "endo_lower_adjoint f \<equiv> \<exists>g. endo_galois_connection f g"

definition endo_upper_adjoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "endo_upper_adjoint g \<equiv> \<exists>f. endo_galois_connection f g"

lemma endo_deflation: "endo_galois_connection f g \<Longrightarrow> f (g y) \<le> y"
  by (metis endo_galois_connection_def le_less)

lemma endo_inflation: "endo_galois_connection f g \<Longrightarrow> x \<le> g (f x)"
  by (metis endo_galois_connection_def le_less)

(* Sledgehammer can't seem to use mono due to it's sort constraints *)
definition isotone :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "isotone f \<equiv> \<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"

lemma isotone_is_mono: "isotone f \<Longrightarrow> mono f"
  by (metis (hide_lams, mono_tags) order_class.isotone_def order_class.mono_def)

lemma isotoneD: "\<lbrakk>isotone f; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by (metis isotone_def)

definition idempotent :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent f \<equiv> f \<circ> f = f"

lemma endo_lower_iso: "endo_galois_connection f g \<Longrightarrow> isotone f"
  by (metis endo_galois_connection_def endo_inflation isotone_def order_trans)

lemma endo_upper_iso: "endo_galois_connection f g \<Longrightarrow> isotone g"
  by (metis (lifting) endo_deflation endo_galois_connection_def isotone_def order_trans)

lemma endo_lower_comp: "endo_galois_connection f g \<Longrightarrow> f \<circ> g \<circ> f = f"
proof
  fix x
  assume "endo_galois_connection f g"
  thus "(f \<circ> g \<circ> f) x = f x"
    by (metis comp_apply endo_deflation endo_galois_connection_def endo_inflation isotoneD less_le less_le_not_le endo_lower_iso endo_upper_adjoint_def)
qed

lemma endo_upper_comp: "endo_galois_connection f g \<Longrightarrow> g \<circ> f \<circ> g = g"
proof
  fix x
  assume "endo_galois_connection f g"
  thus "(g \<circ> f \<circ> g) x = g x"
    by (metis (full_types) antisym endo_deflation endo_inflation isotone_def o_apply endo_upper_iso)
qed

lemma endo_upper_idempotency1: "endo_galois_connection f g \<Longrightarrow> idempotent (f \<circ> g)"
  by (metis idempotent_def o_assoc endo_upper_comp)

lemma endo_upper_idempotency2: "endo_galois_connection f g \<Longrightarrow> idempotent (g \<circ> f)"
  by (metis idempotent_def o_assoc endo_lower_comp)

lemma endo_galois_comp: assumes g1: "endo_galois_connection F G" and g2 :"endo_galois_connection H K"
  shows "endo_galois_connection (F \<circ> H) (K \<circ> G)"
  using g1 g2 by (simp add: endo_galois_connection_def)

lemma endo_galois_id: "endo_galois_connection id id" by (metis endo_galois_connection_def id_def)

lemma endo_galois_isotone1: "endo_galois_connection f g \<Longrightarrow> isotone (g \<circ> f)"
  by (simp add: endo_galois_connection_def isotone_def) (metis local.dual_order.trans local.order.refl)

lemma endo_galois_isotone2: "endo_galois_connection f g \<Longrightarrow> isotone (f \<circ> g)"
  by (metis isotone_def endo_lower_iso o_apply endo_upper_iso)

lemma endo_cancel: assumes g: "endo_galois_connection f g" shows "f (g x) \<le> g (f x)"
  by (metis assms endo_deflation endo_inflation order_trans)

lemma endo_cancel_cor1: assumes g: "endo_galois_connection f g"
  shows "(g x = g y) \<longleftrightarrow> (f (g x) = f (g y))"
  by (metis assms endo_upper_comp o_apply)

lemma endo_cancel_cor2: assumes g: "endo_galois_connection f g"
  shows "(f x = f y) \<longleftrightarrow> (g (f x) = g (f y))"
  by (metis assms endo_lower_comp o_apply)

lemma endo_semi_inverse1: "endo_galois_connection f g \<Longrightarrow> f x = f (g (f x))"
  by (metis o_def endo_lower_comp)

lemma endo_semi_inverse2: "endo_galois_connection f g \<Longrightarrow> g x = g (f (g x))"
  by (metis o_def endo_upper_comp)

lemma endo_universal_mapping_property1:
  assumes a: "isotone g" and b: "\<forall>x. x \<le> g (f x)"
  and c: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
  shows "endo_galois_connection f g"
  by (metis a b c endo_galois_connection_def isotoneD order_trans)

lemma endo_universal_mapping_property2:
  assumes a: "isotone f" and b: "\<forall>x. f (g x) \<le> x"
  and c: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
  shows "endo_galois_connection f g"
  by (metis a b c endo_galois_connection_def isotoneD order_trans)

lemma endo_galois_ump2: "endo_galois_connection f g = (isotone f \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis endo_deflation endo_galois_connection_def endo_lower_iso endo_universal_mapping_property2)

lemma endo_galois_ump1: "endo_galois_connection f g = (isotone g \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis endo_galois_connection_def endo_inflation endo_universal_mapping_property1 endo_upper_iso)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma endo_ore_galois:
  assumes"\<forall>x. x \<le> g (f x)" and "\<forall>x. f (g x) \<le> x"
  and "isotone f" and  "isotone g"
  shows "endo_galois_connection f g"
  by (metis assms isotoneD order_trans endo_universal_mapping_property1)

(* +------------------------------------------------------------------------+
   | Theorems 4.32(a) and 4.32(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma endo_perfect1: "endo_galois_connection f g \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  by (metis (full_types) image_iff range_eqI endo_semi_inverse2)

lemma endo_perfect2: "endo_galois_connection f g \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (metis (full_types) image_iff range_eqI endo_semi_inverse1)

end

definition pleq :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "pleq f g \<equiv> \<forall>x. f x \<le> g x"

definition galois_connection :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "galois_connection f g \<equiv> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"

locale bi_ord = ord1: order le1 l1 + ord2: order le2 l2
  for le1 (infix "\<le>\<^sub>1" 50)
  and l1
  and le2 (infix "\<le>\<^sub>2" 50)
  and l2

begin

  definition galois_connection2 :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
    "galois_connection2 f g \<equiv> \<forall>x y. (f x \<le>\<^sub>2 y) \<longleftrightarrow> (x \<le>\<^sub>1 g y)"

end

sublocale order \<subseteq> bi_ord "(op \<le>)" "(op <)" "(op \<le>)" "(op <)"
  by unfold_locales

thm galois_connection2_def

context order
begin

  thm galois_connection2_def

end

find_theorems name:galois_connection2

lemma any_orders: "bi_ord (op \<le> :: 'a::order \<Rightarrow> 'a \<Rightarrow> bool) (op <) (op \<le> :: 'b::order \<Rightarrow> 'b \<Rightarrow> bool) (op <)"
  by unfold_locales

thm bi_ord.galois_connection2_def[OF any_orders] galois_connection_def

lemma "bi_ord.galois_connection2 (op \<le>) (op \<le>) f g = galois_connection f g"
  by (simp add: bi_ord.galois_connection2_def[OF any_orders] galois_connection_def)

lemma galoisD: "galois_connection f g \<Longrightarrow> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"
  by (simp add: galois_connection_def)

lemma rev_galoisD: "galois_connection f g \<Longrightarrow> \<forall>x y.  (x \<le> g y) \<longleftrightarrow> (f x \<le> y)"
  by (simp add: galois_connection_def)

definition lower_adjoint :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "lower_adjoint f \<equiv> \<exists>g. galois_connection f g"

definition upper_adjoint :: "('b::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "upper_adjoint g \<equiv> \<exists>f. galois_connection f g"

lemma deflation: "galois_connection f g \<Longrightarrow> f (g y) \<le> y"
  by (metis galois_connection_def le_less)

lemma deflationD: "galois_connection f g \<Longrightarrow> \<forall>y. f (g y) \<le> y"
  by (metis galois_connection_def le_less)

lemma inflation: "galois_connection f g \<Longrightarrow> x \<le> g (f x)"
  by (metis galois_connection_def le_less)

lemma inflationD: "galois_connection f g \<Longrightarrow> \<forall>x. x \<le> g (f x)"
  by (metis galois_connection_def le_less)

definition idempotent :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent f \<equiv> f \<circ> f = f"

lemma lower_iso: "galois_connection f g \<Longrightarrow> mono f"
  apply (frule galoisD)
  apply (auto simp add: mono_def)
  apply (drule inflationD)
  apply (erule_tac x = y in allE) back
  by (metis order_trans)

lemma upper_iso: "galois_connection f g \<Longrightarrow> mono g"
  apply (frule rev_galoisD)
  apply (auto simp add: mono_def)
  apply (drule deflationD)
  apply (erule_tac x = x in allE)
  by (metis order_trans)

lemma lower_comp: "galois_connection f g \<Longrightarrow> f \<circ> g \<circ> f = f"
proof
  fix x
  assume "galois_connection f g"
  thus "(f \<circ> g \<circ> f) x = f x"
    apply (simp add: galois_connection_def)
    by (metis `galois_connection f g` lower_iso monoE order_class.order.antisym order_refl)
qed

lemma upper_comp: "galois_connection f g \<Longrightarrow> g \<circ> f \<circ> g = g"
proof
  fix x
  assume "galois_connection f g"
  thus "(g \<circ> f \<circ> g) x = g x"
    apply (simp add: galois_connection_def)
    by (metis `galois_connection f g` monoE order_class.order.antisym order_refl upper_iso)
qed

lemma upper_idempotency1: "galois_connection f g \<Longrightarrow> idempotent (f \<circ> g)"
  by (metis idempotent_def o_assoc upper_comp)

lemma upper_idempotency2: "galois_connection f g \<Longrightarrow> idempotent (g \<circ> f)"
  by (metis idempotent_def o_assoc lower_comp)

lemma galois_comp: assumes g1: "galois_connection F G" and g2 :"galois_connection H K"
  shows "galois_connection (F \<circ> H) (K \<circ> G)"
  using g1 g2 by (simp add: galois_connection_def)

lemma galois_id: "galois_connection id id"
  by (simp add: galois_connection_def)

lemma galois_isotone1: "galois_connection f g \<Longrightarrow> mono (g \<circ> f)"
  by (simp add: galois_connection_def mono_def) (metis order_refl order_trans)

lemma galois_isotone2: "galois_connection f g \<Longrightarrow> mono (f \<circ> g)"
  by (metis mono_def lower_iso o_apply upper_iso)

lemma point_id1: "galois_connection f g \<Longrightarrow> id \<sqsubseteq> g \<circ> f"
  by (metis inflation id_apply o_apply pleq_def)

lemma point_id2: "galois_connection f g \<Longrightarrow> f \<circ> g \<sqsubseteq> id"
  by (metis deflation id_apply o_apply pleq_def)

lemma point_cancel: assumes g: "galois_connection f g" shows "f \<circ> g \<sqsubseteq> g \<circ> f" using g
  by (simp add: galois_connection_def o_def pleq_def) (metis g monoE order_refl upper_iso)

lemma cancel: assumes g: "galois_connection f g" shows "f (g x) \<le> g (f x)"
  by (metis assms deflation inflation order_trans)

lemma cancel_cor1: assumes g: "galois_connection f g"
  shows "(g x = g y) \<longleftrightarrow> (f (g x) = f (g y))"
  by (metis assms upper_comp o_apply)

lemma cancel_cor2: assumes g: "galois_connection f g"
  shows "(f x = f y) \<longleftrightarrow> (g (f x) = g (f y))"
  by (metis assms lower_comp o_apply)

lemma semi_inverse1: "galois_connection f g \<Longrightarrow> f x = f (g (f x))"
  by (metis o_def lower_comp)

lemma semi_inverse2: "galois_connection f g \<Longrightarrow> g x = g (f (g x))"
  by (metis o_def upper_comp)

lemma universal_mapping_property1:
  assumes a: "mono g" and b: "\<forall>x. x \<le> g (f x)"
  and c: "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
  shows "galois_connection f g"
  by (metis (full_types) a b c galois_connection_def monoD order_trans)

lemma universal_mapping_property2:
  assumes a: "mono f" and b: "\<forall>x. f (g x) \<le> x"
  and c: "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
  shows "galois_connection f g"
  by (metis (full_types) a b c galois_connection_def monoD order_trans)

lemma galois_ump2: "galois_connection f g = (mono f \<and> (\<forall>y. f (g y) \<le> y) \<and> (\<forall>x y. f x \<le> y \<longrightarrow> x \<le> g y))"
  by (metis deflation galois_connection_def lower_iso universal_mapping_property2)

lemma galois_ump1: "galois_connection f g = (mono g \<and> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>x y. x \<le> g y \<longrightarrow> f x \<le> y))"
  by (metis galois_connection_def inflation universal_mapping_property1 upper_iso)

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes"\<forall>x. x \<le> g (f x)" and "\<forall>x. f (g x) \<le> x"
  and "mono f" and  "mono g"
  shows "galois_connection f g"
  by (metis assms monoD order_trans universal_mapping_property1)

(* +------------------------------------------------------------------------+
   | Theorems 4.32(a) and 4.32(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma perfect1: "galois_connection f g \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  by (metis (full_types) image_iff range_eqI semi_inverse2)

lemma perfect2: "galois_connection f g \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (metis (full_types) image_iff range_eqI semi_inverse1)

(* Fixpoints *)

find_consts name:ccpo

sublocale order \<subseteq> dual: order "op \<ge>" "op >"
  by (rule local.dual_order)

context order
begin

definition is_lpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lpp x f \<equiv> f x \<le> x \<and> (\<forall>y. f y \<le> y \<longrightarrow> x \<le> y)"

definition is_gpp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gpp x f \<equiv> x \<le> f x \<and> (\<forall>y. y \<le> f y \<longrightarrow> y \<le> x)"

lemma lpp_unique: "\<lbrakk>is_lpp x f; is_lpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (auto intro: antisym simp only: is_lpp_def)

lemma gpp_unique: "\<lbrakk>is_gpp x f; is_gpp y f\<rbrakk> \<Longrightarrow> x = y"
  by (auto intro: antisym simp only: is_gpp_def)

definition is_lfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lfp x f \<equiv> f x = x \<and> (\<forall>y. f y = y \<longrightarrow> x \<le> y)"

definition is_gfp :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_gfp x f \<equiv> x = f x \<and> (\<forall>y. f y = y \<longrightarrow> y \<le> x)"

definition least_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" (binder "\<mu>" 10) where
  "\<mu> x. f x \<equiv> THE x. is_lfp x f"

notation least_fixpoint ("\<mu>")

lemma lfp_eta: "(\<mu> x. f x) = \<mu> f" by simp

lemma lfp_equality: "is_lfp x f \<Longrightarrow> \<mu> f = x"
  by (metis (lifting) eq_iff is_lfp_def least_fixpoint_def the_equality)

lemma lpp_is_lfp: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> is_lpp x f \<Longrightarrow> is_lfp x f"
  by (auto intro: antisym simp add: is_lfp_def is_lpp_def)

definition greatest_fixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" (binder "\<nu>" 10) where
  "\<nu> x. f x \<equiv> THE x. is_gfp x f"

notation greatest_fixpoint ("\<nu>")

lemma gfp_equality: "is_gfp x f \<Longrightarrow> \<nu> f = x"
  by (metis (lifting) eq_iff greatest_fixpoint_def is_gfp_def the_equality)

lemma gpp_is_gfp: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> is_gpp x f \<Longrightarrow> is_gfp x f"
  by (auto intro: antisym simp add: is_gfp_def is_gpp_def)

end

lemma continuity_mono:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "(\<And>X. Sup (f ` X) = f (Sup X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis Sup_le_iff antisym atMost_iff imageI order_refl)

lemma Inf_continuity_mono:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "(\<And>X. Inf (f ` X) = f (Inf X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis antisym atLeast_iff image_eqI le_Inf_iff order_refl)

definition (in order) directed :: "'a set \<Rightarrow> bool" where
  "directed X \<equiv> X \<noteq> {} \<and> (\<forall>x y. x \<in> X \<and> y \<in> X \<longrightarrow> (\<exists>z. x \<le> z \<and> y \<le> z))"

context complete_lattice
begin

lemma continuity_mono1: "(\<And>X. Sup (f ` X) = f (Sup X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis Sup_le_iff antisym atMost_iff imageI order_refl)

lemma continuity_mono2: "(\<And>X. Inf (f ` X) = f (Inf X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis (full_types) Inf_atLeastAtMost Inf_superset_mono atLeastatMost_subset_iff eq_refl image_mono)

lemma scott_continuity_mono: "(\<And>X. directed X \<Longrightarrow> Sup (f ` X) = f (Sup X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
proof -
  assume scott_continuity: "\<And>X. directed X \<Longrightarrow> Sup (f ` X) = f (Sup X)"
 
  {
    fix x y
    have "directed {x, y}"
    by (auto intro: exI[of _ "sup x y"] simp add: directed_def)
    hence "Sup (f ` {x, y}) = f (Sup {x, y})"
      by (metis scott_continuity)
    hence "sup (f x) (f y) = f (sup x y)"
      by auto
  }
  moreover assume "x \<le> y"
  ultimately show ?thesis
    by (metis le_iff_sup)
qed 

lemma Inf_continuity_mono1: "(\<And>X. Inf (f ` X) = f (Inf X)) \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis antisym atLeast_iff image_eqI le_Inf_iff order_refl)

theorem knaster_tarski_lpp:
  assumes "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y)" shows "\<exists>!x. is_lpp x f"
proof
  let ?H = "{u. f u \<le> u}"
  let ?a = "Inf ?H"

  have "f ?a \<le> ?a"
  proof -
    have "\<forall>x\<in>?H. ?a \<le> x"
      by (auto intro: Inf_lower)
    hence "\<forall>x\<in>?H. f ?a \<le> f x"
      by (metis assms)
    hence "\<forall>x\<in>?H. f ?a \<le> x"
      by (metis (lifting) mem_Collect_eq order_trans)
    thus "f ?a \<le> ?a"
      by (metis Inf_greatest lfp_def)
  qed
  moreover show "\<And>x. is_lpp x f \<Longrightarrow> x = ?a"
    by (metis eq_iff is_lpp_def lfp_def lfp_greatest lfp_lowerbound)
  ultimately show "is_lpp ?a f"
    by (metis is_lpp_def lfp_def lfp_lowerbound)
qed

theorem knaster_tarski: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> \<exists>!x. is_lfp x f"
  by (metis knaster_tarski_lpp lfp_equality lpp_is_lfp)

corollary is_lfp_lfp [intro?]:
  "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> is_lfp (\<mu> f) f"
  by (metis knaster_tarski_lpp lfp_equality lpp_is_lfp)

theorem knaster_tarski_gpp:
  assumes "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y)" shows "\<exists>!x. is_gpp x f"
proof
  let ?H = "{u. u \<le> f u}"
  let ?a = "Sup ?H"

  have "?a \<le> f ?a"
  proof -
    have "\<forall>x\<in>?H. x \<le> ?a"
      by (metis Sup_upper)
    hence "\<forall>x\<in>?H. f x \<le> f ?a"
      by (metis assms)
    hence "\<forall>x\<in>?H. x \<le> f ?a"
      by (metis (lifting) mem_Collect_eq order_trans)
    thus "?a \<le> f ?a"
      by (metis Sup_least gfp_def)
  qed
  moreover show "\<And>x. is_gpp x f \<Longrightarrow> x = ?a"
    by (metis (lifting, full_types) Sup_upper calculation eq_iff is_gpp_def mem_Collect_eq)
  ultimately show "is_gpp ?a f"
    by (simp add: is_gpp_def) (metis (full_types) Sup_upper mem_Collect_eq)
qed

theorem knaster_tarski_gfp: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> \<exists>!x. is_gfp x f"
  by (metis gfp_equality gpp_is_gfp knaster_tarski_gpp)

corollary is_gfp_gfp [intro?]:
  "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> is_gfp (\<nu> f) f"
  by (metis gfp_equality knaster_tarski_gfp)

lemma fp_compute [simp]: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> f (\<mu> f) = \<mu> f"
  by (metis is_lfp_def is_lfp_lfp)

lemma gfp_compute [simp]: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> f (\<nu> f) = \<nu> f"
  by (metis is_gfp_def is_gfp_gfp)

lemma fp_induct [intro?]:
  assumes "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y)" and "f x \<le> x" shows "\<mu> f \<le> x"
  by (metis (full_types) assms is_lpp_def knaster_tarski_lpp lfp_equality lpp_is_lfp)

lemma gfp_induct [intro?]:
  assumes "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y)" and "x \<le> f x" shows "x \<le> \<nu> f"
  by (metis assms gpp_is_gfp is_gfp_gfp is_gpp_def knaster_tarski_gfp knaster_tarski_gpp)

primrec iter :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iter f 0 x = x"
| "iter f (Suc n) x = f (iter f n x)"

lemma iter_mono: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> x \<le> y \<Longrightarrow> iter f n x \<le> iter f n y"
  by (induct n) simp_all

lemma iter_pp: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> f y \<le> y \<Longrightarrow> iter f n y \<le> y"
  apply (induct n)
  apply simp
  by (metis (full_types) iter.simps(2) order_trans)

lemma iter_plus: "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> iter f n bot \<le> iter f (n + m) bot"
proof (induct n)
  case 0 thus ?case
    by auto
next
  case (Suc n)
  thus ?case
    by auto
qed

theorem kleene_lfp:
  assumes scott_continuity: "(\<And>X. directed X \<Longrightarrow> Sup (f ` X) = f (Sup X))"
  shows "\<mu> f = Sup {iter f n bot|n. True}"
proof -
  let ?C = "{iter f n bot|n. True}"
  let ?c = "Sup {iter f n bot|n. True}"

  have directed_C: "directed ?C"
    apply (auto simp add: directed_def)
    apply (rename_tac n m)
    apply (rule_tac x = "iter f (n + m) bot" in exI)
    apply auto
    apply (metis iter_plus scott_continuity scott_continuity_mono)
    by (metis add.commute iter_plus scott_continuity scott_continuity_mono)

  have "f ?c \<le> ?c"
  proof -
    have "f ?c = Sup (f ` ?C)"
      by (metis scott_continuity[OF directed_C])
    also have "... \<le> ?c"
      apply (rule Sup_mono)
      apply (auto simp add: image_def)
      apply (rule_tac x = "iter f (Suc n) bot" in exI)
      apply auto
      by (metis iter.simps(2))
    finally show ?thesis .
  qed

  moreover have "(\<forall>y. f y \<le> y \<longrightarrow> ?c \<le> y)"
  proof clarify
    fix y assume y_fp: "f y \<le> y"
    have "bot \<le> y"
      by (metis bot_least)
    hence "\<forall>n. iter f n bot \<le> iter f n y"
      by (metis scott_continuity scott_continuity_mono iter_mono)
     hence "\<forall>n. iter f n bot \<le> y"
      by (metis scott_continuity scott_continuity_mono iter_pp order_trans y_fp)
    thus "?c \<le> y"
      by (auto intro!: Sup_least)
  qed

  ultimately have "is_lpp ?c f"
    by (auto simp add: is_lpp_def)
  hence "is_lfp ?c f"
    by (metis (full_types) scott_continuity scott_continuity_mono lpp_is_lfp)
  thus "\<mu> f = ?c"
    by (metis lfp_equality)
qed

lemma kleene_gfp:
  assumes continuity: "(\<And>X. Inf (f ` X) = f (Inf X))"
  shows "\<nu> f = Inf {iter f n top|n. True}"
proof -
  let ?C = "{iter f n top|n. True}"
  let ?c = "Inf {iter f n top|n. True}"

  have "?c \<le> f ?c"
  proof -
    have "?c \<le> Inf (f ` ?C)"
      apply (rule Inf_mono)
      apply (auto simp add: image_def)
      apply (rule_tac x = "iter f (Suc n) top" in exI)
      apply auto
      by (metis iter.simps(2))
    also have "... \<le> f ?c"
      by (metis continuity eq_refl)
    finally show ?thesis .
  qed

  moreover have "(\<forall>y. y \<le> f y \<longrightarrow> y \<le> ?c)"
  proof clarify
    fix y assume y_fp: "y \<le> f y"
    have "y \<le> top"
     by (metis top_greatest)
    hence "\<forall>n. iter f n y \<le> iter f n top"
      by (metis continuity Inf_continuity_mono1 iter_mono)
    moreover have "\<forall>n. y \<le> iter f n y"
    proof clarify
      fix n show "y \<le> iter f n y" apply (induct n) apply simp_all
        apply (rule order_trans[of _ "f y"])
        apply (metis y_fp)
        apply (rule Inf_continuity_mono1[OF continuity])
        by auto
    qed
    ultimately have "\<forall>n. y \<le> iter f n top"
      by (metis order_trans)
    thus "y \<le> ?c"
      by (auto intro!: Inf_greatest)
  qed

  ultimately have "is_gpp ?c f"
    by (auto simp add: is_gpp_def)
  hence "is_gfp ?c f"
    by (metis (full_types) Inf_continuity_mono1 continuity gpp_is_gfp)
  thus "\<nu> f = ?c"
    by (metis gfp_equality)
qed

lemma gfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> y \<le> x\<rbrakk> \<Longrightarrow> x = \<nu> f"
  by (metis gfp_equality is_gfp_def)

lemma lfp_equality_var [intro?]: "\<lbrakk>f x = x; \<And>y. f y = y \<Longrightarrow> x \<le> y\<rbrakk> \<Longrightarrow> x = \<mu> f"
  by (metis is_lfp_def lfp_equality)

theorem endo_fixpoint_fusion [simp]:
  assumes upper_ex: "endo_lower_adjoint f"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu> h) = \<mu> k"
proof
  show "k (f (\<mu> h)) = f (\<mu> h)"
    by (metis comm fp_compute hiso isotone_def o_eq_dest_lhs)
next
  fix y assume ky: "k y = y"
  obtain g where conn: "endo_galois_connection f g" by (metis endo_lower_adjoint_def upper_ex)
  have "\<mu> h \<le> g y" using isotoneD[OF hiso]
  proof (rule fp_induct)
    have "f (g y) \<le> y" by (metis conn endo_deflation)
    hence "f (h (g y)) \<le> y" by (metis comm kiso ky isotoneD o_def)
    thus "h (g y) \<le> g y" by (metis conn endo_galois_connection_def)
  qed
  thus "f (\<mu> h) \<le> y" by (metis conn endo_galois_connection_def)
qed

theorem endo_greatest_fixpoint_fusion [simp]:
  assumes lower_ex: "endo_upper_adjoint g"
  and hiso: "isotone h" and kiso: "isotone k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (\<nu> h) = \<nu> k"
proof
  show "k (g (\<nu> h)) = g (\<nu> h)"
    by (metis comm gfp_compute hiso isotone_def o_eq_dest_lhs)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "endo_galois_connection f g" by (metis lower_ex endo_upper_adjoint_def)
  have "f y \<le> \<nu> h" using isotoneD[OF hiso]
  proof (rule gfp_induct)
    have "y \<le> g (f y)" by (metis conn endo_inflation)
    hence "y \<le> g (h (f y))" by (metis (full_types) comm comp_apply isotoneD kiso ky)
    thus "f y \<le> h (f y)" by (metis conn endo_galois_connection_def)
  qed
  thus "y \<le> g (\<nu> h)" by (metis conn endo_galois_connection_def)
qed

end

theorem fixpoint_fusion [simp]:
  fixes k :: "'b::complete_lattice \<Rightarrow> 'b"
  and h :: "'a::complete_lattice \<Rightarrow> 'a"
  and f :: "'a \<Rightarrow> 'b"
  assumes upper_ex: "lower_adjoint f"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu> h) = \<mu> k"
proof
  show "k (f (\<mu> h)) = f (\<mu> h)" using monoD[OF hiso]
    by (metis comm fp_compute o_eq_dest_lhs)
next
  fix y :: "'b" assume ky: "k y = y"
  obtain g where conn: "galois_connection f g" by (metis lower_adjoint_def upper_ex)
  have "\<mu> h \<le> g y"
  proof (rule fp_induct)
    fix x y :: 'a assume "x \<le> y" thus "h x \<le> h y"
      by (rule monoD[OF hiso])
  next
    have "f (g y) \<le> y" by (metis conn deflation)
    hence "f (h (g y)) \<le> y" by (metis comm kiso ky monoD o_def)
    thus "h (g y) \<le> g y" by (metis conn galois_connection_def)
  qed
  thus "f (\<mu> h) \<le> y" by (metis conn galois_connection_def)
qed

theorem greatest_fixpoint_fusion [simp]:
  fixes k :: "'b::complete_lattice \<Rightarrow> 'b"
  and h :: "'a::complete_lattice \<Rightarrow> 'a"
  and f :: "'a \<Rightarrow> 'b"
  assumes lower_ex: "upper_adjoint g"
  and hiso: "mono h" and kiso: "mono k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (\<nu> h) = \<nu> k"
proof
  show "k (g (\<nu> h)) = g (\<nu> h)" using monoD[OF hiso]
    by (metis (full_types) comm comp_apply gfp_compute)
next
  fix y assume ky: "k y = y"
  obtain f where conn: "galois_connection f g" by (metis lower_ex upper_adjoint_def)
  have "f y \<le> \<nu> h"
  proof (rule gfp_induct)
    fix x y :: 'a assume "x \<le> y" thus "h x \<le> h y"
      by (rule monoD[OF hiso])
  next
    have "y \<le> g (f y)" by (metis conn inflation)
    hence "y \<le> g (h (f y))" by (metis (full_types) comm comp_apply monoD kiso ky)
    thus "f y \<le> h (f y)" by (metis conn galois_connection_def)
  qed
  thus "y \<le> g (\<nu> h)" by (metis conn galois_connection_def)
qed

definition join_preserving :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool" where
  "join_preserving f \<equiv> \<forall>X. Sup (f ` X) = f (Sup X)"

definition meet_preserving :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool" where
  "meet_preserving g \<equiv> \<forall>X. Inf (g ` X) = g (Inf X)"

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma (in complete_lattice) Sup_eq_equiv: "Sup A = x \<longleftrightarrow> (\<forall>z. (x \<le> z \<longleftrightarrow> (\<forall>y\<in>A. y \<le> z)))"
  apply default
  apply (metis Sup_le_iff)
  by (metis (full_types) Sup_le_iff Sup_upper le_iff_inf less_infI2 less_le order_refl)

lemma (in complete_lattice) Inf_eq_equiv: "Inf A = x \<longleftrightarrow> (\<forall>z. (z \<le> x \<longleftrightarrow> (\<forall>y\<in>A. z \<le> y)))"
  apply default
  apply (metis Inf_greatest Inf_lower order_trans)
  by (metis Inf_atLeast Inf_lower Inf_superset_mono atLeast_def mem_Collect_eq order.antisym subsetI)

lemma lower_adjoint_Sup:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes "Sup X = x" and "lower_adjoint f" shows "Sup (f ` X) = f x" using assms
  apply (simp add: Sup_eq_equiv lower_adjoint_def)
  apply (erule exE)
  apply (simp add: galois_ump2 mono_def)
  apply (erule conjE)+
  by (metis (mono_tags, hide_lams) SUP_le_iff SUP_upper eq_iff order.trans)

lemma lower_preserves_join: "lower_adjoint f \<Longrightarrow> join_preserving f"
  by (metis join_preserving_def lower_adjoint_Sup)

theorem suprema_galois: "galois_connection f g = (join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y))"
proof (intro iffI conjI)
  assume "galois_connection f g"
  hence "lower_adjoint f"
    by (metis lower_adjoint_def)
  thus "join_preserving f"
    by (rule lower_preserves_join)
  from `galois_connection f g`
  show "\<forall>y. Sup {x. f x \<le> y} = g y"
    by (simp add: Sup_eq_equiv galois_ump2 mono_def) (metis (full_types) order_trans)
next
  assume "join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)"
  hence f_jp: "join_preserving f" and a2: "\<And>y. Sup {x. f x \<le> y} = g y"
    by auto
  have f_iso: "mono f"
    apply (rule monoI)
    apply (rule continuity_mono) back
    apply (metis f_jp join_preserving_def)
    by simp
  show "galois_connection f g"
  proof (simp add: galois_connection_def)
    have "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
      using a2 by (auto simp only: Sup_eq_equiv)
    moreover have "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
    proof (intro impI allI)
      fix x y
      assume gr: "x \<le> g y"
      show "f x \<le> y"
      proof -
        have lem: "Sup (f ` {x. f x \<le> y}) \<le> y"
          by (rule Sup_least) auto

        have "f x \<le> y \<Longrightarrow> x \<le> Sup {z. f z \<le> y}"
          by (metis `join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` gr)
        moreover have "x \<le> Sup {z. f z \<le> y} \<Longrightarrow> f x \<le> f (Sup {z. f z \<le> y})"
          by (metis f_iso monoD)
        moreover have "(f x \<le> f (Sup {z. f z \<le> y})) = (f x \<le> Sup (f ` {z. f z \<le> y}))"
          by (metis (full_types) `join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` join_preserving_def)
        moreover have "... \<Longrightarrow> f x \<le> y" using lem
          by (metis order_trans)
        ultimately show ?thesis
          by (metis `join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` gr)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)"
      by auto
  qed
qed

lemma lower_is_jp: "lower_adjoint f \<longleftrightarrow> join_preserving f"
proof
  assume "lower_adjoint f" thus "join_preserving f"
    by (metis lower_preserves_join)
next
  assume "join_preserving f"
  moreover hence "\<exists>g. \<forall>y. Sup {x. f x \<le> y} = g y"
    by auto
  ultimately show "lower_adjoint f"
    by (metis (full_types) lower_adjoint_def suprema_galois)
qed

context complete_lattice begin

definition endo_join_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "endo_join_preserving f \<equiv> \<forall>X. Sup (f ` X) = f (Sup X)"

definition endo_meet_preserving :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "endo_meet_preserving g \<equiv> \<forall>X. Inf (g ` X) = g (Inf X)"

(* +------------------------------------------------------------------------+
   | Theorems 4.25(a) and 4.25(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma endo_lower_adjoint_Sup: "Sup X = x \<Longrightarrow> endo_lower_adjoint f \<Longrightarrow> Sup (f ` X) = f x"
  apply (simp only: Sup_eq_equiv endo_lower_adjoint_def)
  apply (erule exE)
  apply (simp add: endo_galois_ump2 isotone_def)
  apply (erule conjE)+
  apply auto
  apply (metis local.endo_galois_ump1 local.endo_galois_ump2 local.isotone_def)
  by (metis local.dual_order.trans)

lemma endo_lower_preserves_join: "endo_lower_adjoint f \<Longrightarrow> endo_join_preserving f"
  by (metis endo_join_preserving_def endo_lower_adjoint_Sup)

theorem endo_suprema_galois: "endo_galois_connection f g = (endo_join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y))"
proof (intro iffI conjI)
  assume "endo_galois_connection f g"
  hence "endo_lower_adjoint f"
    by (metis endo_lower_adjoint_def)
  thus "endo_join_preserving f"
    by (rule endo_lower_preserves_join)
  from `endo_galois_connection f g`
  show "\<forall>y. Sup {x. f x \<le> y} = g y"
    by (simp add: Sup_eq_equiv endo_galois_ump2 isotone_def) (metis (full_types) order_trans)
next
  assume "endo_join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)"
  hence f_jp: "endo_join_preserving f" and a2: "\<And>y. Sup {x. f x \<le> y} = g y"
    by auto
  hence f_iso: "isotone f"
    by (metis (mono_tags) continuity_mono1 endo_join_preserving_def isotone_def)
  show "endo_galois_connection f g"
  proof (simp add: endo_galois_connection_def)
    have "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
      using a2 by (auto simp only: Sup_eq_equiv)
    moreover have "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
    proof (intro impI allI)
      fix x y
      assume gr: "x \<le> g y"
      show "f x \<le> y"
      proof -
        have lem: "Sup (f ` {x. f x \<le> y}) \<le> y"
          by (metis (full_types) SUP_def SUP_le_iff mem_Collect_eq)

        have "f x \<le> y \<Longrightarrow> x \<le> Sup {z. f z \<le> y}"
          by (metis `endo_join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` gr)
        moreover have "x \<le> Sup {z. f z \<le> y} \<Longrightarrow> f x \<le> f (Sup {z. f z \<le> y})"
          by (metis f_iso isotoneD)
        moreover have "(f x \<le> f (Sup {z. f z \<le> y})) = (f x \<le> Sup (f ` {z. f z \<le> y}))"
          by (metis (full_types) `endo_join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` endo_join_preserving_def)
        moreover have "... \<Longrightarrow> f x \<le> y" using lem
          by (metis order_trans)
        ultimately show ?thesis
          by (metis `endo_join_preserving f \<and> (\<forall>y. Sup {x. f x \<le> y} = g y)` gr)
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)"
      by auto
  qed
qed

lemma endo_lower_is_jp: "endo_lower_adjoint f \<longleftrightarrow> endo_join_preserving f"
proof
  assume "endo_lower_adjoint f" thus "endo_join_preserving f"
    by (metis endo_lower_preserves_join)
next
  assume "endo_join_preserving f"
  moreover hence "\<exists>g. \<forall>y. Sup {x. f x \<le> y} = g y"
    by auto
  ultimately show "endo_lower_adjoint f"
    by (metis (full_types) endo_lower_adjoint_def endo_suprema_galois)
qed

lemma endo_upper_adjoint_Inf: "Inf X = x \<Longrightarrow> endo_upper_adjoint f \<Longrightarrow> Inf (f ` X) = f x"
  apply (simp only: Inf_eq_equiv endo_upper_adjoint_def)
  apply (erule exE)
  apply (simp add: endo_galois_ump2 isotone_def)
  apply (erule conjE)+
  apply auto
  apply (metis local.dual_order.trans)
  by (metis order_trans)

lemma endo_upper_preserves_meet: "endo_upper_adjoint f \<Longrightarrow> endo_meet_preserving f"
  by (metis endo_meet_preserving_def endo_upper_adjoint_Inf)

theorem endo_infima_galois: "endo_galois_connection f g = (endo_meet_preserving g \<and> (\<forall>y. Inf {x. y \<le> g x} = f y))"
proof (intro iffI conjI)
  assume "endo_galois_connection f g"
  hence "endo_upper_adjoint g"
    by (metis endo_upper_adjoint_def)
  thus "endo_meet_preserving g"
    by (rule endo_upper_preserves_meet)
  from `endo_galois_connection f g`
  show "\<forall>y. Inf {x. y \<le> g x} = f y"
    by (simp add: Inf_eq_equiv endo_galois_ump1 isotone_def) (metis (full_types) order_trans)
next
  assume "endo_meet_preserving g \<and> (\<forall>y. Inf {x. y \<le> g x} = f y)"
  hence f_jp: "endo_meet_preserving g" and a2: "\<And>y. Inf {x. y \<le> g x} = f y"
    by auto
  hence f_iso: "isotone g"
    by (metis (mono_tags) continuity_mono2 endo_meet_preserving_def isotone_def)
  show "endo_galois_connection f g"
  proof (simp add: endo_galois_connection_def)
    have "\<forall>x y. (x \<le> g y) \<longrightarrow> (f x \<le> y)"
      using a2 by (metis Inf_lower mem_Collect_eq)
    moreover have "\<forall>x y. (f x \<le> y) \<longrightarrow> (x \<le> g y)"
    proof (intro impI allI)
      fix x y
      assume gr: "f x \<le> y"
      thus "x \<le> g y"
      proof -
        have lem: "x \<le> Inf (g ` {y. x \<le> g y})"
          by (metis (full_types) INF_def INF_greatest mem_Collect_eq)

        also have "... \<le> g y"
          by (metis (mono_tags) `endo_meet_preserving g \<and> (\<forall>y. Inf {x. y \<le> g x} = f y)` endo_meet_preserving_def f_iso gr isotoneD)

        finally show ?thesis .
      qed
    qed
    ultimately show "\<forall>x y. (f x \<le> y) = (x \<le> g y)"
      by auto
  qed
qed

(* Dual theorem *)
lemma endo_upper_is_mp: "endo_upper_adjoint g \<longleftrightarrow> endo_meet_preserving g"
proof
  assume "endo_upper_adjoint g" thus "endo_meet_preserving g"
    by (metis endo_upper_preserves_meet)
next
  assume "endo_meet_preserving g"
  moreover hence "\<exists>f. \<forall>x. Inf {y. x \<le> g y} = f x"
    by auto
  ultimately show "endo_upper_adjoint g"
    by (metis endo_infima_galois endo_upper_adjoint_def)
qed

end

end
