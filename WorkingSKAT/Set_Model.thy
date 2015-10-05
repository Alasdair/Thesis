theory Set_Model
  imports Lattice
begin

definition SET where "SET \<equiv> \<lparr>carrier = UNIV, le = op \<subseteq>\<rparr>"

lemma SET_ord [intro]: "order SET"
  by (auto simp add: order_def SET_def)

lemma SET_js [intro]: "join_semilattice SET"
  by (auto simp add: join_semilattice_def join_semilattice_axioms_def order.is_lub_simp[OF SET_ord] intro: SET_ord) (auto simp add: SET_def)

lemma SET_ms [intro]: "meet_semilattice SET"
  by (auto simp add: meet_semilattice_def meet_semilattice_axioms_def order.is_glb_simp[OF SET_ord] intro: SET_ord) (auto simp add: SET_def)

lemma SET_lattice [intro]: "lattice SET"
  by (auto simp add: lattice_def intro: SET_ms SET_js)

lemma SET_meet [simp]: "x \<sqinter>\<^bsub>SET\<^esub> y = x \<inter> y"
  apply (simp add: order.meet_def[OF SET_ord] order.glb_def[OF SET_ord])
  apply (rule the1I2)
  apply auto
  apply (rule_tac x = "x \<inter> y" in exI)
  apply (simp add: order.is_glb_simp[OF SET_ord])
  apply (simp add: SET_def)
  apply (simp add: order.is_glb_simp[OF SET_ord], simp add: SET_def, blast)
  apply (simp add: order.is_glb_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_glb_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_glb_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_glb_simp[OF SET_ord], simp add: SET_def, blast)
  done

lemma SET_join [simp]: "x \<squnion>\<^bsub>SET\<^esub> y = x \<union> y"
  apply (simp add: order.join_def[OF SET_ord] order.lub_def[OF SET_ord])
  apply (rule the1I2)
  apply auto
  apply (rule_tac x = "x \<union> y" in exI)
  apply (simp add: order.is_lub_simp[OF SET_ord])
  apply (simp add: SET_def)
  apply (simp add: order.is_lub_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_lub_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_lub_simp[OF SET_ord], simp add: SET_def, blast)
  apply (simp add: order.is_lub_simp[OF SET_ord], simp add: SET_def, metis in_mono)
  apply (simp add: order.is_lub_simp[OF SET_ord], simp add: SET_def, blast)
  done

lemma SET_distrib [intro]: "distributive_lattice SET"
  by (auto simp add: distributive_lattice_def distributive_lattice_axioms_def intro: SET_lattice)

lemma SET_bounded [intro]: "bounded_lattice SET"
  by (simp add: bounded_lattice_def bounded_lattice_axioms_def SET_lattice) (auto simp add: SET_def)

lemma SET_top [simp]: "bounded_lattice.top SET = UNIV"
  by (simp add: bounded_lattice.top_def[OF SET_bounded], rule the1I2, auto simp add: SET_def)

lemma SET_bot [simp]: "bounded_lattice.bot SET = {}"
  by (simp add: bounded_lattice.bot_def[OF SET_bounded], rule the1I2, auto simp add: SET_def)

lemma SET_compl [intro]: "complemented_lattice SET"
  apply (simp add: complemented_lattice_def SET_bounded complemented_lattice_axioms_def)
  apply (simp add: SET_def)
  apply safe
  apply (rule_tac x = "-x" in exI)
  apply (rule conjI)
  by blast+

lemma SET_ba [intro]: "boolean_algebra SET"
  by (auto simp add: boolean_algebra_def)

lemma SET_cjs [intro]: "complete_join_semilattice SET"
  apply (auto simp add: complete_join_semilattice_def complete_join_semilattice_axioms_def)
  apply (rule_tac x = "\<Union>X" in bexI)
  apply (simp add: order.is_lub_simp[OF SET_ord])
  apply (auto simp add: SET_def)
  done

lemma SET_cms [intro]: "complete_meet_semilattice SET"
  by (metis SET_cjs complete_join_semilattice.is_cms)

lemma SET_cl [intro]: "complete_lattice SET"
  by (auto simp add: complete_lattice_def)

lemma SET_top_var [simp]: "complete_meet_semilattice.top SET = UNIV"
  by (simp add: complete_meet_semilattice.top_def[OF SET_cms], rule the1I2, auto simp add: SET_def)

lemma SET_bot_var [simp]: "complete_join_semilattice.bot SET = {}"
  by (simp add: complete_join_semilattice.bot_def[OF SET_cjs], rule the1I2, auto simp add: SET_def)

lemma SET_cbl: "complete_boolean_lattice SET"
  by (auto simp add: complete_boolean_lattice_def complete_boolean_lattice_axioms_def, rule_tac x = "-x" in exI, auto simp add: SET_def)

end
