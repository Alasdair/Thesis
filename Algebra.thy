theory Algebra
  imports "$AFP/Kleene_Algebra/Kleene_Algebra" Fixpoint Omega_Algebra
begin

notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)

class par_dioid = join_semilattice_zero + one +
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<parallel>" 69)
  assumes par_assoc [simp]: "x \<parallel> (y \<parallel> z) = (x \<parallel> y) \<parallel> z"
  and par_comm: "x \<parallel> y = y \<parallel> x"
  and par_distl [simp]: "x \<parallel> (y + z) = x \<parallel> y + x \<parallel> z"
  and par_unitl [simp]: "1 \<parallel> x = x"
  and par_annil [simp]: "0 \<parallel> x = 0"

begin

  lemma par_distr [simp]: "(x+y) \<parallel> z = x \<parallel> z + y \<parallel> z" 
    by (metis par_comm par_distl)

  lemma par_isol [intro]: "x \<le> y \<Longrightarrow> x \<parallel> z \<le> y \<parallel> z"
    by (metis order_prop par_distr)
 
  lemma par_isor [intro]: "x \<le> y \<Longrightarrow> z \<parallel> x \<le> z \<parallel> y"
    by (metis par_comm par_isol)

  lemma par_unitr [simp]: "x \<parallel> 1 = x"
    by (metis par_comm par_unitl)

  lemma par_annir [simp]: "x \<parallel> 0 = 0"
    by (metis par_annil par_comm)

  lemma par_subdistl: "x \<parallel> z \<le> (x + y) \<parallel> z"
    by (metis order_prop par_distr)

  lemma par_subdistr: "z \<parallel> x \<le> z \<parallel> (x + y)"
    by (metis par_comm par_subdistl)

  lemma par_double_iso [intro]: "w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> w \<parallel> y \<le> x \<parallel> z"
    by (metis order_trans par_isol par_isor)

end

class weak_trioid = par_dioid + dioid_one_zerol

class trioid = par_dioid + dioid_one_zero + complete_lattice

locale rg_algebra =
  fixes restrict :: "'b::complete_lattice \<Rightarrow> 'a::trioid \<Rightarrow> 'a::trioid" (infixr "\<Colon>" 55)
  and rg :: "'b::complete_lattice \<Rightarrow> 'a::trioid \<Rightarrow> 'a::trioid" (infixr "\<leadsto>" 55)
  and guar :: "'b::complete_lattice \<Rightarrow> 'a::trioid"
  assumes mod_coext: "r \<Colon> x \<le> x"
  and guar_iso: "r \<le> s \<Longrightarrow> guar r \<le> guar s"
  and mod_top: "top \<Colon> x = x"
  and rg_top: "top \<leadsto> x = x"
  and mod_inter: "r \<sqinter> s \<Colon> x = r \<Colon> s \<Colon> x"
  and mod_isotone: "r \<le> s \<Longrightarrow> r \<Colon> x \<le> s \<Colon> x"
  and galois: "(r \<Colon> x \<le> y) \<longleftrightarrow> (x \<le> r \<leadsto> y)"
  and rg_antitone: "r \<le> s  \<Longrightarrow> s \<leadsto> x \<le> r \<leadsto> x"
  and guar_par: "guar g1 \<parallel> guar g2 = guar (g1 \<squnion> g2)"

  and rg_axiom: "r \<Colon> (r \<squnion> g2 \<leadsto> guar g1 \<sqinter> x) \<parallel> (r \<squnion> g1 \<leadsto> guar g2 \<sqinter> y) \<le> (guar g1 \<sqinter> x) \<parallel> (guar g2 \<sqinter> y)"

begin

  lemma rg_axiom_var: "(r \<squnion> g2 \<leadsto> guar g1 \<sqinter> x) \<parallel> (r \<squnion> g1 \<leadsto> guar g2 \<sqinter> y) \<le> r \<leadsto> (guar g1 \<sqinter> x) \<parallel> (guar g2 \<sqinter> y)"
    by (metis galois rg_axiom)

  lemma rg_ext: "x \<le> r \<leadsto> x"
    by (metis galois mod_coext)

  lemma mod_prog_iso: "x \<le> y \<Longrightarrow> r \<Colon> x \<le> r \<Colon> y"
    by (metis ab_semigroup_add_class.add_ac(1) dual_order.order_iff_strict galois order_prop)

  lemma rg_prog_iso: "x \<le> y \<Longrightarrow> r \<leadsto> x \<le> r \<leadsto> y"
    by (metis dual_order.trans galois order_refl)

  lemma rg_mono: "r \<le> s \<Longrightarrow> x \<le> y \<Longrightarrow> s \<leadsto> x \<le> r \<leadsto> y"
    by (metis galois rg_antitone sup.coboundedI1 sup.orderE sup_commute)

  lemma "r \<squnion> s \<leadsto> x \<le> r \<leadsto> s \<leadsto> x"
    apply (rule rg_mono)
    apply (metis sup.cobounded1)
    by (metis rg_ext)

  lemma "r \<Colon> r \<leadsto> x \<le> r \<Colon> x"
    by (metis galois inf_idem mod_inter mod_prog_iso order_refl)

  definition quintuple :: "'b \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [20,20,20,20,20] 1000) where
    "r, g \<turnstile> \<lbrace>p\<rbrace> x \<lbrace>q\<rbrace> \<equiv> (p \<cdot> x \<le> r \<leadsto> guar g \<sqinter> q) \<and> (guar r \<parallel> q \<le> q)"

  lemma "r \<Colon> r \<leadsto> x \<le> r \<Colon> x"
    by (metis galois inf_idem mod_inter mod_prog_iso order_refl)

  lemma "r \<leadsto> x \<le> r \<leadsto> r \<Colon> x"
    by (metis galois inf_idem mod_inter mod_prog_iso order_refl)

  lemma rely_swap: "r \<Colon> r \<leadsto> x \<le> r \<leadsto> r \<Colon> x"
    by (metis galois order_refl rg_prog_iso)

  theorem parallel_rule:
    assumes "r \<squnion> g1 \<le> r2"
    and "r \<squnion> g2 \<le> r1"
    and "g1 \<squnion> g2 \<le> g"
    and "r1, g1 \<turnstile> \<lbrace>p\<rbrace> x \<lbrace>q1\<rbrace>"
    and "r2, g2 \<turnstile> \<lbrace>p\<rbrace> y \<lbrace>q2\<rbrace>"
    and "p \<cdot> (x \<parallel> y) \<le> p \<cdot> x \<parallel> p \<cdot> y"
    shows "r, g \<turnstile> \<lbrace>p\<rbrace> x \<parallel> y \<lbrace>q1 \<sqinter> q2\<rbrace>"
  proof -
    from assms(5) have g1_preserves_q2: "guar g1 \<parallel> q2 \<le> q2"
      by (simp add: quintuple_def) (metis assms(1) dual_order.trans guar_iso par_isol sup.boundedE)

    from assms(5) have r2_preserves_q2: "guar r2 \<parallel> q2 \<le> q2"
      by (simp add: quintuple_def)

    from assms(4) have g2_preserves_q1: "q1 \<parallel> guar g2 \<le> q1"
      by (simp add: quintuple_def) (metis assms(2) guar_iso par_comm par_isor sup.boundedE sup_absorb2)

    from assms(4) have r1_preserves_q1: "guar r1 \<parallel> q1 \<le> q1"
      by (simp add: quintuple_def)

    have "p \<cdot> (x \<parallel> y) \<le> p \<cdot> x \<parallel> p \<cdot> y"
      by (metis assms(6))
    also have "... \<le> (r1 \<leadsto> guar g1 \<sqinter> q1) \<parallel> (r2 \<leadsto> guar g2 \<sqinter> q2)"
      by (metis assms(4) assms(5) par_double_iso quintuple_def)
    also have "... \<le> (r \<squnion> g2 \<leadsto> guar g1 \<sqinter> q1) \<parallel> (r \<squnion> g1 \<leadsto> guar g2 \<sqinter> q2)"
      by (metis assms(1) assms(2) par_double_iso rg_antitone)
    also have "... \<le> r \<leadsto> (guar g1 \<sqinter> q1) \<parallel> (guar g2 \<sqinter> q2)"
      by (metis rg_axiom_var)
    also have "... \<le> r \<leadsto> guar (g1 \<squnion> g2) \<sqinter> (q1 \<sqinter> q2)"
      apply (auto intro!: rg_prog_iso)
      apply (metis guar_par inf.cobounded2 inf_commute par_double_iso)
      apply (metis g2_preserves_q1 inf_commute inf_sup_ord(2) order.trans par_double_iso)
      by (metis g1_preserves_q2 inf.bounded_iff inf.cobounded2 inf_absorb2 par_double_iso)
    finally have "p \<cdot> (x \<parallel> y) \<le> r \<leadsto> guar (g1 \<squnion> g2) \<sqinter> (q1 \<sqinter> q2)" .
    moreover have "guar r \<parallel> q1 \<sqinter> q2 \<le> q1 \<sqinter> q2"
      apply auto
      apply (metis assms(2) guar_iso inf_sup_ord(1) order_trans par_double_iso r1_preserves_q1 sup.boundedE)
      by (metis assms(1) guar_iso inf_sup_ord(2) order_trans par_double_iso r2_preserves_q2 sup.boundedE)
    ultimately show ?thesis
      apply (simp add: quintuple_def)
      apply (erule order_trans)
      by (metis assms(3) guar_iso inf_mono order_refl rg_prog_iso)
  qed

end

end
