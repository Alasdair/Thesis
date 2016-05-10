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

  lemma par_double_iso [intro!]: "w \<le> x \<Longrightarrow> y \<le> z \<Longrightarrow> w \<parallel> y \<le> x \<parallel> z"
    by (metis order_trans par_isol par_isor)

end

class weak_trioid = par_dioid + dioid_one_zerol

class trioid = par_dioid + left_kleene_algebra + residual_r_op +
  fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<otimes>" 69)
  assumes meet_leq: "(x \<le> y) \<longleftrightarrow> (x = x \<otimes> y)"
  and meet_assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  and meet_sym: "x \<otimes> y = y \<otimes> x"
  and preimp_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"

begin

  lemma meet_idem [simp]: "x \<otimes> x = x"
    by (metis local.meet_leq local.order_refl)

  lemma meet_1 [simp]: "x \<otimes> y \<le> y"
    by (simp add: meet_leq meet_assoc)

  lemma meet_2 [simp]: "y \<otimes> x \<le> y"
    by (metis local.meet_sym meet_1)

  lemma preimp_isor: "x \<le> y \<Longrightarrow> p \<rightarrow> x \<le> p \<rightarrow> y"
    by (metis local.order.trans local.order_refl local.preimp_galois)

  lemma meet_is_meet: "x \<le> y \<otimes> z \<longleftrightarrow> (x \<le> y) \<and> (x \<le> z)"
    by (metis (poly_guards_query) local.meet_assoc local.meet_leq local.meet_sym meet_idem)

  lemma meet_interchange: "(x \<otimes> y) \<parallel> (z \<otimes> w) \<le> (x \<parallel> z) \<otimes> (y \<parallel> w)"
    by (auto simp add: meet_is_meet)

  lemma meet_iso: "x \<le> y \<Longrightarrow> z \<le> w \<Longrightarrow> x \<otimes> z \<le> y \<otimes> w"
    by (metis local.meet_leq meet_idem meet_is_meet)

  lemma absorb1: "x \<otimes> (x + y) = x"
    by (rule antisym) (simp add: meet_is_meet)+
    
  lemma absorb2: "x + (x \<otimes> y) = x"
    by (metis add_commute local.less_eq_def meet_2)

end 

locale rg_algebra =
  fixes rg :: "'b::complete_lattice \<Rightarrow> 'a::trioid \<Rightarrow> 'a::trioid" (infixr "\<rhd>" 55)
  and guar :: "'b::complete_lattice \<Rightarrow> 'a::trioid"
  assumes rely_mult: "(r \<rhd> x) \<cdot> (r \<rhd> y) \<le> r \<rhd> (x \<cdot> y)"
  and rely_star: "(r \<rhd> x)\<^sup>\<star> \<le> r \<rhd> (x\<^sup>\<star>)"
  and rely_iso: "x \<le> y \<Longrightarrow> r \<rhd> x \<le> r \<rhd> y"
  and rely_coext: "x \<le> r \<rhd> x"
  and rely_idem: "r \<rhd> r \<rhd> x = r \<rhd> x"
  and rely_anti: "r \<le> g \<Longrightarrow> g \<rhd> x \<le> r \<rhd> x"
  and guar_par: "guar r \<parallel> guar g \<le> guar (r \<squnion> g)"
  and guar_mult: "guar r \<cdot> guar g \<le> guar (r \<squnion> g)"
  and guar_star: "(guar g)\<^sup>\<star> = guar g"
  and guar_meet: "(x \<otimes> guar g) \<cdot> (y \<otimes> guar g) = x\<cdot>y \<otimes> guar g"
  and rely_guarantee: "(r \<squnion> g\<^sub>2 \<rhd> x \<otimes> guar g\<^sub>1) \<parallel> (r \<squnion> g\<^sub>1 \<rhd> y \<otimes> guar g\<^sub>2) \<le> r \<rhd> (x \<otimes> guar g\<^sub>1) \<parallel> (y \<otimes> guar g\<^sub>2)"
  and guar_iso: "r \<le> s \<Longrightarrow> guar r \<le> guar s"

begin

definition quintuple :: "'b \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_, _ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [20,20,20,20,20] 1000) where
    "r, g \<turnstile> \<lbrace>p\<rbrace> x \<lbrace>q\<rbrace> \<equiv> (x \<le> p \<rightarrow> (r \<rhd> q \<otimes> guar g))"

lemma parallel_rule:
  assumes test_interchange: "\<And>x y. (p\<^sub>1 \<rightarrow> x) \<parallel> (p\<^sub>2 \<rightarrow> y) \<le> (p\<^sub>1 \<otimes> p\<^sub>2) \<rightarrow> (x \<parallel> y)"
  and test_post: "(q\<^sub>1 \<parallel> q\<^sub>2) \<otimes> guar g \<le> r \<rhd> q\<^sub>1 \<otimes> q\<^sub>2 \<otimes> guar g"
  and "r \<squnion> g\<^sub>1 \<le> r\<^sub>2" and "r \<squnion> g\<^sub>2 \<le> r\<^sub>1"
  and "g\<^sub>1 \<squnion> g\<^sub>2 \<le> g"
  and left_prog: "r\<^sub>1, g\<^sub>1 \<turnstile> \<lbrace>p\<^sub>1\<rbrace> x \<lbrace>q\<^sub>1\<rbrace>"
  and right_prog: "r\<^sub>2, g\<^sub>2 \<turnstile> \<lbrace>p\<^sub>2\<rbrace> y \<lbrace>q\<^sub>2\<rbrace>"
  shows "r, g \<turnstile> \<lbrace>p\<^sub>1 \<otimes> p\<^sub>2\<rbrace> x \<parallel> y \<lbrace>q\<^sub>1 \<otimes> q\<^sub>2\<rbrace>"
proof -
  have "x \<parallel> y \<le> (p\<^sub>1 \<rightarrow> (r\<^sub>1 \<rhd> q\<^sub>1 \<otimes> guar g\<^sub>1)) \<parallel> (p\<^sub>2 \<rightarrow> (r\<^sub>2 \<rhd> q\<^sub>2 \<otimes> guar g\<^sub>2))"
    by (metis left_prog par_double_iso quintuple_def right_prog)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r\<^sub>1 \<rhd> q\<^sub>1 \<otimes> guar g\<^sub>1) \<parallel> (r\<^sub>2 \<rhd> q\<^sub>2 \<otimes> guar g\<^sub>2)"
    by (rule test_interchange)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<squnion> g\<^sub>2 \<rhd> q\<^sub>1 \<otimes> guar g\<^sub>1) \<parallel> (r \<squnion> g\<^sub>1 \<rhd> q\<^sub>2 \<otimes> guar g\<^sub>2)"
    by (metis assms(3) assms(4) par_double_iso preimp_isor rely_anti)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<rhd> (q\<^sub>1 \<otimes> guar g\<^sub>1) \<parallel> (q\<^sub>2 \<otimes> guar g\<^sub>2))"
    by (metis preimp_isor rely_guarantee)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<rhd> (q\<^sub>1 \<parallel> q\<^sub>2) \<otimes> (guar g\<^sub>1 \<parallel> guar g\<^sub>2))"
    by (intro preimp_isor rely_iso meet_interchange)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<rhd> (q\<^sub>1 \<parallel> q\<^sub>2) \<otimes> guar g)"
    by (metis (poly_guards_query) assms(5) guar_iso guar_par meet_2 meet_is_meet meet_sym order_trans preimp_isor rely_iso)
  also have "... \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<rhd> (q\<^sub>1 \<otimes> q\<^sub>2) \<otimes> guar g)"
    by (metis preimp_isor rely_idem rely_iso test_post)
  finally have "x \<parallel> y \<le> p\<^sub>1 \<otimes> p\<^sub>2 \<rightarrow> (r \<rhd> (q\<^sub>1 \<otimes> q\<^sub>2) \<otimes> guar g)" .
  thus ?thesis
    by (simp only: quintuple_def[symmetric])
qed

end

end
