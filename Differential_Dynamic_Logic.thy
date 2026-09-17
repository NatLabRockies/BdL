(***************************************************************)
(**                                                           **)
(**                                                           **)
(** Author(s): Yakoub Nemouchi (NLR, Golden, CO, USA)         **)
(**            Peter  Graf     (NLR, Golden, CO, USA)         **)
(** Email: Yakoub.Nemouchi@nlr.gov                            **)
(**                                                           **) 
(** See CONTRIBUTORS, LICENSE and CITATION files for details. **)
(***************************************************************)
theory Differential_Dynamic_Logic

imports Real_Analysis_More
begin
section \<open>Differential Dynamic Logic\<close>
subsection \<open>Differential Induction\<close>

lemma DI_Generic:
  assumes iv: \<open>0 \<le> invar (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes induct_step:
          \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                      0 \<le> Dinvar (f \<tau> (y \<tau>)) \<close>
  assumes t: \<open>0 \<le> (t::real)\<close>
  shows \<open>(0::real) \<le> invar (y t)\<close>
proof -
  have invar_vderiv: 
    \<open>((\<lambda>\<tau>. invar (y \<tau>)) has_vderiv_on
      (\<lambda>\<tau>. (SOME Dinvar. (invar has_derivative Dinvar) (at (y \<tau>))) (f \<tau> (y \<tau>)))) {0..t}\<close>
    unfolding has_vderiv_on_def has_vector_derivative_def
  proof
    fix x assume hx: \<open>x \<in> {0..t}\<close>
    then have hx0: \<open>0 \<le> x\<close> and hxt: \<open>x \<le> t\<close> 
           by auto
    obtain Dinvar where
      invar_at_x: "(invar has_derivative Dinvar) (at (y x))" and
      ineq:       "Dinvar (f x (y x)) \<ge> 0"
      using induct_step hx 
        by blast
    have Dinvar_eq: \<open>(SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) = Dinvar\<close>
      using invar_at_x
      by (metis frechet_derivative_at frechet_derivative_def)
    have y_deriv: "(y has_derivative (\<lambda>v. v *\<^sub>R f x (y x))) (at x within {0..t})"
      using ODE hx
      by (simp add: has_vderiv_on_def has_vector_derivative_def solves_ode_def)
    have chain: "((invar \<circ> y) has_derivative (Dinvar \<circ> (\<lambda>v. v *\<^sub>R f x (y x))))
                 (at x within {0..t})"
      apply (rule diff_chain_within)
       apply (rule y_deriv)
      using invar_at_x has_derivative_at_withinI
      apply blast
      done
    have eq: "(Dinvar \<circ> (\<lambda>v. v *\<^sub>R f x (y x))) = (\<lambda>xa. xa *\<^sub>R Dinvar (f x (y x)))"
      using invar_at_x
      by (auto simp add: comp_def has_derivative_bounded_linear linear_simps(5))
    show \<open>((\<lambda>\<tau>. invar (y \<tau>)) has_derivative
           (\<lambda>xa. xa *\<^sub>R
                 (SOME Dinvar. (invar has_derivative Dinvar) (at (y x)))
                  (f x (y x))))
           (at x within {0..t})\<close>
      apply (rule has_derivative_eq_rhs)
       apply (rule chain[unfolded comp_def])
      using Dinvar_eq eq
      apply (auto simp add:  comp_def)
      done
  qed
  have deriv_nonneg: 
    \<open>\<And>x. x \<in> {0..t} \<Longrightarrow>
         0 \<le> (SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) (f x (y x))\<close>
  proof -
    fix x assume hx: "x \<in> {0..t}"
    obtain Dinvar where
      invar_at_x: "(invar has_derivative Dinvar) (at (y x))" and
      ineq:       "Dinvar (f x (y x)) \<ge> 0"
      using induct_step hx 
      by blast
    have Dinvar_eq: \<open>(SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) = Dinvar\<close>
      using invar_at_x
      by (metis frechet_derivative_at frechet_derivative_def)
    show \<open>0 \<le> (SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) (f x (y x))\<close>
      using ineq Dinvar_eq by simp
  qed
  have Fx: \<open>invar (y t) - invar (y 0) =
            integral {0..t} (\<lambda>x.
            (SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) (f x (y x)))\<close>
    apply (subst integral_unique[THEN sym,
           of \<open>(\<lambda>x. (SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) (f x (y x)))\<close>
              \<open>invar (y t) - invar (y 0)\<close>
              \<open>{0..t}\<close>])
     apply auto
    apply (rule fundamental_theorem_of_calculus'[OF t])
    apply (rule invar_vderiv)
    done              
  have F'_geq: 
    \<open>0 \<le> integral {0..t} (\<lambda>x. (SOME Dinvar. (invar has_derivative Dinvar) (at (y x))) (f x (y x)))\<close>
    apply (rule integral_nonneg)
    apply (rule has_integral_integrable
           [where i=\<open>invar (y t) - invar (y 0)\<close>])
    apply (rule fundamental_theorem_of_calculus'[OF t])
     apply (rule invar_vderiv)
    using deriv_nonneg 
    apply auto
    done
  show ?thesis
    using iv Fx F'_geq 
    by linarith
qed

text \<open>Domain-aware @\{thm DI\_Generic\} inspied by textbook differemtial induction \cite{Platzer2018}.  The induction step may assume
  @\{term \<open>y tau in Q\<close>\}; the conclusion additionally yields @\{term \<open>y t in Q\<close>\}.\<close>

lemma DI_Generic_dom:
  assumes iv: \<open>0 \<le> invar (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes induct_step:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow>
       \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                  0 \<le> Dinvar (f \<tau> (y \<tau>))\<close>
  assumes t: \<open>0 \<le> (t::real)\<close>
  shows \<open>y t \<in> Q \<and> (0::real) \<le> invar (y t)\<close>
proof -
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)
  have step': 
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
     \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                0 \<le> Dinvar (f \<tau> (y \<tau>))\<close>
    using induct_step y_in_Q 
    by blast
  have main: \<open>0 \<le> invar (y t)\<close>
    using DI_Generic[OF iv ODE step' t] .
  have endpoint: \<open>y t \<in> Q\<close> using y_in_Q[of t] t by simp
  show ?thesis 
    using endpoint main 
    by simp
qed

lemma DI_Vect:
  fixes y :: \<open>real \<Rightarrow> (real, 'a:: finite) vec\<close>
  fixes h :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes g :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes iv: \<open>h (y 0) \<le> g ((y 0)::(real, 'a::finite) vec)\<close>
  assumes ODE: \<open>(y solves_ode f) {0 .. t} Q\<close>
  assumes induct_step:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
            \<exists> Dh Dg. (h has_derivative Dh) (at (y \<tau>)) \<and>
                     (g has_derivative Dg) (at (y \<tau>)) \<and>
            Dh (f \<tau> (y \<tau>)) \<le> Dg (f \<tau> (y \<tau>))\<close>
  assumes t: \<open>0 \<le> (t::real)\<close>
  shows \<open>h (y t) \<le> ((g (y t))::real)\<close>
proof -
  have geq0: \<open>0 \<le> (\<lambda>v. g v - h v) (y t)\<close>
    apply (rule DI_Generic[where invar = \<open>\<lambda>v. g v - h v\<close>])
       apply (simp add: iv)
      apply (rule ODE)
     subgoal for \<tau>
       proof -
         assume h_\<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
         then have h_\<tau>_t0: \<open>0 \<le> \<tau>\<close> and h_\<tau>_t: \<open>\<tau> \<le> t\<close> by auto
         obtain Dh Dg where
           h_at_\<tau>: "(h has_derivative Dh) (at (y \<tau>))" and
           g_at_\<tau>: "(g has_derivative Dg) (at (y \<tau>))" and
           ineq:   "Dh (f \<tau> (y \<tau>)) \<le> Dg (f \<tau> (y \<tau>))"
           using induct_step ODE t h_\<tau>_t0 h_\<tau>_t h_\<tau>_in 
           by blast
         show \<open>\<exists>Dinvar. ((\<lambda>v. g v - h v) has_derivative Dinvar) (at (y \<tau>)) \<and>
                        0 \<le> Dinvar (f \<tau> (y \<tau>))\<close>
           apply (rule exI[where x=\<open>\<lambda>v. Dg v - Dh v\<close>])
           apply (rule conjI)
            apply (rule has_derivative_diff[OF g_at_\<tau> h_at_\<tau>])
           using ineq 
           apply simp
           done
       qed
       apply (rule t)
       done
     show ?thesis 
       using geq0 
       by simp
   qed


text \<open>
  Spatial form; a drop-in companion to @\{thm DI\_Vect\}, identical except
  that the induction step may assume @\{term \<open>y tau in Q\<close>\} and the
  conclusion additionally yields @{term \<open>y t \<in> Q\<close>}.  Proved by reduction
  to @{thm DI_Vect}.\<close>

lemma DI_Vect_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a:: finite) vec\<close>
  fixes h g :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes iv: \<open>h (y 0) \<le> g (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes induct_step:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow>
            \<exists> Dh Dg. (h has_derivative Dh) (at (y \<tau>)) \<and>
                     (g has_derivative Dg) (at (y \<tau>)) \<and>
                     Dh (f \<tau> (y \<tau>)) \<le> Dg (f \<tau> (y \<tau>))\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>y t \<in> Q \<and> h (y t) \<le> g (y t)\<close>
proof -
  \<comment> \<open>Codomain content of solves\_ode: the trajectory stays in Q.\<close>
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)
  \<comment> \<open>Discharge the `y tau in Q` premise pointwise, recovering DI\_Vect's step.\<close>
  have step': \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
            \<exists> Dh Dg. (h has_derivative Dh) (at (y \<tau>)) \<and>
                     (g has_derivative Dg) (at (y \<tau>)) \<and>
                     Dh (f \<tau> (y \<tau>)) \<le> Dg (f \<tau> (y \<tau>))\<close>
    using induct_step y_in_Q by blast
  have ineq: \<open>h (y t) \<le> g (y t)\<close>
    using DI_Vect[OF iv ODE step' t] .
  have endpoint: \<open>y t \<in> Q\<close> 
    using y_in_Q[of t] t 
    by simp
  show ?thesis 
    using endpoint ineq 
    by simp
qed


text \<open>
  Velocity form; explicit time-derivative
  functions @\{term g'\} and @\{term h'\} supplied as @\{const has\_vderiv\_on\}
  facts.  The induction step compares the composed time-derivatives
  @\{term \<open>h' tau (y tau) <= g' tau (y tau)\<close>\} under the domain hypothesis
  @{term \<open>y \<tau> \<in> Q\<close>}.  Proved directly via the fundamental theorem of
  calculus, mirroring the second half of @{thm DI_Generic}.\<close>

lemma DI_Vect_dom_vderiv:
  fixes y :: \<open>real \<Rightarrow> (real, 'a:: finite) vec\<close>
  fixes h g :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes h' g' :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> real\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes iv: \<open>h (y 0) \<le> g (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes g'_vderiv: \<open>((\<lambda>s. g (y s)) has_vderiv_on (\<lambda>s. g' s (y s))) {0..t}\<close>
  assumes h'_vderiv: \<open>((\<lambda>s. h (y s)) has_vderiv_on (\<lambda>s. h' s (y s))) {0..t}\<close>
  assumes induct_step:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow> h' \<tau> (y \<tau>) \<le> g' \<tau> (y \<tau>)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>y t \<in> Q \<and> h (y t) \<le> g (y t)\<close>
proof -
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)

  \<comment> \<open>The gap function goy - hoy has the difference of the supplied
      time-derivatives.\<close>
  have F_vderiv: \<open>((\<lambda>s. g (y s) - h (y s)) has_vderiv_on
                   (\<lambda>s. g' s (y s) - h' s (y s))) {0..t}\<close>
    using has_vderiv_on_diff[OF g'_vderiv h'_vderiv] .

  \<comment> \<open>Pointwise nonnegativity of the gap's derivative, using `y tau in Q`.\<close>
  have deriv_nn: \<open>\<And>s. s \<in> {0..t} \<Longrightarrow> 0 \<le> g' s (y s) - h' s (y s)\<close>
    using induct_step y_in_Q 
    by simp

  \<comment> \<open>FTC: gap(t) - gap(0) equals the integral of the derivative.\<close>
  have gap: \<open>(g (y t) - h (y t)) - (g (y 0) - h (y 0)) =
             integral {0..t} (\<lambda>s. g' s (y s) - h' s (y s))\<close>
    apply (subst integral_unique[THEN sym,
                                 of \<open>\<lambda>s. g' s (y s) - h' s (y s)\<close>
                                    \<open>(g (y t) - h (y t)) - (g (y 0) - h (y 0))\<close> \<open>{0..t}\<close>])
     apply auto
    apply (rule fundamental_theorem_of_calculus'[OF t])
    apply (rule F_vderiv)
    done

  \<comment> \<open>The integral is nonnegative.\<close>
  have integral_nn: \<open>0 \<le> integral {0..t} (\<lambda>s. g' s (y s) - h' s (y s))\<close>
    apply (rule integral_nonneg)
     apply (rule has_integral_integrable [where i=\<open>(g (y t) - h (y t)) - (g (y 0) - h (y 0))\<close>])
     apply (rule fundamental_theorem_of_calculus'[OF t])
     apply (rule F_vderiv)
    using deriv_nn
    apply auto
    done

  have ineq: \<open>h (y t) \<le> g (y t)\<close>
    using gap integral_nn iv by linarith
  have endpoint: \<open>y t \<in> Q\<close> using y_in_Q[of t] t by simp
  show ?thesis using endpoint ineq by simp
qed

subsection \<open>Differential Ghost\<close>

(* ================================================================== *)
(* Part 1: Explicit solution for linear scalar ODE y' = \<alpha>(\<tau>)\<sqdot>y + \<beta>(\<tau>) *)
(* ================================================================== *)

lemma linear_ode_solution:
  fixes a b :: \<open>real \<Rightarrow> real\<close>
  fixes y0:: real
  assumes a_cont: \<open>continuous_on {0..t} a\<close>
  assumes b_cont: \<open>continuous_on {0..t} b\<close>
  shows \<open>\<exists> y. y 0 = y0 \<and> (continuous_on {0..t} y) \<and> 
             (\<forall>\<tau>. \<tau> \<in> {0..t} \<longrightarrow>  
                 (y has_vector_derivative (a \<tau> * y \<tau> + b \<tau>)) (at \<tau> within {0..t}))\<close>
proof -
  (* ---- Define the integrating factor exponent A(\<tau>) = \<integral>\<^sub>0\<^sup>t \<alpha>(s) ds ---- *)
  define A where \<open>A \<equiv> \<lambda>\<tau>. integral {0..\<tau>} a\<close>

  (* ---- A is continuous on {0..t} for any t ---- *)
  have A_cont: \<open>continuous_on {0..t} A\<close> 
    unfolding A_def
    using a_cont
    by (auto intro!: indefinite_integral_continuous_1)

  (* ---- A has derivative \<alpha>(\<tau>) by FTC ---- *)
  have A_deriv: \<open>(A has_vector_derivative a \<tau>) (at \<tau> within {0..t})\<close>
    if h\<tau>: \<open>\<tau> \<in> {0..t}\<close> for \<tau>
    unfolding A_def
    using a_cont h\<tau>
    by (intro integral_has_vector_derivative) auto

  (* ---- e^{A(\<tau>)} has derivative \<alpha>(\<tau>) \<sqdot> e^{A(\<tau>)} by chain rule ---- *)
  have expA_deriv: \<open>((\<lambda>\<tau>. exp (A \<tau>)) has_vector_derivative 
      (a \<tau> * exp (A \<tau>))) (at \<tau> within {0..t})\<close>
    if h\<tau>: \<open>\<tau> \<in> {0..t}\<close> for \<tau>
  proof -
    have \<open>(A has_vector_derivative a \<tau>) (at \<tau> within {0..t})\<close>
      using A_deriv h\<tau> 
      by blast
    moreover have \<open>(exp has_field_derivative exp (A \<tau>)) (at (A \<tau>))\<close>
      by (rule DERIV_exp)
    ultimately show ?thesis
      using field_vector_diff_chain_within[of A \<open>a \<tau>\<close> \<tau> \<open>{0..t}\<close> exp \<open>exp (A \<tau>)\<close>]
      apply (simp add: comp_def mult.commute)
      using DERIV_exp has_field_derivative_at_within 
      by blast
  qed

  (* ---- e^{-A(\<tau>)} has derivative -\<alpha>(\<tau>) \<sqdot> e^{-A(\<tau>)} ---- *)
  have exp_negA_deriv: \<open>((\<lambda>\<tau>. exp (- A \<tau>)) has_vector_derivative 
      (- a \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})\<close>
    if h\<tau>: \<open>\<tau> \<in> {0..t}\<close> for \<tau> 
  proof -
    have \<open>((\<lambda>\<tau>. - A \<tau>) has_vector_derivative (- a \<tau>)) (at \<tau> within {0..t})\<close>
      using A_deriv[OF h\<tau>]
      by (auto intro: has_vector_derivative_minus)
    moreover have \<open>(exp has_field_derivative exp (- A \<tau>)) (at (- A \<tau>))\<close>
      by (rule DERIV_exp)
    ultimately show ?thesis
      using field_vector_diff_chain_within[of \<open>\<lambda>\<tau>. - A \<tau>\<close> \<open>- a \<tau>\<close> \<tau> \<open>{0..t}\<close> exp \<open>exp (- A \<tau>)\<close>]
      apply (simp add: comp_def mult.commute)
      using DERIV_exp has_field_derivative_at_within
      by blast
  qed

  (* ---- Define the inner integral I(\<tau>) = \<integral>\<^sub>0\<^sup>\<tau> \<beta>(s) \<sqdot> e^{-A(s)} ds ---- *)
  define I where \<open>I \<equiv> \<lambda>\<tau>. integral {0..\<tau>} (\<lambda>s. b s * exp (- A s))\<close>

  (* ---- The integrand \<beta> \<sqdot> e^{-A} is continuous ---- *)
  have integrand_cont: \<open>continuous_on {0..t} (\<lambda>s. b s * exp (- A s))\<close> 
    using b_cont A_cont
    by (intro continuous_intros) auto

  (* ---- I is continuous ---- *)
  have I_cont: \<open>continuous_on {0..t} I\<close> 
    unfolding I_def
    using integrand_cont
    by (auto intro!: indefinite_integral_continuous_1)

  (* ---- I has derivative \<beta>(\<tau>) \<sqdot> e^{-A(\<tau>)} by FTC ---- *)
  have I_deriv: \<open>(I has_vector_derivative (b \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})\<close>
    if h\<tau>: \<open>\<tau> \<in> {0..t}\<close> for \<tau> 
    unfolding I_def
    using integrand_cont h\<tau>
    by (intro integral_has_vector_derivative) auto

  (* ---- I(0) = 0 ---- *)
  have I_zero: \<open>I 0 = 0\<close>
    unfolding I_def 
    by simp

  (* ---- A(0) = 0 ---- *)
  have A_zero: \<open>A 0 = 0\<close>
    unfolding A_def 
    by simp

  (* ---- Define the solution y(\<tau>) = e^{A(\<tau>)} \<sqdot> (y\<^sub>0 + I(\<tau>)) ---- *)
  define y where \<open>y \<equiv> \<lambda>\<tau>. exp (A \<tau>) * (y0 + I \<tau>)\<close>

  (* ---- Initial condition: y(0) = e\<^sup>0 \<sqdot> (y\<^sub>0+ 0) = y\<^sub>0---- *)
  have y_init: \<open>y 0 = y0\<close>
    unfolding y_def 
    using A_zero I_zero 
    by simp

  (* ---- y is continuous ---- *)
  have y_cont: \<open>continuous_on {0..t} y\<close>
    unfolding y_def
    using A_cont I_cont
    by (intro continuous_intros) auto

  (* ---- y has the right derivative: y'(\<tau>) = \<alpha>(\<tau>)\<sqdot>y(\<tau>) + \<beta>(\<tau>) ---- *)
  have y_deriv: \<open>(y has_vector_derivative (a \<tau> * y \<tau> + b \<tau>)) (at \<tau> within {0..t})\<close>
    if h\<tau>: \<open>\<tau> \<in> {0..t}\<close> for \<tau>
  proof -
    have f_deriv: \<open>((\<lambda>\<tau>. exp (A \<tau>)) has_vector_derivative 
                   (a \<tau> * exp (A \<tau>))) (at \<tau> within {0..t})\<close>
      using expA_deriv h\<tau> 
      by blast

    have g_deriv: \<open>((\<lambda>\<tau>. y0 + I \<tau>) has_vector_derivative 
                   (b \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})\<close>
    proof -
      have \<open>(I has_vector_derivative (b \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})\<close>
        using I_deriv h\<tau> 
        by blast
      then have \<open>((\<lambda>\<tau>. y0 + I \<tau>) has_vector_derivative (0 + b \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})\<close>
        by (intro has_vector_derivative_add has_vector_derivative_const)
      then show ?thesis 
           by simp
    qed

    (* Apply product rule *)
    have \<open>(y has_vector_derivative (a \<tau> * exp (A \<tau>) * (y0 + I \<tau>) + exp (A \<tau>) * (b \<tau> * exp (- A \<tau>)))) 
          (at \<tau> within {0..t})\<close>
      unfolding y_def
      using f_deriv g_deriv
    proof -
      have "((\<lambda>r. exp (A r) * (y0 + I r)) has_vector_derivative exp (A \<tau>) * (b \<tau> * exp (- A \<tau>)) + a \<tau> * exp (A \<tau>) * (y0 + I \<tau>)) (at \<tau> within {0..t})"
        using f_deriv g_deriv has_vector_derivative_mult 
        by blast
      then show "((\<lambda>r. exp (A r) * (y0 + I r)) has_vector_derivative a \<tau> * exp (A \<tau>) * (y0 + I \<tau>) + exp (A \<tau>) * (b \<tau> * exp (- A \<tau>))) (at \<tau> within {0..t})"
        by (simp add: Groups.add_ac(2))
    qed

    (* Now simplify the derivative expression *)
    moreover have \<open>a \<tau> * exp (A \<tau>) * (y0 + I \<tau>) + exp (A \<tau>) * (b \<tau> * exp (- A \<tau>)) = 
                   a \<tau> * y \<tau> + b \<tau>\<close>
    proof -
      have \<open>exp (A \<tau>) * exp (- A \<tau>) = 1\<close>
        by (simp add: exp_minus_inverse)
      thus ?thesis
        unfolding y_def
        by (simp add: algebra_simps)
    qed
    ultimately show ?thesis
      by (auto intro: has_vector_derivative_eq_rhs)
  qed
  
  (* ---- Package the result ---- *)
  show ?thesis
    by (auto intro!: exI[where x=y] y_init y_cont y_deriv)
qed

lemma assemble_test:
  fixes x :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes y :: \<open>real \<Rightarrow> real\<close>
  fixes gi :: 'a
  assumes x_deriv: \<open>(x has_derivative Dx) (at \<tau> within S)\<close>
  assumes y_deriv: \<open>(y has_derivative Dy) (at \<tau> within S)\<close>
  shows \<open>((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>))) 
          has_derivative
          (\<lambda>h. (vec_lambda) ((\<lambda>i. vec_nth (Dx h) i) (gi:= Dy h))))
          (at \<tau> within S)\<close>
proof -
  let ?e = \<open>axis gi 1 :: (real, 'a) vec\<close>
  (* Rewrite ?z as: x \<tau> + (y \<tau> - vec_nth (x \<tau>) gi) *\<^sub>R ?e *)
  have eq: \<open>(vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>)) = 
            x \<tau> + (y \<tau> - vec_nth (x \<tau>) gi) *\<^sub>R ?e\<close> for \<tau>
    by (simp add: vec_eq_iff axis_def)
  show ?thesis
    unfolding eq
  proof -
    (* (\<lambda>v. vec_nth v gi) is bounded linear *)
    have bl: \<open>bounded_linear (\<lambda>v. vec_nth v gi)\<close>
      by (rule bounded_linear_vec_nth)

    (* Component gi of x has derivative *)
    have x_gi_deriv: \<open>((\<lambda>\<tau>. vec_nth (x \<tau>) gi) has_derivative (\<lambda>h. vec_nth (Dx h) gi)) 
        (at \<tau> within S)\<close>
      using bounded_linear.has_derivative[OF bl x_deriv] 
      by simp

    (* y - x_gi has derivative Dy - Dx_gi *)
    have diff_deriv: \<open>((\<lambda>\<tau>. y \<tau> - vec_nth (x \<tau>) gi) has_derivative 
        (\<lambda>h. Dy h - vec_nth (Dx h) gi)) (at \<tau> within S)\<close>
      using y_deriv x_gi_deriv 
      by (rule has_derivative_diff)

    (* scalar * constant vector has derivative *)
    have scaled_deriv: \<open>((\<lambda>\<tau>. (y \<tau> - vec_nth (x \<tau>) gi) *\<^sub>R ?e) has_derivative 
        (\<lambda>h. (Dy h - vec_nth (Dx h) gi) *\<^sub>R ?e)) (at \<tau> within S)\<close>
      using diff_deriv has_derivative_scaleR_left 
      by blast

    (* x + scaled has derivative *)
    have \<open>((\<lambda>\<tau>. x \<tau> + (y \<tau> - vec_nth (x \<tau>) gi) *\<^sub>R ?e) has_derivative 
        (\<lambda>h. Dx h + (Dy h - vec_nth (Dx h) gi) *\<^sub>R ?e)) (at \<tau> within S)\<close>
      using x_deriv scaled_deriv 
      by (rule has_derivative_add)

    moreover have \<open>(\<lambda>h. Dx h + (Dy h - vec_nth (Dx h) gi) *\<^sub>R ?e) = 
                   (\<lambda>h. (vec_lambda) ((\<lambda>i. vec_nth (Dx h) i) (gi:= Dy h)))\<close>
      by (auto simp: vec_eq_iff axis_def fun_eq_iff)
 
    ultimately show \<open>((\<lambda>\<tau>. x \<tau> + (y \<tau> - vec_nth (x \<tau>) gi) *\<^sub>R ?e) has_derivative
        (\<lambda>h. (vec_lambda) ((\<lambda>i. vec_nth (Dx h) i) (gi:= Dy h))))
        (at \<tau> within S)\<close>
      by simp
  qed
qed
(* ================================================================== *)
(* Part 2: The Differential Ghost (DG) lemma                          *)
(* ================================================================== *)

text \<open>
  DG says: given a solution x of the original ODE on \{0..t\},
  and continuous ghost coefficients a, b, for any initial ghost
  value y0, there exists a ghost trajectory y such that the
  combined trajectory (x with y at position gi) solves the
  extended ODE.

  The user then feeds this combined trajectory into DI\_Generic/DI\_Vect for specific
  trajectory invariance proofs.
\<close>
lemma DG:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes a b :: \<open>real \<Rightarrow> real\<close>
  fixes y0 :: real
  fixes gi :: 'a
  assumes y_sol: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes a_cont: \<open>continuous_on {0..t} a\<close>
  assumes b_cont: \<open>continuous_on {0..t} b\<close>
  assumes gi_zero: \<open>\<And>\<tau> v. vec_nth (f \<tau> v) gi = 0\<close>
  assumes gi_fresh: \<open>\<And>\<tau> v w. (\<forall>i. i \<noteq> gi \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow> f \<tau> v = f \<tau> w\<close>
  shows 
    \<open>\<exists> yi. yi 0 = y0 \<and>
         ((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (y \<tau>) i) (gi:= yi \<tau>)))
           solves_ode 
          (\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>))))) {0..t} UNIV\<close>
proof -
  (* ---- Step 1: Get ghost trajectory from linear_ode_solution ---- *)
  obtain yi where 
    y_init: \<open>yi 0 = y0\<close> and
    y_cont: \<open>continuous_on {0..t} yi\<close> and
    y_deriv: \<open>\<forall>\<tau>. \<tau> \<in> {0..t} \<longrightarrow> (yi has_vector_derivative (a \<tau> * yi \<tau> + b \<tau>)) (at \<tau> within {0..t})\<close>
    using linear_ode_solution[OF a_cont b_cont]
    by blast

  (* ---- Step 2: Name combined trajectory and extended vector field ---- *)
  let ?z = \<open>\<lambda>\<tau>. ((vec_lambda) ((\<lambda>i. vec_nth (y \<tau>) i) (gi:= yi \<tau>))) :: (real, 'a) vec\<close>
  let ?g = \<open>\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>)))\<close>

  (* ---- Step 3: ?z agrees with x on non-ghost components ---- *)
  have z_eq_x: \<open>\<forall>i. i \<noteq> gi \<longrightarrow> vec_nth (?z \<tau>) i = vec_nth (y \<tau>) i\<close>
    for \<tau> by simp

  (* ---- Step 4: f \<tau> (?z \<tau>) = f \<tau> (x \<tau>) ---- *)
  have f_eq: \<open>f \<tau> (?z \<tau>) = f \<tau> (y \<tau>)\<close> for \<tau>
    using gi_fresh z_eq_x 
    by blast

  (* ---- Step 5: target equation for the extended vector field ---- *)
  have target_eq: \<open>?g \<tau> (?z \<tau>) = ((vec_lambda) ((\<lambda>i. vec_nth (f \<tau> (y \<tau>)) i) (gi:= a \<tau> * yi \<tau> + b \<tau>)))\<close> 
    for \<tau> by (simp add: assms(4) f_eq vec_eq_iff)

  (* ---- Step 6: For any t, show ?z solves_ode ?g on {0..t} ---- *)
  have z_sol: \<open>(?z solves_ode ?g) {0..t} UNIV\<close>
  proof -
    (* x has its derivative from x_sol for this t *)
    have x_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) {0..t}\<close>
      using y_sol
      by (simp add: solves_ode_def)

    (* Show ?z has_vderiv_on matching ?g *)
    have z_vderiv: \<open>(?z has_vderiv_on (\<lambda>\<tau>. ?g \<tau> (?z \<tau>))) {0..t}\<close>
      unfolding has_vderiv_on_def has_vector_derivative_def
    proof
      fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>

      have x_at_\<tau>: \<open>(y has_vector_derivative f \<tau> (y \<tau>)) 
          (at \<tau> within {0..t})\<close>
        using x_vderiv h\<tau>
        by (simp add: has_vderiv_on_def)

      have y_at_\<tau>: \<open>(yi has_vector_derivative (a \<tau> * yi \<tau> + b \<tau>)) 
          (at \<tau> within {0..t})\<close>
        using y_deriv h\<tau> 
        by blast

      have x_has_deriv: \<open>(y has_derivative (\<lambda>xa. xa *\<^sub>R f \<tau> (y \<tau>))) 
          (at \<tau> within {0..t})\<close>
        using x_at_\<tau> 
        by (simp add: has_vector_derivative_def)

      have y_has_deriv: \<open>(yi has_derivative (\<lambda>xa. xa *\<^sub>R (a \<tau> * yi \<tau> + b \<tau>))) 
          (at \<tau> within {0..t})\<close>
        using y_at_\<tau> 
        by (simp add: has_vector_derivative_def)

      have \<open>(?z has_derivative 
             (\<lambda>h. (vec_lambda) 
                  ((\<lambda>i. vec_nth ((\<lambda>xa. xa *\<^sub>R f \<tau> (y \<tau>)) h) i) (gi:= (\<lambda>xa. xa *\<^sub>R (a \<tau> * yi \<tau> + b \<tau>)) h))
             )
            )
            (at \<tau> within {0..t})\<close>
        using assemble_test[OF x_has_deriv y_has_deriv] 
        by simp

      moreover have \<open>(\<lambda>h. \<chi> i. if i = gi then h *\<^sub>R (a \<tau> * yi \<tau> + b \<tau>) 
                               else vec_nth (h *\<^sub>R f \<tau> (y \<tau>)) i) = 
                     (\<lambda>h. h *\<^sub>R ?g \<tau> (?z \<tau>))\<close>
        using target_eq 
        by (auto simp: vec_eq_iff fun_eq_iff scaleR_vec_def)

      ultimately show \<open>((?z) has_derivative (\<lambda>xa. xa *\<^sub>R ?g \<tau> (?z \<tau>))) 
          (at \<tau> within {0..t})\<close> unfolding fun_upd_def
        by simp
    qed

    (* ?z is continuous *)
    have z_cont: \<open>continuous_on {0..t} ?z\<close>
      using vderiv_on_continuous_on z_vderiv 
      by blast

    show ?thesis
      using z_vderiv z_cont
      by (intro solves_odeI) auto
  qed

  (* ---- Conclude ---- *)
  show ?thesis
    using z_sol 
    by (auto intro!: exI[where x=yi] y_init )
qed

lemma DG_backward:
  fixes x :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  assumes x_sol: \<open>(x solves_ode f) {0..t} Q\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes a_cont: \<open>continuous_on {0..t} a\<close>
  assumes b_cont: \<open>continuous_on {0..t} b\<close>
  assumes gi_zero: \<open>\<And>\<tau> v. vec_nth (f \<tau> v) gi = 0\<close>
  assumes gi_fresh: \<open>\<And>\<tau> v w. (\<forall>i. i \<noteq> gi \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow> f \<tau> v = f \<tau> w\<close>
  assumes ghost_step: 
          \<open>\<And>y. y 0 = y0 \<Longrightarrow>
              ((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>)))
                solves_ode 
              (\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>))))) 
             {0..t} UNIV \<Longrightarrow> P (x t)\<close>
  shows \<open>P (x t)\<close>
proof -
  obtain y where y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>)))
        solves_ode (\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>))))) 
       {0..t} UNIV\<close>
    using DG[OF x_sol a_cont b_cont gi_zero gi_fresh] 
    by auto
  show \<open>P (x t)\<close>
    using ghost_step[OF y_init combined_sol] .
qed

lemma DG_elim:
  fixes x :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  assumes x_sol: \<open>(x solves_ode f) {0..t} Q\<close>
  assumes a_cont: \<open>continuous_on {0..t} a\<close>
  assumes b_cont: \<open>continuous_on {0..t} b\<close>
  assumes gi_zero: \<open>\<And>\<tau> v. vec_nth (f \<tau> v) gi = 0\<close>
  assumes gi_fresh: \<open>\<And>\<tau> v w. (\<forall>i. i \<noteq> gi \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow> f \<tau> v = f \<tau> w\<close>
  assumes ghost_step: \<open>\<And>y. y 0 = y0 \<Longrightarrow>
             ((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>)))
              solves_ode 
             (\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>))))) 
             {0..t} UNIV
            \<Longrightarrow> thesis\<close>
  shows \<open>thesis\<close>
proof -
  obtain y where y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
     \<open>((\<lambda>\<tau>. (vec_lambda) ((\<lambda>i. vec_nth (x \<tau>) i) (gi:= y \<tau>)))
       solves_ode 
      (\<lambda>\<tau> v. f \<tau> v + ((vec_lambda) ((\<lambda>i. 0) (gi:= a \<tau> * vec_nth v gi + b \<tau>))))) 
      {0..t} UNIV\<close>
    using DG[OF x_sol a_cont b_cont gi_zero gi_fresh] 
    by auto
  show thesis
    using ghost_step[OF y_init combined_sol] .
qed
subsection \<open>Differential Cut (DC)\<close>
text \<open>
  Part 1: The Differential Cut (DC)

  DC IN dDL THEORY
  In Platzer's Differential Dynamic Logic, the DC axiom is:

      [x' = f(x) \& Q]C    [x' = f(x) \& (Q and C)]P
      --------------------------------------------
                  [x' = f(x) \& Q]P

  To prove P is invariant in domain Q, it suffices to first
  prove some intermediate cut-formula C is invariant in Q, and then
  prove P is invariant in the STRENGTHENED domain Q and C.

  \textbf{WHY DC IS POWERFUL}\\
  Many properties cannot be proved directly by DI because the local
  derivative check fails when considered in isolation. But once we
  STRENGTHEN our knowledge with previously-proved invariants, the
  local check often becomes tractable.

  Example use case (Toggle Switch):
\begin{itemize}
\item Want to prove: u(t) <= M  (concentration bounded above)
\item DI fails directly: when u is small, du/dt may not be <= 0
\item But if we KNOW u, v >= 0, then for u close to M we can show du/dt <= 0
\item DC strategy:
  1. First prove u >= 0 is invariant (cut-formula C)
  2. Then prove u <= M is invariant FROM u >= 0
\end{itemize}

  \textbf{ISABELLE FORMALIZATION}\\
  Our DC lemma simply restricts the domain constraint of `solves\_ode`
  given that the trajectory already satisfies the cut-formula at every
  point in the time interval.
\<close>

lemma DC:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes Q :: \<open>(real, 'a) vec set\<close>
  fixes C :: \<open>(real, 'a) vec \<Rightarrow> bool\<close>
  assumes y_sol: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes C_inv: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> C (y \<tau>)\<close>
  shows \<open>(y solves_ode f) {0..t} (Q \<inter> {v. C v})\<close>
proof -
  (* Extract the two components of solves_ode *)
  have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) {0..t}\<close>
    using y_sol 
    by (simp add: solves_ode_def)
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using y_sol 
    by (simp add: solves_ode_def Pi_def)

  (* The trajectory is in the strengthened domain Q \<inter> {v. C v} *)
  have y_in_QC: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q \<inter> {v. C v}\<close>
    using y_in_Q C_inv 
    by auto

  (* Reassemble solves_ode with the strengthened domain *)
  show ?thesis
    using y_vderiv y_in_QC
    by (intro solves_odeI) (auto simp: Pi_def)
qed

subsection \<open>DI boundary\<close>

text \<open>
  DI\_boundary , Boundary-Aware Differential Induction.\\

  \textbf{RESEARCH CONTRIBUTION}\\
  This file formalizes a STRENGTHENED variant of differential induction
  that exploits BOUNDARY structure to prove non-negativity invariants.

  In the original DI axiom (formalized in this development as DI\_Generic
  and DI\_Vect), the inductive step requires the Lie derivative of the
  candidate invariant to be non-negative AT EVERY POINT along the
  trajectory. This works for global invariants such as conservation laws
  (where the Lie derivative is identically zero), but it FAILS for many
  natural non-negativity invariants that are only at risk on the
  boundary \{invar = 0\}.

  \textbf{EXAMPLE OF THE LIMITATION}\\
  Consider the gene-regulatory ODE:

      du/dt = alpha / (1 + v\textasciicircum{}beta) - u

  We want to prove that u(0) >= 0 implies u(t) >= 0 for all t.

\begin{itemize}
\item The Lie derivative of `u` is `alpha/(1+v\textasciicircum{}beta) - u`.
\item This is NOT globally non-negative: when u is large, it becomes negative.
\item Hence DI\_Vect cannot discharge the inductive step over the whole
  trajectory.
\item However, the invariant `u >= 0` can only fail by `u` crossing zero.
  At u = 0, the Lie derivative reduces to `alpha/(1+v\textasciicircum{}beta) >= 0`, so the
  boundary is repelling.
\end{itemize}

  This is exactly the situation `DI\_boundary` is designed to handle.

  \textbf{THE KEY INSIGHT}\\
  A continuous function cannot change sign without passing through zero.
  Hence, to prove `g(tau) >= 0` is invariant, it suffices to ensure that
  whenever `g(tau) = 0`, the trajectory cannot "exit" into negative values.
  This is enforced by requiring the time-derivative of `g` to be STRICTLY
  POSITIVE at every boundary point , strictly positive derivatives
  guarantee a right-neighborhood where the function is strictly positive.

  \textbf{RELATIONSHIP TO PRIOR WORK}\\
  This corresponds to Platzer's "Differential Invariants" extension of
  dDL, where boundary-aware induction is one of the standard refinements
  of plain DI. The axiom is closely related to:
\begin{itemize}
\item "Strict differential induction" (DI>)
\item Barrier certificate methods in control theory
\item The viability theorem in differential inclusion theory
\end{itemize}

  Our formalization makes the proof structure explicit and reusable in
  Isabelle/HOL, opening the path to verifying non-negativity for a broad
  class of biological and chemical systems.
\<close>

text \<open>
  Part 2: The main DI\_boundary lemma

  STATEMENT:
    Given an ODE solution y : [0,t] -> vec and a Fr?chet-differentiable
    certificate function invar : vec -> real, whose non-negative region
    \{v. 0 <= invar v\} is the invariant to be established, IF:
\begin{enumerate}
\item invar(y(0)) >= 0  (initial condition)
\item For every tau in [0,t] where invar(y(tau)) = 0, the Lie derivative
  is STRICTLY positive:
  EX Dinvar. (invar has\_derivative Dinvar) (at (y tau)) and
  0 < Dinvar (f tau (y tau))
\item differentiability along the trajectory is what gives continuity
  of invar o y
\end{enumerate}
    THEN invar(y(t)) >= 0.

  \textbf{PROOF STRATEGY:}\\
    By contradiction. Assume invar(y(t)) < 0.
    Define g(tau) = invar(y(tau)) and S = \{tau in [0,t] | g(tau) < 0\}.
    Since t in S, we have S /= \{\}, so tau* = inf S exists.
    By continuity of g and the inf property, g(tau*) = 0.
    Apply boundary\_step at tau* to get strictly positive derivative l > 0
    of g at tau* (via the chain rule).
    Apply deriv\_pos\_right\_strict to get a right neighborhood where g > 0.
    But this contradicts tau* = inf S (which would have points in S
    arbitrarily close to tau* from above, where g < 0).
\<close>

lemma DI_boundary:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes invar :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  assumes iv: \<open>0 \<le> invar (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes t: \<open>0 \<le> t\<close>
  (* Differentiability of the certificate function "invar" everywhere along the trajectory.
     This gives us continuity of invar \<circ> y, which is essential for 
     the first-hit-time argument. *)
  assumes invar_diff: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
        \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>))\<close>
  (* Boundary condition: at every point where invar = 0, the Lie
     derivative is STRICTLY positive (the trajectory points 
     strictly into the safe region). *)
  assumes boundary_step: 
     \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> invar (y \<tau>) = 0 \<Longrightarrow>
        \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                  0 < Dinvar (f \<tau> (y \<tau>))\<close>
  shows \<open>0 \<le> invar (y t)\<close>
proof (rule ccontr)
  assume neg: \<open>\<not> 0 \<le> invar (y t)\<close>
  hence g_t_neg: \<open>invar (y t) < 0\<close> 
    by simp

  (* We define g = invar \<circ> y, the real-valued function we'll analyze *)
  let ?g = \<open>\<lambda>\<tau>. invar (y \<tau>)\<close>

  (* ---- Step 1: g is continuous on [0, t] ---- *)
  (* y is differentiable (from solves_ode), hence continuous.
     invar is differentiable along y, hence continuous along y.
     Composition is continuous. *)
  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast
  
  have invar_cont_at_y: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> continuous (at (y \<tau>)) invar\<close>
    using invar_diff has_derivative_continuous 
    by blast

  have g_cont: \<open>continuous_on {0..t} ?g\<close>
  proof -
    have \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> continuous (at \<tau> within {0..t}) ?g\<close>
    proof -
      fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>
      have y_cont_at_\<tau>: \<open>continuous (at \<tau> within {0..t}) y\<close>
        using y_cont h\<tau> by (simp add: continuous_on_eq_continuous_within)
      have invar_cont: \<open>continuous (at (y \<tau>)) invar\<close>
        using invar_cont_at_y[OF h\<tau>] .
      show \<open>continuous (at \<tau> within {0..t}) ?g\<close>
        using continuous_within_compose3 invar_cont y_cont_at_\<tau> 
        by blast       
    qed
    thus ?thesis 
      by (simp add: continuous_on_eq_continuous_within)
  qed

  (* ---- Step 2: We define S and show it has an infimum \<tau>* ---- *)
  define S where \<open>S = {\<tau>. \<tau> \<in> {0..t} \<and> ?g \<tau> < 0}\<close>
  have S_nonempty: \<open>S \<noteq> {}\<close>
    using g_t_neg t 
    by (auto simp: S_def)
  have S_bdd: \<open>bdd_below S\<close>
    by (auto simp: S_def bdd_below_def)
  have S_subset: \<open>S \<subseteq> {0..t}\<close>
    by (auto simp: S_def)

  define \<tau>_star where \<open>\<tau>_star = Inf S\<close>

  have \<tau>_star_lb: \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau>_star \<le> \<tau>\<close>
    unfolding \<tau>_star_def using S_bdd 
    by (auto intro: cInf_lower)

  have \<tau>_star_in_interval: \<open>\<tau>_star \<in> {0..t}\<close>
  proof -
    have \<open>0 \<le> \<tau>_star\<close>
      unfolding \<tau>_star_def using S_bdd S_subset
      by (meson atLeastAtMost_iff cInf_greatest S_nonempty subsetD)
    moreover have \<open>\<tau>_star \<le> t\<close>
      using S_nonempty t g_t_neg S_def \<tau>_star_def \<tau>_star_lb
      unfolding \<tau>_star_def S_def
      by auto
    ultimately show ?thesis 
      by simp
  qed

  (* ---- Step 3: g(\<tau>\<^sup>\<star>) = 0 ---- *)
  (* From two directions: 
     (a) g(\<tau>\<^sup>\<star>) \<le> 0 because there are points in S arbitrarily close to \<tau>\<^sup>\<star>
     (b) g(\<tau>\<^sup>\<star>) \<ge> 0 because all \<tau> < \<tau>\<^sup>\<star> satisfy g(\<tau>) \<ge> 0  *)

  have g_at_\<tau>_star_le_0: \<open>?g \<tau>_star \<le> 0\<close>
  proof -
    (* By inf property, there's a sequence in S converging to \<tau>_star *)
    obtain seq where seq_in_S: \<open>\<And>n. seq n \<in> S\<close> 
                and seq_lim: \<open>seq \<longlonglongrightarrow> \<tau>_star\<close>
      using closure_contains_Inf[OF S_nonempty S_bdd]
      unfolding \<tau>_star_def
      by (metis closure_sequential)
    have \<open>\<And>n. ?g (seq n) < 0\<close>
      using seq_in_S by (auto simp: S_def)
    moreover have \<open>(\<lambda>n. ?g (seq n)) \<longlonglongrightarrow> ?g \<tau>_star\<close>
    proof -
      have seq_in: \<open>\<forall>n. seq n \<in> {0..t}\<close>
        using seq_in_S S_subset 
        by blast
      have ev_in: \<open>eventually (\<lambda>n. seq n \<in> {0..t}) sequentially\<close>
        using seq_in by simp
      show ?thesis
        using continuous_on_tendsto_compose[OF g_cont seq_lim \<open>\<tau>_star \<in> {0..t}\<close> ev_in] 
        by blast
    qed
    ultimately show \<open>?g \<tau>_star \<le> 0\<close>
      by (simp add: Lim_bounded order_less_le)
  qed

  have g_at_\<tau>_star_ge_0: \<open>?g \<tau>_star \<ge> 0\<close>
  proof -
    (* For any \<tau> < \<tau>_star with \<tau> \<in> [0, t], we have \<tau> \<notin> S, so g(\<tau>) \<ge> 0 *)
    show ?thesis
    proof (cases \<open>\<tau>_star = 0\<close>)
      case True
      thus ?thesis using iv 
        by simp
    next
      case False
      hence \<tau>_star_pos: \<open>0 < \<tau>_star\<close> 
        using \<open>\<tau>_star \<in> {0..t}\<close> 
        by simp
      (* Take a sequence approaching \<tau>_star from below within [0, \<tau>_star) *)
      have \<open>\<And>\<tau>. 0 \<le> \<tau> \<and> \<tau> < \<tau>_star \<Longrightarrow> ?g \<tau> \<ge> 0\<close>
      proof -
        fix \<tau> assume h\<tau>: \<open>0 \<le> \<tau> \<and> \<tau> < \<tau>_star\<close>
        have \<open>\<tau> \<notin> S\<close>
          using h\<tau> \<tau>_star_lb not_less 
          by blast
        moreover have \<open>\<tau> \<in> {0..t}\<close>
          using h\<tau> \<open>\<tau>_star \<in> {0..t}\<close> 
          by auto
        ultimately show \<open>?g \<tau> \<ge> 0\<close>
          by (auto simp: S_def)
      qed
      (* Take limit \<tau> \<rightarrow> \<tau>_star from below *)
      have \<open>(\<lambda>n. ?g (\<tau>_star - \<tau>_star/(real (Suc (Suc n))))) \<longlonglongrightarrow> ?g \<tau>_star\<close>
      proof -
        have lim_arg: \<open>(\<lambda>n. \<tau>_star - \<tau>_star/(real (Suc (Suc n)))) \<longlonglongrightarrow> \<tau>_star\<close>
        proof -
          have \<open>(\<lambda>n. \<tau>_star/(real (Suc (Suc n)))) \<longlonglongrightarrow> 0\<close>
            using LIMSEQ_inverse_real_of_nat LIMSEQ_Suc lim_const_over_n 
            by blast
          thus ?thesis
            using tendsto_const tendsto_diff 
            by fastforce
        qed
        have all_in: \<open>\<And>n. \<tau>_star - \<tau>_star/(real (Suc (Suc n))) \<in> {0..t}\<close>
        proof -
          fix n
          have s_pos: \<open>0 < \<tau>_star/(real (Suc (Suc n)))\<close>
            using \<tau>_star_pos 
            by simp
          have s_lt: \<open>\<tau>_star/(real (Suc (Suc n))) < \<tau>_star\<close>
            using \<tau>_star_pos 
            by (simp add: divide_less_eq)
          have lo: \<open>0 \<le> \<tau>_star - \<tau>_star/(real (Suc (Suc n)))\<close>
            using s_lt 
            by linarith
          have hi: \<open>\<tau>_star - \<tau>_star/(real (Suc (Suc n))) \<le> t\<close>
            using \<open>\<tau>_star \<in> {0..t}\<close> s_pos by auto
          show \<open>\<tau>_star - \<tau>_star/(real (Suc (Suc n))) \<in> {0..t}\<close>
            using lo hi 
            by simp
        qed
        have ev_in: \<open>eventually (\<lambda>n. \<tau>_star - \<tau>_star/(real (Suc (Suc n))) \<in> {0..t}) sequentially\<close>
          using all_in 
          by simp
        show ?thesis
          using continuous_on_tendsto_compose[OF g_cont lim_arg \<open>\<tau>_star \<in> {0..t}\<close> ev_in] .
      qed
      moreover have \<open>\<And>n. 0 \<le> ?g (\<tau>_star - \<tau>_star/(real (Suc (Suc n))))\<close>
      proof -
        fix n
        have lo: \<open>0 \<le> \<tau>_star - \<tau>_star/(real (Suc (Suc n)))\<close>
        proof -
          have \<open>\<tau>_star/(real (Suc (Suc n))) \<le> \<tau>_star\<close>
          proof -
            have \<open>\<tau>_star * 1 \<le> \<tau>_star * real (Suc (Suc n))\<close>
              using \<tau>_star_pos 
              by simp
            thus ?thesis
              using \<tau>_star_pos 
              by (simp add: pos_divide_le_eq)
          qed
          thus ?thesis 
            by linarith
        qed
        have lt: \<open>\<tau>_star - \<tau>_star/(real (Suc (Suc n))) < \<tau>_star\<close>
          using \<tau>_star_pos 
          by simp
        show \<open>0 \<le> ?g (\<tau>_star - \<tau>_star/(real (Suc (Suc n))))\<close>
          using \<open>\<And>\<tau>. 0 \<le> \<tau> \<and> \<tau> < \<tau>_star \<Longrightarrow> 0 \<le> ?g \<tau>\<close>[of \<open>\<tau>_star - \<tau>_star/(real (Suc (Suc n)))\<close>]
                lo lt
          by simp
      qed
      ultimately show \<open>0 \<le> ?g \<tau>_star\<close>
        using Lim_bounded2 
        by blast
    qed
  qed

  have g_at_\<tau>_star_eq_0: \<open>?g \<tau>_star = 0\<close>
    using g_at_\<tau>_star_le_0 g_at_\<tau>_star_ge_0 
    by linarith

  (* ---- Step 4: Apply the boundary condition at \<tau>_star ---- *)
  obtain Dinvar where 
    invar_at_\<tau>_star: \<open>(invar has_derivative Dinvar) (at (y \<tau>_star))\<close> and
    Dinvar_pos: \<open>0 < Dinvar (f \<tau>_star (y \<tau>_star))\<close>
    using boundary_step[OF \<tau>_star_in_interval g_at_\<tau>_star_eq_0]
    by blast

  (* ---- Step 5: Chain rule, g has strictly positive derivative at \<tau>_star ---- *)
  (* (y has_vector_derivative f \<tau>_star (y \<tau>_star)) (at \<tau>_star within {0..t}) *)
  have y_vderiv_at_\<tau>_star: 
    \<open>(y has_vector_derivative f \<tau>_star (y \<tau>_star)) (at \<tau>_star within {0..t})\<close>
    using ODE \<tau>_star_in_interval
    by (simp add: solves_ode_def has_vderiv_on_def)

  have y_has_deriv: 
    \<open>(y has_derivative (\<lambda>s. s *\<^sub>R f \<tau>_star (y \<tau>_star))) (at \<tau>_star within {0..t})\<close>
    using y_vderiv_at_\<tau>_star 
    by (simp add: has_vector_derivative_def)

  have invar_at_within: 
    \<open>(invar has_derivative Dinvar) (at (y \<tau>_star) within UNIV)\<close>
    using invar_at_\<tau>_star 
    by simp

  have chain: \<open>((invar \<circ> y) has_derivative (Dinvar \<circ> (\<lambda>s. s *\<^sub>R f \<tau>_star (y \<tau>_star))))
               (at \<tau>_star within {0..t})\<close>
    by (rule diff_chain_within[OF y_has_deriv has_derivative_at_withinI[OF invar_at_\<tau>_star]])

  (* The composed derivative simplifies: 
       (Dinvar \<circ> (\<lambda>s. s *\<^sub>R v))(s) = s * Dinvar(v)
     where v = f \<tau>_star (y \<tau>_star) *)
  let ?l = \<open>Dinvar (f \<tau>_star (y \<tau>_star))\<close>

  have lin_simp: \<open>(Dinvar \<circ> (\<lambda>s. s *\<^sub>R f \<tau>_star (y \<tau>_star))) = (\<lambda>s. s * ?l)\<close>
    using has_derivative_bounded_linear[OF invar_at_\<tau>_star]
    by (auto simp: comp_def linear_simps(5))

  have g_has_deriv: \<open>(?g has_derivative (\<lambda>s. s * ?l)) (at \<tau>_star within {0..t})\<close>
    using chain lin_simp 
    by (simp add: comp_def)

  (* Convert to has_real_derivative form *)
  have g_has_real_deriv: \<open>(?g has_real_derivative ?l) (at \<tau>_star within {0..t})\<close>
    using g_has_deriv 
    by (simp add: has_field_derivative_def mult_commute_abs)

  (* ---- Step 6: Right neighborhood of \<tau>_star where g > 0 ---- *)
  (* We need this to be at the unrestricted (at \<tau>_star), not just within {0..t}.
     This works as long as \<tau>_star is in (\<tau>_star < t). *)
  (* CASE: \<tau>_star < t *)
  (* CASE: \<tau>_star = t, but then S has only the point t itself,
           and continuity gives g(t) = lim_{\<tau>\<rightarrow>t-} g(\<tau>) \<ge> 0
           contradicting g_t_neg directly. *)

  have \<open>\<tau>_star < t \<or> \<tau>_star = t\<close>
    using \<tau>_star_in_interval 
    by auto

  thus False
  proof
    assume \<tau>_star_lt_t: \<open>\<tau>_star < t\<close>

    (* ---- We obtain a right-neighborhood of \<tau>_star where g > 0 ---- *)
    (* Case split on whether \<tau>_star is at the left boundary (..= 0) or 
       strictly in (..> 0). *)
    have right_inc: \<open>\<exists>d > 0. \<forall>h. 0 < h \<and> h < d \<longrightarrow> ?g \<tau>_star < ?g (\<tau>_star + h)\<close>
    proof (cases \<open>0 < \<tau>_star\<close>)
      case True
      (* Interior case: \<tau>_star \<in> interior [0, t]. Convert within-derivative to 
         unrestricted derivative via at_within_interior, then apply 
         the standard positive-derivative-implies-right-increment lemma. *)
      have interior_mem: \<open>\<tau>_star \<in> interior {0..t}\<close>
        using True \<tau>_star_lt_t 
        by simp
      have at_eq: \<open>at \<tau>_star within {0..t} = at \<tau>_star\<close>
        using at_within_interior[OF interior_mem] .
      have g_deriv_at: \<open>(?g has_real_derivative ?l) (at \<tau>_star)\<close>
        using g_has_real_deriv at_eq 
        by simp
      show ?thesis
        using deriv_pos_right_strict[OF g_deriv_at Dinvar_pos] .
    next
      case False
      (* Left-boundary case: \<tau>_star = 0. *)
      hence \<tau>_star_eq_0: \<open>\<tau>_star = 0\<close> 
        using \<tau>_star_in_interval 
        by auto
      have g_deriv_within_0: \<open>(?g has_real_derivative ?l) (at 0 within {0..t})\<close>
        using g_has_real_deriv \<tau>_star_eq_0 
        by simp
      have t_pos: \<open>0 < t\<close> 
        using \<tau>_star_lt_t \<tau>_star_eq_0 
        by simp
      have rewrite_interval: \<open>{0..t} = {(0::real)..t}\<close> 
        by simp
      have \<open>\<exists>d > 0. \<forall>h. 0 < h \<and> h < d \<longrightarrow> ?g 0 < ?g (0 + h)\<close>
        using has_real_derivative_pos_inc_right_within[
                OF g_deriv_within_0 t_pos Dinvar_pos] .
      thus ?thesis 
        using \<tau>_star_eq_0 
        by simp
    qed

    (* ---- Extract d from right_inc and derive contradiction ---- *)
    obtain d where d_pos: \<open>0 < d\<close> and 
      d_inc: \<open>\<forall>h. 0 < h \<and> h < d \<longrightarrow> ?g \<tau>_star < ?g (\<tau>_star + h)\<close>
      using right_inc 
      by blast

    (* Build \<epsilon> = min(d/2, (t - \<tau>_star)/2) so that any point within \<epsilon> of 
       \<tau>_star is still in {0..t} and within d of \<tau>_star *)
    define \<epsilon> where \<open>\<epsilon> = min (d/2) ((t - \<tau>_star)/2)\<close>
    have \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
      using d_pos \<tau>_star_lt_t 
      by (simp add: \<epsilon>_def)

    (* By the inf property, there exists \<tau> \<in> S with \<tau> < \<tau>_star + \<epsilon> *)
    have \<open>\<exists>\<tau> \<in> S. \<tau> < \<tau>_star + \<epsilon>\<close>
      unfolding \<tau>_star_def
      using S_nonempty S_bdd \<epsilon>_pos cInf_lessD
      by (metis \<tau>_star_def less_add_same_cancel1)

    then obtain \<tau> where \<tau>_in_S: \<open>\<tau> \<in> S\<close> and \<tau>_close: \<open>\<tau> < \<tau>_star + \<epsilon>\<close> by blast

    (* \<tau>_star \<le> \<tau> because \<tau>_star is a lower bound of S *)
    have \<tau>_ge_\<tau>_star: \<open>\<tau>_star \<le> \<tau>\<close>
      using \<tau>_in_S \<tau>_star_lb 
      by simp

    (* \<tau> \<noteq> \<tau>_star because g(\<tau>_star) = 0 but g(\<tau>) < 0 for \<tau> \<in> S *)
    have \<tau>_ne_\<tau>_star: \<open>\<tau> \<noteq> \<tau>_star\<close>
      using \<tau>_in_S g_at_\<tau>_star_eq_0 
      by (auto simp: S_def)

    have \<tau>_gt_\<tau>_star: \<open>\<tau>_star < \<tau>\<close>
      using \<tau>_ge_\<tau>_star \<tau>_ne_\<tau>_star 
      by simp

    (* Let h = \<tau> - \<tau>_star. Then 0 < h < \<epsilon> \<le> d/2 < d, so d_inc applies *)
    define h where \<open>h = \<tau> - \<tau>_star\<close>
    have h_pos: \<open>0 < h\<close>
      using \<tau>_gt_\<tau>_star 
      by (simp add: h_def)
    have h_lt_d: \<open>h < d\<close>
      using \<tau>_close \<epsilon>_pos d_pos 
      by (simp add: h_def \<epsilon>_def)

    (* Apply d_inc: g(\<tau>_star) < g(\<tau>_star + h) = g(\<tau>) *)
    have \<open>?g \<tau>_star < ?g (\<tau>_star + h)\<close>
      using d_inc h_pos h_lt_d 
      by blast
    hence g_\<tau>_pos: \<open>?g \<tau>_star < ?g \<tau>\<close>
      by (simp add: h_def)
    hence \<open>0 < ?g \<tau>\<close>
      using g_at_\<tau>_star_eq_0 
      by linarith

    (* But \<tau> \<in> S means g(\<tau>) < 0. Contradiction. *)
    moreover have \<open>?g \<tau> < 0\<close>
      using \<tau>_in_S 
      by (auto simp: S_def)

    ultimately show False 
      by linarith

  next
    (* ---- CASE \<tau>_star = t ---- *)
    (* Direct contradiction: g(\<tau>_star) = 0 but g(t) < 0 *)
    assume \<tau>_star_eq_t: \<open>\<tau>_star = t\<close>
    have \<open>?g t = 0\<close>
      using g_at_\<tau>_star_eq_0 \<tau>_star_eq_t by simp
    moreover have \<open>?g t < 0\<close>
      using g_t_neg .
    ultimately show False 
      by linarith
  qed
qed

text \<open>Domain-aware @\{thm DI\_boundary\}.  Only the strict-inward boundary
  condition is gated by @\{term \<open>y tau in Q\<close>\}; the differentiability side
  condition stays global.\<close>

lemma DI_boundary_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes invar :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  assumes iv: \<open>0 \<le> invar (y 0)\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes invar_diff: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
        \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>))\<close>
  assumes boundary_step:
     \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow> invar (y \<tau>) = 0 \<Longrightarrow>
        \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                  0 < Dinvar (f \<tau> (y \<tau>))\<close>
  shows \<open>y t \<in> Q \<and> 0 \<le> invar (y t)\<close>
proof -
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)
  have boundary_step': \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> invar (y \<tau>) = 0 \<Longrightarrow>
        \<exists> Dinvar. (invar has_derivative Dinvar) (at (y \<tau>)) \<and>
                  0 < Dinvar (f \<tau> (y \<tau>))\<close>
    using boundary_step y_in_Q by blast
  have main: \<open>0 \<le> invar (y t)\<close>
    using DI_boundary[OF iv ODE t invar_diff boundary_step'] .
  have endpoint: \<open>y t \<in> Q\<close> 
    using y_in_Q[of t] t 
    by simp
  show ?thesis 
    using endpoint main 
    by simp
qed

subsection \<open>DI Convergence Rate\<close>
text \<open>
  Finite-time convergence by accumulated rate.  A non-decreasing
  differentiable function whose rate is at least @\{term delta\} while it stays
  below the target @\{term \<open>Ltarget\<close>\} must exceed that target once
  @{term T} outruns the initial gap.  Positivity of @{term \<epsilon>} is not
  required: @{term \<epsilon>} enters only through the combination
  @{term \<open>Ltarget\<close>}.\<close>

lemma convergence_rate_core:
  fixes u \<phi> :: \<open>real \<Rightarrow> real\<close>
  fixes Ltarget \<delta> T :: real
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes below_final: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> u \<tau> \<le> u T\<close>  
  assumes u_vderiv: \<open>(u has_vderiv_on \<phi>) {0..T}\<close>
  assumes rate_below_target: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> u \<tau> \<le> Ltarget \<Longrightarrow> \<delta> \<le> \<phi> \<tau>\<close>
  assumes T_large: \<open>(Ltarget - u 0) / \<delta> < T\<close>
  shows \<open>Ltarget < u T\<close>
proof (rule ccontr)
  assume neg: \<open>\<not> Ltarget < u T \<close>
  hence u_T_low: \<open>u T \<le> Ltarget\<close> by simp

  \<comment> \<open>Step 1: monotonicity propagates the assumed failure backwards.\<close>
  have u_below: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> u \<tau> \<le> Ltarget\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    have \<open>u \<tau> \<le> u T\<close> using below_final[OF h\<tau>] .
    thus \<open>u \<tau> \<le> Ltarget\<close> using u_T_low 
      by linarith
  qed

  \<comment> \<open>Step 2: hence the rate is uniformly at least delta.\<close>
  have rate_uniform: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>  \<delta> \<le>  \<phi> \<tau>\<close>
    using rate_below_target u_below 
    by simp

  \<comment> \<open>Step 3: FTC.\<close>
  have ftc: \<open>u T - u 0 = integral {0..T} \<phi>\<close>
    using u_vderiv T_nn
    by (metis (no_types, lifting) fundamental_theorem_of_calculus' integral_unique)

  \<comment> \<open>Step 4: integral monotonicity.\<close>
  have \<phi>_integrable: \<open>\<phi> integrable_on {0..T}\<close>
  proof -
    have \<open>(\<phi> has_integral (u T - u 0)) {0..T}\<close>
      using u_vderiv T_nn
      using fundamental_theorem_of_calculus' 
      by blast
    thus ?thesis 
      using has_integral_integrable 
      by blast
  qed

  have const_integrable: \<open>(\<lambda>\<tau>::real. \<delta>) integrable_on {0..T}\<close> 
    by simp

  have integral_lb: \<open>integral {0..T} \<phi> \<ge> integral {0..T} (\<lambda>\<tau>. \<delta>)\<close>
    using \<phi>_integrable const_integrable rate_uniform
    by (intro integral_le) auto

  have const_integral: \<open>integral {0..T} (\<lambda>\<tau>::real. \<delta>) = \<delta> * T\<close>
    using T_nn 
    by simp

  \<comment> \<open>Step 5: accumulated growth.\<close>
  have growth: \<open> u 0 + \<delta> * T \<le> u T \<close>
    using ftc integral_lb const_integral 
    by linarith

  \<comment> \<open>Step 6: T\_large overshoots the gap - contradiction.\<close>
  from T_large \<delta>_pos have \<open>Ltarget - u 0 < \<delta> * T \<close>
    by (simp add: pos_divide_less_eq mult.commute)
  hence \<open>Ltarget < u 0 + \<delta> * T\<close> 
    by linarith
  hence \<open>Ltarget < u T\<close> 
    using growth 
    by linarith
  thus False 
    using u_T_low 
    by linarith
qed

text \<open>
  DI\_convergence\_rate , Finite-Time Convergence Axiom

  \textbf{RESEARCH CONTRIBUTION}\\
  This subsection formalizes a NEW dDL axiom for finite-time convergence of
  monotonic invariants. It is the second novel dDL proof rule in our development
  (after DI\_boundary), and it captures the proof pattern that gave us
  the epsilon-convergence result for the min(x,y) CRN.

  \textbf{THE PATTERN BEING ABSTRACTED}\\
  Many computing CRNs work by monotonically accumulating an output value
  toward a target. For such systems, finite-time convergence proofs all
  the following the same shape:

\begin{enumerate}
\item The output is monotonically non-decreasing.
\item Whenever the output is still strictly below the target, the rate
  of progress is bounded below by some delta > 0.
\item By the fundamental theorem of calculus, the integrated progress
  over time T is at least delta*T.
\item Hence, after time T > (target - initial)/delta, the output exceeds
  the target.
\end{enumerate}

  The min(x,y), max(x,y), threshold detectors, and many other "monotonic
  accumulator" CRNs all instantiate this pattern. With DI\_convergence\_rate
  as a black-box axiom, each instance becomes a one-line application:
  just plug in the rate bound delta (a function of epsilon) and the monotonicity
  proof.

  \textbf{RELATIONSHIP TO PRIOR AXIOMS}\\
\begin{itemize}
\item DI (DI\_Generic, DI\_Vect): proves invariants over arbitrary trajectories
\item DG: proves strict positivity by ghost-witnessing
\item DC: lifts a proven invariant into a domain restriction
\item DI\_boundary: proves non-negativity by checking only the boundary
\item DI\_convergence\_rate (this rule): proves finite-time CONVERGENCE
  rates for monotonic invariants
\end{itemize}

  Each axiom captures a different proof strategy. Together they form
  a compositional toolkit for reasoning about dynamical systems and
  biological computers.

  \textbf{PROOF STRATEGY OF THE AXIOM}\\
  By contradiction. Suppose quant(y(T)) <= Ltarget. By monotonicity,
  quant(y(tau)) <= Ltarget for all tau in [0..T]. By the rate hypothesis,
  the time derivative is >= delta throughout [0..T]. By FTC,

    quant(y(T)) - quant(y(0)) = integral0T (d/dtau quant(y(tau))) dtau >= delta*T.

  So quant(y(T)) >= quant(y(0)) + delta*T > L - epsilon (using T > (Ltarget-quant(y(0)))/delta).
  Contradiction.
\<close>

lemma DI_convergence_rate:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes quant :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes Ltarget \<delta> T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  \<comment> \<open>The quantity along the trajectory never exceeds its final value on [0,T].\<close>
  assumes below_final: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> quant (y \<tau>) \<le> quant (y T)\<close>
  \<comment> \<open>At each time the measure is differentiable at the trajectory point, and
      while it remains below the target its Lie derivative is at least delta.\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         \<exists> Dquant. (quant has_derivative Dquant) (at (y \<tau>)) \<and>
                   (quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> Dquant (f \<tau> (y \<tau>)))\<close>
  \<comment> \<open>T is large enough for delta*T to outrun the initial gap.\<close>
  assumes T_large: \<open>(Ltarget - quant (y 0)) / \<delta> < T\<close>
  shows \<open>Ltarget < quant (y T)\<close>

proof -
  \<comment> \<open>We define the canonically chosen spatial derivative of quant along the
      trajectory.  The choice is legitimate because the Frechet derivative is
      unique (frechet\_derivative\_at): the SOME-selected map provably equals
      any witness supplied by induct\_step.\<close>
  define Dquant where
    \<open>Dquant = (\<lambda>\<tau>. SOME D. (quant has_derivative D) (at (y \<tau>)))\<close>

  \<comment> \<open>STEP 0.  Both properties of the chosen derivative, established once.
      STEP 1 uses the differentiability conjunct, STEP 2 the guarded rate
      conjunct.\<close>
  have Dquant_props:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         (quant has_derivative (Dquant \<tau>)) (at (y \<tau>)) \<and>
         (quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> Dquant \<tau> (f \<tau> (y \<tau>)))\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    obtain D where
      quant_at: \<open>(quant has_derivative D) (at (y \<tau>))\<close> and
      ineq: \<open>quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> D (f \<tau> (y \<tau>))\<close>
      using induct_step h\<tau> 
      by blast
    have Dquant_eq: \<open>Dquant \<tau> = D\<close>
      unfolding Dquant_def 
      using quant_at
      by (metis frechet_derivative_at frechet_derivative_def)
    show \<open>(quant has_derivative (Dquant \<tau>)) (at (y \<tau>)) \<and>
          (quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> Dquant \<tau> (f \<tau> (y \<tau>)))\<close>
      using quant_at ineq Dquant_eq 
      by simp
  qed

  \<comment> \<open>STEP 1.  Chain rule: we assemble the composed time-derivative on \{0..T\}.
      ODE premise supplies y' = f tau (y tau), the outer map; Dquant\_props supplies the
      spatial derivative of quant at y tau, the inner map.  
      Structure of the proof similar to DI\_Generic proof.\<close>
  have quant_vderiv:
    \<open>((\<lambda>\<tau>. quant (y \<tau>)) has_vderiv_on (\<lambda>\<tau>. Dquant \<tau> (f \<tau> (y \<tau>)))) {0..T}\<close>
    unfolding has_vderiv_on_def has_vector_derivative_def
  proof
    fix x assume hx: \<open>x \<in> {0..T}\<close>
    have quant_at_x: \<open>(quant has_derivative (Dquant x)) (at (y x))\<close>
      using Dquant_props[OF hx] 
      by simp
    have y_deriv: \<open>(y has_derivative (\<lambda>v. v *\<^sub>R f x (y x)))
                   (at x within {0..T})\<close>
      using ODE hx
      by (simp add: has_vderiv_on_def has_vector_derivative_def solves_ode_def)
    have chain: \<open>((quant \<circ> y) has_derivative (Dquant x \<circ> (\<lambda>v. v *\<^sub>R f x (y x))))
                 (at x within {0..T})\<close>
      apply (rule diff_chain_within)
       apply (rule y_deriv)
      using quant_at_x has_derivative_at_withinI
      apply blast
      done
    have eq: \<open>(Dquant x \<circ> (\<lambda>v. v *\<^sub>R f x (y x))) =
              (\<lambda>xa. xa *\<^sub>R Dquant x (f x (y x)))\<close>
      using quant_at_x
      by (auto simp add: comp_def has_derivative_bounded_linear linear_simps(5))
    show \<open>((\<lambda>\<tau>. quant (y \<tau>)) has_derivative
           (\<lambda>xa. xa *\<^sub>R Dquant x (f x (y x))))
          (at x within {0..T})\<close>
      apply (rule has_derivative_eq_rhs)
       apply (rule chain[unfolded comp_def])
      using eq
      apply (auto simp add: comp_def)
      done
  qed

  \<comment> \<open>STEP 2.  The guarded rate condition is now a projection of Dquant\_props.\<close>
  have rate_below_target:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> quant (y \<tau>) \<le> Ltarget \<Longrightarrow>
         \<delta> \<le> Dquant \<tau> (f \<tau> (y \<tau>))\<close>
    using Dquant_props 
    by blast

  \<comment> \<open>STEP 3.  Hand off to convergence\_rate\_core.\<close>
  show ?thesis
    using convergence_rate_core
            [where u = \<open>\<lambda>\<tau>. quant (y \<tau>)\<close> and \<phi> = \<open>\<lambda>\<tau>. Dquant \<tau> (f \<tau> (y \<tau>))\<close>,
             OF T_nn \<delta>_pos below_final quant_vderiv rate_below_target T_large] .
qed


text \<open>Domain-aware @\{thm DI\_convergence\_rate\}.  The differential obligation
  may assume @\{term \<open>y tau in Q\<close>\}; the conclusion additionally yields
  @{term \<open>y T \<in> Q\<close>}.  Monotonicity stays ungated, matching the treatment of
  background regularity conditions in the other @{text \<open>_dom\<close>} siblings.\<close>

lemma DI_convergence_rate_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes quant :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes Ltarget \<delta> T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes below_final: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> quant (y \<tau>) \<le> quant (y T)\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow>
         \<exists> Dquant. (quant has_derivative Dquant) (at (y \<tau>)) \<and>
                   (quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> Dquant (f \<tau> (y \<tau>)))\<close>
  assumes T_large: \<open>(Ltarget - quant (y 0)) / \<delta> < T\<close>
  shows \<open>y T \<in> Q \<and> Ltarget < quant (y T)\<close>
proof -
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)
  have step': \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         \<exists> Dquant. (quant has_derivative Dquant) (at (y \<tau>)) \<and>
                   (quant (y \<tau>) \<le> Ltarget \<longrightarrow> \<delta> \<le> Dquant (f \<tau> (y \<tau>)))\<close>
    using induct_step y_in_Q 
    by blast
  have main: \<open>Ltarget < quant (y T)\<close>
    using DI_convergence_rate[OF ODE T_nn \<delta>_pos below_final step' T_large] .
  have endpoint: \<open>y T \<in> Q\<close> using y_in_Q[of T] T_nn by simp
  show ?thesis using endpoint main 
    by simp
qed

text \<open>
  \textbf{USAGE NOTES}\\
  To apply DI\_convergence\_rate to a specific computing CRN:

\begin{enumerate}
\item Identify the progress measure `quant` (typically a single vector
  component)
\item Identify the target `Ltarget` (the value the CRN computes, less any
  margin the application wants)
\item Identify the rate `delta` (depends on the ODE and on that margin)
\item Provide:
  - The ODE solution
  - `below\_final`: the measure never exceeds its final value on [0,T]
  (often a separate lemma using DI\_Vect)
  - `induct\_step`: at each trajectory point, the measure is
  differentiable and, WHILE it remains below the target, its Lie
  derivative is at least delta.  The composed time-derivative is NOT
  supplied - the rule derives it from the ODE by the chain rule.
  - `T\_large`: T outruns the initial gap.
\end{enumerate}

  EXAMPLE: For min(x,y) with ODE d[Z]/dt = k*X*Y, with margin epsilon:
\begin{itemize}
\item quant   = vec\_nth v 2  (Z component)
\item Ltarget = min(x0, y0) - epsilon
\item delta       = k * epsilon\textasciicircum{}2  (when Z <= Ltarget, conservation gives X, Y >= epsilon,
  so dZ/dt = k*X*Y >= k*epsilon\textasciicircum{}2)
\item T\_large : T > (Ltarget - Z(0)) / (k * epsilon\textasciicircum{}2)
\end{itemize}

  Remark: the rule itself has no epsilon, only
  `Ltarget`.  Positivity of epsilon is needed here to establish the rate bound
  (X, Y >= epsilon gives X*Y >= epsilon\textasciicircum{}2), not by the rule.
\<close>

subsection \<open>Lyapunov reachability\<close>
text \<open>
  Gr\"onwall-type comparison.  If a differentiable function decays at least
  proportionally to its own value, it is bounded by the corresponding
  exponential.  Note this holds for ANY real @\{term delta\} and for @\{term u\} of
  either sign: positivity of the rate and non-negativity of @\{term u\} belong
  to the Lyapunov READING of the result, not to its proof.\<close>

lemma gronwall_comparison_core:
  fixes u \<phi> :: \<open>real \<Rightarrow> real\<close>
  fixes \<delta> T :: real
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_vderiv: \<open>(u has_vderiv_on \<phi>) {0..T}\<close>
  assumes rate: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> \<phi> \<tau> \<le> -\<delta> * u \<tau>\<close>
  shows \<open>u T \<le> u 0 * exp (-\<delta> * T)\<close>
proof -
  \<comment> \<open>The compensated function g tau = u tau * exp(delta*tau), re-scaled to cancel the
      expected decay: if u decays exactly at rate -delta*u then g is constant,
      and if it decays faster then g decreases.\<close>
  let ?g = \<open>\<lambda>\<tau>::real. u \<tau> * exp (\<delta> * \<tau>)\<close>

  have exp_vderiv: \<open>((\<lambda>\<tau>. exp (\<delta> * \<tau>)) has_vderiv_on (\<lambda>\<tau>. \<delta> * exp (\<delta> * \<tau>))) {0..T}\<close>
    unfolding has_vderiv_on_def has_vector_derivative_def
    by (auto intro!: derivative_eq_intros)

  \<comment> \<open>Product rule.\<close>
  have g_vderiv_raw:
    \<open>(?g has_vderiv_on
      (\<lambda>\<tau>. \<phi> \<tau> * exp (\<delta> * \<tau>) + u \<tau> * (\<delta> * exp (\<delta> * \<tau>)))) {0..T}\<close>
    using has_vderiv_on_mult[OF u_vderiv exp_vderiv]
    by (simp add: add.commute)

  have g_vderiv:
    \<open>(?g has_vderiv_on
      (\<lambda>\<tau>. (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>))) {0..T}\<close>
  proof -
    have eq: \<open>\<And>\<tau>. \<phi> \<tau> * exp (\<delta> * \<tau>) + u \<tau> * (\<delta> * exp (\<delta> * \<tau>)) =
                   (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>)\<close>
      by (simp add: algebra_simps)
    show ?thesis
      using g_vderiv_raw 
      by (simp add: eq)
  qed

  \<comment> \<open>The rate hypothesis makes g's derivative non-positive.\<close>
  have rate_sum_nonpos:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> \<phi> \<tau> + \<delta> * u \<tau> \<le> 0\<close>
    using rate le_eq_neg
    by (auto simp add: algebra_simps)

  have exp_pos: \<open>\<And>\<tau>. 0 < exp (\<delta> * \<tau>)\<close>
    by simp

  have g_deriv_nonpos:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>) \<le> 0\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    have a: \<open>\<phi> \<tau> + \<delta> * u \<tau> \<le> 0\<close> using rate_sum_nonpos h\<tau> .
    have b: \<open>0 \<le> exp (\<delta> * \<tau>)\<close> using exp_pos by (simp add: less_imp_le)
    show \<open>(\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>) \<le> 0\<close>
      using a b 
      by (simp add: mult_nonpos_nonneg)
  qed

  \<comment> \<open>FTC: g is non-increasing.\<close>
  have g_monotone: \<open>?g T \<le> ?g 0\<close>
  proof -
    have ftc: \<open>?g T - ?g 0 =
               integral {0..T} (\<lambda>\<tau>. (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>))\<close>
      using g_vderiv T_nn
      by (metis (no_types, lifting) fundamental_theorem_of_calculus' integral_unique)
    have integrand_nonpos: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
                               (\<lambda>\<tau>. (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>)) \<tau> \<le> 0\<close>
      using g_deriv_nonpos 
      by simp
    have integral_nonpos:
      \<open>integral {0..T} (\<lambda>\<tau>. (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>)) \<le> 0\<close>
    proof -
      have \<open>integral {0..T} (\<lambda>\<tau>. (\<phi> \<tau> + \<delta> * u \<tau>) * exp (\<delta> * \<tau>))
            \<le> integral {0..T} (\<lambda>\<tau>::real. 0)\<close>
        apply (rule integral_le)
          apply (use integrand_nonpos in auto)
        using T_nn fundamental_theorem_of_calculus' g_vderiv
        apply blast
        done
      thus ?thesis 
        by simp
    qed
    from ftc integral_nonpos have \<open>?g T - ?g 0 \<le> 0\<close> by simp
    thus ?thesis 
      by simp
  qed

  have g_at_0: \<open>?g 0 = u 0\<close>
    by simp

  have g_at_T: \<open>?g T = u T * exp (\<delta> * T)\<close>
    by simp

  have product_bound: \<open>u T * exp (\<delta> * T) \<le> u 0\<close>
    using g_monotone g_at_0 g_at_T 
    by simp

  have exp_T_pos: \<open>0 < exp (\<delta> * T)\<close>
    by simp

  show \<open>u T \<le> u 0 * exp (-\<delta> * T)\<close>
  proof -
    have \<open>u T = u T * exp (\<delta> * T) * exp (-\<delta> * T)\<close>
      using exp_T_pos 
      by (simp add: exp_minus field_simps)
    also have \<open>\<dots> \<le> u 0 * exp (-\<delta> * T)\<close>
      using product_bound exp_pos[of T] 
      by (simp add: mult_right_mono)
    finally show ?thesis .
  qed
qed

text \<open>
  REACH\_lyapunov , Lyapunov-based exponential decay reachability

  CONTEXT
  The other formalized dDL proof rules (DI\_Vect, DI\_boundary, DC, DG) handle invariance-style
  reasoning: "once in a safe equilibrium, stay in a safe equilibrium."
   Our earlier novel proof rule
  (DI\_convergence\_rate) extend dDL toward convergence to safe equilibrium at a
  guaranteed rate.  REACH\_lyapunov continues this line by extending dDL to
  handle LYAPUNOV-BASED REACHABILITY: "a trajectory whose Lyapunov function
  decreases at a rate proportional to its current value reaches any target
  sublevel set in bounded time."

  This proof rule is specifically motivated by biological computing properties
  that involve "behavior outside the steady state" , induced switching in
  toggle switches, convergence after perturbation, feedback loop settling
  after a disturbance.  Classical Lyapunov stability theorems have exactly
  this shape, and REACH\_lyapunov is the finite-horizon, dDL-compatible
  packaging of the classical Lyapunov stability theorems.

  STATEMENT (informal)
  Given an ODE solution y on [0..T], a non-negative Lyapunov function V,
  and a pointwise rate bound phi(tau) <= -delta * V(y(tau)) on the time derivative
  of V o y, the value V(y(T)) is bounded by V(y(0)) * exp(-delta * T).

  \textbf{PROOF STRATEGY}\\
  Define g(tau) = V(y(tau)) * exp(delta*tau).  Compute g's vderiv via the product
  rule: g'(tau) = (phi(tau) + delta*V(y(tau))) * exp(delta*tau).  From the rate hypothesis
  phi(tau) + delta*V(y(tau)) <= 0, and since exp(delta*tau) > 0, we have g'(tau) <= 0 on
  [0..T].  Integrating: g(T) - g(0) = integral0T g' <= 0, so g(T) <= g(0).
  Since g(0) = V(y(0)) and g(T) = V(y(T))*exp(delta*T), dividing yields
  V(y(T)) <= V(y(0))*exp(-delta*T).

  This is classical Gronwall-type reasoning, packaged as a dDL axiom.
\<close>
lemma REACH_lyapunov:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes V :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes \<delta> T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  \<comment> \<open>At each time the Lyapunov function V is differentiable at the trajectory
      point, and its Lie derivative is at most -delta times its current value.\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         \<exists> DV. (V has_derivative DV) (at (y \<tau>)) \<and>
               DV (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
  shows \<open>V (y T) \<le> V (y 0) * exp (-\<delta> * T)\<close>
proof -
  \<comment> \<open>We define the canonically chosen spatial derivative of V along the trajectory.
      The choice is legitimate because the Frechet derivative is unique
      (frechet\_derivative\_at): the SOME-selected map provably equals any
      witness supplied by induct\_step. We then proceed as in the proof of DI\_convergence\_rate\<close>
  define DV where
    \<open>DV = (\<lambda>\<tau>. SOME D. (V has_derivative D) (at (y \<tau>)))\<close>

  \<comment> \<open>STEP 0.  Both properties of the chosen derivative, established once.
      STEP 1 uses the differentiability conjunct, STEP 2 the rate conjunct.\<close>
  have DV_props:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         (V has_derivative (DV \<tau>)) (at (y \<tau>)) \<and>
         DV \<tau> (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    obtain D where
      V_at: \<open>(V has_derivative D) (at (y \<tau>))\<close> and
      ineq: \<open>D (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
      using induct_step h\<tau> 
      by blast
    have DV_eq: \<open>DV \<tau> = D\<close>
      unfolding DV_def using V_at
      by (metis frechet_derivative_at frechet_derivative_def)
    show \<open>(V has_derivative (DV \<tau>)) (at (y \<tau>)) \<and>
          DV \<tau> (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
      using V_at ineq DV_eq 
      by simp
  qed

  \<comment> \<open>STEP 1.  Chain rule: we assemble the composed time-derivative on \{0..T\}.
      The premise ODE supplies y' = f tau (y tau), the outer map; DV\_props supplies the
      spatial derivative of V at y tau, the inner map.\<close>
  have V_vderiv:
    \<open>((\<lambda>\<tau>. V (y \<tau>)) has_vderiv_on (\<lambda>\<tau>. DV \<tau> (f \<tau> (y \<tau>)))) {0..T}\<close>
    unfolding has_vderiv_on_def has_vector_derivative_def
  proof
    fix x assume hx: \<open>x \<in> {0..T}\<close>
    have V_at_x: \<open>(V has_derivative (DV x)) (at (y x))\<close>
      using DV_props[OF hx] 
      by simp
    have y_deriv: \<open>(y has_derivative (\<lambda>v. v *\<^sub>R f x (y x)))
                   (at x within {0..T})\<close>
      using ODE hx
      by (simp add: has_vderiv_on_def has_vector_derivative_def solves_ode_def)
    have chain: \<open>((V \<circ> y) has_derivative (DV x \<circ> (\<lambda>v. v *\<^sub>R f x (y x))))
                 (at x within {0..T})\<close>
      apply (rule diff_chain_within)
       apply (rule y_deriv)
      using V_at_x has_derivative_at_withinI
      apply blast
      done
    have eq: \<open>(DV x \<circ> (\<lambda>v. v *\<^sub>R f x (y x))) =
              (\<lambda>xa. xa *\<^sub>R DV x (f x (y x)))\<close>
      using V_at_x
      by (auto simp add: comp_def has_derivative_bounded_linear linear_simps(5))
    show \<open>((\<lambda>\<tau>. V (y \<tau>)) has_derivative
           (\<lambda>xa. xa *\<^sub>R DV x (f x (y x))))
          (at x within {0..T})\<close>
      apply (rule has_derivative_eq_rhs)
       apply (rule chain[unfolded comp_def])
      using eq
      apply (auto simp add: comp_def)
      done
  qed

  \<comment> \<open>STEP 2.  The rate condition is now a projection of DV\_props.\<close>
  have rate:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> DV \<tau> (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
    using DV_props 
    by blast

  \<comment> \<open>STEP 3.  Hand off to gronwall\_comparison\_core.\<close>
  show ?thesis
    using gronwall_comparison_core
            [where u = \<open>\<lambda>\<tau>. V (y \<tau>)\<close> and \<phi> = \<open>\<lambda>\<tau>. DV \<tau> (f \<tau> (y \<tau>))\<close>,
             OF T_nn V_vderiv rate] .
qed


text \<open>Domain-aware @\{thm REACH\_lyapunov\}. Only the rate-proportional
     (Lie-derivative) condition is constrained by @\{term \<open>y tau in Q\<close>\}; nonnegativity
     of @{term V} stays global.\<close>

lemma REACH_lyapunov_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes V :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes \<delta> T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow>
         \<exists> DV. (V has_derivative DV) (at (y \<tau>)) \<and>
               DV (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
  shows \<open>y T \<in> Q \<and> V (y T) \<le> V (y 0) * exp (-\<delta> * T)\<close>
proof -
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using ODE 
    by (auto simp add: solves_ode_def Pi_iff)
  have step': \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         \<exists> DV. (V has_derivative DV) (at (y \<tau>)) \<and>
               DV (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
    using induct_step y_in_Q 
    by blast
  have main: \<open>V (y T) \<le> V (y 0) * exp (-\<delta> * T)\<close>
    using REACH_lyapunov[OF ODE T_nn step'] .
  have endpoint: \<open>y T \<in> Q\<close> using y_in_Q[of T] T_nn by simp
  show ?thesis 
    using endpoint main 
    by simp
qed

corollary REACH_lyapunov_sublevel_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes V :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes \<delta> L T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> y \<tau> \<in> Q \<Longrightarrow>
         \<exists> DV. (V has_derivative DV) (at (y \<tau>)) \<and>
               DV (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
  assumes sublevel_reached: \<open>V (y 0) * exp (-\<delta> * T) \<le> L\<close>
  shows \<open>y T \<in> Q \<and> V (y T) \<le> L\<close>
proof -
  have main: \<open>y T \<in> Q \<and> V (y T) \<le> V (y 0) * exp (-\<delta> * T)\<close>
    using REACH_lyapunov_dom[OF ODE T_nn induct_step] .
  hence \<open>V (y T) \<le> V (y 0) * exp (-\<delta> * T)\<close> by simp
  also have \<open>\<dots> \<le> L\<close> 
         using sublevel_reached .
  finally have \<open>V (y T) \<le> L\<close> .
  thus ?thesis 
    using main 
    by simp
qed


text \<open>
  USAGE EXAMPLE: Sublevel-set reachability as a corollary

  The exponential decay form is the foundational statement.  For reachability
  applications (e.g., "does the trajectory enter a target sublevel set?"),
  we derive the following corollary:

  If V(y(0)) * exp(-delta*T) <= L, then V(y(T)) <= L.

  In particular, for any target level L > 0, the time
    T = (1/delta) * log(V(y(0))/L)
  suffices (assuming V(y(0)) > L) to reach the sublevel set \{V <= L\}.
\<close>

corollary REACH_lyapunov_sublevel:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes V :: \<open>(real, 'a) vec \<Rightarrow> real\<close>
  fixes \<delta> L T :: real
  assumes ODE: \<open>(y solves_ode f) {0..T} Q\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 
         \<exists> DV. (V has_derivative DV) (at (y \<tau>)) \<and>
               DV (f \<tau> (y \<tau>)) \<le> -\<delta> * V (y \<tau>)\<close>
  assumes sublevel_reached: \<open>V (y 0) * exp (-\<delta> * T) \<le> L\<close>
  shows \<open>V (y T) \<le> L\<close>
  using REACH_lyapunov[OF ODE T_nn induct_step] sublevel_reached
  by simp

subsection \<open>DI Rectangle Box a.k.a DI Frame Rule\<close>

lemma continuous_strictly_interior_neighborhood:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes \<tau>_star t :: real
  assumes y_cont: \<open>continuous_on {0..t} y\<close>
  assumes \<tau>_in: \<open>\<tau>_star \<in> {0..t}\<close>
  assumes strict: \<open>\<And>i. lo i < vec_nth (y \<tau>_star) i \<and> vec_nth (y \<tau>_star) i < hi i\<close>
  shows \<open>\<exists>\<delta> > 0. \<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_star\<bar> < \<delta> \<longrightarrow> 
                 (\<forall>i. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
proof -
  (* Define the open box *)
  define open_box :: \<open>(real, 'a) vec set\<close> 
    where \<open>open_box = {v. \<forall>i. lo i < vec_nth v i \<and> vec_nth v i < hi i}\<close>

  (* The open box is open *)
  have open_box_open: \<open>open open_box\<close>
  proof -
    have proj_cont: \<open>\<And>i. continuous_on UNIV (\<lambda>v::(real, 'a) vec. vec_nth v i)\<close>
      by (auto intro: continuous_on_component)
    have lo_open: \<open>\<And>i. open {v :: (real, 'a) vec. lo i < vec_nth v i}\<close>
    proof -
      fix i
      show \<open>open {v :: (real, 'a) vec. lo i < vec_nth v i}\<close>
        using open_Collect_less[OF continuous_on_const[where c="lo i"] 
                                    proj_cont[of i]]
        by simp
    qed
    have hi_open: \<open>\<And>i. open {v :: (real, 'a) vec. vec_nth v i < hi i}\<close>
    proof -
      fix i
      show \<open>open {v :: (real, 'a) vec. vec_nth v i < hi i}\<close>
        using open_Collect_less[OF proj_cont[of i] 
                                    continuous_on_const[where c="hi i"]]
        by simp
    qed
    have \<open>open_box = (\<Inter>i\<in>UNIV. {v. lo i < vec_nth v i} \<inter> {v. vec_nth v i < hi i})\<close>
      unfolding open_box_def by blast
    moreover have \<open>open (\<Inter>i\<in>UNIV. {v :: (real, 'a) vec. lo i < vec_nth v i} 
                                  \<inter> {v. vec_nth v i < hi i})\<close>
      using lo_open hi_open 
      by (auto simp: open_INT open_Int)
    ultimately show ?thesis by simp
  qed

  (* y \<tau>_star is in the open box *)
  have y_\<tau>_star_in: \<open>y \<tau>_star \<in> open_box\<close>
    using strict 
    unfolding open_box_def 
    by blast

  (* By continuity, the pre-image is open in {0..t} *)
  have preimage_open: \<open>openin (top_of_set {0..t}) (y -` open_box \<inter> {0..t})\<close>
    using y_cont open_box_open 
    by (metis Int_ac(3) continuous_openin_preimage_eq)

  (* \<tau>_star is in the pre-image *)
  have \<tau>_star_in_preimage: \<open>\<tau>_star \<in> y -` open_box \<inter> {0..t}\<close>
    using \<tau>_in y_\<tau>_star_in 
    by auto

  (* An open set in top_of_set {0..t} contains a ball around every point *)
  obtain \<delta> where \<delta>_pos: \<open>0 < \<delta>\<close> 
             and \<delta>_ball: \<open>ball \<tau>_star \<delta> \<inter> {0..t} \<subseteq> y -` open_box \<inter> {0..t}\<close>
    using preimage_open \<tau>_star_in_preimage
    by (metis openin_contains_ball)

  (* Translate the ball condition into an \<epsilon>-\<delta> statement *)
  show ?thesis
  proof (rule exI[where x=\<delta>], intro conjI)
    show \<open>0 < \<delta>\<close> using \<delta>_pos .
  next
    show \<open>\<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_star\<bar> < \<delta> \<longrightarrow> 
          (\<forall>i. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
    proof (intro ballI impI)
      fix \<tau> assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> and \<tau>_close: \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>\<close>
      have \<open>\<tau> \<in> ball \<tau>_star \<delta>\<close>
        using \<tau>_close by (simp add: dist_real_def)
      with \<tau>_in_t \<delta>_ball have \<open>\<tau> \<in> y -` open_box\<close>
        by blast
      hence \<open>y \<tau> \<in> open_box\<close> by auto
      thus \<open>\<forall>i. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i\<close>
        unfolding open_box_def 
        by blast
    qed
  qed
qed

lemma continuous_within_gt_neighborhood:
  fixes \<phi> :: \<open>real \<Rightarrow> real\<close>
  assumes cont: \<open>continuous (at x within S) \<phi>\<close>
  assumes bound: \<open>c < \<phi> x\<close>
  shows \<open>\<exists>d > 0. \<forall>\<tau> \<in> S. \<bar>\<tau> - x\<bar> < d \<longrightarrow> c < \<phi> \<tau>\<close>
proof -
  define \<epsilon> where \<open>\<epsilon> = \<phi> x - c\<close>
  have \<epsilon>_pos: \<open>0 < \<epsilon>\<close> 
    using bound 
    unfolding \<epsilon>_def 
    by simp
  from cont have \<open>\<exists>d > 0. \<forall>\<tau> \<in> S. dist \<tau> x < d \<longrightarrow> dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
    unfolding continuous_within_eps_delta 
    using \<epsilon>_pos 
    by blast
  then obtain d where d_pos: \<open>0 < d\<close>
                  and d_prop: \<open>\<forall>\<tau> \<in> S. dist \<tau> x < d \<longrightarrow> dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
    by blast
  show ?thesis
  proof (intro exI[where x=d] conjI)
    show \<open>0 < d\<close> using d_pos .
  next
    show \<open>\<forall>\<tau> \<in> S. \<bar>\<tau> - x\<bar> < d \<longrightarrow> c < \<phi> \<tau>\<close>
    proof (intro ballI impI)
      fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> S\<close> and \<tau>_close: \<open>\<bar>\<tau> - x\<bar> < d\<close>
      have \<open>dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
        using d_prop \<tau>_in \<tau>_close 
        by (simp add: dist_real_def)
      hence \<open>\<bar>\<phi> \<tau> - \<phi> x\<bar> < \<epsilon>\<close>
        by (simp add: dist_real_def)
      hence \<open>\<phi> x - \<epsilon> < \<phi> \<tau>\<close>
        by auto
      thus \<open>c < \<phi> \<tau>\<close>
        unfolding \<epsilon>_def 
        by simp
    qed
  qed
qed

lemma continuous_within_lt_neighborhood:
  fixes \<phi> :: \<open>real \<Rightarrow> real\<close>
  assumes cont: \<open>continuous (at x within S) \<phi>\<close>
  assumes bound: \<open>\<phi> x < c\<close>
  shows \<open>\<exists>d > 0. \<forall>\<tau> \<in> S. \<bar>\<tau> - x\<bar> < d \<longrightarrow> \<phi> \<tau> < c\<close>
proof -
  define \<epsilon> where \<open>\<epsilon> = c - \<phi> x\<close>
  have \<epsilon>_pos: \<open>0 < \<epsilon>\<close> using bound unfolding \<epsilon>_def by simp
  from cont have \<open>\<exists>d > 0. \<forall>\<tau> \<in> S. dist \<tau> x < d \<longrightarrow> dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
    unfolding continuous_within_eps_delta 
    using \<epsilon>_pos 
    by blast
  then obtain d where d_pos: \<open>0 < d\<close>
                  and d_prop: \<open>\<forall>\<tau> \<in> S. dist \<tau> x < d \<longrightarrow> dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
    by blast
  show ?thesis
  proof (intro exI[where x=d] conjI)
    show \<open>0 < d\<close> using d_pos .
  next
    show \<open>\<forall>\<tau> \<in> S. \<bar>\<tau> - x\<bar> < d \<longrightarrow> \<phi> \<tau> < c\<close>
    proof (intro ballI impI)
      fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> S\<close> and \<tau>_close: \<open>\<bar>\<tau> - x\<bar> < d\<close>
      have \<open>dist (\<phi> \<tau>) (\<phi> x) < \<epsilon>\<close>
        using d_prop \<tau>_in \<tau>_close 
        by (simp add: dist_real_def)
      hence \<open>\<bar>\<phi> \<tau> - \<phi> x\<bar> < \<epsilon>\<close>
        by (simp add: dist_real_def)
      hence \<open>\<phi> \<tau> < \<phi> x + \<epsilon>\<close>
        by auto
      thus \<open>\<phi> \<tau> < c\<close>
        unfolding \<epsilon>_def 
        by simp
    qed
  qed
qed

lemma solves_ode_inward_neighborhood:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes \<tau>_star t :: real
  fixes Q :: \<open>(real, 'a) vec set\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes \<tau>_in: \<open>\<tau>_star \<in> {0..t}\<close>
  assumes \<tau>_lt_t: \<open>\<tau>_star < t\<close>
  assumes in_box_at: \<open>\<And>i. lo i \<le> vec_nth (y \<tau>_star) i \<and> vec_nth (y \<tau>_star) i \<le> hi i\<close>
  assumes lower_edge_inward_at:
    \<open>\<And>i. vec_nth (y \<tau>_star) i = lo i \<Longrightarrow> 0 < vec_nth (f \<tau>_star (y \<tau>_star)) i\<close>
  assumes upper_edge_inward_at:
    \<open>\<And>i. vec_nth (y \<tau>_star) i = hi i \<Longrightarrow> vec_nth (f \<tau>_star (y \<tau>_star)) i < 0\<close>
  shows \<open>\<exists>\<epsilon> > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                    (\<forall>i. lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
proof -
  (* Extract that y is continuous and has vderiv from the premise ODE *)
  have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) {0..t}\<close>
    using ODE 
    by (simp add: solves_ode_def)
  
  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast

  (* For each coordinate i, obtain a \<delta>_i > 0 such that the coordinate 
     stays within its bounds for \<tau> \<in> (\<tau>_star, \<tau>_star + \<delta>_i] \<inter> {0..t} *)
  have per_coord: \<open>\<And>i. \<exists>\<delta>_i > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                                    lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i
    define \<phi> where \<open>\<phi> = (\<lambda>\<tau>. vec_nth (y \<tau>) i)\<close>
    define \<phi>'_val where \<open>\<phi>'_val = vec_nth (f \<tau>_star (y \<tau>_star)) i\<close>

    have \<phi>_cont: \<open>continuous_on {0..t} \<phi>\<close>
      unfolding \<phi>_def using y_cont
      by (auto intro: continuous_on_compose2[OF continuous_on_component])

    have \<phi>_deriv: \<open>(\<phi> has_real_derivative \<phi>'_val) (at \<tau>_star within {0..t})\<close>
    proof -
      have y_at: \<open>(y has_vector_derivative f \<tau>_star (y \<tau>_star)) (at \<tau>_star within {0..t})\<close>
        using y_vderiv \<tau>_in unfolding has_vderiv_on_def by blast
      hence y_deriv: \<open>(y has_derivative (\<lambda>h. h *\<^sub>R f \<tau>_star (y \<tau>_star))) 
                      (at \<tau>_star within {0..t})\<close>
        unfolding has_vector_derivative_def 
        by blast
      have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>_star))\<close>
        by (rule has_derivative_vec_nth)
      have composed: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                       (\<lambda>h. vec_nth (h *\<^sub>R f \<tau>_star (y \<tau>_star)) i)) 
                      (at \<tau>_star within {0..t})\<close>
        using has_derivative_compose[OF y_deriv proj] by simp
      have eq: \<open>(\<lambda>h. vec_nth (h *\<^sub>R f \<tau>_star (y \<tau>_star)) i) = (\<lambda>h. h * \<phi>'_val)\<close>
        unfolding \<phi>'_val_def 
        by auto
      show ?thesis
        unfolding \<phi>_def has_field_derivative_def
        using composed eq 
        by (simp add: mult_commute_abs)
    qed

    have lo_bound: \<open>lo i \<le> \<phi> \<tau>_star\<close> and hi_bound: \<open>\<phi> \<tau>_star \<le> hi i\<close>
      unfolding \<phi>_def using in_box_at by auto

    have \<phi>_cont_at: \<open>continuous (at \<tau>_star within {0..t}) \<phi>\<close>
      using \<phi>_cont \<tau>_in
      by (simp add: continuous_on_eq_continuous_within)

    show \<open>\<exists>\<delta>_i > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                        lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof (cases \<open>\<phi> \<tau>_star = lo i\<close>; cases \<open>\<phi> \<tau>_star = hi i\<close>)
      assume at_lo: \<open>\<phi> \<tau>_star = lo i\<close> and at_hi: \<open>\<phi> \<tau>_star = hi i\<close>
      have \<open>0 < \<phi>'_val\<close> using lower_edge_inward_at at_lo unfolding \<phi>_def \<phi>'_val_def by simp
      moreover have \<open>\<phi>'_val < 0\<close> 
        using upper_edge_inward_at at_hi 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      ultimately have False 
                   by simp
      thus ?thesis 
             by blast
    next
      assume at_lo: \<open>\<phi> \<tau>_star = lo i\<close> and not_hi: \<open>\<phi> \<tau>_star \<noteq> hi i\<close>
      have \<phi>'_pos: \<open>0 < \<phi>'_val\<close>
        using lower_edge_inward_at at_lo 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>h. 0 < h \<Longrightarrow> \<tau>_star + h \<in> {0..t} \<Longrightarrow> h < d_lo \<Longrightarrow> 
                                        \<phi> \<tau>_star < \<phi> (\<tau>_star + h)\<close>
        using has_real_derivative_pos_inc_right[OF \<phi>_deriv \<phi>'_pos]
        by metis
      have \<phi>_lt_hi: \<open>\<phi> \<tau>_star < hi i\<close> using hi_bound not_hi by auto
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_hi \<Longrightarrow> \<phi> \<tau> < hi i\<close>
        using continuous_within_lt_neighborhood[OF \<phi>_cont_at \<phi>_lt_hi] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> 
        using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> 
          using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
            using h \<tau>_in 
            by auto
          have h_val: \<open>\<tau> - \<tau>_star > 0\<close> 
            using h 
            by auto
          have \<open>\<phi> \<tau>_star < \<phi> \<tau>\<close>
          proof -
            have \<open>\<tau>_star + (\<tau> - \<tau>_star) \<in> {0..t}\<close> 
              using \<tau>_in_t 
              by simp
            moreover have \<open>\<tau> - \<tau>_star < d_lo\<close> 
              using h 
              unfolding \<delta>_i_def
              by linarith
            ultimately show ?thesis 
              using d_lo_prop[of \<open>\<tau> - \<tau>_star\<close>] h_val 
              by simp
          qed
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close> 
            using at_lo 
            unfolding \<phi>_def 
            by simp
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < d_hi\<close> 
            using h 
            unfolding \<delta>_i_def 
            by auto
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using d_hi_prop \<tau>_in_t 
            unfolding \<phi>_def 
            by fastforce
          from lo_ok hi_ok 
            show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    next
      assume not_lo: \<open>\<not> (\<phi> \<tau>_star = lo i)\<close> and at_hi: \<open>\<phi> \<tau>_star = hi i\<close>
      have \<phi>'_neg: \<open>\<phi>'_val < 0\<close>
        using upper_edge_inward_at at_hi 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      define \<psi> where \<open>\<psi> = (\<lambda>\<tau>. - \<phi> \<tau>)\<close>
      have \<psi>_deriv: \<open>(\<psi> has_real_derivative (- \<phi>'_val)) (at \<tau>_star within {0..t})\<close>
        unfolding \<psi>_def using \<phi>_deriv  Deriv.field_differentiable_minus
        by blast
      have neg_pos: \<open>0 < - \<phi>'_val\<close> using \<phi>'_neg by simp
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>h. 0 < h \<Longrightarrow> \<tau>_star + h \<in> {0..t} \<Longrightarrow> h < d_hi \<Longrightarrow> 
                                        \<psi> \<tau>_star < \<psi> (\<tau>_star + h)\<close>
        using has_real_derivative_pos_inc_right[OF \<psi>_deriv neg_pos]
        by metis
      have \<phi>_gt_lo: \<open>lo i < \<phi> \<tau>_star\<close> using lo_bound not_lo by auto
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_lo \<Longrightarrow> lo i < \<phi> \<tau>\<close>
        using continuous_within_gt_neighborhood[OF \<phi>_cont_at \<phi>_gt_lo] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> 
        using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> 
          using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
            using h \<tau>_in 
            by auto
          have h_val: \<open>\<tau> - \<tau>_star > 0\<close> 
            using h 
            by auto
          have \<open>\<psi> \<tau>_star < \<psi> (\<tau>_star + (\<tau> - \<tau>_star))\<close>
          proof -
            have \<open>\<tau>_star + (\<tau> - \<tau>_star) \<in> {0..t}\<close> 
              using \<tau>_in_t 
              by simp
            moreover have \<open>\<tau> - \<tau>_star < d_hi\<close> 
              using h 
              unfolding \<delta>_i_def
              by linarith
            ultimately show ?thesis 
              using d_hi_prop[of \<open>\<tau> - \<tau>_star\<close>] h_val 
              by simp
          qed
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using at_hi 
            unfolding \<psi>_def \<phi>_def 
            by simp
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < d_lo\<close> 
            using h unfolding \<delta>_i_def 
            by auto
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close>
            using d_lo_prop \<tau>_in_t unfolding \<phi>_def
            by fastforce
          from lo_ok hi_ok 
            show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    next
      assume not_lo: \<open>\<not> (\<phi> \<tau>_star = lo i)\<close> and not_hi: \<open>\<not> (\<phi> \<tau>_star = hi i)\<close>
      have \<phi>_gt_lo: \<open>lo i < \<phi> \<tau>_star\<close> 
        using lo_bound not_lo 
        by auto
      have \<phi>_lt_hi: \<open>\<phi> \<tau>_star < hi i\<close> 
        using hi_bound not_hi 
        by auto
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_lo \<Longrightarrow> lo i < \<phi> \<tau>\<close>
        using continuous_within_gt_neighborhood[OF \<phi>_cont_at \<phi>_gt_lo] 
        by blast
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_hi \<Longrightarrow> \<phi> \<tau> < hi i\<close>
        using continuous_within_lt_neighborhood[OF \<phi>_cont_at \<phi>_lt_hi] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> 
        using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
            using h \<tau>_in 
            by auto
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>_i\<close> 
            using h 
            by auto
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close>
            using d_lo_prop \<tau>_in_t 
            unfolding \<phi>_def \<delta>_i_def
            by fastforce
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>_i\<close> 
            using h 
            by auto
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using d_hi_prop \<tau>_in_t 
            unfolding \<phi>_def \<delta>_i_def 
            by fastforce
          from lo_ok hi_ok 
            show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    qed
  qed (* STEP A: per-coordinate existence of \<delta>_i *)

  (* Take \<epsilon> as the minimum over all coordinates *)
  have ex_global: \<open>\<exists>\<epsilon> > 0. \<forall>i. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                                   lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    define \<delta>_fun where \<open>\<delta>_fun = (\<lambda>i. SOME \<delta>_i. 0 < \<delta>_i \<and> 
        (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i))\<close>
    have \<delta>_fun_spec: \<open>\<And>i. 0 < \<delta>_fun i \<and> 
        (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_fun i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
    proof -
      fix i
      from per_coord[of i] obtain \<delta>_i where 
        \<open>0 < \<delta>_i\<close> and
        \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        by blast
      from per_coord[of i] have ex_i: 
        \<open>\<exists>\<delta>_i. 0 < \<delta>_i \<and> 
          (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        by blast
      show \<open>0 < \<delta>_fun i \<and> 
            (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_fun i \<and> \<tau> \<le> t \<longrightarrow> 
                 lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        unfolding \<delta>_fun_def
        by (rule someI_ex[OF ex_i])
    qed
    define \<epsilon> where \<open>\<epsilon> = Min (\<delta>_fun ` UNIV)\<close>
    have \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
      unfolding \<epsilon>_def 
      using \<delta>_fun_spec 
      by simp
    have \<epsilon>_le: \<open>\<And>i. \<epsilon> \<le> \<delta>_fun i\<close>
      unfolding \<epsilon>_def 
      by simp
    show ?thesis
    proof (rule exI[where x=\<epsilon>], intro conjI)
      show \<open>0 < \<epsilon>\<close> using \<epsilon>_pos .
    next
      show \<open>\<forall>i \<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      proof (intro allI impI)
        fix i \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t\<close>
        have \<open>\<tau> < \<tau>_star + \<delta>_fun i\<close> using h \<epsilon>_le[of i] 
          by auto
        with h \<delta>_fun_spec[of i]
        show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
          by blast
      qed
    qed (* STEP B: take Min over all \<delta>_i's *)
qed
show ?thesis
  using ex_global 
  by blast
qed

lemma DI_Rec_Box:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes t :: real
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  assumes box_ordered: \<open>\<And>i. lo i < hi i\<close>
  assumes lower_edge_inward:
    \<open>\<And>i v \<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (f \<tau> v) i\<close>
  assumes upper_edge_inward:
    \<open>\<And>i v \<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (f \<tau> v) i < 0\<close>
  shows \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
proof -
  (* We define the "in_box" predicate for readability *)
  define in_box :: \<open>(real, 'a) vec \<Rightarrow> bool\<close> 
    where \<open>in_box = (\<lambda>v. \<forall>i. lo i \<le> vec_nth v i \<and> vec_nth v i \<le> hi i)\<close>

(* Trajectory continuity from the premise ODE *)
  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast

(* Main claim: the trajectory is in the box at every time *)
  have main_claim: \<open>\<forall>\<tau> \<in> {0..t}. in_box (y \<tau>)\<close>
  proof (rule ccontr)
    (* Step 1: Set up the contradiction *)
    assume neg: \<open>\<not> (\<forall>\<tau> \<in> {0..t}. in_box (y \<tau>))\<close>
    then obtain \<tau>_bad where \<tau>_bad_in: \<open>\<tau>_bad \<in> {0..t}\<close> 
      and \<tau>_bad_out: \<open>\<not> in_box (y \<tau>_bad)\<close>
      by blast

(* Step 2: We define S as the set of times at which the trajectory 
       is outside the box, and show it is non-empty *)
    define S where \<open>S = {\<tau>. \<tau> \<in> {0..t} \<and> \<not> in_box (y \<tau>)}\<close>
    have S_nonempty: \<open>S \<noteq> {}\<close>
      using \<tau>_bad_in \<tau>_bad_out by (auto simp: S_def)
    have S_subset: \<open>S \<subseteq> {0..t}\<close>
      by (auto simp: S_def)
    have S_bdd: \<open>bdd_below S\<close>
      by (auto simp: S_def bdd_below_def)

(* Step 3: We define \<tau>_exit as the infimum of S *)
    define \<tau>_exit where \<open>\<tau>_exit = Inf S\<close>

    have \<tau>_exit_lb: \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau>_exit \<le> \<tau>\<close>
      unfolding \<tau>_exit_def 
      using S_bdd 
      by (auto intro: cInf_lower)

    have \<tau>_exit_in_interval: \<open>\<tau>_exit \<in> {0..t}\<close>
    proof -
      have \<open>0 \<le> \<tau>_exit\<close>
        unfolding \<tau>_exit_def 
        using S_bdd S_subset S_nonempty
        by (meson atLeastAtMost_iff cInf_greatest subsetD)
      moreover have \<open>\<tau>_exit \<le> t\<close>
        unfolding \<tau>_exit_def 
        using S_nonempty S_subset assms(1) atLeastAtMost_subset_contains_Inf 
        by presburger
      ultimately show ?thesis 
        by simp
    qed

(* Step 4: We show that y \<tau>_exit is in the closed box (via continuity) *)
    have y_\<tau>_exit_in_box: \<open>in_box (y \<tau>_exit)\<close>
    proof -
      have box_closed: \<open>closed {v :: (real, 'a) vec. in_box v}\<close>
      proof -
        have proj_cont: \<open>\<And>i. continuous_on UNIV (\<lambda>v::(real, 'a) vec. vec_nth v i)\<close>
          by (auto intro: continuous_on_component)
        have lo_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
            using closed_Collect_le[OF continuous_on_const[where c="lo i"] 
                proj_cont[of i]]
            by simp
        qed
        have hi_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
            using closed_Collect_le[OF proj_cont[of i] 
                continuous_on_const[where c="hi i"]]
            by simp
        qed
        have \<open>{v :: (real, 'a) vec. in_box v} = 
              (\<Inter>i\<in>UNIV. {v. lo i \<le> vec_nth v i} \<inter> {v. vec_nth v i \<le> hi i})\<close>
          unfolding in_box_def 
          by blast
        moreover have \<open>closed (\<Inter>i\<in>UNIV. {v :: (real, 'a) vec. lo i \<le> vec_nth v i} 
                                      \<inter> {v. vec_nth v i \<le> hi i})\<close>
          using lo_closed hi_closed 
          by (auto simp: closed_INT closed_Int)
        ultimately show ?thesis 
          by simp
      qed
      show ?thesis
      proof (cases \<open>\<tau>_exit = 0\<close>)
        case True
        have \<open>in_box (y 0)\<close>
          unfolding in_box_def 
          using iv 
          by blast
        thus ?thesis using True 
          by simp
      next
        case False
        with \<tau>_exit_in_interval 
        have \<tau>_exit_pos: \<open>0 < \<tau>_exit\<close>
          by simp

(* For any \<tau> \<in> [0, \<tau>_exit[, in_box (y \<tau>) holds *)
        have before_is_safe: \<open>\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> < \<tau>_exit \<Longrightarrow> in_box (y \<tau>)\<close>
        proof -
          fix \<tau> assume \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_lt: \<open>\<tau> < \<tau>_exit\<close>
          have \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
            using \<tau>_nn \<tau>_lt \<tau>_exit_in_interval 
            by auto
          have \<open>\<tau> \<notin> S\<close>
            using \<tau>_lt \<tau>_exit_lb 
            by force
          thus \<open>in_box (y \<tau>)\<close>
            using \<tau>_in 
            by (auto simp: S_def)
        qed

(* We define a sequence \<tau>_n \<rightarrow> \<tau>_exit from below, staying in [0, \<tau>_exit[ *)
        define \<tau>_seq where \<open>\<tau>_seq = (\<lambda>n::nat. \<tau>_exit - \<tau>_exit / (real n + 2))\<close>

        have \<tau>_seq_nn: \<open>\<And>n. 0 \<le> \<tau>_seq n\<close>
        proof -
          fix n
          have \<open>\<tau>_exit / (real n + 2) \<le> \<tau>_exit\<close>
            using \<tau>_exit_pos 
            by (simp add: field_simps)
          thus \<open>0 \<le> \<tau>_seq n\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_lt: \<open>\<And>n. \<tau>_seq n < \<tau>_exit\<close>
        proof -
          fix n
          have \<open>0 < \<tau>_exit / (real n + 2)\<close>
            using \<tau>_exit_pos 
            by simp
          thus \<open>\<tau>_seq n < \<tau>_exit\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_limit: \<open>\<tau>_seq \<longlonglongrightarrow> \<tau>_exit\<close>
        proof -
          have \<open>(\<lambda>n. \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> 0\<close>
          proof -
            have f1: "\<forall>r n. (\<lambda>na. r / real (na + n)) \<longlonglongrightarrow> 0"
              using LIMSEQ_ignore_initial_segment lim_const_over_n 
              by blast
            have "\<exists>r n. (\<lambda>na. r / real (na + n)) = (\<lambda>n. \<tau>_exit / (real n + real 2))"
              by (metis (full_types) Multiseries_Expansion.intyness_simps(1))
            then show ?thesis
              using f1 
              by (metis (no_types) Multiseries_Expansion.intyness_simps(6))
          qed
          hence \<open>(\<lambda>n. \<tau>_exit - \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> \<tau>_exit - 0\<close>
            by (rule tendsto_diff[OF tendsto_const])
          thus ?thesis
            unfolding \<tau>_seq_def 
            by simp
        qed

(* Each y (\<tau>_seq n) is in the box *)
        have y_seq_in_box: \<open>\<And>n. in_box (y (\<tau>_seq n))\<close>
          using before_is_safe \<tau>_seq_nn \<tau>_seq_lt 
          by blast

(* y is continuous, so y \<circ> \<tau>_seq \<longlonglongrightarrow> y \<tau>_exit *)
        have y_seq_limit: \<open>(\<lambda>n. y (\<tau>_seq n)) \<longlonglongrightarrow> y \<tau>_exit\<close>
        proof -
          have \<tau>_seq_in: \<open>\<And>n. \<tau>_seq n \<in> {0..t}\<close>
            using \<tau>_seq_nn \<tau>_seq_lt \<tau>_exit_in_interval
            by (meson atLeastAtMost_iff basic_trans_rules(22) order_less_le)
          have y_cont_at_\<tau>_exit: \<open>continuous (at \<tau>_exit within {0..t}) y\<close>
            using y_cont \<tau>_exit_in_interval 
            by (simp add: continuous_on_eq_continuous_within)
          show ?thesis
            using continuous_within_tendsto_compose'[where f = y]
              \<tau>_seq_limit \<tau>_seq_in \<tau>_exit_in_interval y_cont_at_\<tau>_exit
            by blast
        qed

(* Box is closed, so limit of in_box sequence is in_box *)
        show ?thesis
          using box_closed y_seq_in_box y_seq_limit
          by (metis closed_sequentially mem_Collect_eq)
      qed
    qed

    have \<tau>_exit_lt_t: \<open>\<tau>_exit < t\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<tau>_exit < t\<close>
      with \<tau>_exit_in_interval have \<tau>_exit_eq_t: \<open>\<tau>_exit = t\<close> by simp
          (* Every element of S is \<le> t and \<ge> \<tau>_exit = t, so S = {t} *)
      have \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau> = t\<close>
      proof -
        fix \<tau> assume \<tau>_in_S: \<open>\<tau> \<in> S\<close>
        hence \<open>\<tau> \<in> {0..t}\<close> 
          using S_subset 
          by blast
        moreover have \<open>\<tau>_exit \<le> \<tau>\<close> 
          using \<tau>_in_S \<tau>_exit_lb 
          by blast
        ultimately show \<open>\<tau> = t\<close> 
          using \<tau>_exit_eq_t 
          by simp
      qed
        (* So S = {t} and thus t \<in> S *)
      with S_nonempty 
      have t_in_S: \<open>t \<in> S\<close> 
        by blast
          (* But y \<tau>_exit = y t is in the box *)
      have \<open>in_box (y t)\<close> 
        using y_\<tau>_exit_in_box \<tau>_exit_eq_t 
        by simp
          (* Contradiction with t \<in> S *)
      thus False using t_in_S 
        by (simp add: S_def)
    qed
      (* Step 5: Case split on whether y \<tau>_exit is at an edge or strictly interior *)
    show False
    proof (cases \<open>\<exists>i. vec_nth (y \<tau>_exit) i = lo i \<or> vec_nth (y \<tau>_exit) i = hi i\<close>)
      case False  
        (* STRICT INTERIOR CASE: use continuity helper to derive contradiction *)
      note no_edge = False
      have strict_interior: \<open>\<And>i. lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
      proof -
        fix i
        from y_\<tau>_exit_in_box have 
          bounds: \<open>lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
          unfolding in_box_def 
          by blast
        from no_edge have neither: \<open>vec_nth (y \<tau>_exit) i \<noteq> lo i \<and> vec_nth (y \<tau>_exit) i \<noteq> hi i\<close>
          by blast
        from bounds neither show \<open>lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
          by auto
      qed

(* We apply the helper to get a neighborhood where y stays strictly interior *)
      obtain \<delta> where \<delta>_pos: \<open>0 < \<delta>\<close>
        and \<delta>_ball: \<open>\<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<longrightarrow> 
                              (\<forall>i. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
        using continuous_strictly_interior_neighborhood[OF y_cont \<tau>_exit_in_interval strict_interior]
        by blast

(* The neighborhood contains points strictly in the box *)
      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<Longrightarrow> in_box (y \<tau>)\<close>
      proof -
        fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close> and \<tau>_close: \<open>\<bar>\<tau> - \<tau>_exit\<bar> < \<delta>\<close>
        from \<delta>_ball \<tau>_in \<tau>_close have 
          \<open>\<forall>i. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i\<close>
          by blast
        thus \<open>in_box (y \<tau>)\<close>
          unfolding in_box_def
          by (simp add: dual_order.strict_iff_order)
      qed

(* an element of S in [\<tau>_exit, \<tau>_exit + \<delta>/2) *)
      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
        and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<delta>/2\<close>
          unfolding \<tau>_exit_def[symmetric] using \<delta>_pos by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis 
          using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb 
        by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset 
        by blast
      have \<tau>_s_close: \<open>\<bar>\<tau>_s - \<tau>_exit\<bar> < \<delta>\<close>
        using \<tau>_s_ge \<tau>_s_lt \<delta>_pos 
        by auto

      have \<open>in_box (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_in_t \<tau>_s_close 
        by blast
      moreover have \<open>\<not> in_box (y \<tau>_s)\<close>
        using \<tau>_s_in_S 
        by (simp add: S_def)
      ultimately show False 
        by blast
    next
      case True
      have lower_at: \<open>\<And>i. vec_nth (y \<tau>_exit) i = lo i \<Longrightarrow> 0 < vec_nth (f \<tau>_exit (y \<tau>_exit)) i\<close>
        using lower_edge_inward \<tau>_exit_in_interval y_\<tau>_exit_in_box
        unfolding in_box_def 
        by blast
      have upper_at: \<open>\<And>i. vec_nth (y \<tau>_exit) i = hi i \<Longrightarrow> vec_nth (f \<tau>_exit (y \<tau>_exit)) i < 0\<close>
        using upper_edge_inward \<tau>_exit_in_interval y_\<tau>_exit_in_box
        unfolding in_box_def 
        by blast
      have box_at: \<open>\<And>i. lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
        using y_\<tau>_exit_in_box 
        unfolding in_box_def 
        by blast

      obtain \<epsilon> where \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
        and \<epsilon>_prop: \<open>\<forall>\<tau>. \<tau>_exit < \<tau> \<and> \<tau> < \<tau>_exit + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                              (\<forall>i. lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        using solves_ode_inward_neighborhood[OF ODE \<tau>_exit_in_interval \<tau>_exit_lt_t 
            box_at lower_at upper_at]
        by blast

      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau>_exit < \<tau> \<Longrightarrow> \<tau> < \<tau>_exit + \<epsilon> \<Longrightarrow> \<tau> \<le> t \<Longrightarrow> in_box (y \<tau>)\<close>
        using \<epsilon>_prop 
        unfolding in_box_def 
        by blast

      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
        and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<epsilon>/2\<close>
          unfolding \<tau>_exit_def[symmetric] 
          using \<epsilon>_pos 
          by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis 
          using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb 
        by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset 
        by blast
      have \<tau>_s_ne: \<open>\<tau>_s \<noteq> \<tau>_exit\<close>
        using \<tau>_s_in_S y_\<tau>_exit_in_box 
        by (auto simp: S_def)
      have \<tau>_s_gt: \<open>\<tau>_exit < \<tau>_s\<close>
        using \<tau>_s_ge \<tau>_s_ne 
        by simp
      have \<tau>_s_lt_exit_\<epsilon>: \<open>\<tau>_s < \<tau>_exit + \<epsilon>\<close>
        using \<tau>_s_lt \<epsilon>_pos 
        by auto

      have \<open>in_box (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_gt \<tau>_s_lt_exit_\<epsilon> \<tau>_s_in_t 
        by simp
      moreover have \<open>\<not> in_box (y \<tau>_s)\<close>
        using \<tau>_s_in_S 
        by (simp add: S_def)
      ultimately show False by blast
    qed
  qed
  show \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using main_claim 
    unfolding in_box_def 
    by blast
qed

lemma continuous_strictly_interior_neighborhood_active:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes \<tau>_star t :: real
  fixes active :: \<open>'a set\<close>
  assumes y_cont: \<open>continuous_on {0..t} y\<close>
  assumes \<tau>_in: \<open>\<tau>_star \<in> {0..t}\<close>
  assumes strict: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < vec_nth (y \<tau>_star) i \<and> vec_nth (y \<tau>_star) i < hi i\<close>
  shows \<open>\<exists>\<delta> > 0. \<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_star\<bar> < \<delta> \<longrightarrow> 
                 (\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
proof -
  define open_box_active :: \<open>(real, 'a) vec set\<close> 
    where \<open>open_box_active = {v. \<forall>i \<in> active. lo i < vec_nth v i \<and> vec_nth v i < hi i}\<close>
  
  have open_box_active_open: \<open>open open_box_active\<close>
  proof -
    have proj_cont: \<open>\<And>i. continuous_on UNIV (\<lambda>v::(real, 'a) vec. vec_nth v i)\<close>
      by (auto intro: continuous_on_component)
    have lo_open: \<open>\<And>i. open {v :: (real, 'a) vec. lo i < vec_nth v i}\<close>
    proof -
      fix i
      show \<open>open {v :: (real, 'a) vec. lo i < vec_nth v i}\<close>
        using open_Collect_less[OF continuous_on_const[where c="lo i"] 
                                    proj_cont[of i]]
        by simp
    qed
    have hi_open: \<open>\<And>i. open {v :: (real, 'a) vec. vec_nth v i < hi i}\<close>
    proof -
      fix i
      show \<open>open {v :: (real, 'a) vec. vec_nth v i < hi i}\<close>
        using open_Collect_less[OF proj_cont[of i] 
                                    continuous_on_const[where c="hi i"]]
        by simp
    qed
    have \<open>open_box_active = (\<Inter>i\<in>active. {v. lo i < vec_nth v i} \<inter> {v. vec_nth v i < hi i})\<close>
      unfolding open_box_active_def by blast
    moreover have \<open>open (\<Inter>i\<in>active. {v :: (real, 'a) vec. lo i < vec_nth v i} 
                                   \<inter> {v. vec_nth v i < hi i})\<close>
      using lo_open hi_open 
        by (auto simp: open_INT open_Int)
    ultimately show ?thesis by simp
  qed

  have y_\<tau>_star_in: \<open>y \<tau>_star \<in> open_box_active\<close>
    using strict 
    unfolding open_box_active_def 
    by blast

  have preimage_open: \<open>openin (top_of_set {0..t}) (y -` open_box_active \<inter> {0..t})\<close>
    using y_cont open_box_active_open 
    by (metis Int_ac(3) continuous_openin_preimage_eq)

  have \<tau>_star_in_preimage: \<open>\<tau>_star \<in> y -` open_box_active \<inter> {0..t}\<close>
    using \<tau>_in y_\<tau>_star_in 
    by auto

  obtain \<delta> where \<delta>_pos: \<open>0 < \<delta>\<close> 
             and \<delta>_ball: \<open>ball \<tau>_star \<delta> \<inter> {0..t} \<subseteq> y -` open_box_active \<inter> {0..t}\<close>
    using preimage_open \<tau>_star_in_preimage
    by (metis openin_contains_ball)

  show ?thesis
  proof (rule exI[where x=\<delta>], intro conjI)
    show \<open>0 < \<delta>\<close> using \<delta>_pos .
  next
    show \<open>\<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_star\<bar> < \<delta> \<longrightarrow> 
          (\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
    proof (intro ballI impI ballI)
      fix \<tau> i
      assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
      assume \<tau>_close: \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>\<close>
      assume i_in: \<open>i \<in> active\<close>
      have \<open>\<tau> \<in> ball \<tau>_star \<delta>\<close>
        using \<tau>_close 
        by (simp add: dist_real_def)
      with \<tau>_in_t \<delta>_ball have \<open>\<tau> \<in> y -` open_box_active\<close>
        by blast
      hence \<open>y \<tau> \<in> open_box_active\<close> 
        by auto
      thus \<open>lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i\<close>
        using i_in unfolding open_box_active_def 
        by blast
    qed
  qed
qed

lemma solves_ode_inward_neighborhood_active:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes \<tau>_star t :: real
  fixes Q :: \<open>(real, 'a) vec set\<close>
  fixes active :: \<open>'a set\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes \<tau>_in: \<open>\<tau>_star \<in> {0..t}\<close>
  assumes \<tau>_lt_t: \<open>\<tau>_star < t\<close>
  assumes in_box_at: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i \<le> vec_nth (y \<tau>_star) i \<and> vec_nth (y \<tau>_star) i \<le> hi i\<close>
  assumes lower_edge_inward_at:
    \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_star) i = lo i \<Longrightarrow> 0 < vec_nth (f \<tau>_star (y \<tau>_star)) i\<close>
  assumes upper_edge_inward_at:
    \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_star) i = hi i \<Longrightarrow> vec_nth (f \<tau>_star (y \<tau>_star)) i < 0\<close>
  shows \<open>\<exists>\<epsilon> > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                    (\<forall>i \<in> active. lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
proof -
  have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) {0..t}\<close>
    using ODE 
    by (simp add: solves_ode_def)
  
  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast

  have per_coord: \<open>\<And>i. i \<in> active \<Longrightarrow> 
    \<exists>\<delta>_i > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i assume i_act: \<open>i \<in> active\<close>
    define \<phi> where \<open>\<phi> = (\<lambda>\<tau>. vec_nth (y \<tau>) i)\<close>
    define \<phi>'_val where \<open>\<phi>'_val = vec_nth (f \<tau>_star (y \<tau>_star)) i\<close>

    have \<phi>_cont: \<open>continuous_on {0..t} \<phi>\<close>
      unfolding \<phi>_def 
      using y_cont
      by (auto intro: continuous_on_compose2[OF continuous_on_component])

    have \<phi>_deriv: \<open>(\<phi> has_real_derivative \<phi>'_val) (at \<tau>_star within {0..t})\<close>
    proof -
      have y_at: \<open>(y has_vector_derivative f \<tau>_star (y \<tau>_star)) (at \<tau>_star within {0..t})\<close>
        using y_vderiv \<tau>_in 
        unfolding has_vderiv_on_def 
        by blast
      hence y_deriv: \<open>(y has_derivative (\<lambda>h. h *\<^sub>R f \<tau>_star (y \<tau>_star))) 
                      (at \<tau>_star within {0..t})\<close>
        unfolding has_vector_derivative_def 
        by blast
      have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>_star))\<close>
        by (rule has_derivative_vec_nth)
      have composed: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                       (\<lambda>h. vec_nth (h *\<^sub>R f \<tau>_star (y \<tau>_star)) i)) 
                      (at \<tau>_star within {0..t})\<close>
        using has_derivative_compose[OF y_deriv proj] 
        by simp
      have eq: \<open>(\<lambda>h. vec_nth (h *\<^sub>R f \<tau>_star (y \<tau>_star)) i) = (\<lambda>h. h * \<phi>'_val)\<close>
        unfolding \<phi>'_val_def 
        by auto
      show ?thesis
        unfolding \<phi>_def has_field_derivative_def
        using composed eq 
        by (simp add: mult_commute_abs)
    qed

    have lo_bound: \<open>lo i \<le> \<phi> \<tau>_star\<close> and hi_bound: \<open>\<phi> \<tau>_star \<le> hi i\<close>
      unfolding \<phi>_def 
      using in_box_at[OF i_act]
      by auto

    have \<phi>_cont_at: \<open>continuous (at \<tau>_star within {0..t}) \<phi>\<close>
      using \<phi>_cont \<tau>_in 
      by (simp add: continuous_on_eq_continuous_within)

    show \<open>\<exists>\<delta>_i > 0. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                        lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof (cases \<open>\<phi> \<tau>_star = lo i\<close>; cases \<open>\<phi> \<tau>_star = hi i\<close>)
      assume at_lo: \<open>\<phi> \<tau>_star = lo i\<close> and at_hi: \<open>\<phi> \<tau>_star = hi i\<close>
      have \<open>0 < \<phi>'_val\<close> 
        using lower_edge_inward_at[OF i_act] at_lo 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      moreover 
        have \<open>\<phi>'_val < 0\<close> 
        using upper_edge_inward_at[OF i_act] at_hi 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      ultimately have False by simp
      thus ?thesis by blast
    next
      assume at_lo: \<open>\<phi> \<tau>_star = lo i\<close> and not_hi: \<open>\<phi> \<tau>_star \<noteq> hi i\<close>
      have \<phi>'_pos: \<open>0 < \<phi>'_val\<close>
        using lower_edge_inward_at[OF i_act] at_lo 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>h. 0 < h \<Longrightarrow> \<tau>_star + h \<in> {0..t} \<Longrightarrow> h < d_lo \<Longrightarrow> 
                                        \<phi> \<tau>_star < \<phi> (\<tau>_star + h)\<close>
        using has_real_derivative_pos_inc_right[OF \<phi>_deriv \<phi>'_pos]
        by metis
      have \<phi>_lt_hi: \<open>\<phi> \<tau>_star < hi i\<close> using hi_bound not_hi by auto
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_hi \<Longrightarrow> \<phi> \<tau> < hi i\<close>
        using continuous_within_lt_neighborhood[OF \<phi>_cont_at \<phi>_lt_hi] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> 
        using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> using h \<tau>_in by auto
          have h_val: \<open>\<tau> - \<tau>_star > 0\<close> using h by auto
          have \<open>\<phi> \<tau>_star < \<phi> \<tau>\<close>
          proof -
            have \<open>\<tau>_star + (\<tau> - \<tau>_star) \<in> {0..t}\<close> 
              using \<tau>_in_t 
              by simp
            moreover 
              have \<open>\<tau> - \<tau>_star < d_lo\<close> 
                using h 
                unfolding \<delta>_i_def 
                by linarith
            ultimately show ?thesis using d_lo_prop[of \<open>\<tau> - \<tau>_star\<close>] h_val by simp
          qed
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close> 
            using at_lo 
            unfolding \<phi>_def 
            by simp
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < d_hi\<close> using h unfolding \<delta>_i_def by auto
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using d_hi_prop \<tau>_in_t 
            unfolding \<phi>_def 
            by fastforce
          from lo_ok hi_ok 
          show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    next
      assume not_lo: \<open>\<not> (\<phi> \<tau>_star = lo i)\<close> and at_hi: \<open>\<phi> \<tau>_star = hi i\<close>
      have \<phi>'_neg: \<open>\<phi>'_val < 0\<close>
        using upper_edge_inward_at[OF i_act] at_hi 
        unfolding \<phi>_def \<phi>'_val_def 
        by simp
      define \<psi> where \<open>\<psi> = (\<lambda>\<tau>. - \<phi> \<tau>)\<close>
      have \<psi>_deriv: \<open>(\<psi> has_real_derivative (- \<phi>'_val)) (at \<tau>_star within {0..t})\<close>
        unfolding \<psi>_def 
        using \<phi>_deriv Deriv.field_differentiable_minus 
        by blast
      have neg_pos: \<open>0 < - \<phi>'_val\<close> using \<phi>'_neg by simp
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>h. 0 < h \<Longrightarrow> \<tau>_star + h \<in> {0..t} \<Longrightarrow> h < d_hi \<Longrightarrow> 
                                        \<psi> \<tau>_star < \<psi> (\<tau>_star + h)\<close>
        using has_real_derivative_pos_inc_right[OF \<psi>_deriv neg_pos]
        by metis
      have \<phi>_gt_lo: \<open>lo i < \<phi> \<tau>_star\<close> using lo_bound not_lo by auto
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_lo \<Longrightarrow> lo i < \<phi> \<tau>\<close>
        using continuous_within_gt_neighborhood[OF \<phi>_cont_at \<phi>_gt_lo] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
            using h \<tau>_in 
            by auto
          have h_val: \<open>\<tau> - \<tau>_star > 0\<close> 
            using h 
            by auto
          have \<open>\<psi> \<tau>_star < \<psi> (\<tau>_star + (\<tau> - \<tau>_star))\<close>
          proof -
            have \<open>\<tau>_star + (\<tau> - \<tau>_star) \<in> {0..t}\<close> 
              using \<tau>_in_t 
              by simp
            moreover have \<open>\<tau> - \<tau>_star < d_hi\<close> using h unfolding \<delta>_i_def by linarith
            ultimately show ?thesis using d_hi_prop[of \<open>\<tau> - \<tau>_star\<close>] h_val by simp
          qed
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using at_hi 
            unfolding \<psi>_def \<phi>_def 
            by simp
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < d_lo\<close> 
            using h 
            unfolding \<delta>_i_def 
            by auto
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close>
            using d_lo_prop \<tau>_in_t 
            unfolding \<phi>_def 
            by fastforce
          from lo_ok hi_ok 
          show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    next
      assume not_lo: \<open>\<not> (\<phi> \<tau>_star = lo i)\<close> and not_hi: \<open>\<not> (\<phi> \<tau>_star = hi i)\<close>
      have \<phi>_gt_lo: \<open>lo i < \<phi> \<tau>_star\<close> using lo_bound not_lo by auto
      have \<phi>_lt_hi: \<open>\<phi> \<tau>_star < hi i\<close> using hi_bound not_hi by auto
      obtain d_lo where d_lo_pos: \<open>0 < d_lo\<close>
                    and d_lo_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_lo \<Longrightarrow> lo i < \<phi> \<tau>\<close>
        using continuous_within_gt_neighborhood[OF \<phi>_cont_at \<phi>_gt_lo] 
        by blast
      obtain d_hi where d_hi_pos: \<open>0 < d_hi\<close>
                    and d_hi_prop: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_star\<bar> < d_hi \<Longrightarrow> \<phi> \<tau> < hi i\<close>
        using continuous_within_lt_neighborhood[OF \<phi>_cont_at \<phi>_lt_hi] 
        by blast
      define \<delta>_i where \<open>\<delta>_i = min d_lo d_hi\<close>
      have \<delta>_i_pos: \<open>0 < \<delta>_i\<close> 
        using d_lo_pos d_hi_pos 
        unfolding \<delta>_i_def 
        by simp
      show ?thesis
      proof (intro exI[where x=\<delta>_i] conjI)
        show \<open>0 < \<delta>_i\<close> using \<delta>_i_pos .
      next
        show \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
                  lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        proof (intro allI impI)
          fix \<tau> assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t\<close>
          have \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> using h \<tau>_in by auto
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>_i\<close> using h by auto
          hence lo_ok: \<open>lo i \<le> vec_nth (y \<tau>) i\<close>
            using d_lo_prop \<tau>_in_t 
            unfolding \<phi>_def \<delta>_i_def 
            by fastforce
          have \<open>\<bar>\<tau> - \<tau>_star\<bar> < \<delta>_i\<close> 
            using h 
            by auto
          hence hi_ok: \<open>vec_nth (y \<tau>) i \<le> hi i\<close>
            using d_hi_prop \<tau>_in_t 
            unfolding \<phi>_def \<delta>_i_def 
            by fastforce
          from lo_ok hi_ok 
          show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close> 
            by blast
        qed
      qed
    qed
  qed

  have ex_global: \<open>\<exists>\<epsilon> > 0. \<forall>i \<in> active. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                                           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    define \<delta>_fun where \<open>\<delta>_fun = (\<lambda>i. SOME \<delta>_i. 0 < \<delta>_i \<and> 
        (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i))\<close>
    have \<delta>_fun_spec: \<open>\<And>i. i \<in> active \<Longrightarrow> 0 < \<delta>_fun i \<and> 
        (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_fun i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
    proof -
      fix i assume i_act: \<open>i \<in> active\<close>
      from per_coord[OF i_act] obtain \<delta>_i where 
        \<open>0 < \<delta>_i\<close> and
        \<open>\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
             lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
        by blast
      from per_coord[OF i_act] have ex_i:
        \<open>\<exists>\<delta>_i. 0 < \<delta>_i \<and> 
          (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_i \<and> \<tau> \<le> t \<longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        by blast
      show \<open>0 < \<delta>_fun i \<and> 
            (\<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<delta>_fun i \<and> \<tau> \<le> t \<longrightarrow> 
                 lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        unfolding \<delta>_fun_def
        by (rule someI_ex[OF ex_i])
    qed
    (* Take the minimum over all coordinates (even inactive), with 1 as a safety *)
    define \<epsilon> where \<open>\<epsilon> = Min (insert 1 (\<delta>_fun ` active))\<close>
    have \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
    proof -
      have \<open>0 < (1::real)\<close> by simp
      moreover have \<open>\<And>x. x \<in> \<delta>_fun ` active \<Longrightarrow> 0 < x\<close>
        using \<delta>_fun_spec 
        by auto
      ultimately show ?thesis
        unfolding \<epsilon>_def 
        by simp
    qed
    have \<epsilon>_le: \<open>\<And>i. i \<in> active \<Longrightarrow> \<epsilon> \<le> \<delta>_fun i\<close>
      unfolding \<epsilon>_def 
      by simp
   show ?thesis
    proof (rule exI[where x=\<epsilon>], intro conjI)
      show \<open>0 < \<epsilon>\<close> using \<epsilon>_pos .
    next
      show \<open>\<forall>i \<in> active. \<forall>\<tau>. \<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                              lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      proof (intro ballI allI impI)
        fix i \<tau>
        assume i_act: \<open>i \<in> active\<close>
        assume h: \<open>\<tau>_star < \<tau> \<and> \<tau> < \<tau>_star + \<epsilon> \<and> \<tau> \<le> t\<close>
        have \<open>\<tau> < \<tau>_star + \<delta>_fun i\<close> using h \<epsilon>_le[OF i_act] by auto
        with h \<delta>_fun_spec[OF i_act]
        show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
          by blast
      qed
    qed
  qed
  show ?thesis
    using ex_global 
    by blast
qed

lemma DI_Frame_Rule_partial:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes t :: real
  fixes active :: \<open>'a set\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  assumes active_ordered: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  assumes lower_edge_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (f \<tau> v) i\<close>
  assumes upper_edge_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (f \<tau> v) i < 0\<close>
  assumes inactive_maintained:
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  shows \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
proof -
  (* Active-restricted in_box predicate *)
  define in_box_active :: \<open>(real, 'a) vec \<Rightarrow> bool\<close> 
    where \<open>in_box_active = (\<lambda>v. \<forall>i \<in> active. lo i \<le> vec_nth v i \<and> vec_nth v i \<le> hi i)\<close>

  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast

  have active_main: \<open>\<forall>\<tau> \<in> {0..t}. in_box_active (y \<tau>)\<close>
  proof (rule ccontr)
    assume neg: \<open>\<not> (\<forall>\<tau> \<in> {0..t}. in_box_active (y \<tau>))\<close>
    then obtain \<tau>_bad where \<tau>_bad_in: \<open>\<tau>_bad \<in> {0..t}\<close> 
                         and \<tau>_bad_out: \<open>\<not> in_box_active (y \<tau>_bad)\<close>
      by blast

    define S where \<open>S = {\<tau>. \<tau> \<in> {0..t} \<and> \<not> in_box_active (y \<tau>)}\<close>
    have S_nonempty: \<open>S \<noteq> {}\<close>
      using \<tau>_bad_in \<tau>_bad_out 
      by (auto simp: S_def)
    have S_subset: \<open>S \<subseteq> {0..t}\<close>
      by (auto simp: S_def)
    have S_bdd: \<open>bdd_below S\<close>
      by (auto simp: S_def bdd_below_def)

    define \<tau>_exit where \<open>\<tau>_exit = Inf S\<close>

    have \<tau>_exit_lb: \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau>_exit \<le> \<tau>\<close>
      unfolding \<tau>_exit_def 
      using S_bdd 
      by (auto intro: cInf_lower)

    have \<tau>_exit_in_interval: \<open>\<tau>_exit \<in> {0..t}\<close>
    proof -
      have \<open>0 \<le> \<tau>_exit\<close>
        unfolding \<tau>_exit_def 
        using S_bdd S_subset S_nonempty
        by (meson atLeastAtMost_iff cInf_greatest subsetD)
      moreover have \<open>\<tau>_exit \<le> t\<close>
        unfolding \<tau>_exit_def 
        using S_nonempty S_subset t_nn atLeastAtMost_subset_contains_Inf 
        by presburger
      ultimately 
      show ?thesis 
        by simp
    qed

    (* y \<tau>_exit satisfies active-restricted bounds (by continuity) *)
    have y_\<tau>_exit_in_box: \<open>in_box_active (y \<tau>_exit)\<close>
    proof -
      have box_closed: \<open>closed {v :: (real, 'a) vec. in_box_active v}\<close>
      proof -
        have proj_cont: \<open>\<And>i. continuous_on UNIV (\<lambda>v::(real, 'a) vec. vec_nth v i)\<close>
          by (auto intro: continuous_on_component)
        have lo_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
            using closed_Collect_le[OF continuous_on_const[where c="lo i"] 
                                        proj_cont[of i]]
            by simp
        qed
        have hi_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
            using closed_Collect_le[OF proj_cont[of i] 
                                        continuous_on_const[where c="hi i"]]
            by simp
        qed
        have \<open>{v :: (real, 'a) vec. in_box_active v} = 
              (\<Inter>i\<in>active. {v. lo i \<le> vec_nth v i} \<inter> {v. vec_nth v i \<le> hi i})\<close>
          unfolding in_box_active_def 
          by blast
        moreover have \<open>closed (\<Inter>i\<in>active. {v :: (real, 'a) vec. lo i \<le> vec_nth v i} 
                                        \<inter> {v. vec_nth v i \<le> hi i})\<close>
          using lo_closed hi_closed 
          by (auto simp: closed_INT closed_Int)
        ultimately 
        show ?thesis 
          by simp
      qed
      show ?thesis
      proof (cases \<open>\<tau>_exit = 0\<close>)
        case True
        have \<open>in_box_active (y 0)\<close>
          unfolding in_box_active_def 
          using iv 
          by blast
        thus ?thesis 
          using True 
          by simp
      next
        case False
        with \<tau>_exit_in_interval have \<tau>_exit_pos: \<open>0 < \<tau>_exit\<close>
          by simp

        have before_is_safe: \<open>\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> < \<tau>_exit \<Longrightarrow> in_box_active (y \<tau>)\<close>
        proof -
          fix \<tau> assume \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_lt: \<open>\<tau> < \<tau>_exit\<close>
          have \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
            using \<tau>_nn \<tau>_lt \<tau>_exit_in_interval 
            by auto
          have \<open>\<tau> \<notin> S\<close>
            using \<tau>_lt \<tau>_exit_lb 
            by force
          thus \<open>in_box_active (y \<tau>)\<close>
            using \<tau>_in 
            by (auto simp: S_def)
        qed

        define \<tau>_seq where \<open>\<tau>_seq = (\<lambda>n::nat. \<tau>_exit - \<tau>_exit / (real n + 2))\<close>

        have \<tau>_seq_nn: \<open>\<And>n. 0 \<le> \<tau>_seq n\<close>
        proof -
          fix n
          have \<open>\<tau>_exit / (real n + 2) \<le> \<tau>_exit\<close>
            using \<tau>_exit_pos 
            by (simp add: field_simps)
          thus \<open>0 \<le> \<tau>_seq n\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_lt: \<open>\<And>n. \<tau>_seq n < \<tau>_exit\<close>
        proof -
          fix n
          have \<open>0 < \<tau>_exit / (real n + 2)\<close>
            using \<tau>_exit_pos 
            by simp
          thus \<open>\<tau>_seq n < \<tau>_exit\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_limit: \<open>\<tau>_seq \<longlonglongrightarrow> \<tau>_exit\<close>
        proof -
          have \<open>(\<lambda>n. \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> 0\<close>
          proof -
            have f1: "\<forall>r n. (\<lambda>na. r / real (na + n)) \<longlonglongrightarrow> 0"
              using LIMSEQ_ignore_initial_segment lim_const_over_n 
              by blast
            have "\<exists>r n. (\<lambda>na. r / real (na + n)) = (\<lambda>n. \<tau>_exit / (real n + real 2))"
              by (metis (full_types) Multiseries_Expansion.intyness_simps(1))
            then show ?thesis
              using f1 
              by (metis (no_types) Multiseries_Expansion.intyness_simps(6))
          qed
          hence \<open>(\<lambda>n. \<tau>_exit - \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> \<tau>_exit - 0\<close>
            by (rule tendsto_diff[OF tendsto_const])
          thus ?thesis
            unfolding \<tau>_seq_def 
            by simp
        qed

        have y_seq_in_box: \<open>\<And>n. in_box_active (y (\<tau>_seq n))\<close>
          using before_is_safe \<tau>_seq_nn \<tau>_seq_lt 
          by blast

        have y_seq_limit: \<open>(\<lambda>n. y (\<tau>_seq n)) \<longlonglongrightarrow> y \<tau>_exit\<close>
        proof -
          have \<tau>_seq_in: \<open>\<And>n. \<tau>_seq n \<in> {0..t}\<close>
            using \<tau>_seq_nn \<tau>_seq_lt \<tau>_exit_in_interval
            by (meson atLeastAtMost_iff basic_trans_rules(22) order_less_le)
          have y_cont_at_\<tau>_exit: \<open>continuous (at \<tau>_exit within {0..t}) y\<close>
            using y_cont \<tau>_exit_in_interval 
            by (simp add: continuous_on_eq_continuous_within)
          show ?thesis
            using continuous_within_tendsto_compose'[where f = y]
                  \<tau>_seq_limit \<tau>_seq_in \<tau>_exit_in_interval y_cont_at_\<tau>_exit
            by blast
        qed

        show ?thesis
          using box_closed y_seq_in_box y_seq_limit
          by (metis closed_sequentially mem_Collect_eq)
      qed
    qed

    have \<tau>_exit_lt_t: \<open>\<tau>_exit < t\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<tau>_exit < t\<close>
      with \<tau>_exit_in_interval have \<tau>_exit_eq_t: \<open>\<tau>_exit = t\<close> 
        by simp
      have \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau> = t\<close>
      proof -
        fix \<tau> assume \<tau>_in_S: \<open>\<tau> \<in> S\<close>
        hence \<open>\<tau> \<in> {0..t}\<close> 
          using S_subset 
          by blast
        moreover have \<open>\<tau>_exit \<le> \<tau>\<close> 
          using \<tau>_in_S \<tau>_exit_lb 
          by blast
        ultimately show \<open>\<tau> = t\<close> 
          using \<tau>_exit_eq_t 
          by simp
      qed
      with S_nonempty have t_in_S: \<open>t \<in> S\<close> 
        by blast
      have \<open>in_box_active (y t)\<close> 
        using y_\<tau>_exit_in_box \<tau>_exit_eq_t 
        by simp
      thus False 
        using t_in_S 
        by (simp add: S_def)
    qed

    (* Case split on whether y \<tau>_exit has an active coordinate at an edge *)
    show False
    proof (cases \<open>\<exists>i \<in> active. vec_nth (y \<tau>_exit) i = lo i \<or> vec_nth (y \<tau>_exit) i = hi i\<close>)
      case False
      (* STRICT INTERIOR CASE (over active coords): use continuity helper *)
      note no_edge = False
      have strict_interior: 
        \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close>
        from y_\<tau>_exit_in_box i_act 
        have bounds: \<open>lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
          unfolding in_box_active_def 
          by blast
        from no_edge i_act have neither: 
          \<open>vec_nth (y \<tau>_exit) i \<noteq> lo i \<and> vec_nth (y \<tau>_exit) i \<noteq> hi i\<close>
          by blast
        from bounds neither show \<open>lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
          by auto
      qed

      obtain \<delta> where \<delta>_pos: \<open>0 < \<delta>\<close>
                 and \<delta>_ball: \<open>\<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<longrightarrow> 
                              (\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
        using continuous_strictly_interior_neighborhood_active[OF y_cont \<tau>_exit_in_interval 
                                                                  strict_interior]
        by blast

      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<Longrightarrow> in_box_active (y \<tau>)\<close>
      proof -
        fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close> and \<tau>_close: \<open>\<bar>\<tau> - \<tau>_exit\<bar> < \<delta>\<close>
        from \<delta>_ball \<tau>_in \<tau>_close have 
          \<open>\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i\<close>
          by blast
        thus \<open>in_box_active (y \<tau>)\<close>
          unfolding in_box_active_def
          by (simp add: dual_order.strict_iff_order)
      qed

      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
                   and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<delta>/2\<close>
          unfolding \<tau>_exit_def[symmetric] using \<delta>_pos by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb 
        by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset 
        by blast
      have \<tau>_s_close: \<open>\<bar>\<tau>_s - \<tau>_exit\<bar> < \<delta>\<close>
        using \<tau>_s_ge \<tau>_s_lt \<delta>_pos 
        by auto

      have \<open>in_box_active (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_in_t \<tau>_s_close by blast
      moreover have \<open>\<not> in_box_active (y \<tau>_s)\<close>
        using \<tau>_s_in_S 
        by (simp add: S_def)
      ultimately show False 
        by blast
    next
      case True
      have lower_at: \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_exit) i = lo i \<Longrightarrow> 
                              0 < vec_nth (f \<tau>_exit (y \<tau>_exit)) i\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close> and eq_lo: \<open>vec_nth (y \<tau>_exit) i = lo i\<close>
        have all_coords: \<open>\<And>j. lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
        proof -
          fix j
          show \<open>lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
          proof (cases \<open>j \<in> active\<close>)
            case True
            thus ?thesis 
              using y_\<tau>_exit_in_box 
              unfolding in_box_active_def 
              by blast
          next
            case False
            thus ?thesis 
              using inactive_maintained[OF _ \<tau>_exit_in_interval] 
              by blast
          qed
        qed
        show \<open>0 < vec_nth (f \<tau>_exit (y \<tau>_exit)) i\<close>
          using lower_edge_inward[OF i_act \<tau>_exit_in_interval all_coords eq_lo] .
      qed
      have upper_at: \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_exit) i = hi i \<Longrightarrow> 
                              vec_nth (f \<tau>_exit (y \<tau>_exit)) i < 0\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close> and eq_hi: \<open>vec_nth (y \<tau>_exit) i = hi i\<close>
        have all_coords: \<open>\<And>j. lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
        proof -
          fix j
          show \<open>lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
          proof (cases \<open>j \<in> active\<close>)
            case True
            thus ?thesis 
              using y_\<tau>_exit_in_box 
              unfolding in_box_active_def 
              by blast
          next
            case False
            thus ?thesis 
              using inactive_maintained[OF _ \<tau>_exit_in_interval] 
              by blast
          qed
        qed
        show \<open>vec_nth (f \<tau>_exit (y \<tau>_exit)) i < 0\<close>
          using upper_edge_inward[OF i_act \<tau>_exit_in_interval all_coords eq_hi] .
      qed
      have box_at: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
        using y_\<tau>_exit_in_box 
        unfolding in_box_active_def 
        by blast

      obtain \<epsilon> where \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
                 and \<epsilon>_prop: \<open>\<forall>\<tau>. \<tau>_exit < \<tau> \<and> \<tau> < \<tau>_exit + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                              (\<forall>i \<in> active. lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        using solves_ode_inward_neighborhood_active[OF ODE \<tau>_exit_in_interval \<tau>_exit_lt_t 
                                                       box_at lower_at upper_at]
        by blast

      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau>_exit < \<tau> \<Longrightarrow> \<tau> < \<tau>_exit + \<epsilon> \<Longrightarrow> \<tau> \<le> t \<Longrightarrow> in_box_active (y \<tau>)\<close>
        using \<epsilon>_prop 
        unfolding in_box_active_def 
        by blast

      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
                   and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<epsilon>/2\<close>
          unfolding \<tau>_exit_def[symmetric] 
          using \<epsilon>_pos 
          by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis 
          using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset by blast
      have \<tau>_s_ne: \<open>\<tau>_s \<noteq> \<tau>_exit\<close>
        using \<tau>_s_in_S y_\<tau>_exit_in_box by (auto simp: S_def)
      have \<tau>_s_gt: \<open>\<tau>_exit < \<tau>_s\<close>
        using \<tau>_s_ge \<tau>_s_ne by simp
      have \<tau>_s_lt_exit_\<epsilon>: \<open>\<tau>_s < \<tau>_exit + \<epsilon>\<close>
        using \<tau>_s_lt \<epsilon>_pos by auto

      have \<open>in_box_active (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_gt \<tau>_s_lt_exit_\<epsilon> \<tau>_s_in_t 
        by simp
      moreover have \<open>\<not> in_box_active (y \<tau>_s)\<close>
        using \<tau>_s_in_S by (simp add: S_def)
      ultimately show False by blast
    qed
  qed

  (* Combine active_main with inactive_maintained *)
  show \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
               lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix \<tau> i
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof (cases \<open>i \<in> active\<close>)
      case True
      thus ?thesis 
        using active_main \<tau>_in 
        unfolding in_box_active_def 
        by blast
    next
      case False
      thus ?thesis 
        using inactive_maintained \<tau>_in 
        by blast
    qed
  qed
qed

text \<open>
   DOMAIN-AWARE MODULARITY RULE - DI\_Frame\_Rule\_partial\_dom.

   This is the evolution-domain-aware ("dL-faithful") version of the axis
   aligned bounded box modularity rule DI\_Frame\_Rule\_partial.
   Unlike the DI\_Vect\_dom-style siblings, this one does NOT reduce to its canonical counterpart:
   the per-component bound conditions quantify over arbitrary states v, and
   gating them by `v in Q` WEAKENS the hypothesis (a strictly stronger
   lemma).  So this is a from-scratch proof, a faithful copy of the
   DI\_Frame\_Rule\_partial first-hit-time reasoning, with the single
   addition that at the exit time the trajectory point is known to lie in
   the evolution domain Q, which discharges the now-gated bound condition.

   Differences from DI\_Frame\_Rule\_partial (all marked `CHANGE N` below):
     1,2. The lower/upper bound conditions gain a hypothesis `v in Q`.
\begin{enumerate}
\item The conclusion gains the conjunct `y tau in Q`.
\item `y\_in\_Q` is extracted from the ODE near the top.
\item The two bound-condition applications (at the exit time) supply
  `y tau\_exit in Q`.
\item The final assembly attaches `y tau in Q`.
\end{enumerate}
   `inactive\_maintained` stays unconstrained: it is the dynamical-frame condition
   on the trajectory, not a Lie-derivative check, so Q does not gate it.
\<close>
lemma DI_Frame_Rule_partial_dom:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  fixes lo hi :: \<open>'a \<Rightarrow> real\<close>
  fixes t :: real
  fixes active :: \<open>'a set\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes ODE: \<open>(y solves_ode f) {0..t} Q\<close>
  assumes iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  assumes active_ordered: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  assumes lower_edge_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> v \<in> Q \<Longrightarrow>
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
             vec_nth v i = lo i \<Longrightarrow>
             0 < vec_nth (f \<tau> v) i\<close>
  assumes upper_edge_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> v \<in> Q \<Longrightarrow>
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
             vec_nth v i = hi i \<Longrightarrow>
             vec_nth (f \<tau> v) i < 0\<close>
  assumes inactive_maintained:
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  shows \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow>
               y \<tau> \<in> Q \<and> lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
proof -
  (* Active-restricted in_box predicate *)
  define in_box_active :: \<open>(real, 'a) vec \<Rightarrow> bool\<close> 
    where \<open>in_box_active = (\<lambda>v. \<forall>i \<in> active. lo i \<le> vec_nth v i \<and> vec_nth v i \<le> hi i)\<close>

  have y_cont: \<open>continuous_on {0..t} y\<close>
    using ODE solves_ode_continuous_on 
    by blast

 have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> y \<tau> \<in> Q\<close>
   using ODE 
   by (auto simp add: solves_ode_def Pi_iff)

  have active_main: \<open>\<forall>\<tau> \<in> {0..t}. in_box_active (y \<tau>)\<close>
  proof (rule ccontr)
    assume neg: \<open>\<not> (\<forall>\<tau> \<in> {0..t}. in_box_active (y \<tau>))\<close>
    then obtain \<tau>_bad where \<tau>_bad_in: \<open>\<tau>_bad \<in> {0..t}\<close> 
                         and \<tau>_bad_out: \<open>\<not> in_box_active (y \<tau>_bad)\<close>
      by blast

    define S where \<open>S = {\<tau>. \<tau> \<in> {0..t} \<and> \<not> in_box_active (y \<tau>)}\<close>
    have S_nonempty: \<open>S \<noteq> {}\<close>
      using \<tau>_bad_in \<tau>_bad_out 
      by (auto simp: S_def)
    have S_subset: \<open>S \<subseteq> {0..t}\<close>
      by (auto simp: S_def)
    have S_bdd: \<open>bdd_below S\<close>
      by (auto simp: S_def bdd_below_def)

    define \<tau>_exit where \<open>\<tau>_exit = Inf S\<close>

    have \<tau>_exit_lb: \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau>_exit \<le> \<tau>\<close>
      unfolding \<tau>_exit_def 
      using S_bdd 
      by (auto intro: cInf_lower)

    have \<tau>_exit_in_interval: \<open>\<tau>_exit \<in> {0..t}\<close>
    proof -
      have \<open>0 \<le> \<tau>_exit\<close>
        unfolding \<tau>_exit_def 
        using S_bdd S_subset S_nonempty
        by (meson atLeastAtMost_iff cInf_greatest subsetD)
      moreover have \<open>\<tau>_exit \<le> t\<close>
        unfolding \<tau>_exit_def 
        using S_nonempty S_subset t_nn atLeastAtMost_subset_contains_Inf 
        by presburger
      ultimately 
      show ?thesis 
        by simp
    qed

    have y_\<tau>_exit_in_box: \<open>in_box_active (y \<tau>_exit)\<close>
    proof -
      have box_closed: \<open>closed {v :: (real, 'a) vec. in_box_active v}\<close>
      proof -
        have proj_cont: \<open>\<And>i. continuous_on UNIV (\<lambda>v::(real, 'a) vec. vec_nth v i)\<close>
          by (auto intro: continuous_on_component)
        have lo_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. lo i \<le> vec_nth v i}\<close>
            using closed_Collect_le[OF continuous_on_const[where c="lo i"] 
                                        proj_cont[of i]]
            by simp
        qed
        have hi_closed: \<open>\<And>i. closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
        proof -
          fix i
          show \<open>closed {v :: (real, 'a) vec. vec_nth v i \<le> hi i}\<close>
            using closed_Collect_le[OF proj_cont[of i] 
                                        continuous_on_const[where c="hi i"]]
            by simp
        qed
        have \<open>{v :: (real, 'a) vec. in_box_active v} = 
              (\<Inter>i\<in>active. {v. lo i \<le> vec_nth v i} \<inter> {v. vec_nth v i \<le> hi i})\<close>
          unfolding in_box_active_def 
          by blast
        moreover 
        have \<open>closed (\<Inter>i\<in>active. {v :: (real, 'a) vec. lo i \<le> vec_nth v i} 
                                        \<inter> {v. vec_nth v i \<le> hi i})\<close>
          using lo_closed hi_closed 
          by (auto simp: closed_INT closed_Int)
        ultimately 
        show ?thesis 
          by simp
      qed
      show ?thesis
      proof (cases \<open>\<tau>_exit = 0\<close>)
        case True
        have \<open>in_box_active (y 0)\<close>
          unfolding in_box_active_def 
          using iv 
          by blast
        thus ?thesis 
          using True 
          by simp
      next
        case False
        with \<tau>_exit_in_interval 
        have \<tau>_exit_pos: \<open>0 < \<tau>_exit\<close>
          by simp

        have before_is_safe: \<open>\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> < \<tau>_exit \<Longrightarrow> in_box_active (y \<tau>)\<close>
        proof -
          fix \<tau> assume \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_lt: \<open>\<tau> < \<tau>_exit\<close>
          have \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
            using \<tau>_nn \<tau>_lt \<tau>_exit_in_interval 
            by auto
          have \<open>\<tau> \<notin> S\<close>
            using \<tau>_lt \<tau>_exit_lb 
            by force
          thus \<open>in_box_active (y \<tau>)\<close>
            using \<tau>_in 
            by (auto simp: S_def)
        qed

        define \<tau>_seq where \<open>\<tau>_seq = (\<lambda>n::nat. \<tau>_exit - \<tau>_exit / (real n + 2))\<close>

        have \<tau>_seq_nn: \<open>\<And>n. 0 \<le> \<tau>_seq n\<close>
        proof -
          fix n
          have \<open>\<tau>_exit / (real n + 2) \<le> \<tau>_exit\<close>
            using \<tau>_exit_pos 
            by (simp add: field_simps)
          thus \<open>0 \<le> \<tau>_seq n\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_lt: \<open>\<And>n. \<tau>_seq n < \<tau>_exit\<close>
        proof -
          fix n
          have \<open>0 < \<tau>_exit / (real n + 2)\<close>
            using \<tau>_exit_pos 
            by simp
          thus \<open>\<tau>_seq n < \<tau>_exit\<close>
            unfolding \<tau>_seq_def 
            by simp
        qed

        have \<tau>_seq_limit: \<open>\<tau>_seq \<longlonglongrightarrow> \<tau>_exit\<close>
        proof -
          have \<open>(\<lambda>n. \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> 0\<close>
          proof -
            have f1: "\<forall>r n. (\<lambda>na. r / real (na + n)) \<longlonglongrightarrow> 0"
              using LIMSEQ_ignore_initial_segment lim_const_over_n 
              by blast
            have "\<exists>r n. (\<lambda>na. r / real (na + n)) = (\<lambda>n. \<tau>_exit / (real n + real 2))"
              by (metis (full_types) Multiseries_Expansion.intyness_simps(1))
            then show ?thesis
              using f1 
              by (metis (no_types) Multiseries_Expansion.intyness_simps(6))
          qed
          hence \<open>(\<lambda>n. \<tau>_exit - \<tau>_exit / (real n + 2)) \<longlonglongrightarrow> \<tau>_exit - 0\<close>
            by (rule tendsto_diff[OF tendsto_const])
          thus ?thesis
            unfolding \<tau>_seq_def 
            by simp
        qed

        have y_seq_in_box: \<open>\<And>n. in_box_active (y (\<tau>_seq n))\<close>
          using before_is_safe \<tau>_seq_nn \<tau>_seq_lt 
          by blast

        have y_seq_limit: \<open>(\<lambda>n. y (\<tau>_seq n)) \<longlonglongrightarrow> y \<tau>_exit\<close>
        proof -
          have \<tau>_seq_in: \<open>\<And>n. \<tau>_seq n \<in> {0..t}\<close>
            using \<tau>_seq_nn \<tau>_seq_lt \<tau>_exit_in_interval
            by (meson atLeastAtMost_iff basic_trans_rules(22) order_less_le)
          have y_cont_at_\<tau>_exit: \<open>continuous (at \<tau>_exit within {0..t}) y\<close>
            using y_cont \<tau>_exit_in_interval 
            by (simp add: continuous_on_eq_continuous_within)
          show ?thesis
            using continuous_within_tendsto_compose'[where f = y]
                  \<tau>_seq_limit \<tau>_seq_in \<tau>_exit_in_interval y_cont_at_\<tau>_exit
            by blast
        qed
        show ?thesis
          using box_closed y_seq_in_box y_seq_limit
          by (metis closed_sequentially mem_Collect_eq)
      qed
    qed

    have \<tau>_exit_lt_t: \<open>\<tau>_exit < t\<close>
    proof (rule ccontr)
      assume \<open>\<not> \<tau>_exit < t\<close>
      with \<tau>_exit_in_interval have \<tau>_exit_eq_t: \<open>\<tau>_exit = t\<close> by simp
      have \<open>\<And>\<tau>. \<tau> \<in> S \<Longrightarrow> \<tau> = t\<close>
      proof -
        fix \<tau> assume \<tau>_in_S: \<open>\<tau> \<in> S\<close>
        hence \<open>\<tau> \<in> {0..t}\<close> using S_subset by blast
        moreover have \<open>\<tau>_exit \<le> \<tau>\<close> using \<tau>_in_S \<tau>_exit_lb by blast
        ultimately show \<open>\<tau> = t\<close> using \<tau>_exit_eq_t by simp
      qed
      with S_nonempty have t_in_S: \<open>t \<in> S\<close> by blast
      have \<open>in_box_active (y t)\<close> using y_\<tau>_exit_in_box \<tau>_exit_eq_t by simp
      thus False using t_in_S by (simp add: S_def)
    qed

    show False
    proof (cases \<open>\<exists>i \<in> active. vec_nth (y \<tau>_exit) i = lo i \<or> vec_nth (y \<tau>_exit) i = hi i\<close>)
      case False
      note no_edge = False
      have strict_interior: 
        \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close>
        from y_\<tau>_exit_in_box i_act 
        have bounds: \<open>lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
          unfolding in_box_active_def 
          by blast
        from no_edge i_act 
        have neither: \<open>vec_nth (y \<tau>_exit) i \<noteq> lo i \<and> vec_nth (y \<tau>_exit) i \<noteq> hi i\<close>
          by blast
        from bounds neither 
        show \<open>lo i < vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i < hi i\<close>
          by auto
      qed

      obtain \<delta> where \<delta>_pos: \<open>0 < \<delta>\<close>
                 and \<delta>_ball: \<open>\<forall>\<tau> \<in> {0..t}. \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<longrightarrow> 
                              (\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i)\<close>
        using continuous_strictly_interior_neighborhood_active[OF y_cont \<tau>_exit_in_interval 
                                                                  strict_interior]
        by blast

      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> \<bar>\<tau> - \<tau>_exit\<bar> < \<delta> \<Longrightarrow> in_box_active (y \<tau>)\<close>
      proof -
        fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close> and \<tau>_close: \<open>\<bar>\<tau> - \<tau>_exit\<bar> < \<delta>\<close>
        from \<delta>_ball \<tau>_in \<tau>_close 
        have \<open>\<forall>i \<in> active. lo i < vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i < hi i\<close>
          by blast
        thus \<open>in_box_active (y \<tau>)\<close>
          unfolding in_box_active_def
          by (simp add: dual_order.strict_iff_order)
      qed

      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
                   and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<delta>/2\<close>
          unfolding \<tau>_exit_def[symmetric] 
          using \<delta>_pos 
          by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<delta>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis 
          using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset by blast
      have \<tau>_s_close: \<open>\<bar>\<tau>_s - \<tau>_exit\<bar> < \<delta>\<close>
        using \<tau>_s_ge \<tau>_s_lt \<delta>_pos by auto

      have \<open>in_box_active (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_in_t \<tau>_s_close by blast
      moreover have \<open>\<not> in_box_active (y \<tau>_s)\<close>
        using \<tau>_s_in_S by (simp add: S_def)
      ultimately show False by blast
    next
      case True
      have lower_at: \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_exit) i = lo i \<Longrightarrow> 
                              0 < vec_nth (f \<tau>_exit (y \<tau>_exit)) i\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close> and eq_lo: \<open>vec_nth (y \<tau>_exit) i = lo i\<close>
        have all_coords: \<open>\<And>j. lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
        proof -
          fix j
          show \<open>lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
          proof (cases \<open>j \<in> active\<close>)
            case True
            thus ?thesis 
              using y_\<tau>_exit_in_box 
              unfolding in_box_active_def 
              by blast
          next
            case False
            thus ?thesis 
              using inactive_maintained[OF _ \<tau>_exit_in_interval] 
              by blast
          qed
        qed
        show \<open>0 < vec_nth (f \<tau>_exit (y \<tau>_exit)) i\<close>
          using lower_edge_inward[OF i_act \<tau>_exit_in_interval y_in_Q[OF \<tau>_exit_in_interval] 
                                     all_coords eq_lo] .
      qed
      have upper_at: \<open>\<And>i. i \<in> active \<Longrightarrow> vec_nth (y \<tau>_exit) i = hi i \<Longrightarrow> 
                              vec_nth (f \<tau>_exit (y \<tau>_exit)) i < 0\<close>
      proof -
        fix i assume i_act: \<open>i \<in> active\<close> and eq_hi: \<open>vec_nth (y \<tau>_exit) i = hi i\<close>
        have all_coords: \<open>\<And>j. lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
        proof -
          fix j
          show \<open>lo j \<le> vec_nth (y \<tau>_exit) j \<and> vec_nth (y \<tau>_exit) j \<le> hi j\<close>
          proof (cases \<open>j \<in> active\<close>)
            case True
            thus ?thesis 
              using y_\<tau>_exit_in_box 
              unfolding in_box_active_def 
              by blast
          next
            case False
            thus ?thesis 
              using inactive_maintained[OF _ \<tau>_exit_in_interval] 
              by blast
          qed
        qed
        show \<open>vec_nth (f \<tau>_exit (y \<tau>_exit)) i < 0\<close>
          using upper_edge_inward[OF i_act \<tau>_exit_in_interval y_in_Q[OF \<tau>_exit_in_interval] 
                                     all_coords eq_hi] .
      qed
      have box_at: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i \<le> vec_nth (y \<tau>_exit) i \<and> vec_nth (y \<tau>_exit) i \<le> hi i\<close>
        using y_\<tau>_exit_in_box 
        unfolding in_box_active_def 
        by blast

      obtain \<epsilon> where \<epsilon>_pos: \<open>0 < \<epsilon>\<close>
                 and \<epsilon>_prop: \<open>\<forall>\<tau>. \<tau>_exit < \<tau> \<and> \<tau> < \<tau>_exit + \<epsilon> \<and> \<tau> \<le> t \<longrightarrow> 
                              (\<forall>i \<in> active. lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i)\<close>
        using solves_ode_inward_neighborhood_active[OF ODE \<tau>_exit_in_interval \<tau>_exit_lt_t 
                                                       box_at lower_at upper_at]
        by blast

      have neighborhood_in_box: 
        \<open>\<And>\<tau>. \<tau>_exit < \<tau> \<Longrightarrow> \<tau> < \<tau>_exit + \<epsilon> \<Longrightarrow> \<tau> \<le> t \<Longrightarrow> in_box_active (y \<tau>)\<close>
        using \<epsilon>_prop 
        unfolding in_box_active_def 
        by blast

      obtain \<tau>_s where \<tau>_s_in_S: \<open>\<tau>_s \<in> S\<close> 
                   and \<tau>_s_lt: \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
      proof -
        have \<open>Inf S < \<tau>_exit + \<epsilon>/2\<close>
          unfolding \<tau>_exit_def[symmetric] using \<epsilon>_pos by simp
        with S_nonempty S_bdd obtain \<tau>_s where 
          \<open>\<tau>_s \<in> S\<close> and \<open>\<tau>_s < \<tau>_exit + \<epsilon>/2\<close>
          by (metis cInf_lessD)
        thus ?thesis 
          using that 
          by blast
      qed

      have \<tau>_s_ge: \<open>\<tau>_exit \<le> \<tau>_s\<close>
        using \<tau>_s_in_S \<tau>_exit_lb by blast
      have \<tau>_s_in_t: \<open>\<tau>_s \<in> {0..t}\<close>
        using \<tau>_s_in_S S_subset by blast
      have \<tau>_s_ne: \<open>\<tau>_s \<noteq> \<tau>_exit\<close>
        using \<tau>_s_in_S y_\<tau>_exit_in_box by (auto simp: S_def)
      have \<tau>_s_gt: \<open>\<tau>_exit < \<tau>_s\<close>
        using \<tau>_s_ge \<tau>_s_ne by simp
      have \<tau>_s_lt_exit_\<epsilon>: \<open>\<tau>_s < \<tau>_exit + \<epsilon>\<close>
        using \<tau>_s_lt \<epsilon>_pos by auto

      have \<open>in_box_active (y \<tau>_s)\<close>
        using neighborhood_in_box \<tau>_s_gt \<tau>_s_lt_exit_\<epsilon> \<tau>_s_in_t 
        by simp 
      moreover have \<open>\<not> in_box_active (y \<tau>_s)\<close>
        using \<tau>_s_in_S by (simp add: S_def)
      ultimately show False by blast
    qed
  qed
  show \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow>
               y \<tau> \<in> Q \<and> lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix \<tau> i
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have inQ: \<open>y \<tau> \<in> Q\<close> using y_in_Q[OF \<tau>_in] .
    have box: \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof (cases \<open>i \<in> active\<close>)
      case True
      thus ?thesis 
        using active_main \<tau>_in
        unfolding in_box_active_def 
        by blast
    next
      case False
      thus ?thesis 
        using inactive_maintained \<tau>_in 
        by blast
    qed
    show \<open>y \<tau> \<in> Q \<and> lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      using inQ box 
      by blast
  qed
qed

end