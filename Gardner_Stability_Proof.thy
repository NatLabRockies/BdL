(***************************************************************)
(**                                                           **)
(** Author(s): Yakoub Nemouchi (NLR, Golden, CO, USA)         **)
(**            Peter  Graf     (NLR, Golden, CO, USA)         **)
(** Email:     Yakoub.Nemouchi@nlr.gov                        **)
(**            Peter.Graf@nlr.gov                             **)
(**                                                           **)
(** Copyright © 2026 Alliance for Energy Innovation, LLC.     **)
(** License: BSD 3-Clause, see LICENSE.                       **)
(** See CONTRIBUTORS and CITATION files for details.          **)
(***************************************************************)
theory Gardner_Stability_Proof

imports Differential_Dynamic_Logic

begin
section \<open>Case study: Proving Stability of Gardner Induced Switching\<close>


text \<open>
  SANITY CHECK: REACH\_lyapunov applied to a trivial 1D linear ODE

  SETUP
  -----
  Consider the simplest possible scalar linear ODE:

      du/dt = -2*u

  with initial condition u(0) = 1.  The exact solution is u(tau) = exp(-2tau).

  Define the Lyapunov function V(v) = (vec\_nth v 0)\textasciicircum{}2 (squared component).
  Along the trajectory:

      V(y(tau)) = u(tau)\textasciicircum{}2 = exp(-4tau)
      (V o y)'(tau) = 2*u(tau)*u'(tau) = 2*u(tau)*(-2*u(tau)) = -4*u(tau)\textasciicircum{}2 = -4*V(y(tau))

  So the rate bound phi(tau) <= -delta*V(y(tau)) holds with delta = 4.

  REACH\_lyapunov then gives:

      V(y(T)) <= V(y(0)) * exp(-4*T) = 1 * exp(-4*T) = exp(-4*T)

  i.e., u(T)\textasciicircum{}2 <= exp(-4*T), which is TIGHT (the trajectory achieves equality).

  PURPOSE
  This sanity check validates two things:

1. The REACH\_lyapunov axiom's obligations (ODE, T\_nn, delta\_pos, V\_vderiv,
  V\_nn, rate\_proportional) are ergonomic to discharge in a concrete
  setting.  Each obligation becomes a named `have` statement in the
  proof, following the "obligations on top, axiom on bottom" template.

1. The obligation shapes generalize to higher-dimensional cases.  The
  same template will be used for the Gardner toggle switch proof, just
  with a 2D state space, a time-varying field, and a quadratic
  Lyapunov function centered at the pulse equilibrium.

  This lemma also serves as a pedagogical example for the paper , the
  simplest possible demonstration of REACH\_lyapunov in action.
\<close>

lemma REACH_lyapunov_sanity_check:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth v 0)))) 
                    {0..T} UNIV\<close>
      \<comment> \<open>ODE: du/dt = -2*u, written in the vec\_lambda and fun\_upd
         form used throughout the CRN benchmarks\<close>
  assumes iv: \<open>vec_nth (y 0) 0 = 1\<close>
      \<comment> \<open>Initial condition: u(0) = 1\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  shows \<open>(vec_nth (y T) 0)^2 \<le> exp (-4 * T)\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Apply REACH_lyapunov with the following instantiation:
     
       V     = \<lambda>v. (vec_nth v 0)^2      (Lyapunov function: squared component)
       \<phi>     = \<lambda>\<tau>. -4 * (vec_nth (y \<tau>) 0)^2   (time derivative of V \<circ> y)
       \<delta>     = 4                         (exponential decay rate)
     
     Then REACH_lyapunov concludes V(y(T)) \<le> V(y(0)) \<sqdot> exp(-4\<sqdot>T).
     Since V(y(0)) = (vec_nth (y 0) 0)^2 = 1^2 = 1 from `iv`, the 
     right-hand side simplifies to exp(-4\<sqdot>T), giving the goal.
     
     Each of REACH_lyapunov's six proof obligations is discharged as a named 
     `have` statement below, in the order the axiom expects them.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 1 (ODE): passed directly from `y_sol`, no have needed.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 2 (T_nn): passed directly from `T_nn`, no have needed.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 3 (\<delta>_pos): \<delta> = 4 > 0, trivial.
     ========================================================================== *)
  have \<delta>_pos: \<open>(0::real) < 4\<close> by simp

  (* ==========================================================================
     PROOF OBLIGATION 4 (V_vderiv): The composition (V \<circ> y)(\<tau>) = (vec_nth (y \<tau>) 0)^2 
     has time derivative \<phi>(\<tau>) = -4 \<sqdot> (vec_nth (y \<tau>) 0)^2 on {0..T}.
     
     Derivation: (V \<circ> y)'(\<tau>) = 2 \<sqdot> vec_nth (y \<tau>) 0 \<sqdot> (vec_nth (y \<tau>) 0)'
     The time derivative of vec_nth (y \<tau>) 0 is the 0-th component of the 
     field at y(\<tau>), which by the ODE is -2 \<sqdot> vec_nth (y \<tau>) 0.  
     Therefore (V \<circ> y)'(\<tau>) = 2 \<sqdot> u \<sqdot> (-2 \<sqdot> u) = -4 \<sqdot> u^2.
     
     The Isabelle mechanics: we extract the vderiv of vec_nth (y \<tau>) 0 from 
     y_sol, then apply the chain rule via derivative_eq_intros on 
     has_derivative.
     ========================================================================== *)
 have u_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) 0) has_vderiv_on 
                   (\<lambda>\<tau>. -2 * vec_nth (y \<tau>) 0)) {0..T}\<close>
  proof -
    have y_vderiv: \<open>(y has_vderiv_on 
                     (\<lambda>\<tau>. vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0)))) {0..T}\<close>
      using y_sol by (simp add: solves_ode_def)
    have proj_deriv: \<open>\<And>p. ((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) 
                          (at p within UNIV)\<close>
      by (rule has_derivative_vec_nth)
    show ?thesis
      using y_vderiv
      unfolding has_vderiv_on_def has_vector_derivative_def
    proof (clarify, goal_cases)
      case (1 \<tau>)
      have y_at_\<tau>: \<open>(y has_derivative 
                     (\<lambda>x. x *\<^sub>R vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0)))) 
                    (at \<tau> within {0..T})\<close>
        using 1 by simp
      have composed: \<open>((\<lambda>\<tau>'. vec_nth (y \<tau>') 0) has_derivative 
                         (\<lambda>x. vec_nth (x *\<^sub>R vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0))) 0)) 
                       (at \<tau> within {0..T})\<close>
        using has_derivative_compose[OF y_at_\<tau> proj_deriv] 
        by simp
      show ?case
        using composed 
        by (simp add: fun_upd_def)
    qed
  qed

  \<comment> \<open>Pointwise derivative of V = (lambdav. (vec\_nth v 0)\textasciicircum{}2) at a state p:
      the linear map w |-> 2 * (vec\_nth p 0) * (vec\_nth w 0).\<close>
  have V_deriv:
    \<open>\<And>p::(real,'p) vec. ((\<lambda>v::(real,'p) vec. (vec_nth v 0)^2) has_derivative
            (\<lambda>w. 2 * vec_nth p 0 * vec_nth w 0)) (at p)\<close>
  proof -
    fix p :: \<open>(real,'p) vec\<close>
    have proj: \<open>((\<lambda>v::(real,'p) vec. vec_nth v 0)
                   has_derivative (\<lambda>w. vec_nth w 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have sq: \<open>((\<lambda>z::real. z^2)
                 has_derivative (\<lambda>h. 2 * vec_nth p 0 * h)) (at (vec_nth p 0))\<close>
      by (auto intro!: derivative_eq_intros)
    show \<open>((\<lambda>v::(real,'p) vec. (vec_nth v 0)^2)
             has_derivative (\<lambda>w. 2 * vec_nth p 0 * vec_nth w 0)) (at p)\<close>
      using has_derivative_compose[OF proj sq] 
      by (simp add: comp_def)
  qed

  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
      \<exists>DV. ((\<lambda>v::(real,'p) vec. (vec_nth v 0)^2) has_derivative DV) (at (y \<tau>)) \<and>
           DV (vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0))) \<le>
              -4 * (vec_nth (y \<tau>) 0)^2\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    have lie: \<open>(\<lambda>w. 2 * vec_nth (y \<tau>) 0 * vec_nth w 0)
                 (vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0)))
               = -4 * (vec_nth (y \<tau>) 0)^2\<close>
      by (simp add: fun_upd_def power2_eq_square)
    show \<open>\<exists>DV. ((\<lambda>v::(real,'p) vec. (vec_nth v 0)^2) has_derivative DV) (at (y \<tau>)) \<and>
               DV (vec_lambda ((\<lambda>k. 0)(0 := -2 * vec_nth (y \<tau>) 0))) \<le>
                  -4 * (vec_nth (y \<tau>) 0)^2\<close>
      using V_deriv[of \<open>y \<tau>\<close>] lie by auto
  qed

  have bound: \<open>(vec_nth (y T) 0)^2 \<le> (vec_nth (y 0) 0)^2 * exp (-4 * T)\<close>
    using REACH_lyapunov[where V = \<open>\<lambda>v::(real,'p) vec. (vec_nth v 0)^2\<close> and \<delta> = 4,
                         OF y_sol T_nn induct_step]
    by simp

  show ?thesis
    using bound iv 
    by simp
qed

text \<open>
  \textbf{GARDNER TOGGLE SWITCH , INDUCED SWITCHING VIA PULSED DYNAMICS}\\
  This example formalizes "induced switching" for the symmetric Gardner
  toggle switch.  Three-interval structure:
    Interval 1: [0, t\_start]     baseline dynamics, trajectory in R\_A
    Interval 2: [t\_start, t\_end] pulsed dynamics, trajectory moves to R\_B
    Interval 3: [t\_end, T]       baseline dynamics, trajectory stays in R\_B

  All definitions and lemmas live inside the appropriate locale's
  main `begin ... end` block (no reopened `context` blocks).  This
  ensures derived locales see the definitions as first-class members.
\<close>


subsection \<open>Baseline and pulsed vector fields\<close>

definition gardner_baseline_field :: 
  \<open>real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 
   (real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> 
   (real, 'p) vec\<close> where
  \<open>gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v = 
     vec_lambda ((\<lambda>k::'p. 0)(
       0 := \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
       1 := \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))\<close>

definition gardner_pulse_field :: 
  \<open>real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 
   (real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> 
   (real, 'p) vec\<close> where
  \<open>gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> v = 
     vec_lambda ((\<lambda>k::'p. 0)(
       0 := \<alpha>_low / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
       1 := \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))\<close>


subsection \<open>Baseline parameter regime\<close>

locale gardner_baseline_params =
  fixes \<alpha>_base :: real
  fixes \<beta> \<gamma> :: nat
  assumes \<alpha>_base_above_threshold: \<open>2 < \<alpha>_base\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>


subsection \<open>Pulsed parameter regime with equilibrium, Lyapunov function, 
  and decrease estimate\<close>

text \<open>
  This locale fixes the pulse parameters and the pulsed equilibrium,
  AND defines V\_pulse, coupling\_Q, M\_crude, and proves the decrease
  estimate.  Everything lives in a single begin/end block so that
  derived locales see all definitions as first-class members.
\<close>
definition M_sharp_scalar :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real\<close> where
  \<open>M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max = 
     u_pulse * (v_max + v_pulse) / (1 + v_min^2) +
     v_pulse * (u_max + u_pulse) / (1 + u_min^2)\<close>

locale gardner_pulse_params = gardner_baseline_params +
  fixes \<alpha>_low :: real
  fixes u_pulse v_pulse :: real
  assumes \<alpha>_low_pos: \<open>0 < \<alpha>_low\<close>
  assumes \<alpha>_low_below_base: \<open>\<alpha>_low < \<alpha>_base\<close>
  assumes u_pulse_pos: \<open>0 < u_pulse\<close>
  assumes v_pulse_pos: \<open>0 < v_pulse\<close>
  assumes u_pulse_equilibrium: \<open>\<alpha>_low / (1 + v_pulse^\<beta>) = u_pulse\<close>
  assumes v_pulse_equilibrium: \<open>\<alpha>_base / (1 + u_pulse^\<gamma>) = v_pulse\<close>
begin

text \<open>Pulsed equilibrium as a vector.\<close>

definition E_pulse :: 
  \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close> where
  \<open>E_pulse = vec_lambda ((\<lambda>k::'p. 0)(0 := u_pulse, 1 := v_pulse))\<close>

lemma E_pulse_u_component: 
  \<open>vec_nth (E_pulse :: (real, 'p::{finite, linordered_nonzero_semiring}) vec) 0 = u_pulse\<close>
  by (simp add: E_pulse_def fun_upd_def)

lemma E_pulse_v_component: 
  \<open>vec_nth (E_pulse :: (real, 'p::{finite, linordered_nonzero_semiring}) vec) 1 = v_pulse\<close>
  by (simp add: E_pulse_def fun_upd_def)

text \<open>Lyapunov function V\_pulse.\<close>

definition V_pulse :: 
  \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> real\<close> where
  \<open>V_pulse v = (vec_nth v 0 - u_pulse)^2 / 2 + (vec_nth v 1 - v_pulse)^2 / 2\<close>

lemma V_pulse_nn: \<open>0 \<le> V_pulse v\<close>
  by (simp add: V_pulse_def)

lemma V_pulse_has_derivative:
  fixes p :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  shows \<open>(V_pulse has_derivative
           (\<lambda>w. (vec_nth p 0 - u_pulse) * vec_nth w 0
              + (vec_nth p 1 - v_pulse) * vec_nth w 1)) (at p)\<close>
proof -
  have proj0: \<open>((\<lambda>v::(real,'p) vec. vec_nth v 0)
                  has_derivative (\<lambda>w. vec_nth w 0)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have proj1: \<open>((\<lambda>v::(real,'p) vec. vec_nth v 1)
                  has_derivative (\<lambda>w. vec_nth w 1)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have sq0: \<open>((\<lambda>z::real. (z - u_pulse)^2 / 2)
               has_derivative (\<lambda>h. (vec_nth p 0 - u_pulse) * h))
             (at (vec_nth p 0))\<close>
    by (auto intro!: derivative_eq_intros)
  have sq1: \<open>((\<lambda>z::real. (z - v_pulse)^2 / 2)
               has_derivative (\<lambda>h. (vec_nth p 1 - v_pulse) * h))
             (at (vec_nth p 1))\<close>
    by (auto intro!: derivative_eq_intros)
  have c0: \<open>((\<lambda>v::(real,'p) vec. (vec_nth v 0 - u_pulse)^2 / 2)
               has_derivative (\<lambda>w. (vec_nth p 0 - u_pulse) * vec_nth w 0)) (at p)\<close>
    using has_derivative_compose[OF proj0 sq0] 
    by (simp add: comp_def)
  have c1: \<open>((\<lambda>v::(real,'p) vec. (vec_nth v 1 - v_pulse)^2 / 2)
               has_derivative (\<lambda>w. (vec_nth p 1 - v_pulse) * vec_nth w 1)) (at p)\<close>
    using has_derivative_compose[OF proj1 sq1] 
    by (simp add: comp_def)
  show ?thesis
    unfolding V_pulse_def
    using has_derivative_add[OF c0 c1] 
    by simp
qed

lemma V_pulse_zero_at_E_pulse: 
  \<open>V_pulse (E_pulse :: (real, 'p::{finite, linordered_nonzero_semiring}) vec) = 0\<close>
  by (simp add: V_pulse_def E_pulse_def fun_upd_def)

text \<open>Coupling term Q and the Lie derivative identity.\<close>

definition coupling_Q :: 
  \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> real\<close> where
  \<open>coupling_Q v = 
     \<alpha>_low  * (vec_nth v 1 + v_pulse) / ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2)) +
     \<alpha>_base * (vec_nth v 0 + u_pulse) / ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<close>


lemma V_pulse_lie_derivative_symbolic:
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  shows \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
         (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) =
         -2 * V_pulse v - 
         (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<close>
proof -
  have denom_v_pos: \<open>0 < 1 + (vec_nth v 1)^2\<close> 
    by (meson rel_simps(68) zero_compare_simps(1) zero_le_power2)
  have denom_u_pos: \<open>0 < 1 + (vec_nth v 0)^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_v_nz: \<open>1 + (vec_nth v 1)^2 \<noteq> 0\<close> 
    using denom_v_pos 
    by simp
  have denom_u_nz: \<open>1 + (vec_nth v 0)^2 \<noteq> 0\<close> 
    using denom_u_pos
    by simp

  have \<alpha>_low_eq: \<open>\<alpha>_low = u_pulse * (1 + v_pulse^2)\<close>
    using u_pulse_equilibrium[symmetric] \<beta>_eq u_pulse_pos 
    by auto

  have \<alpha>_base_eq: \<open>\<alpha>_base = v_pulse * (1 + u_pulse^2)\<close>
    using v_pulse_equilibrium[symmetric] \<gamma>_eq v_pulse_pos 
    by auto

  (* --- First half: the u-direction identity --- *)
  (* 
     We prove: u_t \<cdot> (\<alpha>_low/(1+v\<^sup>2) - u) = -u_t\<^sup>2 - u_t\<cdot>v_t \<cdot> u_pulse\<cdot>(v+v_pulse)/(1+v\<^sup>2)
     
     This is done by:
     1. Substituting \<alpha>_low = u_pulse\<sqdot>(1+v_pulse²)
     2. Rewriting \<alpha>_low/(1+v²) - u = u_pulse\<sqdot>(1+v_pulse²)/(1+v²) - u_pulse - ũ
     3. Combining: u_pulse\<sqdot>[(1+v_pulse²)/(1+v²) - 1] - ũ
                 = u_pulse\<sqdot>(v_pulse² - v²)/(1+v²) - ũ
     4. Factoring v_pulse² - v² = -(v-v_pulse)(v+v_pulse) = -ṽ\<sqdot>(v+v_pulse)
  *)

  have u_half_field: \<open>\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0 = 
                      -u_pulse * (vec_nth v 1 - v_pulse) * (vec_nth v 1 + v_pulse) 
                        / (1 + (vec_nth v 1)^2) - (vec_nth v 0 - u_pulse)\<close>
  proof -
    have step1: \<open>\<alpha>_low / (1 + (vec_nth v 1)^2) = 
                  u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v 1)^2)\<close>
      using \<alpha>_low_eq 
      by simp

    have step2: \<open>u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v 1)^2) - vec_nth v 0 = 
                  u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v 1)^2) 
                  - u_pulse - (vec_nth v 0 - u_pulse)\<close>
      by simp

    have step3: \<open>u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v 1)^2) - u_pulse = 
                  u_pulse * ((1 + v_pulse^2) - (1 + (vec_nth v 1)^2)) / (1 + (vec_nth v 1)^2)\<close>
      using denom_v_nz
      by (metis divide_diff_eq_iff right_diff_distrib)

    have step4: \<open>(1 + v_pulse^2) - (1 + (vec_nth v 1)^2) = 
                  -((vec_nth v 1 - v_pulse) * (vec_nth v 1 + v_pulse))\<close>
      by (simp add: power2_eq_square algebra_simps)
    from step1 step2 step3 step4 
    show ?thesis 
      by auto
  qed

  have u_half: \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) = 
                - ((vec_nth v 0 - u_pulse)^2) 
                - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * 
                    (u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2))\<close>
  proof -
    have \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) =
          (vec_nth v 0 - u_pulse) * 
            (-u_pulse * (vec_nth v 1 - v_pulse) * (vec_nth v 1 + v_pulse) 
               / (1 + (vec_nth v 1)^2) - (vec_nth v 0 - u_pulse))\<close>
      using u_half_field by simp
    also have \<open>\<dots> = 
          -((vec_nth v 0 - u_pulse)^2) 
          - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * 
              (u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2))\<close>
      apply (simp add: algebra_simps power2_eq_square)
      apply argo
      done
    finally show ?thesis .
  qed

  (* --- Second half: the v-direction identity (symmetric) --- *)

  have v_half_field: \<open>\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1 = 
                      -v_pulse * (vec_nth v 0 - u_pulse) * (vec_nth v 0 + u_pulse) 
                        / (1 + (vec_nth v 0)^2) - (vec_nth v 1 - v_pulse)\<close>
  proof -
    have step1: \<open>\<alpha>_base / (1 + (vec_nth v 0)^2) = 
                  v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v 0)^2)\<close>
      using \<alpha>_base_eq 
      by simp
    have step2: \<open>v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v 0)^2) - vec_nth v 1 = 
                  v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v 0)^2) 
                  - v_pulse - (vec_nth v 1 - v_pulse)\<close>
      by simp
    have step3: \<open>v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v 0)^2) - v_pulse = 
                  v_pulse * ((1 + u_pulse^2) - (1 + (vec_nth v 0)^2)) / (1 + (vec_nth v 0)^2)\<close>
      using denom_u_nz
      by (metis (no_types, lifting) nonzero_mult_div_cancel_right right_diff_distrib' 
                times_divide_eq_left)
    have step4: \<open>(1 + u_pulse^2) - (1 + (vec_nth v 0)^2) = 
                  -((vec_nth v 0 - u_pulse) * (vec_nth v 0 + u_pulse))\<close>
      by (simp add: power2_eq_square algebra_simps)
    from step1 step2 step3 step4 
    show ?thesis 
      by auto
  qed
  have v_half: \<open>(vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) = 
                -((vec_nth v 1 - v_pulse)^2) 
                - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * 
                    (v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2))\<close>
  proof -
    have \<open>(vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) =
          (vec_nth v 1 - v_pulse) * 
            (-v_pulse * (vec_nth v 0 - u_pulse) * (vec_nth v 0 + u_pulse) 
               / (1 + (vec_nth v 0)^2) - (vec_nth v 1 - v_pulse))\<close>
      using v_half_field 
      by simp
    also have \<open>\<dots> = 
          -((vec_nth v 1 - v_pulse)^2) 
          - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * 
              (v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2))\<close>
      apply (simp add: algebra_simps power2_eq_square)
      apply argo
      done
    finally show ?thesis .
  qed

  (* --- Combining the two halves --- *)

  have coupling_Q_as_halves: 
    \<open>coupling_Q v = 
       u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2) +
       v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2)\<close>
  proof -
    have v_factor: \<open>\<alpha>_low * (vec_nth v 1 + v_pulse) / 
                    ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2)) = 
                    u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2)\<close>
    proof -
      have \<open>\<alpha>_low * (vec_nth v 1 + v_pulse) / 
            ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2)) = 
            (u_pulse * (1 + v_pulse^2)) * (vec_nth v 1 + v_pulse) / 
            ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<close>
        using \<alpha>_low_eq 
        by simp
      also have \<open>\<dots> = u_pulse * (vec_nth v 1 + v_pulse) * (1 + v_pulse^2) / 
                       ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<close>
        by (simp add: mult.commute mult.left_commute)
      also have \<open>\<dots> = u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2)\<close>
             using assms(1) u_pulse_equilibrium 
             by auto
      finally show ?thesis .
    qed
    have u_factor: \<open>\<alpha>_base * (vec_nth v 0 + u_pulse) / 
                    ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2)) = 
                    v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2)\<close>
    proof -
      have \<open>\<alpha>_base * (vec_nth v 0 + u_pulse) / 
            ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2)) = 
            (v_pulse * (1 + u_pulse^2)) * (vec_nth v 0 + u_pulse) / 
            ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<close>
        using \<alpha>_base_eq 
        by simp
      also have \<open>\<dots> = v_pulse * (vec_nth v 0 + u_pulse) * (1 + u_pulse^2) / 
                       ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<close>
        by (simp add: mult.commute mult.left_commute)
      also have \<open>\<dots> = v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2)\<close>
             using assms(2) v_pulse_equilibrium 
             by auto
      finally show ?thesis .
    qed
    show ?thesis
      unfolding coupling_Q_def
      using v_factor u_factor 
      by simp
  qed

  (* --- Final assembly: LHS = u_half + v_half; RHS uses coupling_Q_as_halves --- *)

  have \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
        (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) = 
        -((vec_nth v 0 - u_pulse)^2) - (vec_nth v 1 - v_pulse)^2
        - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * 
            (u_pulse * (vec_nth v 1 + v_pulse) / (1 + (vec_nth v 1)^2) + 
             v_pulse * (vec_nth v 0 + u_pulse) / (1 + (vec_nth v 0)^2))\<close>
    using u_half v_half 
    by (simp add: algebra_simps)
  also have \<open>\<dots> = -((vec_nth v 0 - u_pulse)^2) - (vec_nth v 1 - v_pulse)^2
                  - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<close>
    using coupling_Q_as_halves 
    by simp
  also have \<open>\<dots> = -2 * V_pulse v 
                  - (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<close>
    by (simp add: V_pulse_def)
  finally show ?thesis .
qed
text \<open>Crude bound on |Q|.\<close>

definition M_crude :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real\<close> where
  \<open>M_crude u_min u_max v_min v_max = 
     \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse) +
     \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>

lemma coupling_Q_bound_crude:
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes u_min u_max v_min v_max :: real
  assumes u_bounds: \<open>u_min \<le> vec_nth v 0\<close> \<open>vec_nth v 0 \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v 1\<close> \<open>vec_nth v 1 \<le> v_max\<close>
  shows \<open>\<bar>coupling_Q v\<bar> \<le> M_crude u_min u_max v_min v_max\<close>
proof -
  (* --- Positivity facts we'll need --- *)
  have \<alpha>_low_nn: \<open>0 \<le> \<alpha>_low\<close> using \<alpha>_low_pos by simp
  have \<alpha>_base_nn: \<open>0 \<le> \<alpha>_base\<close> using \<alpha>_base_above_threshold by simp
  have v_pulse_nn: \<open>0 \<le> v_pulse\<close> using v_pulse_pos by simp
  have u_pulse_nn: \<open>0 \<le> u_pulse\<close> using u_pulse_pos by simp

  have denom_v_pos: \<open>0 < 1 + (vec_nth v 1)^2\<close> by (simp add: add_pos_nonneg)
  have denom_u_pos: \<open>0 < 1 + (vec_nth v 0)^2\<close> by (simp add: add_pos_nonneg)
  have denom_vp_pos: \<open>0 < 1 + v_pulse^2\<close> by (simp add: add_pos_nonneg)
  have denom_up_pos: \<open>0 < 1 + u_pulse^2\<close> by (simp add: add_pos_nonneg)

  have prod_vv_ge1: \<open>1 \<le> (1 + (vec_nth v 1)^2) * (1 + v_pulse^2)\<close>
  proof -
    have \<open>1 \<le> 1 + (vec_nth v 1)^2\<close> by simp
    moreover have \<open>1 \<le> 1 + v_pulse^2\<close> by simp
    ultimately show ?thesis
      by (metis mult_mono' zero_le_one mult_1)
  qed
  have prod_uu_ge1: \<open>1 \<le> (1 + (vec_nth v 0)^2) * (1 + u_pulse^2)\<close>
  proof -
    have \<open>1 \<le> 1 + (vec_nth v 0)^2\<close> by simp
    moreover have \<open>1 \<le> 1 + u_pulse^2\<close> by simp
    ultimately show ?thesis
      by (metis mult_mono' zero_le_one  mult_1)
  qed

  have prod_vv_pos: \<open>0 < (1 + (vec_nth v 1)^2) * (1 + v_pulse^2)\<close>
    using denom_v_pos denom_vp_pos 
    by simp
  have prod_uu_pos: \<open>0 < (1 + (vec_nth v 0)^2) * (1 + u_pulse^2)\<close>
    using denom_u_pos denom_up_pos 
    by simp

  (* --- Stage 1: Bound |v| and |u| by max of region bounds --- *)

  have abs_v_le: \<open>\<bar>vec_nth v 1\<bar> \<le> max \<bar>v_min\<bar> \<bar>v_max\<bar>\<close>
    using v_bounds
    by linarith

  have abs_u_le: \<open>\<bar>vec_nth v 0\<bar> \<le> max \<bar>u_min\<bar> \<bar>u_max\<bar>\<close>
    using u_bounds
    by linarith 

  (* --- Stage 2: Bound each term of coupling_Q individually --- *)

  (* v-term bound *)
  have v_term_bound: 
    \<open>\<bar>\<alpha>_low * (vec_nth v 1 + v_pulse) / ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<bar> \<le>
      \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse)\<close>
  proof -
    have step1: \<open>\<bar>\<alpha>_low * (vec_nth v 1 + v_pulse) / 
                   ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<bar>
                = \<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar> / 
                   ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<close>
      using \<alpha>_low_nn prod_vv_pos 
      by (simp add: abs_mult)
    have step2: \<open>\<bar>vec_nth v 1 + v_pulse\<bar> \<le> \<bar>vec_nth v 1\<bar> + v_pulse\<close>
      using v_pulse_nn 
      by (simp add: abs_triangle_ineq)
    have step3: \<open>\<bar>vec_nth v 1\<bar> + v_pulse \<le> max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse\<close>
      using abs_v_le 
      by simp
    have step4: \<open>\<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar> \<le>
                 \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse)\<close>
      using step2 step3 \<alpha>_low_nn 
      by (simp add: mult_left_mono)
    (* Now dividing by something \<ge> 1 *)
    have step5: \<open>\<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar> / 
                 ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2)) \<le>
                  \<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar>\<close>
    proof -
      have numer_nn: \<open>0 \<le> \<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar>\<close>
        using \<alpha>_low_nn by simp
      from numer_nn prod_vv_ge1 show ?thesis
        using frac_le[where y = "\<alpha>_low * \<bar>vec_nth v 1 + v_pulse\<bar>" 
                        and w = 1 
                        and z = "(1 + (vec_nth v 1)^2) * (1 + v_pulse^2)"]
        by simp
    qed
    from step1 step4 step5 
    show ?thesis
      by linarith
  qed

  (* u-term bound , symmetric *)
  have u_term_bound: 
    \<open>\<bar>\<alpha>_base * (vec_nth v 0 + u_pulse) / ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<bar> \<le>
      \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
  proof -
    have step1: \<open>\<bar>\<alpha>_base * (vec_nth v 0 + u_pulse) / 
                   ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<bar> =
                 \<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar> / 
                   ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<close>
      using \<alpha>_base_nn prod_uu_pos 
      by (simp add: abs_mult)
    have step2: \<open>\<bar>vec_nth v 0 + u_pulse\<bar> \<le> \<bar>vec_nth v 0\<bar> + u_pulse\<close>
      using u_pulse_nn 
      by (simp add: abs_triangle_ineq)
    have step3: \<open>\<bar>vec_nth v 0\<bar> + u_pulse \<le> max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse\<close>
      using abs_u_le 
      by simp
    have step4: \<open>\<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar> 
                 \<le> \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
      using step2 step3 \<alpha>_base_nn 
      by (simp add: mult_left_mono)
    have step5: \<open>\<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar> / 
                 ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2)) \<le> 
                  \<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar>\<close>
    proof -
      have numer_nn: \<open>0 \<le> \<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar>\<close>
        using \<alpha>_base_nn 
        by simp
      from numer_nn prod_uu_ge1 show ?thesis
        using frac_le[where y = "\<alpha>_base * \<bar>vec_nth v 0 + u_pulse\<bar>" 
                        and w = 1 
                        and z = "(1 + (vec_nth v 0)^2) * (1 + u_pulse^2)"]
        by simp
    qed
    from step1 step4 step5 show ?thesis
      by linarith
  qed

  (* --- Stage 3: Triangle inequality and combining --- *)

  have \<open>\<bar>coupling_Q v\<bar> \<le> 
        \<bar>\<alpha>_low * (vec_nth v 1 + v_pulse) / ((1 + (vec_nth v 1)^2) * (1 + v_pulse^2))\<bar> +
        \<bar>\<alpha>_base * (vec_nth v 0 + u_pulse) / ((1 + (vec_nth v 0)^2) * (1 + u_pulse^2))\<bar>\<close>
    unfolding coupling_Q_def by (rule abs_triangle_ineq)
  also have \<open>\<dots> \<le> \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse) + 
                  \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
    using v_term_bound u_term_bound by linarith
  also have \<open>\<dots> = M_crude u_min u_max v_min v_max\<close>
    unfolding M_crude_def 
    by simp
  finally show ?thesis .
qed

lemma coupling_Q_bound_sharp:
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes u_min u_max v_min v_max :: real
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  assumes u_min_nn: \<open>0 \<le> u_min\<close>
  assumes v_min_nn: \<open>0 \<le> v_min\<close>
  assumes u_bounds: \<open>u_min \<le> vec_nth v 0\<close> \<open>vec_nth v 0 \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v 1\<close> \<open>vec_nth v 1 \<le> v_max\<close>
  shows \<open>\<bar>coupling_Q v\<bar> \<le> M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
proof -
  define u where \<open>u = vec_nth v 0\<close>
  define w where \<open>w = vec_nth v 1\<close>

  have u_nn: \<open>0 \<le> u\<close> using u_min_nn u_bounds unfolding u_def by simp
  have w_nn: \<open>0 \<le> w\<close> using v_min_nn v_bounds unfolding w_def by simp
  have u_pulse_nn: \<open>0 \<le> u_pulse\<close> using u_pulse_pos by simp
  have v_pulse_nn: \<open>0 \<le> v_pulse\<close> using v_pulse_pos by simp

  have denom_w_pos: \<open>0 < 1 + w^2\<close> by (simp add: add_pos_nonneg)
  have denom_u_pos: \<open>0 < 1 + u^2\<close> by (simp add: add_pos_nonneg)
  have denom_w_min_pos: \<open>0 < 1 + v_min^2\<close> by (simp add: add_pos_nonneg)
  have denom_u_min_pos: \<open>0 < 1 + u_min^2\<close> by (simp add: add_pos_nonneg)
  have denom_vp_pos: \<open>0 < 1 + v_pulse^2\<close> by (simp add: add_pos_nonneg)
  have denom_up_pos: \<open>0 < 1 + u_pulse^2\<close> by (simp add: add_pos_nonneg)

  have \<alpha>_low_eq: \<open>\<alpha>_low = u_pulse * (1 + v_pulse^2)\<close>
    using u_pulse_equilibrium \<beta>_eq denom_vp_pos 
    by (simp add: field_simps)
  have \<alpha>_base_eq: \<open>\<alpha>_base = v_pulse * (1 + u_pulse^2)\<close>
    using v_pulse_equilibrium \<gamma>_eq denom_up_pos 
    by (simp add: field_simps)

  have Q_eq: \<open>coupling_Q v = u_pulse * (w + v_pulse) / (1 + w^2) +
                              v_pulse * (u + u_pulse) / (1 + u^2)\<close>
  proof -
    have \<open>coupling_Q v = 
            \<alpha>_low * (w + v_pulse) / ((1 + w^2) * (1 + v_pulse^2)) +
            \<alpha>_base * (u + u_pulse) / ((1 + u^2) * (1 + u_pulse^2))\<close>
      unfolding coupling_Q_def u_def w_def by simp
    also have \<open>... = 
               u_pulse * (1 + v_pulse^2) * (w + v_pulse) / ((1 + w^2) * (1 + v_pulse^2)) +
               v_pulse * (1 + u_pulse^2) * (u + u_pulse) / ((1 + u^2) * (1 + u_pulse^2))\<close>
      using \<alpha>_low_eq \<alpha>_base_eq by simp
    also have \<open>... = u_pulse * (w + v_pulse) / (1 + w^2) +
                      v_pulse * (u + u_pulse) / (1 + u^2)\<close>
      using denom_vp_pos denom_up_pos     
      by simp
    finally show ?thesis .
  qed

  have num1_nn: \<open>0 \<le> w + v_pulse\<close> using w_nn v_pulse_nn by simp
  have num2_nn: \<open>0 \<le> u + u_pulse\<close> using u_nn u_pulse_nn by simp

  have term1_nn: \<open>0 \<le> u_pulse * (w + v_pulse) / (1 + w^2)\<close>
    using u_pulse_nn num1_nn denom_w_pos 
    by (simp add: divide_nonneg_pos)
  have term2_nn: \<open>0 \<le> v_pulse * (u + u_pulse) / (1 + u^2)\<close>
    using v_pulse_nn num2_nn denom_u_pos 
    by (simp add: divide_nonneg_pos)

  have Q_nn: \<open>0 \<le> coupling_Q v\<close>
    using term1_nn term2_nn Q_eq 
    by simp
  hence abs_Q: \<open>\<bar>coupling_Q v\<bar> = coupling_Q v\<close> 
    by simp

  have num1_bound: \<open>w + v_pulse \<le> v_max + v_pulse\<close>
    using v_bounds unfolding w_def 
    by simp
  have denom1_bound: \<open>1 + v_min^2 \<le> 1 + w^2\<close>
    using v_bounds v_min_nn w_nn unfolding w_def 
    by simp
  have term1_bound: \<open>u_pulse * (w + v_pulse) / (1 + w^2) \<le> 
                     u_pulse * (v_max + v_pulse) / (1 + v_min^2)\<close>
  proof -
    have num_mono: \<open>u_pulse * (w + v_pulse) \<le> u_pulse * (v_max + v_pulse)\<close>
      using num1_bound u_pulse_nn 
      by (simp add: mult_left_mono)
    have num_nn: \<open>0 \<le> u_pulse * (w + v_pulse)\<close>
      using u_pulse_nn num1_nn 
      by simp
    show ?thesis
      using num_mono denom1_bound denom_w_pos denom_w_min_pos num_nn
      by (simp add: frac_le)
  qed

  have num2_bound: \<open>u + u_pulse \<le> u_max + u_pulse\<close>
    using u_bounds unfolding u_def 
    by simp
  have denom2_bound: \<open>1 + u_min^2 \<le> 1 + u^2\<close>
    using u_bounds u_min_nn u_nn unfolding u_def 
    by simp
  have term2_bound: \<open>v_pulse * (u + u_pulse) / (1 + u^2) \<le> 
                     v_pulse * (u_max + u_pulse) / (1 + u_min^2)\<close>
  proof -
    have num_mono: \<open>v_pulse * (u + u_pulse) \<le> v_pulse * (u_max + u_pulse)\<close>
      using num2_bound v_pulse_nn 
      by (simp add: mult_left_mono)
    have num_nn: \<open>0 \<le> v_pulse * (u + u_pulse)\<close>
      using v_pulse_nn num2_nn 
      by simp
    show ?thesis
      using num_mono denom2_bound denom_u_pos denom_u_min_pos num_nn
      by (simp add: frac_le)
  qed

  have \<open>coupling_Q v \<le> 
          u_pulse * (v_max + v_pulse) / (1 + v_min^2) +
          v_pulse * (u_max + u_pulse) / (1 + u_min^2)\<close>
    using Q_eq term1_bound term2_bound 
    by linarith
  also have \<open>... = M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    unfolding M_sharp_scalar_def 
    by simp
  finally have \<open>coupling_Q v \<le> M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close> .

  with abs_Q show ?thesis 
    by simp
qed


text \<open>The Lyapunov decrease estimate.\<close>

lemma V_pulse_decrease_crude:
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes u_min u_max v_min v_max \<delta> :: real
  assumes u_bounds: \<open>u_min \<le> vec_nth v 0\<close> \<open>vec_nth v 0 \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v 1\<close> \<open>vec_nth v 1 \<le> v_max\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes \<delta>_bound: \<open>\<delta> \<le> 2 - M_crude u_min u_max v_min v_max\<close>
  shows \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
         (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) 
         \<le> -\<delta> * V_pulse v\<close>
proof -
  have lie_eq: 
    \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
     (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) =
     -2 * V_pulse v - 
     (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<close>
    using V_pulse_lie_derivative_symbolic[OF \<beta>_eq \<gamma>_eq] .

  have am_gm: \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> \<le> V_pulse v\<close>
  proof -
    have \<open>2 * \<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> \<le>
          (vec_nth v 0 - u_pulse)^2 + (vec_nth v 1 - v_pulse)^2\<close>
      by (metis (no_types, opaque_lifting) abs_mult more_arith_simps(11) power2_abs   
                sum_squares_bound) 
    thus ?thesis
      by (simp add: V_pulse_def)
  qed

  have Q_bound: \<open>\<bar>coupling_Q v\<bar> \<le> M_crude u_min u_max v_min v_max\<close>
    using coupling_Q_bound_crude[OF u_bounds v_bounds] .

  have cross_term_bound: 
    \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<bar> \<le>
      V_pulse v * M_crude u_min u_max v_min v_max\<close>
  proof -
    have \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<bar>
          = \<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> * \<bar>coupling_Q v\<bar>\<close>
      by (simp add: abs_mult)
    also have \<open>\<dots> \<le> V_pulse v * M_crude u_min u_max v_min v_max\<close>
      using am_gm Q_bound V_pulse_nn by (simp add: mult_mono)
    finally show ?thesis .
  qed

  have cross_term_signed: 
    \<open>-(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v \<le>
      V_pulse v * M_crude u_min u_max v_min v_max\<close>
    using cross_term_bound
    by linarith

  have \<open>-2 * V_pulse v - 
        (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v
        \<le> -2 * V_pulse v + V_pulse v * M_crude u_min u_max v_min v_max\<close>
    using cross_term_signed 
    by linarith
  also have \<open>\<dots> = -(2 - M_crude u_min u_max v_min v_max) * V_pulse v\<close>
    by (simp add: algebra_simps)
  also have \<open>\<dots> \<le> -\<delta> * V_pulse v\<close>
    using \<delta>_bound V_pulse_nn 
    by (metis landau_o.R_mult_right_mono more_arith_simps(1))
  finally show ?thesis
    using lie_eq 
    by simp
qed

lemma V_pulse_decrease_sharp:
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes u_min u_max v_min v_max \<delta> :: real
  assumes u_min_nn: \<open>0 \<le> u_min\<close>
  assumes v_min_nn: \<open>0 \<le> v_min\<close>
  assumes u_bounds: \<open>u_min \<le> vec_nth v 0\<close> \<open>vec_nth v 0 \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v 1\<close> \<open>vec_nth v 1 \<le> v_max\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes \<delta>_bound: \<open>\<delta> \<le> 2 - M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
  shows \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
         (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) \<le> 
          -\<delta> * V_pulse v\<close>
proof -
  have lie_eq: 
    \<open>(vec_nth v 0 - u_pulse) * (\<alpha>_low / (1 + (vec_nth v 1)^2) - vec_nth v 0) +
     (vec_nth v 1 - v_pulse) * (\<alpha>_base / (1 + (vec_nth v 0)^2) - vec_nth v 1) =
     -2 * V_pulse v - 
     (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<close>
    using V_pulse_lie_derivative_symbolic[OF \<beta>_eq \<gamma>_eq] .

  have am_gm: \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> \<le> V_pulse v\<close>
  proof -
    have \<open>2 * \<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> \<le>
           (vec_nth v 0 - u_pulse)^2 + (vec_nth v 1 - v_pulse)^2\<close>
      by (metis (no_types, opaque_lifting) abs_mult more_arith_simps(11) 
                power2_abs sum_squares_bound)
    thus ?thesis
      by (simp add: V_pulse_def)
  qed

  have Q_bound: \<open>\<bar>coupling_Q v\<bar> \<le> M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using coupling_Q_bound_sharp[OF \<beta>_eq \<gamma>_eq u_min_nn v_min_nn u_bounds v_bounds] .

  have cross_term_bound: 
    \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<bar> \<le>
      V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
  proof -
    have \<open>\<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v\<bar> =
          \<bar>(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse)\<bar> * \<bar>coupling_Q v\<bar>\<close>
      by (simp add: abs_mult)
    also have \<open>... \<le> V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
      using am_gm Q_bound V_pulse_nn 
      by (simp add: mult_mono)
    finally show ?thesis .
  qed

  have cross_term_signed: 
    \<open>-(vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v \<le>
      V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using cross_term_bound
    by linarith

  have \<open>-2 * V_pulse v - 
        (vec_nth v 0 - u_pulse) * (vec_nth v 1 - v_pulse) * coupling_Q v \<le>
         -2 * V_pulse v + V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using cross_term_signed 
    by linarith
  also have \<open>... = -(2 - M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max) * V_pulse v\<close>
    by (simp add: algebra_simps)
  also have \<open>... \<le> -\<delta> * V_pulse v\<close>
    using \<delta>_bound V_pulse_nn 
    by (metis landau_o.R_mult_right_mono more_arith_simps(1))
  finally show ?thesis
    using lie_eq by simp
qed

end  (* gardner_pulse_params *)


subsection \<open>Trapping region R\_A\<close>

locale gardner_R_A_params = gardner_baseline_params +
  fixes u_A_lo u_A_hi v_A_lo v_A_hi :: real
  assumes u_A_ordered: \<open>u_A_lo < u_A_hi\<close>
  assumes v_A_ordered: \<open>v_A_lo < v_A_hi\<close>
  assumes u_A_positive: \<open>0 < u_A_lo\<close>
  assumes v_A_positive: \<open>0 < v_A_lo\<close>
  \<comment> \<open>Edge conditions in scalar form, without vector quantification\<close>
  assumes R_A_left_edge_inward: 
    \<open>\<And>v_val. v_A_lo \<le> v_val \<Longrightarrow> v_val \<le> v_A_hi \<Longrightarrow>
             0 < \<alpha>_base / (1 + v_val^\<beta>) - u_A_lo\<close>
  assumes R_A_right_edge_inward:
    \<open>\<And>v_val. v_A_lo \<le> v_val \<Longrightarrow> v_val \<le> v_A_hi \<Longrightarrow>
             \<alpha>_base / (1 + v_val^\<beta>) - u_A_hi < 0\<close>
  assumes R_A_bottom_edge_inward:
    \<open>\<And>u_val. u_A_lo \<le> u_val \<Longrightarrow> u_val \<le> u_A_hi \<Longrightarrow>
             0 < \<alpha>_base / (1 + u_val^\<gamma>) - v_A_lo\<close>
  assumes R_A_top_edge_inward:
    \<open>\<And>u_val. u_A_lo \<le> u_val \<Longrightarrow> u_val \<le> u_A_hi \<Longrightarrow>
             \<alpha>_base / (1 + u_val^\<gamma>) - v_A_hi < 0\<close>
begin

definition in_R_A :: 
  \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> bool\<close> where
  \<open>in_R_A v \<longleftrightarrow> u_A_lo \<le> vec_nth v 0 \<and> vec_nth v 0 \<le> u_A_hi \<and>
                v_A_lo \<le> vec_nth v 1 \<and> vec_nth v 1 \<le> v_A_hi\<close>

lemma R_A_forward_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_baseline_field \<alpha>_base \<beta> \<gamma>)) {0..t} UNIV\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes y0_in_R_A: \<open>in_R_A (y 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_A (y \<tau>)\<close>
proof -
  (* We define lo and hi functions for DI_rectangle_box_partial *)
  define lo :: \<open>'p \<Rightarrow> real\<close> where
    \<open>lo = (\<lambda>i. if i = 0 then u_A_lo 
               else if i = 1 then v_A_lo 
               else vec_nth (y 0) i)\<close>
  define hi :: \<open>'p \<Rightarrow> real\<close> where
    \<open>hi = (\<lambda>i. if i = 0 then u_A_hi 
               else if i = 1 then v_A_hi 
               else vec_nth (y 0) i)\<close>
  define active :: \<open>'p set\<close> where
    \<open>active = {0, 1}\<close>

  (* Initial condition: y 0 respects lo and hi *)
  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'p
    show \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof (cases \<open>i = 0\<close>)
      case True
      with y0_in_R_A show ?thesis 
        unfolding in_R_A_def lo_def hi_def by simp
    next
      case False
      show ?thesis
      proof (cases \<open>i = 1\<close>)
        case True
        with y0_in_R_A \<open>i \<noteq> 0\<close> show ?thesis 
          unfolding in_R_A_def lo_def hi_def by simp
      next
        case False
        with \<open>i \<noteq> 0\<close> show ?thesis 
          unfolding lo_def hi_def by simp
      qed
    qed
  qed

  (* active coordinates are strictly ordered *)
  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'p assume \<open>i \<in> active\<close>
    hence \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>lo i < hi i\<close>
    proof
      assume \<open>i = 0\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using u_A_ordered by simp
    next
      assume \<open>i = 1\<close>
      thus \<open>lo i < hi i\<close> 
        unfolding lo_def hi_def 
        using v_A_ordered by simp
    qed
  qed

  (* Lower edge inward for active coordinates *)
  have lower_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
  proof -
    fix i :: 'p and v :: \<open>(real, 'p) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>
    from i_act have \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
    proof
      assume i_eq: \<open>i = 0\<close>
      (* vec_nth v 0 = u_A_lo, and v's coordinate 1 is in [v_A_lo, v_A_hi] *)
      have v0_eq: \<open>vec_nth v 0 = u_A_lo\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have v1_lo: \<open>v_A_lo \<le> vec_nth v 1\<close>
        using bounds[of 1] unfolding lo_def by simp
      have v1_hi: \<open>vec_nth v 1 \<le> v_A_hi\<close>
        using bounds[of 1] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
              \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_A_lo\<close>
        using v0_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
           \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_A_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_A_left_edge_inward[OF v1_lo v1_hi] by simp
    next
      assume i_eq: \<open>i = 1\<close>
      have v1_eq: \<open>vec_nth v 1 = v_A_lo\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have v0_lo: \<open>u_A_lo \<le> vec_nth v 0\<close>
        using bounds[of 0] unfolding lo_def by simp
      have v0_hi: \<open>vec_nth v 0 \<le> u_A_hi\<close>
        using bounds[of 0] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
              \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_A_lo\<close>
        using v1_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
           \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_A_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_A_bottom_edge_inward[OF v0_lo v0_hi] by simp
    qed
  qed

  (* Upper edge inward for active coordinates *)
  have upper_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
  proof -
    fix i :: 'p and v :: \<open>(real, 'p) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>
    from i_act have \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
    proof
      assume i_eq: \<open>i = 0\<close>
      have v0_eq: \<open>vec_nth v 0 = u_A_hi\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have v1_lo: \<open>v_A_lo \<le> vec_nth v 1\<close>
        using bounds[of 1] unfolding lo_def by simp
      have v1_hi: \<open>vec_nth v 1 \<le> v_A_hi\<close>
        using bounds[of 1] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
              \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_A_hi\<close>
        using v0_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
           \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_A_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_A_right_edge_inward[OF v1_lo v1_hi] by simp
    next
      assume i_eq: \<open>i = 1\<close>
      have v1_eq: \<open>vec_nth v 1 = v_A_hi\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have v0_lo: \<open>u_A_lo \<le> vec_nth v 0\<close>
        using bounds[of 0] unfolding lo_def by simp
      have v0_hi: \<open>vec_nth v 0 \<le> u_A_hi\<close>
        using bounds[of 0] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
              \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_A_hi\<close>
        using v1_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
           \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_A_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_A_top_edge_inward[OF v0_lo v0_hi] by simp
    qed
  qed

  (* Inactive coordinates are maintained: the field is 0 for i \<notin> {0,1}, so the 
     trajectory's i-component is constant at its initial value *)
  have inactive_maint: 
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'p and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    from i_inact have i_ne: \<open>i \<noteq> 0\<close> \<open>i \<noteq> 1\<close> unfolding active_def by auto

    (* The i-th component of the field is 0 for this i *)
    have field_zero: \<open>\<And>\<tau>' v. vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
    proof -
      fix \<tau>' :: real and v :: \<open>(real, 'p) vec\<close>
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
        unfolding gardner_baseline_field_def 
        using i_ne by (simp add: fun_upd_def)
    qed

    (* We extract y's vderiv from the ODE *)
    have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>))) {0..t}\<close>
      using y_sol by (simp add: solves_ode_def)

    (* The i-th coordinate function (\<lambda>\<tau>. vec_nth (y \<tau>) i) has vderiv 0 *)
    have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
    proof -
      have \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on 
             (\<lambda>\<tau>. vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>)) i)) {0..t}\<close>
      proof -
        have step1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_vector_derivative (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using y_vderiv unfolding has_vderiv_on_def by blast
        have step2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_derivative (\<lambda>h. h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using step1 unfolding has_vector_derivative_def by blast
        have step3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
              (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
               (at \<tau>' within {0..t})\<close>
        proof -
          fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..t}\<close>
          have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
            by (rule has_derivative_vec_nth)
          show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                 (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
                   (at \<tau>' within {0..t})\<close>
            using has_derivative_compose[OF step2[OF \<tau>'_in] proj] by simp
        qed
        show ?thesis
          unfolding has_vderiv_on_def has_vector_derivative_def
          using step3 by simp
      qed
      thus ?thesis
        using field_zero by simp
    qed

    (* So vec_nth (y \<tau>) i = vec_nth (y 0) i *)
    have const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
      using has_vderiv_on_zero_imp_constant[OF yi_vderiv t_nn \<tau>_in_t] .

    (* And lo i = hi i = vec_nth (y 0) i for inactive coords *)
    show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      using i_ne const unfolding lo_def hi_def by simp
  qed

  (* We apply DI_rectangle_box_partial *)
  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
                     lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF t_nn y_sol iv active_ord 
                                       lower_edge upper_edge inactive_maint]
    by blast

  show \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_A (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have h0: \<open>lo 0 \<le> vec_nth (y \<tau>) 0 \<and> vec_nth (y \<tau>) 0 \<le> hi 0\<close>
      using main[OF \<tau>_in, of 0] .
    have h1: \<open>lo 1 \<le> vec_nth (y \<tau>) 1 \<and> vec_nth (y \<tau>) 1 \<le> hi 1\<close>
      using main[OF \<tau>_in, of 1] .
    show \<open>in_R_A (y \<tau>)\<close>
      using h0 h1 unfolding in_R_A_def lo_def hi_def 
      by simp
  qed
qed
end  (* gardner_R_A_params *)


subsection \<open>Trapping region R\_B\<close>

locale gardner_R_B_params = gardner_baseline_params +
  fixes u_B_lo u_B_hi v_B_lo v_B_hi :: real
  assumes u_B_ordered: \<open>u_B_lo < u_B_hi\<close>
  assumes v_B_ordered: \<open>v_B_lo < v_B_hi\<close>
  assumes u_B_positive: \<open>0 < u_B_lo\<close>
  assumes v_B_positive: \<open>0 < v_B_lo\<close>
  \<comment> \<open>Edge conditions in scalar form, as in gardner\_R\_A\_params\<close>
  assumes R_B_left_edge_inward: 
    \<open>\<And>v_val. v_B_lo \<le> v_val \<Longrightarrow> v_val \<le> v_B_hi \<Longrightarrow>
             0 < \<alpha>_base / (1 + v_val^\<beta>) - u_B_lo\<close>
  assumes R_B_right_edge_inward:
    \<open>\<And>v_val. v_B_lo \<le> v_val \<Longrightarrow> v_val \<le> v_B_hi \<Longrightarrow>
             \<alpha>_base / (1 + v_val^\<beta>) - u_B_hi < 0\<close>
  assumes R_B_bottom_edge_inward:
    \<open>\<And>u_val. u_B_lo \<le> u_val \<Longrightarrow> u_val \<le> u_B_hi \<Longrightarrow>
             0 < \<alpha>_base / (1 + u_val^\<gamma>) - v_B_lo\<close>
  assumes R_B_top_edge_inward:
    \<open>\<And>u_val. u_B_lo \<le> u_val \<Longrightarrow> u_val \<le> u_B_hi \<Longrightarrow>
             \<alpha>_base / (1 + u_val^\<gamma>) - v_B_hi < 0\<close>
begin

definition in_R_B :: 
  \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec \<Rightarrow> bool\<close> where
  \<open>in_R_B v \<longleftrightarrow> u_B_lo \<le> vec_nth v 0 \<and> vec_nth v 0 \<le> u_B_hi \<and>
                v_B_lo \<le> vec_nth v 1 \<and> vec_nth v 1 \<le> v_B_hi\<close>

lemma R_B_forward_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_baseline_field \<alpha>_base \<beta> \<gamma>)) {0..t} UNIV\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes y0_in_R_B: \<open>in_R_B (y 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_B (y \<tau>)\<close>
proof -
  define lo :: \<open>'p \<Rightarrow> real\<close> where
    \<open>lo = (\<lambda>i. if i = 0 then u_B_lo 
               else if i = 1 then v_B_lo 
               else vec_nth (y 0) i)\<close>
  define hi :: \<open>'p \<Rightarrow> real\<close> where
    \<open>hi = (\<lambda>i. if i = 0 then u_B_hi 
               else if i = 1 then v_B_hi 
               else vec_nth (y 0) i)\<close>
  define active :: \<open>'p set\<close> where
    \<open>active = {0, 1}\<close>

  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'p
    show \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof (cases \<open>i = 0\<close>)
      case True
      with y0_in_R_B show ?thesis 
        unfolding in_R_B_def lo_def hi_def 
        by simp
    next
      case False
      show ?thesis
      proof (cases \<open>i = 1\<close>)
        case True
        with y0_in_R_B \<open>i \<noteq> 0\<close> show ?thesis 
          unfolding in_R_B_def lo_def hi_def 
          by simp
      next
        case False
        with \<open>i \<noteq> 0\<close> show ?thesis 
          unfolding lo_def hi_def 
          by simp
      qed
    qed
  qed

  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'p assume \<open>i \<in> active\<close>
    hence \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>lo i < hi i\<close>
    proof
      assume \<open>i = 0\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using u_B_ordered by simp
    next
      assume \<open>i = 1\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using v_B_ordered by simp
    qed
  qed

  have lower_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
  proof -
    fix i :: 'p and v :: \<open>(real, 'p) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>
    from i_act have \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
    proof
      assume i_eq: \<open>i = 0\<close>
      have v0_eq: \<open>vec_nth v 0 = u_B_lo\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have v1_lo: \<open>v_B_lo \<le> vec_nth v 1\<close>
        using bounds[of 1] unfolding lo_def by simp
      have v1_hi: \<open>vec_nth v 1 \<le> v_B_hi\<close>
        using bounds[of 1] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
              \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_B_lo\<close>
        using v0_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
           \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_B_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_B_left_edge_inward[OF v1_lo v1_hi] by simp
    next
      assume i_eq: \<open>i = 1\<close>
      have v1_eq: \<open>vec_nth v 1 = v_B_lo\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have v0_lo: \<open>u_B_lo \<le> vec_nth v 0\<close>
        using bounds[of 0] unfolding lo_def by simp
      have v0_hi: \<open>vec_nth v 0 \<le> u_B_hi\<close>
        using bounds[of 0] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
              \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_B_lo\<close>
        using v1_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
           \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_B_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_B_bottom_edge_inward[OF v0_lo v0_hi] 
        by simp
    qed
  qed

  have upper_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
  proof -
    fix i :: 'p and v :: \<open>(real, 'p) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>
    from i_act have \<open>i = 0 \<or> i = 1\<close> unfolding active_def by blast
    thus \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
    proof
      assume i_eq: \<open>i = 0\<close>
      have v0_eq: \<open>vec_nth v 0 = u_B_hi\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have v1_lo: \<open>v_B_lo \<le> vec_nth v 1\<close>
        using bounds[of 1] unfolding lo_def by simp
      have v1_hi: \<open>vec_nth v 1 \<le> v_B_hi\<close>
        using bounds[of 1] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
              \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_B_hi\<close>
        using v0_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 0 = 
           \<alpha>_base / (1 + (vec_nth v 1)^\<beta>) - u_B_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_B_right_edge_inward[OF v1_lo v1_hi] by simp
    next
      assume i_eq: \<open>i = 1\<close>
      have v1_eq: \<open>vec_nth v 1 = v_B_hi\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have v0_lo: \<open>u_B_lo \<le> vec_nth v 0\<close>
        using bounds[of 0] unfolding lo_def by simp
      have v0_hi: \<open>vec_nth v 0 \<le> u_B_hi\<close>
        using bounds[of 0] unfolding hi_def by simp
      have \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
              \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1\<close>
        unfolding gardner_baseline_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_B_hi\<close>
        using v1_eq by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) 1 = 
           \<alpha>_base / (1 + (vec_nth v 0)^\<gamma>) - v_B_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_B_top_edge_inward[OF v0_lo v0_hi] by simp
    qed
  qed

  have inactive_maint: 
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'p and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    from i_inact have i_ne: \<open>i \<noteq> 0\<close> \<open>i \<noteq> 1\<close> unfolding active_def by auto

    have field_zero: \<open>\<And>\<tau>' v. vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
    proof -
      fix \<tau>' :: real and v :: \<open>(real, 'p) vec\<close>
      show \<open>vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
        unfolding gardner_baseline_field_def 
        using i_ne by (simp add: fun_upd_def)
    qed

    have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>))) {0..t}\<close>
      using y_sol by (simp add: solves_ode_def)

    have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
    proof -
      have \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on 
             (\<lambda>\<tau>. vec_nth (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>)) i)) {0..t}\<close>
      proof -
        have step1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_vector_derivative (gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using y_vderiv unfolding has_vderiv_on_def by blast
        have step2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_derivative (\<lambda>h. h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using step1 unfolding has_vector_derivative_def by blast
        have step3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
              (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
               (at \<tau>' within {0..t})\<close>
        proof -
          fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..t}\<close>
          have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
            by (rule has_derivative_vec_nth)
          show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                 (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
                   (at \<tau>' within {0..t})\<close>
            using has_derivative_compose[OF step2[OF \<tau>'_in] proj] by simp
        qed
        show ?thesis
          unfolding has_vderiv_on_def has_vector_derivative_def
          using step3 by simp
      qed
      thus ?thesis
        using field_zero by simp
    qed

    have const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
      using has_vderiv_on_zero_imp_constant[OF yi_vderiv t_nn \<tau>_in_t] .

    show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      using i_ne const unfolding lo_def hi_def by simp
  qed

  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
                     lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF t_nn y_sol iv active_ord 
                                       lower_edge upper_edge inactive_maint]
    by blast

  show \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_B (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have h0: \<open>lo 0 \<le> vec_nth (y \<tau>) 0 \<and> vec_nth (y \<tau>) 0 \<le> hi 0\<close>
      using main[OF \<tau>_in, of 0] .
    have h1: \<open>lo 1 \<le> vec_nth (y \<tau>) 1 \<and> vec_nth (y \<tau>) 1 \<le> hi 1\<close>
      using main[OF \<tau>_in, of 1] .
    show \<open>in_R_B (y \<tau>)\<close>
      using h0 h1 unfolding in_R_B_def lo_def hi_def by simp
  qed
qed

end  (* gardner_R_B_params *)


subsection \<open>Pulsed reachability via REACH\_lyapunov\<close>

locale gardner_pulse_lyapunov = gardner_pulse_params +
  fixes u_min u_max v_min v_max \<delta> :: real
  assumes region_ordered: \<open>u_min < u_max\<close> \<open>v_min < v_max\<close>
  assumes E_pulse_in_region: 
    \<open>u_min \<le> u_pulse\<close> \<open>u_pulse \<le> u_max\<close>
    \<open>v_min \<le> v_pulse\<close> \<open>v_pulse \<le> v_max\<close>
  assumes u_min_nn: \<open>0 \<le> u_min\<close>
  assumes v_min_nn: \<open>0 \<le> v_min\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes \<delta>_bound: \<open>\<delta> \<le> 2 - M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
begin

lemma pulse_trajectory_exponential_decay:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes \<Delta>t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..\<Delta>t} UNIV\<close>
  assumes \<Delta>t_nn: \<open>0 \<le> \<Delta>t\<close>
  assumes y_in_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow> 
         u_min \<le> vec_nth (y \<tau>) 0 \<and> vec_nth (y \<tau>) 0 \<le> u_max \<and>
         v_min \<le> vec_nth (y \<tau>) 1 \<and> vec_nth (y \<tau>) 1 \<le> v_max\<close>
  shows \<open>V_pulse (y \<Delta>t) \<le> V_pulse (y 0) * exp (-\<delta> * \<Delta>t)\<close>
proof -
    have rate_bound: \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow> 
                        (vec_nth (y \<tau>) 0 - u_pulse) * 
                          (\<alpha>_low / (1 + (vec_nth (y \<tau>) 1)^2) - vec_nth (y \<tau>) 0) +
                        (vec_nth (y \<tau>) 1 - v_pulse) * 
                          (\<alpha>_base / (1 + (vec_nth (y \<tau>) 0)^2) - vec_nth (y \<tau>) 1) 
                        \<le> -\<delta> * V_pulse (y \<tau>)\<close>
    proof -
      fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..\<Delta>t}\<close>
      have region: \<open>u_min \<le> vec_nth (y \<tau>) 0\<close> \<open>vec_nth (y \<tau>) 0 \<le> u_max\<close>
        \<open>v_min \<le> vec_nth (y \<tau>) 1\<close> \<open>vec_nth (y \<tau>) 1 \<le> v_max\<close>
        using y_in_region[OF \<tau>_in] by auto
      show \<open>(vec_nth (y \<tau>) 0 - u_pulse) * 
            (\<alpha>_low / (1 + (vec_nth (y \<tau>) 1)^2) - vec_nth (y \<tau>) 0) +
          (vec_nth (y \<tau>) 1 - v_pulse) * 
            (\<alpha>_base / (1 + (vec_nth (y \<tau>) 0)^2) - vec_nth (y \<tau>) 1) 
          \<le> -\<delta> * V_pulse (y \<tau>)\<close>
        using V_pulse_decrease_sharp[OF \<beta>_eq \<gamma>_eq u_min_nn v_min_nn 
            region \<delta>_pos \<delta>_bound] .
    qed
    have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
                       \<exists>DV. (V_pulse has_derivative DV) (at (y \<tau>)) \<and>
                            DV (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
    proof (rule induct_step_from_lie[where V = V_pulse and 
                                           f = \<open>gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                           y = y and
                                           lin = \<open>\<lambda>\<tau> w. (vec_nth (y \<tau>) 0 - u_pulse) * vec_nth w 0 +
                                                        (vec_nth (y \<tau>) 1 - v_pulse) * vec_nth w 1\<close> 
                                                           and
                                           bnd = \<open>\<lambda>\<tau>. -\<delta> * V_pulse (y \<tau>)\<close> and T = \<Delta>t])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
          (V_pulse has_derivative
            (\<lambda>w. (vec_nth (y \<tau>) 0 - u_pulse) * vec_nth w 0 +
                 (vec_nth (y \<tau>) 1 - v_pulse) * vec_nth w 1)) (at (y \<tau>))\<close>
      using V_pulse_has_derivative by blast
  next
    show \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
          (\<lambda>w. (vec_nth (y \<tau>) 0 - u_pulse) * vec_nth w 0 +
               (vec_nth (y \<tau>) 1 - v_pulse) * vec_nth w 1)
            (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
    proof -
      fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..\<Delta>t}\<close>
      have lie: \<open>(\<lambda>w. (vec_nth (y \<tau>) 0 - u_pulse) * vec_nth w 0 +
                      (vec_nth (y \<tau>) 1 - v_pulse) * vec_nth w 1)
                   (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) =
                   (vec_nth (y \<tau>) 0 - u_pulse) *
                     (\<alpha>_low / (1 + (vec_nth (y \<tau>) 1)^2) - vec_nth (y \<tau>) 0) +
                   (vec_nth (y \<tau>) 1 - v_pulse) *
                     (\<alpha>_base / (1 + (vec_nth (y \<tau>) 0)^2) - vec_nth (y \<tau>) 1)\<close>
        unfolding gardner_pulse_field_def
        by (simp add: fun_upd_def \<beta>_eq \<gamma>_eq)
      show \<open>(\<lambda>w.(vec_nth (y \<tau>) 0 - u_pulse) * vec_nth w 0 + 
                (vec_nth (y \<tau>) 1 - v_pulse) * vec_nth w 1)
                (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
        using rate_bound[OF h\<tau>] lie by simp
    qed
  qed

  show ?thesis
    using REACH_lyapunov[where V = V_pulse and \<delta> = \<delta>,
                         OF y_sol \<Delta>t_nn induct_step]
    by simp
qed

lemma pulse_trajectory_reaches_sublevel:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes \<Delta>t L :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..\<Delta>t} UNIV\<close>
  assumes \<Delta>t_nn: \<open>0 \<le> \<Delta>t\<close>
  assumes y_in_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow> 
         u_min \<le> vec_nth (y \<tau>) 0 \<and> vec_nth (y \<tau>) 0 \<le> u_max \<and>
         v_min \<le> vec_nth (y \<tau>) 1 \<and> vec_nth (y \<tau>) 1 \<le> v_max\<close>
  assumes L_reached: \<open>V_pulse (y 0) * exp (-\<delta> * \<Delta>t) \<le> L\<close>
  shows \<open>V_pulse (y \<Delta>t) \<le> L\<close>
proof -
  have \<open>V_pulse (y \<Delta>t) \<le> V_pulse (y 0) * exp (-\<delta> * \<Delta>t)\<close>
    using pulse_trajectory_exponential_decay[OF y_sol \<Delta>t_nn y_in_region] .
  also have \<open>\<dots> \<le> L\<close>
    using L_reached .
  finally show ?thesis .
qed

end  (* gardner_pulse_lyapunov *)


subsection \<open>Final induced switching theorem\<close>

locale gardner_induced_switching = 
  gardner_R_A_params + gardner_R_B_params + gardner_pulse_lyapunov +
  fixes type1_witness :: \<open>'p::{finite, linordered_nonzero_semiring} itself\<close>
  fixes L_target :: real
  assumes sublevel_in_R_B: 
    \<open>\<And>v :: (real, 'p) vec. V_pulse v \<le> L_target \<Longrightarrow> in_R_B v\<close>
begin

theorem induced_switching:
  fixes y1 y2 y3 :: \<open>real \<Rightarrow> (real, 'p) vec\<close>
  fixes t_start t_end T :: real
  assumes y1_sol: \<open>(y1 solves_ode (gardner_baseline_field \<alpha>_base \<beta> \<gamma>)) 
                     {0..t_start} UNIV\<close>
  assumes y2_sol: \<open>(y2 solves_ode (gardner_pulse_field \<alpha>_base \<alpha>_low \<beta> \<gamma>)) 
                     {0..(t_end - t_start)} UNIV\<close>
  assumes y3_sol: \<open>(y3 solves_ode (gardner_baseline_field \<alpha>_base \<beta> \<gamma>)) 
                     {0..(T - t_end)} UNIV\<close>
  assumes glue1: \<open>y2 0 = y1 t_start\<close>
  assumes glue2: \<open>y3 0 = y2 (t_end - t_start)\<close>
  assumes t_start_nn: \<open>0 \<le> t_start\<close>
  assumes t_end_after_start: \<open>t_start \<le> t_end\<close>
  assumes T_after_end: \<open>t_end \<le> T\<close>
  assumes y1_starts_in_R_A: \<open>in_R_A (y1 0)\<close>
  assumes y2_stays_in_lyapunov_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..(t_end - t_start)} \<Longrightarrow>
         u_min \<le> vec_nth (y2 \<tau>) 0 \<and> vec_nth (y2 \<tau>) 0 \<le> u_max \<and>
         v_min \<le> vec_nth (y2 \<tau>) 1 \<and> vec_nth (y2 \<tau>) 1 \<le> v_max\<close>
  assumes pulse_long_enough: 
    \<open>V_pulse (y2 0) * exp (-\<delta> * (t_end - t_start)) \<le> L_target\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> in_R_B (y3 \<tau>)\<close>
proof -
  have y1_in_R_A: \<open>\<And>\<tau>. \<tau> \<in> {0..t_start} \<Longrightarrow> in_R_A (y1 \<tau>)\<close>
    using R_A_forward_invariant[OF y1_sol t_start_nn y1_starts_in_R_A] .

  have y1_end_in_R_A: \<open>in_R_A (y1 t_start)\<close>
    using y1_in_R_A[of t_start] t_start_nn by simp

  have y2_starts_in_R_A: \<open>in_R_A (y2 0)\<close>
    using glue1 y1_end_in_R_A by simp

  have \<Delta>t_nn: \<open>0 \<le> t_end - t_start\<close>
    using t_end_after_start by simp

  have y2_reaches_sublevel: \<open>V_pulse (y2 (t_end - t_start)) \<le> L_target\<close>
    using pulse_trajectory_reaches_sublevel[OF y2_sol \<Delta>t_nn 
                                               y2_stays_in_lyapunov_region 
                                               pulse_long_enough] .

  have y2_end_in_R_B: \<open>in_R_B (y2 (t_end - t_start))\<close>
    using sublevel_in_R_B[OF y2_reaches_sublevel] .

  have y3_starts_in_R_B: \<open>in_R_B (y3 0)\<close>
    using glue2 y2_end_in_R_B by simp

  have T_end_nn: \<open>0 \<le> T - t_end\<close>
    using T_after_end by simp

  show \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> in_R_B (y3 \<tau>)\<close>
    using R_B_forward_invariant[OF y3_sol T_end_nn y3_starts_in_R_B] .
qed

end  (* gardner_induced_switching *)

subsection \<open>Concrete Gardner instantiation\<close>

subsubsection \<open>Parameter values\<close>

text \<open>
  The concrete parameter values, in this order: the baseline production
  rate alpha\_base; the pulse parameters alpha\_low, u\_pulse and v\_pulse;
  the Hill coefficients beta and gamma; the bounds of the trapping region
  R\_A (high u, low v) and of R\_B (low u, high v); the bounds and decay
  rate delta used by the pulse Lyapunov argument; and the sublevel target
  L\_target for containment in R\_B.  Every definition is collected in
  gardner\_conc\_defs.
\<close>

named_theorems gardner_conc_defs
definition \<alpha>_base_val :: real where [gardner_conc_defs]: \<open>\<alpha>_base_val = 51/16\<close>

definition \<alpha>_low_val :: real where [gardner_conc_defs]: \<open>\<alpha>_low_val = 5/2\<close>
definition u_pulse_val :: real where [gardner_conc_defs]: \<open>u_pulse_val = 1/4\<close>
definition v_pulse_val :: real where [gardner_conc_defs]: \<open>v_pulse_val = 3\<close>

definition \<beta>_val :: nat where [gardner_conc_defs]: \<open>\<beta>_val = 2\<close>
definition \<gamma>_val :: nat where [gardner_conc_defs]: \<open>\<gamma>_val = 2\<close>

definition u_A_lo_val :: real where [gardner_conc_defs]: \<open>u_A_lo_val = 2\<close>
definition u_A_hi_val :: real where [gardner_conc_defs]: \<open>u_A_hi_val = 7/2\<close>
definition v_A_lo_val :: real where [gardner_conc_defs]: \<open>v_A_lo_val = 1/10 \<close> 
definition v_A_hi_val :: real where [gardner_conc_defs]: \<open>v_A_hi_val = 7/10\<close>    

definition u_B_lo_val :: real where [gardner_conc_defs]: \<open>u_B_lo_val = 1/10\<close>
definition u_B_hi_val :: real where [gardner_conc_defs]: \<open>u_B_hi_val = 7/10\<close>
definition v_B_lo_val :: real where [gardner_conc_defs]: \<open>v_B_lo_val = 2\<close>
definition v_B_hi_val :: real where [gardner_conc_defs]: \<open>v_B_hi_val = 7/2\<close>

definition u_min_val :: real where [gardner_conc_defs]: \<open>u_min_val = 1/4\<close>
definition u_max_val :: real where [gardner_conc_defs]: \<open>u_max_val = 5/16\<close>
definition v_min_val :: real where [gardner_conc_defs]: \<open>v_min_val = 5/2\<close>
definition v_max_val :: real where [gardner_conc_defs]:\<open>v_max_val = 7/2\<close>
definition \<delta>_val :: real where [gardner_conc_defs]: \<open>\<delta>_val = 1/8\<close>

definition L_target_val :: real where [gardner_conc_defs]: \<open>L_target_val = 1/100\<close>


subsubsection \<open>Baseline parameters interpretation\<close>

interpretation concrete_baseline:
  gardner_baseline_params \<alpha>_base_val \<beta>_val \<gamma>_val
proof
  show \<open>2 < \<alpha>_base_val\<close>
    unfolding \<alpha>_base_val_def by simp
  show \<open>1 \<le> \<beta>_val\<close>
    unfolding \<beta>_val_def by simp
  show \<open>1 \<le> \<gamma>_val\<close>
    unfolding \<gamma>_val_def by simp
qed


subsubsection \<open>Pulse parameters interpretation\<close>

interpretation concrete_pulse:
  gardner_pulse_params \<alpha>_base_val \<beta>_val \<gamma>_val \<alpha>_low_val u_pulse_val v_pulse_val
proof 
 
  show \<open>0 < \<alpha>_low_val\<close>
    unfolding \<alpha>_low_val_def by simp
  show \<open>\<alpha>_low_val < \<alpha>_base_val\<close>
    unfolding \<alpha>_low_val_def \<alpha>_base_val_def by simp
  show \<open>0 < u_pulse_val\<close>
    unfolding u_pulse_val_def by simp
  show \<open>0 < v_pulse_val\<close>
    unfolding v_pulse_val_def by simp
  show \<open>\<alpha>_low_val / (1 + v_pulse_val ^ \<beta>_val) = u_pulse_val\<close>
    unfolding \<alpha>_low_val_def v_pulse_val_def \<beta>_val_def u_pulse_val_def by simp
  show \<open>\<alpha>_base_val / (1 + u_pulse_val ^ \<gamma>_val) = v_pulse_val\<close>
    unfolding \<alpha>_base_val_def u_pulse_val_def \<gamma>_val_def v_pulse_val_def 
    by (simp add: power2_eq_square)
qed

subsubsection \<open>R\_A trapping region interpretation\<close>

interpretation concrete_R_A:
  gardner_R_A_params \<alpha>_base_val \<beta>_val \<gamma>_val 
                     u_A_lo_val u_A_hi_val v_A_lo_val v_A_hi_val
proof
  show \<open>u_A_lo_val < u_A_hi_val\<close>
    unfolding u_A_lo_val_def u_A_hi_val_def by simp
  show \<open>v_A_lo_val < v_A_hi_val\<close>
    unfolding v_A_lo_val_def v_A_hi_val_def by simp
  show \<open>0 < u_A_lo_val\<close>
    unfolding u_A_lo_val_def by simp
  show \<open>0 < v_A_lo_val\<close>
    unfolding v_A_lo_val_def by simp

  (* Left edge: need 0 < \<alpha>_base / (1 + v^\<beta>) - u_A_lo for v \<in> [v_A_lo, v_A_hi]
     Since 1/(1+v²) is decreasing in v (for v \<ge> 0), the min of \<alpha>_base/(1+v²)
     over v \<in> [1/10, 7/10] occurs at v = v_A_hi = 7/10.
     At v = 7/10: (51/16) / (1 + 49/100) = (51/16) / (149/100) = 5100/2384 = 1275/596
     Need: 1275/596 > u_A_lo = 2, i.e., 1275 > 1192 *)
  show \<open>\<And>v_val. v_A_lo_val \<le> v_val \<Longrightarrow> v_val \<le> v_A_hi_val \<Longrightarrow>
                0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_lo_val\<close>
  proof -
    fix v_val :: real
    assume v_lo: \<open>v_A_lo_val \<le> v_val\<close> and v_hi: \<open>v_val \<le> v_A_hi_val\<close>
    have v_nn: \<open>0 \<le> v_val\<close> 
      using v_lo unfolding v_A_lo_val_def by simp
    have v_min_nn: \<open>0 \<le> v_A_lo_val\<close>
      unfolding v_A_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + v_A_hi_val^2) \<le> \<alpha>_base_val / (1 + v_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_A_lo_val and x_max = v_A_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>u_A_lo_val < \<alpha>_base_val / (1 + v_A_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def v_A_hi_val_def u_A_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_lo_val\<close>
      unfolding \<beta>_val_def by simp
  qed

  (* Right edge: need \<alpha>_base / (1 + v^\<beta>) - u_A_hi < 0 for v \<in> [v_A_lo, v_A_hi]
     Since 1/(1+v²) is decreasing, the max of \<alpha>_base/(1+v²) is at v = v_A_lo.
     At v = 1/10: (51/16)/(101/100) = 5100/1616 = 1275/404 \<approx> 3.156
     Need: 1275/404 < u_A_hi = 7/2 = 1414/404. So 1275 < 1414 *)
  show \<open>\<And>v_val. v_A_lo_val \<le> v_val \<Longrightarrow> v_val \<le> v_A_hi_val \<Longrightarrow>
                \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_hi_val < 0\<close>
  proof -
    fix v_val :: real
    assume v_lo: \<open>v_A_lo_val \<le> v_val\<close> and v_hi: \<open>v_val \<le> v_A_hi_val\<close>
    have v_min_nn: \<open>0 \<le> v_A_lo_val\<close>
      unfolding v_A_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + v_val^2) \<le> \<alpha>_base_val / (1 + v_A_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_A_lo_val and x_max = v_A_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + v_A_lo_val^2) < u_A_hi_val\<close>
      unfolding \<alpha>_base_val_def v_A_lo_val_def u_A_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_hi_val < 0\<close>
      unfolding \<beta>_val_def by simp
  qed

  (* Bottom edge: need 0 < \<alpha>_base / (1 + u^\<gamma>) - v_A_lo for u \<in> [u_A_lo, u_A_hi]
     Min of \<alpha>_base/(1+u²) at u = u_A_hi = 7/2.
     At u = 7/2: (51/16)/(1 + 49/4) = (51/16)/(53/4) = 51\<sqdot>4/(16\<sqdot>53) = 204/848 = 51/212
     Need: 51/212 > v_A_lo = 1/10, i.e., 510/2120 > 212/2120, *)
  show \<open>\<And>u_val. u_A_lo_val \<le> u_val \<Longrightarrow> u_val \<le> u_A_hi_val \<Longrightarrow>
                0 < \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_lo_val\<close>
  proof -
    fix u_val :: real
    assume u_lo: \<open>u_A_lo_val \<le> u_val\<close> and u_hi: \<open>u_val \<le> u_A_hi_val\<close>
    have u_min_nn: \<open>0 \<le> u_A_lo_val\<close>
      unfolding u_A_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + u_A_hi_val^2) \<le> \<alpha>_base_val / (1 + u_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_A_lo_val and x_max = u_A_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>v_A_lo_val < \<alpha>_base_val / (1 + u_A_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def u_A_hi_val_def v_A_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_lo_val\<close>
      unfolding \<gamma>_val_def by simp
  qed

  (* Top edge: need \<alpha>_base / (1 + u^\<gamma>) - v_A_hi < 0 for u \<in> [u_A_lo, u_A_hi]
     Max of \<alpha>_base/(1+u²) at u = u_A_lo = 2.
     At u = 2: (51/16)/(1 + 4) = (51/16)/5 = 51/80
     Need: 51/80 < v_A_hi = 7/10 = 56/80, *)
  show \<open>\<And>u_val. u_A_lo_val \<le> u_val \<Longrightarrow> u_val \<le> u_A_hi_val \<Longrightarrow>
                \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_hi_val < 0\<close>
  proof -
    fix u_val :: real
    assume u_lo: \<open>u_A_lo_val \<le> u_val\<close> and u_hi: \<open>u_val \<le> u_A_hi_val\<close>
    have u_min_nn: \<open>0 \<le> u_A_lo_val\<close>
      unfolding u_A_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + u_val^2) \<le> \<alpha>_base_val / (1 + u_A_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_A_lo_val and x_max = u_A_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + u_A_lo_val^2) < v_A_hi_val\<close>
      unfolding \<alpha>_base_val_def u_A_lo_val_def v_A_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_hi_val < 0\<close>
      unfolding \<gamma>_val_def by simp
  qed
qed


subsubsection \<open>R\_B trapping region interpretation\<close>

interpretation concrete_R_B:
  gardner_R_B_params \<alpha>_base_val \<beta>_val \<gamma>_val 
                     u_B_lo_val u_B_hi_val v_B_lo_val v_B_hi_val
proof
  show \<open>u_B_lo_val < u_B_hi_val\<close>
    unfolding u_B_lo_val_def u_B_hi_val_def by simp
  show \<open>v_B_lo_val < v_B_hi_val\<close>
    unfolding v_B_lo_val_def v_B_hi_val_def by simp
  show \<open>0 < u_B_lo_val\<close>
    unfolding u_B_lo_val_def by simp
  show \<open>0 < v_B_lo_val\<close>
    unfolding v_B_lo_val_def by simp

  (* Left edge: 0 < \<alpha>_base / (1 + v^\<beta>) - u_B_lo for v \<in> [v_B_lo, v_B_hi]
     Min of \<alpha>_base/(1+v²) at v = v_B_hi = 7/2.
     At v = 7/2: (51/16)/(1 + 49/4) = (51/16)/(53/4) = 51/(4\<sqdot>53) = 51/212
     Need: 51/212 > u_B_lo = 1/10, i.e., 510 > 212 *)
  show \<open>\<And>v_val. v_B_lo_val \<le> v_val \<Longrightarrow> v_val \<le> v_B_hi_val \<Longrightarrow>
                0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_B_lo_val\<close>
  proof -
    fix v_val :: real
    assume v_lo: \<open>v_B_lo_val \<le> v_val\<close> and v_hi: \<open>v_val \<le> v_B_hi_val\<close>
    have v_min_nn: \<open>0 \<le> v_B_lo_val\<close>
      unfolding v_B_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + v_B_hi_val^2) \<le> \<alpha>_base_val / (1 + v_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_B_lo_val and x_max = v_B_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>u_B_lo_val < \<alpha>_base_val / (1 + v_B_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def v_B_hi_val_def u_B_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_B_lo_val\<close>
      unfolding \<beta>_val_def by simp
  qed

  (* Right edge: \<alpha>_base / (1 + v^\<beta>) - u_B_hi < 0 for v \<in> [v_B_lo, v_B_hi]
     Max of \<alpha>_base/(1+v²) at v = v_B_lo = 2.
     At v = 2: (51/16)/(1 + 4) = (51/16)/5 = 51/80
     Need: 51/80 < u_B_hi = 7/10 = 56/80 *)
  show \<open>\<And>v_val. v_B_lo_val \<le> v_val \<Longrightarrow> v_val \<le> v_B_hi_val \<Longrightarrow>
                \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_B_hi_val < 0\<close>
  proof -
    fix v_val :: real
    assume v_lo: \<open>v_B_lo_val \<le> v_val\<close> and v_hi: \<open>v_val \<le> v_B_hi_val\<close>
    have v_min_nn: \<open>0 \<le> v_B_lo_val\<close>
      unfolding v_B_lo_val_def by simp
    have \<open>\<alpha>_base_val / (1 + v_val^2) \<le> \<alpha>_base_val / (1 + v_B_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_B_lo_val and x_max = v_B_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + v_B_lo_val^2) < u_B_hi_val\<close>
      unfolding \<alpha>_base_val_def v_B_lo_val_def u_B_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + v_val^\<beta>_val) - u_B_hi_val < 0\<close>
      unfolding \<beta>_val_def 
      by simp
  qed

  (* Bottom edge: 0 < \<alpha>_base / (1 + u^\<gamma>) - v_B_lo for u \<in> [u_B_lo, u_B_hi]
     Min of \<alpha>_base/(1+u²) at u = u_B_hi = 7/10.
     At u = 7/10: (51/16)/(1 + 49/100) = (51/16)/(149/100) = 5100/2384 = 1275/596
     Need: 1275/596 > v_B_lo = 2, i.e., 1275 > 1192 *)
  show \<open>\<And>u_val. u_B_lo_val \<le> u_val \<Longrightarrow> u_val \<le> u_B_hi_val \<Longrightarrow>
                0 < \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_B_lo_val\<close>
  proof -
    fix u_val :: real
    assume u_lo: \<open>u_B_lo_val \<le> u_val\<close> and u_hi: \<open>u_val \<le> u_B_hi_val\<close>
    have u_min_nn: \<open>0 \<le> u_B_lo_val\<close>
      unfolding u_B_lo_val_def 
      by simp
    have \<open>\<alpha>_base_val / (1 + u_B_hi_val^2) \<le> \<alpha>_base_val / (1 + u_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_B_lo_val and x_max = u_B_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>v_B_lo_val < \<alpha>_base_val / (1 + u_B_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def u_B_hi_val_def v_B_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_B_lo_val\<close>
      unfolding \<gamma>_val_def 
      by simp
  qed

  (* Top edge: \<alpha>_base / (1 + u^\<gamma>) - v_B_hi < 0 for u \<in> [u_B_lo, u_B_hi]
     Max of \<alpha>_base/(1+u²) at u = u_B_lo = 1/10.
     At u = 1/10: (51/16)/(1 + 1/100) = (51/16)/(101/100) = 5100/1616 = 1275/404
     Need: 1275/404 < v_B_hi = 7/2 = 1414/404, *)
  show \<open>\<And>u_val. u_B_lo_val \<le> u_val \<Longrightarrow> u_val \<le> u_B_hi_val \<Longrightarrow>
                \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_B_hi_val < 0\<close>
  proof -
    fix u_val :: real
    assume u_lo: \<open>u_B_lo_val \<le> u_val\<close> and u_hi: \<open>u_val \<le> u_B_hi_val\<close>
    have u_min_nn: \<open>0 \<le> u_B_lo_val\<close>
      unfolding u_B_lo_val_def 
      by simp
    have \<open>\<alpha>_base_val / (1 + u_val^2) \<le> \<alpha>_base_val / (1 + u_B_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_B_lo_val and x_max = u_B_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + u_B_lo_val^2) < v_B_hi_val\<close>
      unfolding \<alpha>_base_val_def u_B_lo_val_def v_B_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_B_hi_val < 0\<close>
      unfolding \<gamma>_val_def 
      by simp
  qed
qed
text \<open>
   Stage 3c: gardner\_pulse\_lyapunov interpretation.

   The substantive step is delta\_bound:
     1/8 <= 2 - M\_sharp(1/4, 5/16, 5/2, 7/2)

   Computing M\_sharp:
     M\_sharp = u\_pulse*(v\_max+v\_pulse)/(1+v\_min\textasciicircum{}2) +
               v\_pulse*(u\_max+u\_pulse)/(1+u\_min\textasciicircum{}2)
             = (1/4)*(7/2+3)/(1+25/4) + 3*(5/16+1/4)/(1+1/16)
             = (1/4)*(13/2)/(29/4) + 3*(9/16)/(17/16)
             = 13/58 + 27/17
             = 221/986 + 1566/986
             = 1787/986

   So 2 - M\_sharp = 185/986.
   Check: 1/8 <= 185/986 <=> 986 <= 8*185 = 1480
\<close>


subsubsection \<open>Pulse Lyapunov interpretation\<close>

interpretation concrete_pulse_lyapunov:
  gardner_pulse_lyapunov \<alpha>_base_val \<beta>_val \<gamma>_val \<alpha>_low_val u_pulse_val v_pulse_val
                        u_min_val u_max_val v_min_val v_max_val \<delta>_val
proof
  show \<open>u_min_val < u_max_val\<close>
    unfolding u_min_val_def u_max_val_def by simp
  show \<open>v_min_val < v_max_val\<close>
    unfolding v_min_val_def v_max_val_def by simp
  show \<open>u_min_val \<le> u_pulse_val\<close>
    unfolding u_min_val_def u_pulse_val_def by simp
  show \<open>u_pulse_val \<le> u_max_val\<close>
    unfolding u_pulse_val_def u_max_val_def by simp
  show \<open>v_min_val \<le> v_pulse_val\<close>
    unfolding v_min_val_def v_pulse_val_def by simp
  show \<open>v_pulse_val \<le> v_max_val\<close>
    unfolding v_pulse_val_def v_max_val_def by simp
  show \<open>0 \<le> u_min_val\<close>
    unfolding u_min_val_def by simp
  show \<open>0 \<le> v_min_val\<close>
    unfolding v_min_val_def by simp
  show \<open>0 < \<delta>_val\<close>
    unfolding \<delta>_val_def by simp

  (* The arithmetic check: \<delta>_val = 1/8 \<le> 2 - M_sharp *)
  show \<open>\<delta>_val \<le> 2 - M_sharp_scalar u_pulse_val v_pulse_val 
                                   u_min_val u_max_val v_min_val v_max_val\<close>
    unfolding \<delta>_val_def M_sharp_scalar_def 
              u_pulse_val_def v_pulse_val_def 
              u_min_val_def u_max_val_def v_min_val_def v_max_val_def
    by (simp add: power2_eq_square field_simps)
  show \<open>\<beta>_val = 2\<close>
    unfolding \<beta>_val_def by simp
  show \<open>\<gamma>_val = 2\<close>
    unfolding \<gamma>_val_def by simp
qed

text \<open>
   Stage 4: gardner\_induced\_switching interpretation.

   Instantiates the top-level induced
   switching theorem with the concrete Gardner parameters.

   The substantive obligation is sublevel\_in\_R\_B:
     V\_pulse v <= 1/100  ==>  in\_R\_B v

   Outline of proof:
\begin{itemize}
\item V\_pulse v = (1/2)((u - 1/4)\textasciicircum{}2 + (v? - 3)\textasciicircum{}2) <= 1/100
  gives (u - 1/4)\textasciicircum{}2 <= 1/50 and (v? - 3)\textasciicircum{}2 <= 1/50.
\item From x\textasciicircum{}2 <= 1/50, deduce |x| <= 1/7 (since (1/7)\textasciicircum{}2 = 1/49 > 1/50;
  if |x| > 1/7 then x\textasciicircum{}2 > 1/49 > 1/50, contradiction).
\item So u in [1/4 - 1/7, 1/4 + 1/7] = [3/28, 11/28] <= [1/10, 7/10].
\item And v? in [3 - 1/7, 3 + 1/7] = [20/7, 22/7] <= [2, 7/2].
\end{itemize}
\<close>


subsubsection \<open>Induced switching interpretation\<close>
text \<open>
   Concrete Gardner switching theorem.

   Rather than interpreting gardner\_induced\_switching (which would
   require a concrete finite type satisfying linordered\_nonzero\_semiring,
   which no standard type does), we prove the switching property
   directly as a top-level theorem, staying polymorphic in 'p.

   The theorem uses the already-proven concrete interpretations
   (concrete\_baseline, concrete\_pulse, concrete\_R\_A, concrete\_R\_B,
   concrete\_pulse\_lyapunov) and a proof of sublevel\_in\_R\_B
   specialized to our concrete numerical values.
\<close>


subsubsection \<open>Concrete switching theorem\<close>

text \<open>Helper: sublevel containment for the concrete parameters.\<close>

lemma concrete_sublevel_in_R_B:
  fixes v :: \<open>(real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  assumes V_le: \<open>concrete_pulse.V_pulse v \<le> L_target_val\<close>
  shows \<open>concrete_R_B.in_R_B v\<close>
proof -
  define u where \<open>u = vec_nth v 0\<close>
  define w where \<open>w = vec_nth v 1\<close>

  (* Unfold V_pulse *)
  have V_expand: \<open>concrete_pulse.V_pulse v = 
                 (1/2) * ((u - u_pulse_val)^2 + (w - v_pulse_val)^2)\<close>
    unfolding concrete_pulse.V_pulse_def u_def w_def by simp

  from V_le V_expand have V_ineq:
    \<open>(u - u_pulse_val)^2 + (w - v_pulse_val)^2 \<le> 2 * L_target_val\<close>
    by simp

  (* Both squared terms bounded by 2\<sqdot>L_target = 1/50 *)
  have sq_u_bound: \<open>(u - u_pulse_val)^2 \<le> 2 * L_target_val\<close>
  proof -
    have \<open>0 \<le> (w - v_pulse_val)^2\<close> by simp
    with V_ineq show ?thesis by linarith
  qed
  have sq_w_bound: \<open>(w - v_pulse_val)^2 \<le> 2 * L_target_val\<close>
  proof -
    have \<open>0 \<le> (u - u_pulse_val)^2\<close> by simp
    with V_ineq show ?thesis by linarith
  qed

  (* From x^2 \<le> 1/50, deduce |x| \<le> 1/7 *)
  have abs_u_bound: \<open>\<bar>u - u_pulse_val\<bar> \<le> 1/7\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<bar>u - u_pulse_val\<bar> \<le> 1/7\<close>
    hence gt: \<open>1/7 < \<bar>u - u_pulse_val\<bar>\<close> by simp
    have \<open>(1/7)^2 < \<bar>u - u_pulse_val\<bar>^2\<close>
      using gt 
      by (meson pos2 power_strict_mono semiring_norm(94) zero_le_divide_iff 
                zero_less_one_class.zero_le_one)  
    hence \<open>(1::real)/49 < (u - u_pulse_val)^2\<close>
      by (simp add: power2_eq_square)
    moreover have \<open>2 * L_target_val = 1/50\<close>
      unfolding L_target_val_def 
      by simp
    ultimately have \<open>1/49 < 2 * L_target_val\<close> 
      using sq_u_bound 
      by linarith
    thus False 
      unfolding L_target_val_def 
      by simp
  qed

  have abs_w_bound: \<open>\<bar>w - v_pulse_val\<bar> \<le> 1/7\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<bar>w - v_pulse_val\<bar> \<le> 1/7\<close>
    hence gt: \<open>1/7 < \<bar>w - v_pulse_val\<bar>\<close> by simp
    have \<open>(1/7)^2 < \<bar>w - v_pulse_val\<bar>^2\<close>
      using gt 
      by (metis pos2 power_strict_mono semiring_norm(94) zero_le_divide_iff 
                zero_less_one_class.zero_le_one) 
    hence \<open>(1::real)/49 < (w - v_pulse_val)^2\<close>
      by (simp add: power2_eq_square)
    moreover have \<open>2 * L_target_val = 1/50\<close>
      unfolding L_target_val_def 
      by simp
    ultimately have \<open>1/49 < 2 * L_target_val\<close> 
      using sq_w_bound by linarith
    thus False 
      unfolding L_target_val_def 
      by simp
  qed

  (* From |u - 1/4| \<le> 1/7, get 1/10 \<le> u \<le> 7/10 *)
  have u_range: \<open>u_pulse_val - 1/7 \<le> u \<and> u \<le> u_pulse_val + 1/7\<close>
    using abs_u_bound
    by linarith
  have u_lo: \<open>u_B_lo_val \<le> u\<close>
  proof -
    have \<open>u_B_lo_val \<le> u_pulse_val - 1/7\<close>
      unfolding u_B_lo_val_def u_pulse_val_def by simp
    with u_range show ?thesis 
      by linarith
  qed
  have u_hi: \<open>u \<le> u_B_hi_val\<close>
  proof -
    have \<open>u_pulse_val + 1/7 \<le> u_B_hi_val\<close>
      unfolding u_pulse_val_def u_B_hi_val_def by simp
    with u_range show ?thesis 
      by linarith
  qed

  (* From |w - 3| \<le> 1/7, get 2 \<le> w \<le> 7/2 *)
  have w_range: \<open>v_pulse_val - 1/7 \<le> w \<and> w \<le> v_pulse_val + 1/7\<close>
    using abs_w_bound
    by linarith
  have w_lo: \<open>v_B_lo_val \<le> w\<close>
  proof -
    have \<open>v_B_lo_val \<le> v_pulse_val - 1/7\<close>
      unfolding v_B_lo_val_def v_pulse_val_def 
      by simp
    with w_range show ?thesis 
      by linarith
  qed
  have w_hi: \<open>w \<le> v_B_hi_val\<close>
  proof -
    have \<open>v_pulse_val + 1/7 \<le> v_B_hi_val\<close>
      unfolding v_pulse_val_def v_B_hi_val_def 
      by simp
    with w_range show ?thesis 
      by linarith
  qed

  show \<open>concrete_R_B.in_R_B v\<close>
    unfolding concrete_R_B.in_R_B_def
    using u_lo u_hi w_lo w_hi 
    unfolding u_def w_def 
    by simp
qed


text \<open>Top-level concrete switching theorem.\<close>

theorem gardner_concrete_switching:
  fixes y1 y2 y3 :: \<open>real \<Rightarrow> (real, 'p::{finite, linordered_nonzero_semiring}) vec\<close>
  fixes t_start t_end T :: real
  assumes y1_sol: \<open>(y1 solves_ode (gardner_baseline_field \<alpha>_base_val \<beta>_val \<gamma>_val)) 
                     {0..t_start} UNIV\<close>
  assumes y2_sol: \<open>(y2 solves_ode 
                     (gardner_pulse_field \<alpha>_base_val \<alpha>_low_val \<beta>_val \<gamma>_val)) 
                     {0..(t_end - t_start)} UNIV\<close>
  assumes y3_sol: \<open>(y3 solves_ode (gardner_baseline_field \<alpha>_base_val \<beta>_val \<gamma>_val)) 
                     {0..(T - t_end)} UNIV\<close>
  assumes glue1: \<open>y2 0 = y1 t_start\<close>
  assumes glue2: \<open>y3 0 = y2 (t_end - t_start)\<close>
  assumes t_start_nn: \<open>0 \<le> t_start\<close>
  assumes t_end_after_start: \<open>t_start \<le> t_end\<close>
  assumes T_after_end: \<open>t_end \<le> T\<close>
  assumes y1_starts_in_R_A: \<open>concrete_R_A.in_R_A (y1 0)\<close>
  assumes y2_stays_in_lyapunov_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..(t_end - t_start)} \<Longrightarrow>
         u_min_val \<le> vec_nth (y2 \<tau>) 0 \<and> vec_nth (y2 \<tau>) 0 \<le> u_max_val \<and>
         v_min_val \<le> vec_nth (y2 \<tau>) 1 \<and> vec_nth (y2 \<tau>) 1 \<le> v_max_val\<close>
  assumes pulse_long_enough: 
    \<open>concrete_pulse.V_pulse (y2 0) * exp (-\<delta>_val * (t_end - t_start)) \<le> L_target_val\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> concrete_R_B.in_R_B (y3 \<tau>)\<close>
proof -
  have y1_in_R_A: \<open>\<And>\<tau>. \<tau> \<in> {0..t_start} \<Longrightarrow> concrete_R_A.in_R_A (y1 \<tau>)\<close>
    using concrete_R_A.R_A_forward_invariant[OF y1_sol t_start_nn y1_starts_in_R_A] .

  have y1_end_in_R_A: \<open>concrete_R_A.in_R_A (y1 t_start)\<close>
    using y1_in_R_A[of t_start] t_start_nn 
    by simp

  have y2_starts_in_R_A: \<open>concrete_R_A.in_R_A (y2 0)\<close>
    using glue1 y1_end_in_R_A 
    by simp

  have \<Delta>t_nn: \<open>0 \<le> t_end - t_start\<close>
    using t_end_after_start 
    by simp

  have y2_reaches_sublevel: \<open>concrete_pulse.V_pulse (y2 (t_end - t_start)) \<le> L_target_val\<close>
    using concrete_pulse_lyapunov.pulse_trajectory_reaches_sublevel[
            OF y2_sol \<Delta>t_nn y2_stays_in_lyapunov_region pulse_long_enough] .

  have y2_end_in_R_B: \<open>concrete_R_B.in_R_B (y2 (t_end - t_start))\<close>
    using concrete_sublevel_in_R_B[OF y2_reaches_sublevel] .

  have y3_starts_in_R_B: \<open>concrete_R_B.in_R_B (y3 0)\<close>
    using glue2 y2_end_in_R_B 
    by simp

  have T_end_nn: \<open>0 \<le> T - t_end\<close>
    using T_after_end 
    by simp

  show \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> concrete_R_B.in_R_B (y3 \<tau>)\<close>
    using concrete_R_B.R_B_forward_invariant[OF y3_sol T_end_nn y3_starts_in_R_B] .
qed
text \<open>
   Direct lemma proving gardner\_induced\_switching for concrete values.

   Parameter order (from thm gardner\_induced\_switching\_def):
     TYPE('p)
     alpha\_base beta gamma
     u\_A\_lo u\_A\_hi v\_A\_lo v\_A\_hi
     u\_B\_lo u\_B\_hi v\_B\_lo v\_B\_hi
     alpha\_low u\_pulse v\_pulse
     u\_min u\_max v\_min v\_max delta
     L\_target
\<close>


theorem gardner_induced_switching_concrete:
  \<open>gardner_induced_switching 
     TYPE('p::{finite, linordered_nonzero_semiring})
     \<alpha>_base_val \<beta>_val \<gamma>_val
     u_A_lo_val u_A_hi_val v_A_lo_val v_A_hi_val
     u_B_lo_val u_B_hi_val v_B_lo_val v_B_hi_val
     \<alpha>_low_val u_pulse_val v_pulse_val
     u_min_val u_max_val v_min_val v_max_val \<delta>_val
     L_target_val\<close>
proof (unfold_locales)
  fix v :: \<open>(real, 'p) vec\<close>                                            
  assume \<open>concrete_pulse.V_pulse v \<le> L_target_val\<close>
  then show \<open>concrete_R_B.in_R_B v\<close>
  by (simp add: concrete_sublevel_in_R_B)
qed

end