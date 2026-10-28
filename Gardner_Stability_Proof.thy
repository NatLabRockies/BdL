(***************************************************************)
(**                                                           **)
(** Author(s): Yakoub Nemouchi (NLR, Golden, CO, USA)         **)
(**            Peter  Graf     (NLR, Golden, CO, USA)         **)
(** Email:     Yakoub.Nemouchi@nlr.gov                        **)
(**            Peter.Graf@nlr.gov                             **)
(**                                                           **)
(** Copyright \<copyright> 2026 Alliance for Energy Innovation, LLC.     **)
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

  Define the Lyapunov function V(v) = (vec\_nth v iU)\textasciicircum{}2 (squared component).
  Along the trajectory:

      V(y(tau)) = u(tau)\textasciicircum{}2 = exp(-4tau)
      (V o y)'(tau) = 2*u(tau)*u'(tau) = 2*u(tau)*(-2*u(tau)) = -4*u(tau)\textasciicircum{}2 = -4*V(y(tau))

  REACH\_lyapunov asks for this decay pointwise, as a Lie derivative: at
  every point y(tau) of the trajectory, V has a derivative DV with
  DV(f(y(tau))) <= -delta*V(y(tau)).  Here DV is the linear map
  w |-> 2*u*(vec\_nth w iU), so DV(f(v)) = 2*u*(-2*u) = -4*V(v), and the
  condition holds with delta = 4.

  REACH\_lyapunov then gives:

      V(y(T)) <= V(y(0)) * exp(-4*T) = 1 * exp(-4*T) = exp(-4*T)

  i.e., u(T)\textasciicircum{}2 <= exp(-4*T), which is TIGHT (the trajectory achieves equality).

  PURPOSE
  This sanity check validates two things:
\begin{enumerate}
\item The premises of the provably verified lemma REACH\_lyapunov (ODE,
  T\_nn and induct\_step) are ergonomic to discharge in a concrete
  setting.  ODE and T\_nn are the assumptions y\_sol and T\_nn of the
  sanity check; induct\_step, the pointwise decay condition, becomes a
  named `have` statement in the proof, following the "obligations on top,
  lemma on bottom" template.
\item The obligation shapes generalize to higher-dimensional cases.  The
  same template will be used for the Gardner toggle switch proof, just
  with a 2D state space, a time-varying field, and a quadratic
  Lyapunov function centered at the pulse equilibrium.
\end{enumerate}

  This lemma also serves as a pedagogical example for the paper: the
  simplest possible demonstration of REACH\_lyapunov in action.
\<close>

lemma REACH_lyapunov_sanity_check:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes iU :: 'a
      \<comment> \<open>the coordinate of u; one coordinate needs no distinctness assumption\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(iU := -2 * vec_nth v iU)))) 
                    {0..T} UNIV\<close>
      \<comment> \<open>ODE: du/dt = -2*u, written in the vec\_lambda and fun\_upd
         form used throughout the CRN benchmarks\<close>
  assumes iv: \<open>vec_nth (y 0) iU = 1\<close>
      \<comment> \<open>Initial condition: u(0) = 1\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  shows \<open>(vec_nth (y T) iU)^2 \<le> exp (-4 * T)\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Apply REACH_lyapunov with the following instantiation:
     
       V     = \<lambda>v. (vec_nth v iU)^2      (Lyapunov function: squared component)
       \<delta>     = 4                         (exponential decay rate)
     
     Then REACH_lyapunov concludes V(y(T)) \<le> V(y(0)) \<sqdot> exp(-4\<sqdot>T).
     Since V(y(0)) = (vec_nth (y 0) iU)^2 = 1^2 = 1 from `iv`, the 
     right-hand side simplifies to exp(-4\<sqdot>T), giving the goal.
     
     REACH_lyapunov has three premises: ODE and T_nn are the assumptions
     y_sol and T_nn, and induct_step, the pointwise decay condition, is
     discharged as a named `have` statement below.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 1 (ODE): passed directly from `y_sol`, no have needed.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 2 (T_nn): passed directly from `T_nn`, no have needed.
     ========================================================================== *)

  (* ==========================================================================
     PROOF OBLIGATION 3 (induct_step): at every \<tau> \<in> [0..T], V has a derivative DV
     at y(\<tau>) with DV(f(y(\<tau>))) \<le> -4 \<sqdot> V(y(\<tau>)).  The helper V_deriv gives
     DV(w) = 2 \<sqdot> u \<sqdot> (vec_nth w iU); at the field value f(y(\<tau>)), whose iU
     component is -2 \<sqdot> u, this is 2 \<sqdot> u \<sqdot> (-2 \<sqdot> u) = -4 \<sqdot> u^2.
     ========================================================================== *)

  \<comment> \<open>Pointwise derivative of V = (lambda v. (vec\_nth v iU)\textasciicircum{}2) at a state p:
      the linear map w |-> 2 * (vec\_nth p iU) * (vec\_nth w iU).\<close>
  have V_deriv:
    \<open>\<And>p::(real,'a) vec. ((\<lambda>v::(real,'a) vec. (vec_nth v iU)^2) has_derivative
            (\<lambda>w. 2 * vec_nth p iU * vec_nth w iU)) (at p)\<close>
  proof -
    fix p :: \<open>(real,'a) vec\<close>
    have proj: \<open>((\<lambda>v::(real,'a) vec. vec_nth v iU) has_derivative
                   (\<lambda>w. vec_nth w iU)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have sq: \<open>((\<lambda>z::real. z^2) has_derivative
                 (\<lambda>h. 2 * vec_nth p iU * h)) (at (vec_nth p iU))\<close>
      by (auto intro!: derivative_eq_intros)
    show \<open>((\<lambda>v::(real,'a) vec. (vec_nth v iU)^2) has_derivative
             (\<lambda>w. 2 * vec_nth p iU * vec_nth w iU)) (at p)\<close>
      using has_derivative_compose[OF proj sq] 
      by (simp add: comp_def)
  qed

  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
      \<exists>DV. ((\<lambda>v::(real,'a) vec. (vec_nth v iU)^2) has_derivative DV) (at (y \<tau>)) \<and>
           DV (vec_lambda ((\<lambda>k. 0)(iU := -2 * vec_nth (y \<tau>) iU))) \<le>
              -4 * (vec_nth (y \<tau>) iU)^2\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
    have lie: \<open>(\<lambda>w. 2 * vec_nth (y \<tau>) iU * vec_nth w iU)
                 (vec_lambda ((\<lambda>k. 0)(iU := -2 * vec_nth (y \<tau>) iU))) =
               -4 * (vec_nth (y \<tau>) iU)^2\<close>
      by (simp add: fun_upd_def power2_eq_square)
    show \<open>\<exists>DV. ((\<lambda>v::(real,'a) vec. (vec_nth v iU)^2) has_derivative DV) (at (y \<tau>)) \<and>
               DV (vec_lambda ((\<lambda>k. 0)(iU := -2 * vec_nth (y \<tau>) iU))) \<le>
                  -4 * (vec_nth (y \<tau>) iU)^2\<close>
      using V_deriv[of \<open>y \<tau>\<close>] lie
      by auto
  qed

  have bound: \<open>(vec_nth (y T) iU)^2 \<le> (vec_nth (y 0) iU)^2 * exp (-4 * T)\<close>
    using REACH_lyapunov[where V = \<open>\<lambda>v::(real,'a) vec. (vec_nth v iU)^2\<close> and \<delta> = 4,
                         OF y_sol T_nn induct_step]
    by simp

  show ?thesis
    using bound iv 
    by simp
qed

text \<open>
  \textbf{GARDNER TOGGLE SWITCH: INDUCED SWITCHING VIA PULSED DYNAMICS}\\
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
  \<open>'a::finite \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 
   (real, 'a) vec \<Rightarrow> 
   (real, 'a) vec\<close> where
  \<open>gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v = 
     vec_lambda ((\<lambda>k::'a. 0)(
       iU := \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
       iV := \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))\<close>

definition gardner_pulse_field :: 
  \<open>'a::finite \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 
   (real, 'a) vec \<Rightarrow> 
   (real, 'a) vec\<close> where
  \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> v = 
     vec_lambda ((\<lambda>k::'a. 0)(
       iU := \<alpha>_low / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
       iV := \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))\<close>


subsection \<open>Baseline parameter regime\<close>

locale gardner_baseline_params =
  fixes iU iV :: \<open>'a::finite\<close>
    \<comment> \<open>the coordinates of u and v in the state vector\<close>
  fixes \<alpha>_base :: real
  fixes \<beta> \<gamma> :: nat
  assumes coords: \<open>iU \<noteq> iV\<close>
  assumes \<alpha>_base_above_threshold: \<open>2 < \<alpha>_base\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>
begin

lemmas coords_neq [simp] = coords coords[THEN not_sym]

text \<open>Axis-aligned boxes in the (u, v) plane.\<close>

definition in_box :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real, 'a) vec \<Rightarrow> bool\<close> where
  \<open>in_box ul uh vl vh w \<longleftrightarrow>
     ul \<le> vec_nth w iU \<and> vec_nth w iU \<le> uh \<and> vl \<le> vec_nth w iV \<and> vec_nth w iV \<le> vh\<close>

end


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
  \<open>(real, 'a) vec\<close> where
  \<open>E_pulse = vec_lambda ((\<lambda>k::'a. 0)(iU := u_pulse, iV := v_pulse))\<close>

lemma E_pulse_u_component: 
  \<open>vec_nth (E_pulse :: (real, 'a) vec) iU = u_pulse\<close>
  by (simp add: E_pulse_def fun_upd_def)

lemma E_pulse_v_component: 
  \<open>vec_nth (E_pulse :: (real, 'a) vec) iV = v_pulse\<close>
  by (simp add: E_pulse_def fun_upd_def)

text \<open>Lyapunov function V\_pulse.\<close>

definition V_pulse :: 
  \<open>(real, 'a) vec \<Rightarrow> real\<close> where
  \<open>V_pulse v = (vec_nth v iU - u_pulse)^2 / 2 + (vec_nth v iV - v_pulse)^2 / 2\<close>

lemma V_pulse_nn: \<open>0 \<le> V_pulse v\<close>
  by (simp add: V_pulse_def)

lemma V_pulse_has_derivative:
  fixes p :: \<open>(real, 'a) vec\<close>
  shows \<open>(V_pulse has_derivative
           (\<lambda>w. (vec_nth p iU - u_pulse) * vec_nth w iU +
              (vec_nth p iV - v_pulse) * vec_nth w iV)) (at p)\<close>
proof -
  have proj0: \<open>((\<lambda>v::(real,'a) vec. vec_nth v iU) has_derivative
                  (\<lambda>w. vec_nth w iU)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have proj1: \<open>((\<lambda>v::(real,'a) vec. vec_nth v iV) has_derivative
                  (\<lambda>w. vec_nth w iV)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have sq0: \<open>((\<lambda>z::real. (z - u_pulse)^2 / 2) has_derivative
               (\<lambda>h. (vec_nth p iU - u_pulse) * h))
             (at (vec_nth p iU))\<close>
    by (auto intro!: derivative_eq_intros)
  have sq1: \<open>((\<lambda>z::real. (z - v_pulse)^2 / 2) has_derivative
               (\<lambda>h. (vec_nth p iV - v_pulse) * h))
             (at (vec_nth p iV))\<close>
    by (auto intro!: derivative_eq_intros)
  have c0: \<open>((\<lambda>v::(real,'a) vec. (vec_nth v iU - u_pulse)^2 / 2) has_derivative
               (\<lambda>w. (vec_nth p iU - u_pulse) * vec_nth w iU)) (at p)\<close>
    using has_derivative_compose[OF proj0 sq0] 
    by (simp add: comp_def)
  have c1: \<open>((\<lambda>v::(real,'a) vec. (vec_nth v iV - v_pulse)^2 / 2) has_derivative
               (\<lambda>w. (vec_nth p iV - v_pulse) * vec_nth w iV)) (at p)\<close>
    using has_derivative_compose[OF proj1 sq1] 
    by (simp add: comp_def)
  show ?thesis
    unfolding V_pulse_def
    using has_derivative_add[OF c0 c1] 
    by simp
qed

lemma V_pulse_zero_at_E_pulse: 
  \<open>V_pulse (E_pulse :: (real, 'a) vec) = 0\<close>
  by (simp add: V_pulse_def E_pulse_def fun_upd_def)

text \<open>Coupling term Q and the Lie derivative identity.\<close>

definition coupling_Q :: 
  \<open>(real, 'a) vec \<Rightarrow> real\<close> where
  \<open>coupling_Q v = 
     \<alpha>_low  * (vec_nth v iV + v_pulse) / ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2)) +
     \<alpha>_base * (vec_nth v iU + u_pulse) / ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<close>


lemma V_pulse_lie_derivative_symbolic:
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  fixes v :: \<open>(real, 'a) vec\<close>
  shows \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
         (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) =
         -2 * V_pulse v - 
         (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<close>
proof -
  have denom_v_pos: \<open>0 < 1 + (vec_nth v iV)^2\<close> 
    by (meson rel_simps(68) zero_compare_simps(1) zero_le_power2)
  have denom_u_pos: \<open>0 < 1 + (vec_nth v iU)^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_v_nz: \<open>1 + (vec_nth v iV)^2 \<noteq> 0\<close> 
    using denom_v_pos 
    by simp
  have denom_u_nz: \<open>1 + (vec_nth v iU)^2 \<noteq> 0\<close> 
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

  have u_half_field: \<open>\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU = 
                      -u_pulse * (vec_nth v iV - v_pulse) * (vec_nth v iV + v_pulse) /
                        (1 + (vec_nth v iV)^2) - (vec_nth v iU - u_pulse)\<close>
  proof -
    have step1: \<open>\<alpha>_low / (1 + (vec_nth v iV)^2) = 
                  u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v iV)^2)\<close>
      using \<alpha>_low_eq 
      by simp

    have step2: \<open>u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v iV)^2) - vec_nth v iU = 
                  u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v iV)^2) -
                  u_pulse - (vec_nth v iU - u_pulse)\<close>
      by simp

    have step3: \<open>u_pulse * (1 + v_pulse^2) / (1 + (vec_nth v iV)^2) - u_pulse = 
                  u_pulse * ((1 + v_pulse^2) - (1 + (vec_nth v iV)^2)) / (1 + (vec_nth v iV)^2)\<close>
      using denom_v_nz
      by (metis divide_diff_eq_iff right_diff_distrib)

    have step4: \<open>(1 + v_pulse^2) - (1 + (vec_nth v iV)^2) = 
                  -((vec_nth v iV - v_pulse) * (vec_nth v iV + v_pulse))\<close>
      by (simp add: power2_eq_square algebra_simps)
    from step1 step2 step3 step4 
    show ?thesis 
      by auto
  qed

  have u_half: \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) = 
                - ((vec_nth v iU - u_pulse)^2) -
                (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) *
                    (u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2))\<close>
  proof -
    have \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) =
          (vec_nth v iU - u_pulse) * 
            (-u_pulse * (vec_nth v iV - v_pulse) * (vec_nth v iV + v_pulse) /
               (1 + (vec_nth v iV)^2) - (vec_nth v iU - u_pulse))\<close>
      using u_half_field
      by simp
    also have \<open>\<dots> = 
          -((vec_nth v iU - u_pulse)^2) -
          (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) *
              (u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2))\<close>
      apply (simp add: algebra_simps power2_eq_square)
      apply argo
      done
    finally show ?thesis .
  qed

  (* --- Second half: the v-direction identity (symmetric) --- *)

  have v_half_field: \<open>\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV = 
                      -v_pulse * (vec_nth v iU - u_pulse) * (vec_nth v iU + u_pulse) /
                        (1 + (vec_nth v iU)^2) - (vec_nth v iV - v_pulse)\<close>
  proof -
    have step1: \<open>\<alpha>_base / (1 + (vec_nth v iU)^2) = 
                  v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v iU)^2)\<close>
      using \<alpha>_base_eq 
      by simp
    have step2: \<open>v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v iU)^2) - vec_nth v iV = 
                  v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v iU)^2) -
                  v_pulse - (vec_nth v iV - v_pulse)\<close>
      by simp
    have step3: \<open>v_pulse * (1 + u_pulse^2) / (1 + (vec_nth v iU)^2) - v_pulse = 
                  v_pulse * ((1 + u_pulse^2) - (1 + (vec_nth v iU)^2)) / (1 + (vec_nth v iU)^2)\<close>
      using denom_u_nz
      by (metis (no_types, lifting) nonzero_mult_div_cancel_right right_diff_distrib' 
                times_divide_eq_left)
    have step4: \<open>(1 + u_pulse^2) - (1 + (vec_nth v iU)^2) = 
                  -((vec_nth v iU - u_pulse) * (vec_nth v iU + u_pulse))\<close>
      by (simp add: power2_eq_square algebra_simps)
    from step1 step2 step3 step4 
    show ?thesis 
      by auto
  qed
  have v_half: \<open>(vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) = 
                -((vec_nth v iV - v_pulse)^2) -
                (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) *
                    (v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2))\<close>
  proof -
    have \<open>(vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) =
          (vec_nth v iV - v_pulse) * 
            (-v_pulse * (vec_nth v iU - u_pulse) * (vec_nth v iU + u_pulse) /
               (1 + (vec_nth v iU)^2) - (vec_nth v iV - v_pulse))\<close>
      using v_half_field 
      by simp
    also have \<open>\<dots> = 
          -((vec_nth v iV - v_pulse)^2) -
          (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) *
              (v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2))\<close>
      apply (simp add: algebra_simps power2_eq_square)
      apply argo
      done
    finally show ?thesis .
  qed

  (* --- Combining the two halves --- *)

  have coupling_Q_as_halves: 
    \<open>coupling_Q v = 
       u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2) +
       v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2)\<close>
  proof -
    have v_factor: \<open>\<alpha>_low * (vec_nth v iV + v_pulse) / 
                    ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2)) = 
                    u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2)\<close>
    proof -
      have \<open>\<alpha>_low * (vec_nth v iV + v_pulse) / 
            ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2)) = 
            (u_pulse * (1 + v_pulse^2)) * (vec_nth v iV + v_pulse) / 
            ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<close>
        using \<alpha>_low_eq 
        by simp
      also have \<open>\<dots> = u_pulse * (vec_nth v iV + v_pulse) * (1 + v_pulse^2) / 
                       ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<close>
        by (simp add: mult.commute mult.left_commute)
      also have \<open>\<dots> = u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2)\<close>
        using assms(1) u_pulse_equilibrium
        by auto
      finally show ?thesis .
    qed
    have u_factor: \<open>\<alpha>_base * (vec_nth v iU + u_pulse) / 
                    ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2)) = 
                    v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2)\<close>
    proof -
      have \<open>\<alpha>_base * (vec_nth v iU + u_pulse) / 
            ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2)) = 
            (v_pulse * (1 + u_pulse^2)) * (vec_nth v iU + u_pulse) / 
            ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<close>
        using \<alpha>_base_eq 
        by simp
      also have \<open>\<dots> = v_pulse * (vec_nth v iU + u_pulse) * (1 + u_pulse^2) / 
                       ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<close>
        by (simp add: mult.commute mult.left_commute)
      also have \<open>\<dots> = v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2)\<close>
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

  have \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
        (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) = 
        -((vec_nth v iU - u_pulse)^2) - (vec_nth v iV - v_pulse)^2 -
        (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) *
            (u_pulse * (vec_nth v iV + v_pulse) / (1 + (vec_nth v iV)^2) + 
             v_pulse * (vec_nth v iU + u_pulse) / (1 + (vec_nth v iU)^2))\<close>
    using u_half v_half 
    by (simp add: algebra_simps)
  also have \<open>\<dots> = -((vec_nth v iU - u_pulse)^2) - (vec_nth v iV - v_pulse)^2 -
                  (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<close>
    using coupling_Q_as_halves 
    by simp
  also have \<open>\<dots> = -2 * V_pulse v -
                  (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<close>
    by (simp add: V_pulse_def)
  finally show ?thesis .
qed
text \<open>Crude bound on |Q|.\<close>

definition M_crude :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real\<close> where
  \<open>M_crude u_min u_max v_min v_max = 
     \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse) +
     \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>

lemma coupling_Q_bound_crude:
  fixes v :: \<open>(real, 'a) vec\<close>
  fixes u_min u_max v_min v_max :: real
  assumes u_bounds: \<open>u_min \<le> vec_nth v iU\<close> \<open>vec_nth v iU \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v iV\<close> \<open>vec_nth v iV \<le> v_max\<close>
  shows \<open>\<bar>coupling_Q v\<bar> \<le> M_crude u_min u_max v_min v_max\<close>
proof -
  (* --- Positivity facts we'll need --- *)
  have \<alpha>_low_nn: \<open>0 \<le> \<alpha>_low\<close>
    using \<alpha>_low_pos
    by simp
  have \<alpha>_base_nn: \<open>0 \<le> \<alpha>_base\<close>
    using \<alpha>_base_above_threshold
    by simp
  have v_pulse_nn: \<open>0 \<le> v_pulse\<close>
    using v_pulse_pos
    by simp
  have u_pulse_nn: \<open>0 \<le> u_pulse\<close>
    using u_pulse_pos
    by simp

  have denom_v_pos: \<open>0 < 1 + (vec_nth v iV)^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_u_pos: \<open>0 < 1 + (vec_nth v iU)^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_vp_pos: \<open>0 < 1 + v_pulse^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_up_pos: \<open>0 < 1 + u_pulse^2\<close>
    by (simp add: add_pos_nonneg)

  have prod_vv_ge1: \<open>1 \<le> (1 + (vec_nth v iV)^2) * (1 + v_pulse^2)\<close>
  proof -
    have \<open>1 \<le> 1 + (vec_nth v iV)^2\<close>
      by simp
    moreover have \<open>1 \<le> 1 + v_pulse^2\<close>
      by simp
    ultimately show ?thesis
      by (metis mult_mono' zero_le_one mult_1)
  qed
  have prod_uu_ge1: \<open>1 \<le> (1 + (vec_nth v iU)^2) * (1 + u_pulse^2)\<close>
  proof -
    have \<open>1 \<le> 1 + (vec_nth v iU)^2\<close>
      by simp
    moreover have \<open>1 \<le> 1 + u_pulse^2\<close>
      by simp
    ultimately show ?thesis
      by (metis mult_mono' zero_le_one  mult_1)
  qed

  have prod_vv_pos: \<open>0 < (1 + (vec_nth v iV)^2) * (1 + v_pulse^2)\<close>
    using denom_v_pos denom_vp_pos 
    by simp
  have prod_uu_pos: \<open>0 < (1 + (vec_nth v iU)^2) * (1 + u_pulse^2)\<close>
    using denom_u_pos denom_up_pos 
    by simp

  (* --- Stage 1: Bound |v| and |u| by max of region bounds --- *)

  have abs_v_le: \<open>\<bar>vec_nth v iV\<bar> \<le> max \<bar>v_min\<bar> \<bar>v_max\<bar>\<close>
    using v_bounds
    by linarith

  have abs_u_le: \<open>\<bar>vec_nth v iU\<bar> \<le> max \<bar>u_min\<bar> \<bar>u_max\<bar>\<close>
    using u_bounds
    by linarith 

  (* --- Stage 2: Bound each term of coupling_Q individually --- *)

  (* v-term bound *)
  have v_term_bound: 
    \<open>\<bar>\<alpha>_low * (vec_nth v iV + v_pulse) / ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<bar> \<le>
      \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse)\<close>
  proof -
    have step1: \<open>\<bar>\<alpha>_low * (vec_nth v iV + v_pulse) / 
                   ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<bar> =
                \<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar> /
                   ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<close>
      using \<alpha>_low_nn prod_vv_pos 
      by (simp add: abs_mult)
    have step2: \<open>\<bar>vec_nth v iV + v_pulse\<bar> \<le> \<bar>vec_nth v iV\<bar> + v_pulse\<close>
      using v_pulse_nn 
      by (simp add: abs_triangle_ineq)
    have step3: \<open>\<bar>vec_nth v iV\<bar> + v_pulse \<le> max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse\<close>
      using abs_v_le 
      by simp
    have step4: \<open>\<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar> \<le>
                 \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse)\<close>
      using step2 step3 \<alpha>_low_nn 
      by (simp add: mult_left_mono)
    (* Now dividing by something \<ge> 1 *)
    have step5: \<open>\<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar> / 
                 ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2)) \<le>
                  \<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar>\<close>
    proof -
      have numer_nn: \<open>0 \<le> \<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar>\<close>
        using \<alpha>_low_nn
        by simp
      from numer_nn prod_vv_ge1 show ?thesis
        using frac_le[where y = "\<alpha>_low * \<bar>vec_nth v iV + v_pulse\<bar>" 
                        and w = 1 
                        and z = "(1 + (vec_nth v iV)^2) * (1 + v_pulse^2)"]
        by simp
    qed
    from step1 step4 step5 
    show ?thesis
      by linarith
  qed

  (* u-term bound, symmetric *)
  have u_term_bound: 
    \<open>\<bar>\<alpha>_base * (vec_nth v iU + u_pulse) / ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<bar> \<le>
      \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
  proof -
    have step1: \<open>\<bar>\<alpha>_base * (vec_nth v iU + u_pulse) / 
                   ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<bar> =
                 \<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar> / 
                   ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<close>
      using \<alpha>_base_nn prod_uu_pos 
      by (simp add: abs_mult)
    have step2: \<open>\<bar>vec_nth v iU + u_pulse\<bar> \<le> \<bar>vec_nth v iU\<bar> + u_pulse\<close>
      using u_pulse_nn 
      by (simp add: abs_triangle_ineq)
    have step3: \<open>\<bar>vec_nth v iU\<bar> + u_pulse \<le> max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse\<close>
      using abs_u_le 
      by simp
    have step4: \<open>\<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar> \<le>
                 \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
      using step2 step3 \<alpha>_base_nn 
      by (simp add: mult_left_mono)
    have step5: \<open>\<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar> / 
                 ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2)) \<le> 
                  \<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar>\<close>
    proof -
      have numer_nn: \<open>0 \<le> \<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar>\<close>
        using \<alpha>_base_nn 
        by simp
      from numer_nn prod_uu_ge1 show ?thesis
        using frac_le[where y = "\<alpha>_base * \<bar>vec_nth v iU + u_pulse\<bar>" 
                        and w = 1 
                        and z = "(1 + (vec_nth v iU)^2) * (1 + u_pulse^2)"]
        by simp
    qed
    from step1 step4 step5 show ?thesis
      by linarith
  qed

  (* --- Stage 3: Triangle inequality and combining --- *)

  have \<open>\<bar>coupling_Q v\<bar> \<le> 
        \<bar>\<alpha>_low * (vec_nth v iV + v_pulse) / ((1 + (vec_nth v iV)^2) * (1 + v_pulse^2))\<bar> +
        \<bar>\<alpha>_base * (vec_nth v iU + u_pulse) / ((1 + (vec_nth v iU)^2) * (1 + u_pulse^2))\<bar>\<close>
    unfolding coupling_Q_def
    by (rule abs_triangle_ineq)
  also have \<open>\<dots> \<le> \<alpha>_low * (max \<bar>v_min\<bar> \<bar>v_max\<bar> + v_pulse) + 
                  \<alpha>_base * (max \<bar>u_min\<bar> \<bar>u_max\<bar> + u_pulse)\<close>
    using v_term_bound u_term_bound
    by linarith
  also have \<open>\<dots> = M_crude u_min u_max v_min v_max\<close>
    unfolding M_crude_def 
    by simp
  finally show ?thesis .
qed

lemma coupling_Q_bound_sharp:
  fixes v :: \<open>(real, 'a) vec\<close>
  fixes u_min u_max v_min v_max :: real
  assumes \<beta>_eq: \<open>\<beta> = 2\<close>
  assumes \<gamma>_eq: \<open>\<gamma> = 2\<close>
  assumes u_min_nn: \<open>0 \<le> u_min\<close>
  assumes v_min_nn: \<open>0 \<le> v_min\<close>
  assumes u_bounds: \<open>u_min \<le> vec_nth v iU\<close> \<open>vec_nth v iU \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v iV\<close> \<open>vec_nth v iV \<le> v_max\<close>
  shows \<open>\<bar>coupling_Q v\<bar> \<le> M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
proof -
  define u where \<open>u = vec_nth v iU\<close>
  define w where \<open>w = vec_nth v iV\<close>

  have u_nn: \<open>0 \<le> u\<close>
    using u_min_nn u_bounds
    unfolding u_def
    by simp
  have w_nn: \<open>0 \<le> w\<close>
    using v_min_nn v_bounds
    unfolding w_def
    by simp
  have u_pulse_nn: \<open>0 \<le> u_pulse\<close>
    using u_pulse_pos
    by simp
  have v_pulse_nn: \<open>0 \<le> v_pulse\<close>
    using v_pulse_pos
    by simp

  have denom_w_pos: \<open>0 < 1 + w^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_u_pos: \<open>0 < 1 + u^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_w_min_pos: \<open>0 < 1 + v_min^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_u_min_pos: \<open>0 < 1 + u_min^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_vp_pos: \<open>0 < 1 + v_pulse^2\<close>
    by (simp add: add_pos_nonneg)
  have denom_up_pos: \<open>0 < 1 + u_pulse^2\<close>
    by (simp add: add_pos_nonneg)

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
      unfolding coupling_Q_def u_def w_def
      by simp
    also have \<open>... = 
               u_pulse * (1 + v_pulse^2) * (w + v_pulse) / ((1 + w^2) * (1 + v_pulse^2)) +
               v_pulse * (1 + u_pulse^2) * (u + u_pulse) / ((1 + u^2) * (1 + u_pulse^2))\<close>
      using \<alpha>_low_eq \<alpha>_base_eq
      by simp
    also have \<open>... = u_pulse * (w + v_pulse) / (1 + w^2) +
                      v_pulse * (u + u_pulse) / (1 + u^2)\<close>
      using denom_vp_pos denom_up_pos     
      by simp
    finally show ?thesis .
  qed

  have num1_nn: \<open>0 \<le> w + v_pulse\<close>
    using w_nn v_pulse_nn
    by simp
  have num2_nn: \<open>0 \<le> u + u_pulse\<close>
    using u_nn u_pulse_nn
    by simp

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
    using v_bounds
    unfolding w_def
    by simp
  have denom1_bound: \<open>1 + v_min^2 \<le> 1 + w^2\<close>
    using v_bounds v_min_nn w_nn
    unfolding w_def
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
    using u_bounds
    unfolding u_def
    by simp
  have denom2_bound: \<open>1 + u_min^2 \<le> 1 + u^2\<close>
    using u_bounds u_min_nn u_nn
    unfolding u_def
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
  fixes v :: \<open>(real, 'a) vec\<close>
  fixes u_min u_max v_min v_max \<delta> :: real
  assumes u_bounds: \<open>u_min \<le> vec_nth v iU\<close> \<open>vec_nth v iU \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v iV\<close> \<open>vec_nth v iV \<le> v_max\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes \<delta>_bound: \<open>\<delta> \<le> 2 - M_crude u_min u_max v_min v_max\<close>
  shows \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
         (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) \<le>
         -\<delta> * V_pulse v\<close>
proof -
  have lie_eq: 
    \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
     (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) =
     -2 * V_pulse v - 
     (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<close>
    using V_pulse_lie_derivative_symbolic[OF \<beta>_eq \<gamma>_eq] .

  have am_gm: \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> \<le> V_pulse v\<close>
  proof -
    have \<open>2 * \<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> \<le>
          (vec_nth v iU - u_pulse)^2 + (vec_nth v iV - v_pulse)^2\<close>
      by (metis (no_types, opaque_lifting) abs_mult more_arith_simps(11) power2_abs   
                sum_squares_bound) 
    thus ?thesis
      by (simp add: V_pulse_def)
  qed

  have Q_bound: \<open>\<bar>coupling_Q v\<bar> \<le> M_crude u_min u_max v_min v_max\<close>
    using coupling_Q_bound_crude[OF u_bounds v_bounds] .

  have cross_term_bound: 
    \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<bar> \<le>
      V_pulse v * M_crude u_min u_max v_min v_max\<close>
  proof -
    have \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<bar> =
          \<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> * \<bar>coupling_Q v\<bar>\<close>
      by (simp add: abs_mult)
    also have \<open>\<dots> \<le> V_pulse v * M_crude u_min u_max v_min v_max\<close>
      using am_gm Q_bound V_pulse_nn
      by (simp add: mult_mono)
    finally show ?thesis .
  qed

  have cross_term_signed: 
    \<open>-(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v \<le>
      V_pulse v * M_crude u_min u_max v_min v_max\<close>
    using cross_term_bound
    by linarith

  have \<open>-2 * V_pulse v - 
        (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v \<le>
        -2 * V_pulse v + V_pulse v * M_crude u_min u_max v_min v_max\<close>
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
  fixes v :: \<open>(real, 'a) vec\<close>
  fixes u_min u_max v_min v_max \<delta> :: real
  assumes u_min_nn: \<open>0 \<le> u_min\<close>
  assumes v_min_nn: \<open>0 \<le> v_min\<close>
  assumes u_bounds: \<open>u_min \<le> vec_nth v iU\<close> \<open>vec_nth v iU \<le> u_max\<close>
  assumes v_bounds: \<open>v_min \<le> vec_nth v iV\<close> \<open>vec_nth v iV \<le> v_max\<close>
  assumes \<delta>_pos: \<open>0 < \<delta>\<close>
  assumes \<delta>_bound: \<open>\<delta> \<le> 2 - M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
  shows \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
         (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) \<le> 
          -\<delta> * V_pulse v\<close>
proof -
  have lie_eq: 
    \<open>(vec_nth v iU - u_pulse) * (\<alpha>_low / (1 + (vec_nth v iV)^2) - vec_nth v iU) +
     (vec_nth v iV - v_pulse) * (\<alpha>_base / (1 + (vec_nth v iU)^2) - vec_nth v iV) =
     -2 * V_pulse v - 
     (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<close>
    using V_pulse_lie_derivative_symbolic[OF \<beta>_eq \<gamma>_eq] .

  have am_gm: \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> \<le> V_pulse v\<close>
  proof -
    have \<open>2 * \<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> \<le>
           (vec_nth v iU - u_pulse)^2 + (vec_nth v iV - v_pulse)^2\<close>
      by (metis (no_types, opaque_lifting) abs_mult more_arith_simps(11) 
                power2_abs sum_squares_bound)
    thus ?thesis
      by (simp add: V_pulse_def)
  qed

  have Q_bound: \<open>\<bar>coupling_Q v\<bar> \<le> M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using coupling_Q_bound_sharp[OF \<beta>_eq \<gamma>_eq u_min_nn v_min_nn u_bounds v_bounds] .

  have cross_term_bound: 
    \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<bar> \<le>
      V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
  proof -
    have \<open>\<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v\<bar> =
          \<bar>(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse)\<bar> * \<bar>coupling_Q v\<bar>\<close>
      by (simp add: abs_mult)
    also have \<open>... \<le> V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
      using am_gm Q_bound V_pulse_nn 
      by (simp add: mult_mono)
    finally show ?thesis .
  qed

  have cross_term_signed: 
    \<open>-(vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v \<le>
      V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using cross_term_bound
    by linarith

  have \<open>-2 * V_pulse v - 
        (vec_nth v iU - u_pulse) * (vec_nth v iV - v_pulse) * coupling_Q v \<le>
         -2 * V_pulse v + V_pulse v * M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max\<close>
    using cross_term_signed 
    by linarith
  also have \<open>... = -(2 - M_sharp_scalar u_pulse v_pulse u_min u_max v_min v_max) * V_pulse v\<close>
    by (simp add: algebra_simps)
  also have \<open>... \<le> -\<delta> * V_pulse v\<close>
    using \<delta>_bound V_pulse_nn 
    by (metis landau_o.R_mult_right_mono more_arith_simps(1))
  finally show ?thesis
    using lie_eq
    by simp
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
  \<open>(real, 'a) vec \<Rightarrow> bool\<close> where
  \<open>in_R_A v \<longleftrightarrow> u_A_lo \<le> vec_nth v iU \<and> vec_nth v iU \<le> u_A_hi \<and>
                v_A_lo \<le> vec_nth v iV \<and> vec_nth v iV \<le> v_A_hi\<close>

lemma R_A_forward_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma>)) {0..t} UNIV\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes y0_in_R_A: \<open>in_R_A (y 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_A (y \<tau>)\<close>
proof -
  (* We define lo and hi functions for DI_Frame_Rule_partial *)
  define lo :: \<open>'a \<Rightarrow> real\<close> where
    \<open>lo = (\<lambda>i. if i = iU then u_A_lo 
               else if i = iV then v_A_lo 
               else vec_nth (y 0) i)\<close>
  define hi :: \<open>'a \<Rightarrow> real\<close> where
    \<open>hi = (\<lambda>i. if i = iU then u_A_hi 
               else if i = iV then v_A_hi 
               else vec_nth (y 0) i)\<close>
  define active :: \<open>'a set\<close> where
    \<open>active = {iU, iV}\<close>

  (* Initial condition: y 0 respects lo and hi *)
  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'a
    show \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof (cases \<open>i = iU\<close>)
      case True
      with y0_in_R_A show ?thesis 
        unfolding in_R_A_def lo_def hi_def
        by simp
    next
      case False
      show ?thesis
      proof (cases \<open>i = iV\<close>)
        case True
        with y0_in_R_A \<open>i \<noteq> iU\<close> show ?thesis 
          unfolding in_R_A_def lo_def hi_def
          by simp
      next
        case False
        with \<open>i \<noteq> iU\<close> show ?thesis 
          unfolding lo_def hi_def
          by simp
      qed
    qed
  qed

  (* active coordinates are strictly ordered *)
  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'a assume \<open>i \<in> active\<close>
    hence \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>lo i < hi i\<close>
    proof
      assume \<open>i = iU\<close>
      thus \<open>lo i < hi i\<close>
        unfolding lo_def hi_def
        using u_A_ordered
        by simp
    next
      assume \<open>i = iV\<close>
      thus \<open>lo i < hi i\<close> 
        unfolding lo_def hi_def 
        using v_A_ordered
        by simp
    qed
  qed

  (* Lower edge inward for active coordinates *)
  have lower_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>
    from i_act have \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
    proof
      assume i_eq: \<open>i = iU\<close>
      (* vec_nth v iU = u_A_lo, and v's coordinate iV is in [v_A_lo, v_A_hi] *)
      have v0_eq: \<open>vec_nth v iU = u_A_lo\<close>
        using eq_lo i_eq
        unfolding lo_def
        by simp
      have v1_lo: \<open>v_A_lo \<le> vec_nth v iV\<close>
        using bounds[of iV]
        unfolding lo_def
        by simp
      have v1_hi: \<open>vec_nth v iV \<le> v_A_hi\<close>
        using bounds[of iV]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
              \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_A_lo\<close>
        using v0_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
           \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_A_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_A_left_edge_inward[OF v1_lo v1_hi]
        by simp
    next
      assume i_eq: \<open>i = iV\<close>
      have v1_eq: \<open>vec_nth v iV = v_A_lo\<close>
        using eq_lo i_eq
        unfolding lo_def
        by simp
      have v0_lo: \<open>u_A_lo \<le> vec_nth v iU\<close>
        using bounds[of iU]
        unfolding lo_def
        by simp
      have v0_hi: \<open>vec_nth v iU \<le> u_A_hi\<close>
        using bounds[of iU]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
              \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_A_lo\<close>
        using v1_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
           \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_A_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_A_bottom_edge_inward[OF v0_lo v0_hi]
        by simp
    qed
  qed

  (* Upper edge inward for active coordinates *)
  have upper_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>
    from i_act have \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
    proof
      assume i_eq: \<open>i = iU\<close>
      have v0_eq: \<open>vec_nth v iU = u_A_hi\<close>
        using eq_hi i_eq
        unfolding hi_def
        by simp
      have v1_lo: \<open>v_A_lo \<le> vec_nth v iV\<close>
        using bounds[of iV]
        unfolding lo_def
        by simp
      have v1_hi: \<open>vec_nth v iV \<le> v_A_hi\<close>
        using bounds[of iV]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
              \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_A_hi\<close>
        using v0_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
           \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_A_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_A_right_edge_inward[OF v1_lo v1_hi]
        by simp
    next
      assume i_eq: \<open>i = iV\<close>
      have v1_eq: \<open>vec_nth v iV = v_A_hi\<close>
        using eq_hi i_eq
        unfolding hi_def
        by simp
      have v0_lo: \<open>u_A_lo \<le> vec_nth v iU\<close>
        using bounds[of iU]
        unfolding lo_def
        by simp
      have v0_hi: \<open>vec_nth v iU \<le> u_A_hi\<close>
        using bounds[of iU]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
              \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_A_hi\<close>
        using v1_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
           \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_A_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_A_top_edge_inward[OF v0_lo v0_hi]
        by simp
    qed
  qed

  (* Inactive coordinates are maintained: the field is 0 for i \<notin> {iU, iV}, so the 
     trajectory's i-component is constant at its initial value *)
  have inactive_maint: 
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'a and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    from i_inact have i_ne: \<open>i \<noteq> iU\<close> \<open>i \<noteq> iV\<close>
      unfolding active_def
      by auto

    (* The i-th component of the field is 0 for this i *)
    have field_zero: \<open>\<And>\<tau>' v. vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
    proof -
      fix \<tau>' :: real and v :: \<open>(real, 'a) vec\<close>
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
        unfolding gardner_baseline_field_def 
        using i_ne
        by (simp add: fun_upd_def)
    qed

    (* We extract y's vderiv from the ODE *)
    have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>))) {0..t}\<close>
      using y_sol
      by (simp add: solves_ode_def)

    (* The i-th coordinate function (\<lambda>\<tau>. vec_nth (y \<tau>) i) has vderiv 0 *)
    have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
    proof -
      have \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on 
             (\<lambda>\<tau>. vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>)) i)) {0..t}\<close>
      proof -
        have step1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_vector_derivative (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using y_vderiv
          unfolding has_vderiv_on_def
          by blast
        have step2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_derivative (\<lambda>h. h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using step1
          unfolding has_vector_derivative_def
          by blast
        have step3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
              (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
               (at \<tau>' within {0..t})\<close>
        proof -
          fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..t}\<close>
          have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
            by (rule has_derivative_vec_nth)
          show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                 (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
                   (at \<tau>' within {0..t})\<close>
            using has_derivative_compose[OF step2[OF \<tau>'_in] proj]
            by simp
        qed
        show ?thesis
          unfolding has_vderiv_on_def has_vector_derivative_def
          using step3
          by simp
      qed
      thus ?thesis
        using field_zero
        by simp
    qed

    (* So vec_nth (y \<tau>) i = vec_nth (y 0) i *)
    have const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
      using has_vderiv_on_zero_imp_constant[OF yi_vderiv t_nn \<tau>_in_t] .

    (* And lo i = hi i = vec_nth (y 0) i for inactive coords *)
    show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      using i_ne const
      unfolding lo_def hi_def
      by simp
  qed

  (* We apply DI_Frame_Rule_partial *)
  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
                     lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF t_nn y_sol iv active_ord 
                                       lower_edge upper_edge inactive_maint]
    by blast

  show \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_A (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have h0: \<open>lo iU \<le> vec_nth (y \<tau>) iU \<and> vec_nth (y \<tau>) iU \<le> hi iU\<close>
      using main[OF \<tau>_in, of iU] .
    have h1: \<open>lo iV \<le> vec_nth (y \<tau>) iV \<and> vec_nth (y \<tau>) iV \<le> hi iV\<close>
      using main[OF \<tau>_in, of iV] .
    show \<open>in_R_A (y \<tau>)\<close>
      using h0 h1
      unfolding in_R_A_def lo_def hi_def
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
  \<open>(real, 'a) vec \<Rightarrow> bool\<close> where
  \<open>in_R_B v \<longleftrightarrow> u_B_lo \<le> vec_nth v iU \<and> vec_nth v iU \<le> u_B_hi \<and>
                v_B_lo \<le> vec_nth v iV \<and> vec_nth v iV \<le> v_B_hi\<close>

lemma R_B_forward_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma>)) {0..t} UNIV\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes y0_in_R_B: \<open>in_R_B (y 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_B (y \<tau>)\<close>
proof -
  define lo :: \<open>'a \<Rightarrow> real\<close> where
    \<open>lo = (\<lambda>i. if i = iU then u_B_lo 
               else if i = iV then v_B_lo 
               else vec_nth (y 0) i)\<close>
  define hi :: \<open>'a \<Rightarrow> real\<close> where
    \<open>hi = (\<lambda>i. if i = iU then u_B_hi 
               else if i = iV then v_B_hi 
               else vec_nth (y 0) i)\<close>
  define active :: \<open>'a set\<close> where
    \<open>active = {iU, iV}\<close>

  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'a
    show \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof (cases \<open>i = iU\<close>)
      case True
      with y0_in_R_B show ?thesis 
        unfolding in_R_B_def lo_def hi_def 
        by simp
    next
      case False
      show ?thesis
      proof (cases \<open>i = iV\<close>)
        case True
        with y0_in_R_B \<open>i \<noteq> iU\<close> show ?thesis 
          unfolding in_R_B_def lo_def hi_def 
          by simp
      next
        case False
        with \<open>i \<noteq> iU\<close> show ?thesis 
          unfolding lo_def hi_def 
          by simp
      qed
    qed
  qed

  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'a assume \<open>i \<in> active\<close>
    hence \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>lo i < hi i\<close>
    proof
      assume \<open>i = iU\<close>
      thus \<open>lo i < hi i\<close>
        unfolding lo_def hi_def
        using u_B_ordered
        by simp
    next
      assume \<open>i = iV\<close>
      thus \<open>lo i < hi i\<close>
        unfolding lo_def hi_def
        using v_B_ordered
        by simp
    qed
  qed

  have lower_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>
    from i_act have \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
    proof
      assume i_eq: \<open>i = iU\<close>
      have v0_eq: \<open>vec_nth v iU = u_B_lo\<close>
        using eq_lo i_eq
        unfolding lo_def
        by simp
      have v1_lo: \<open>v_B_lo \<le> vec_nth v iV\<close>
        using bounds[of iV]
        unfolding lo_def
        by simp
      have v1_hi: \<open>vec_nth v iV \<le> v_B_hi\<close>
        using bounds[of iV]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
              \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_B_lo\<close>
        using v0_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
           \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_B_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_B_left_edge_inward[OF v1_lo v1_hi]
        by simp
    next
      assume i_eq: \<open>i = iV\<close>
      have v1_eq: \<open>vec_nth v iV = v_B_lo\<close>
        using eq_lo i_eq
        unfolding lo_def
        by simp
      have v0_lo: \<open>u_B_lo \<le> vec_nth v iU\<close>
        using bounds[of iU]
        unfolding lo_def
        by simp
      have v0_hi: \<open>vec_nth v iU \<le> u_B_hi\<close>
        using bounds[of iU]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
              \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_B_lo\<close>
        using v1_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
           \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_B_lo\<close> .
      show \<open>0 < vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i\<close>
        using i_eq rewrite R_B_bottom_edge_inward[OF v0_lo v0_hi] 
        by simp
    qed
  qed

  have upper_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>
    from i_act have \<open>i = iU \<or> i = iV\<close>
      unfolding active_def
      by blast
    thus \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
    proof
      assume i_eq: \<open>i = iU\<close>
      have v0_eq: \<open>vec_nth v iU = u_B_hi\<close>
        using eq_hi i_eq
        unfolding hi_def
        by simp
      have v1_lo: \<open>v_B_lo \<le> vec_nth v iV\<close>
        using bounds[of iV]
        unfolding lo_def
        by simp
      have v1_hi: \<open>vec_nth v iV \<le> v_B_hi\<close>
        using bounds[of iV]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
              \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_B_hi\<close>
        using v0_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iU = 
           \<alpha>_base / (1 + (vec_nth v iV)^\<beta>) - u_B_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_B_right_edge_inward[OF v1_lo v1_hi]
        by simp
    next
      assume i_eq: \<open>i = iV\<close>
      have v1_eq: \<open>vec_nth v iV = v_B_hi\<close>
        using eq_hi i_eq
        unfolding hi_def
        by simp
      have v0_lo: \<open>u_B_lo \<le> vec_nth v iU\<close>
        using bounds[of iU]
        unfolding lo_def
        by simp
      have v0_hi: \<open>vec_nth v iU \<le> u_B_hi\<close>
        using bounds[of iU]
        unfolding hi_def
        by simp
      have \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
              \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV\<close>
        unfolding gardner_baseline_field_def
        by (simp add: fun_upd_def)
      also have \<open>... = \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_B_hi\<close>
        using v1_eq
        by simp
      finally have rewrite: 
        \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) iV = 
           \<alpha>_base / (1 + (vec_nth v iU)^\<gamma>) - v_B_hi\<close> .
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> v) i < 0\<close>
        using i_eq rewrite R_B_top_edge_inward[OF v0_lo v0_hi]
        by simp
    qed
  qed

  have inactive_maint: 
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'a and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    from i_inact have i_ne: \<open>i \<noteq> iU\<close> \<open>i \<noteq> iV\<close>
      unfolding active_def
      by auto

    have field_zero: \<open>\<And>\<tau>' v. vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
    proof -
      fix \<tau>' :: real and v :: \<open>(real, 'a) vec\<close>
      show \<open>vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' v) i = 0\<close>
        unfolding gardner_baseline_field_def 
        using i_ne
        by (simp add: fun_upd_def)
    qed

    have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>))) {0..t}\<close>
      using y_sol
      by (simp add: solves_ode_def)

    have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
    proof -
      have \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on 
             (\<lambda>\<tau>. vec_nth (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau> (y \<tau>)) i)) {0..t}\<close>
      proof -
        have step1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_vector_derivative (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using y_vderiv
          unfolding has_vderiv_on_def
          by blast
        have step2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_derivative (\<lambda>h. h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using step1
          unfolding has_vector_derivative_def
          by blast
        have step3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
              (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
               (at \<tau>' within {0..t})\<close>
        proof -
          fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..t}\<close>
          have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
            by (rule has_derivative_vec_nth)
          show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                 (\<lambda>h. vec_nth (h *\<^sub>R gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma> \<tau>' (y \<tau>')) i)) 
                   (at \<tau>' within {0..t})\<close>
            using has_derivative_compose[OF step2[OF \<tau>'_in] proj]
            by simp
        qed
        show ?thesis
          unfolding has_vderiv_on_def has_vector_derivative_def
          using step3
          by simp
      qed
      thus ?thesis
        using field_zero
        by simp
    qed

    have const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
      using has_vderiv_on_zero_imp_constant[OF yi_vderiv t_nn \<tau>_in_t] .

    show \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
      using i_ne const
      unfolding lo_def hi_def
      by simp
  qed

  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
                     lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF t_nn y_sol iv active_ord 
                                       lower_edge upper_edge inactive_maint]
    by blast

  show \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_R_B (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have h0: \<open>lo iU \<le> vec_nth (y \<tau>) iU \<and> vec_nth (y \<tau>) iU \<le> hi iU\<close>
      using main[OF \<tau>_in, of iU] .
    have h1: \<open>lo iV \<le> vec_nth (y \<tau>) iV \<and> vec_nth (y \<tau>) iV \<le> hi iV\<close>
      using main[OF \<tau>_in, of iV] .
    show \<open>in_R_B (y \<tau>)\<close>
      using h0 h1
      unfolding in_R_B_def lo_def hi_def
      by simp
  qed
qed

end  (* gardner_R_B_params *)


subsection \<open>Pulsed reachability via REACH\_lyapunov\<close>

text \<open>
  Two arithmetic facts behind the shrinking boxes below.  Suppose a quantity
  x satisfies x - c <= (x0 - c) * e with 0 <= e <= rho, where c is the value
  that pulls x and x0 is the value of x at the start of a time step.  Then x
  stays below every bound M' that lies above c and above c + (M - c) * rho,
  where M bounds x0 from above.  The second lemma is the mirror image for
  lower bounds.
\<close>

lemma exp_approach_upper:
  fixes x0 x c e \<rho> M M' :: real
  assumes rate: \<open>x - c \<le> (x0 - c) * e\<close>
  assumes e_nn: \<open>0 \<le> e\<close>
  assumes e_le: \<open>e \<le> \<rho>\<close>
  assumes x0_le: \<open>x0 \<le> M\<close>
  assumes c_le: \<open>c \<le> M'\<close>
  assumes bound_le: \<open>c + (M - c) * \<rho> \<le> M'\<close>
  shows \<open>x \<le> M'\<close>
proof (cases \<open>c \<le> x0\<close>)
  case True
  have step1: \<open>(x0 - c) * e \<le> (M - c) * e\<close>
  proof (rule mult_right_mono)
    show \<open>x0 - c \<le> M - c\<close>
      using x0_le
      by linarith
    show \<open>0 \<le> e\<close>
      by (rule e_nn)
  qed
  have step2: \<open>(M - c) * e \<le> (M - c) * \<rho>\<close>
  proof (rule mult_left_mono)
    show \<open>e \<le> \<rho>\<close>
      by (rule e_le)
    show \<open>0 \<le> M - c\<close>
      using True x0_le
      by linarith
  qed
  show ?thesis
    using rate step1 step2 bound_le
    by linarith
next
  case False
  have \<open>(x0 - c) * e \<le> 0\<close>
  proof (rule mult_nonpos_nonneg)
    show \<open>x0 - c \<le> 0\<close>
      using False
      by linarith
    show \<open>0 \<le> e\<close>
      by (rule e_nn)
  qed
  then show ?thesis
    using rate c_le
    by linarith
qed

lemma exp_approach_lower:
  fixes x0 x c e \<rho> m m' :: real
  assumes rate: \<open>c - x \<le> (c - x0) * e\<close>
  assumes e_nn: \<open>0 \<le> e\<close>
  assumes e_le: \<open>e \<le> \<rho>\<close>
  assumes x0_ge: \<open>m \<le> x0\<close>
  assumes c_ge: \<open>m' \<le> c\<close>
  assumes bound_ge: \<open>m' \<le> c - (c - m) * \<rho>\<close>
  shows \<open>m' \<le> x\<close>
proof (cases \<open>x0 \<le> c\<close>)
  case True
  have step1: \<open>(c - x0) * e \<le> (c - m) * e\<close>
  proof (rule mult_right_mono)
    show \<open>c - x0 \<le> c - m\<close>
      using x0_ge
      by linarith
    show \<open>0 \<le> e\<close>
      by (rule e_nn)
  qed
  have step2: \<open>(c - m) * e \<le> (c - m) * \<rho>\<close>
  proof (rule mult_left_mono)
    show \<open>e \<le> \<rho>\<close>
      by (rule e_le)
    show \<open>0 \<le> c - m\<close>
      using True x0_ge
      by linarith
  qed
  show ?thesis
    using rate step1 step2 bound_ge
    by linarith
next
  case False
  have \<open>(c - x0) * e \<le> 0\<close>
  proof (rule mult_nonpos_nonneg)
    show \<open>c - x0 \<le> 0\<close>
      using False
      by linarith
    show \<open>0 \<le> e\<close>
      by (rule e_nn)
  qed
  then show ?thesis
    using rate c_ge
    by linarith
qed

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
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes \<Delta>t :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..\<Delta>t} UNIV\<close>
  assumes \<Delta>t_nn: \<open>0 \<le> \<Delta>t\<close>
  assumes y_in_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow> 
         u_min \<le> vec_nth (y \<tau>) iU \<and> vec_nth (y \<tau>) iU \<le> u_max \<and>
         v_min \<le> vec_nth (y \<tau>) iV \<and> vec_nth (y \<tau>) iV \<le> v_max\<close>
  shows \<open>V_pulse (y \<Delta>t) \<le> V_pulse (y 0) * exp (-\<delta> * \<Delta>t)\<close>
proof -
  have rate_bound: \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
                      (vec_nth (y \<tau>) iU - u_pulse) *
                        (\<alpha>_low / (1 + (vec_nth (y \<tau>) iV)^2) - vec_nth (y \<tau>) iU) +
                      (vec_nth (y \<tau>) iV - v_pulse) *
                        (\<alpha>_base / (1 + (vec_nth (y \<tau>) iU)^2) - vec_nth (y \<tau>) iV) \<le>
                      -\<delta> * V_pulse (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..\<Delta>t}\<close>
    have region: \<open>u_min \<le> vec_nth (y \<tau>) iU\<close> \<open>vec_nth (y \<tau>) iU \<le> u_max\<close>
      \<open>v_min \<le> vec_nth (y \<tau>) iV\<close> \<open>vec_nth (y \<tau>) iV \<le> v_max\<close>
      using y_in_region[OF \<tau>_in]
      by auto
    show \<open>(vec_nth (y \<tau>) iU - u_pulse) *
          (\<alpha>_low / (1 + (vec_nth (y \<tau>) iV)^2) - vec_nth (y \<tau>) iU) +
        (vec_nth (y \<tau>) iV - v_pulse) *
          (\<alpha>_base / (1 + (vec_nth (y \<tau>) iU)^2) - vec_nth (y \<tau>) iV) \<le>
        -\<delta> * V_pulse (y \<tau>)\<close>
      using V_pulse_decrease_sharp[OF \<beta>_eq \<gamma>_eq u_min_nn v_min_nn
          region \<delta>_pos \<delta>_bound] .
  qed
  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
                     \<exists>DV. (V_pulse has_derivative DV) (at (y \<tau>)) \<and>
                          DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
  proof (rule induct_step_from_lie[where V = V_pulse and
                                         f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                         y = y and
                                         lin = \<open>\<lambda>\<tau> w. (vec_nth (y \<tau>) iU - u_pulse) * vec_nth w iU +
                                                      (vec_nth (y \<tau>) iV - v_pulse) * vec_nth w iV\<close>
                                                         and
                                         bnd = \<open>\<lambda>\<tau>. -\<delta> * V_pulse (y \<tau>)\<close> and T = \<Delta>t])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
          (V_pulse has_derivative
            (\<lambda>w. (vec_nth (y \<tau>) iU - u_pulse) * vec_nth w iU +
                 (vec_nth (y \<tau>) iV - v_pulse) * vec_nth w iV)) (at (y \<tau>))\<close>
      using V_pulse_has_derivative
      by blast
  next
    show \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow>
          (\<lambda>w. (vec_nth (y \<tau>) iU - u_pulse) * vec_nth w iU +
               (vec_nth (y \<tau>) iV - v_pulse) * vec_nth w iV)
            (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
    proof -
      fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..\<Delta>t}\<close>
      have lie: \<open>(\<lambda>w. (vec_nth (y \<tau>) iU - u_pulse) * vec_nth w iU +
                      (vec_nth (y \<tau>) iV - v_pulse) * vec_nth w iV)
                   (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) =
                   (vec_nth (y \<tau>) iU - u_pulse) *
                     (\<alpha>_low / (1 + (vec_nth (y \<tau>) iV)^2) - vec_nth (y \<tau>) iU) +
                   (vec_nth (y \<tau>) iV - v_pulse) *
                     (\<alpha>_base / (1 + (vec_nth (y \<tau>) iU)^2) - vec_nth (y \<tau>) iV)\<close>
        unfolding gardner_pulse_field_def
        by (simp add: fun_upd_def \<beta>_eq \<gamma>_eq)
      show \<open>(\<lambda>w.(vec_nth (y \<tau>) iU - u_pulse) * vec_nth w iU + 
                (vec_nth (y \<tau>) iV - v_pulse) * vec_nth w iV)
                (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (y \<tau>)) \<le> -\<delta> * V_pulse (y \<tau>)\<close>
        using rate_bound[OF h\<tau>] lie
        by simp
    qed
  qed

  show ?thesis
    using REACH_lyapunov[where V = V_pulse and \<delta> = \<delta>,
                         OF y_sol \<Delta>t_nn induct_step]
    by simp
qed

lemma pulse_trajectory_reaches_sublevel:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes \<Delta>t L :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..\<Delta>t} UNIV\<close>
  assumes \<Delta>t_nn: \<open>0 \<le> \<Delta>t\<close>
  assumes y_in_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..\<Delta>t} \<Longrightarrow> 
         u_min \<le> vec_nth (y \<tau>) iU \<and> vec_nth (y \<tau>) iU \<le> u_max \<and>
         v_min \<le> vec_nth (y \<tau>) iV \<and> vec_nth (y \<tau>) iV \<le> v_max\<close>
  assumes L_reached: \<open>V_pulse (y 0) * exp (-\<delta> * \<Delta>t) \<le> L\<close>
  shows \<open>V_pulse (y \<Delta>t) \<le> L\<close>
proof -
  have \<open>V_pulse (y \<Delta>t) \<le> V_pulse (y 0) * exp (-\<delta> * \<Delta>t)\<close>
    using pulse_trajectory_exponential_decay[OF y_sol \<Delta>t_nn y_in_region] .
  also have \<open>\<dots> \<le> L\<close>
    using L_reached .
  finally show ?thesis .
qed


subsubsection \<open>Approach to the pulsed equilibrium through shrinking boxes\<close>

text \<open>
  The Lyapunov argument above needs the pulse trajectory inside the region
  [u\_min, u\_max] x [v\_min, v\_max] around the pulsed equilibrium.  A
  trajectory that starts in R\_A is far from that region, so it first has to
  get there.  The lemmas below prove this with REACH\_lyapunov applied to
  affine functions.  While v stays above vl, the u-component is pulled
  towards alpha\_low/(1 + vl\textasciicircum{}2) at exponential rate 1;
  while v stays below vh, it is pushed up towards alpha\_low/(1 + vh\textasciicircum{}2);
  and symmetrically for v.  Iterating these four bounds over time steps of
  fixed length yields a chain of nested boxes that closes in on the pulsed
  equilibrium.
\<close>

lemma pulse_field_u:
  \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> w) iU =
     \<alpha>_low / (1 + (vec_nth w iV)^2) - vec_nth w iU\<close>
  unfolding gardner_pulse_field_def
  by (simp add: fun_upd_def \<beta>_eq)

lemma pulse_field_v:
  \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> w) iV =
     \<alpha>_base / (1 + (vec_nth w iU)^2) - vec_nth w iV\<close>
  unfolding gardner_pulse_field_def
  by (simp add: fun_upd_def \<gamma>_eq)

lemma pulse_field_time_invariant:
  \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau>1 w =
   gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau>2 w\<close>
  unfolding gardner_pulse_field_def
  by simp

text \<open>Both coordinates stay non-negative under the pulsed field.\<close>

lemma pulse_u_nonneg:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u0_nn: \<open>0 \<le> vec_nth (z 0) iU\<close>
  shows \<open>0 \<le> vec_nth (z T) iU\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = -u, the Lie derivative
     u - alpha_low/(1 + v^2) is at most u = -1 * V *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. - vec_nth w iU) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (- vec_nth (z \<tau>) iU)\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. - vec_nth w iU\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. - vec_nth h iU\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (- vec_nth (z \<tau>) iU)\<close> and T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. - vec_nth w iU) has_derivative (\<lambda>h. - vec_nth h iU)) (at (z \<tau>))\<close>
      by (rule has_derivative_minus[OF has_derivative_vec_nth])
  next
    fix \<tau> assume \<open>\<tau> \<in> {0..T}\<close>
    have pos: \<open>0 \<le> \<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2)\<close>
    proof (rule divide_nonneg_pos)
      show \<open>0 \<le> \<alpha>_low\<close>
        using \<alpha>_low_pos
        by linarith
      show \<open>0 < 1 + (vec_nth (z \<tau>) iV)^2\<close>
        by (rule add_pos_nonneg) simp_all
    qed
    have fu: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU =
              \<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2) - vec_nth (z \<tau>) iU\<close>
      by (rule pulse_field_u)
    show \<open>- vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU \<le>
            - 1 * (- vec_nth (z \<tau>) iU)\<close>
      using pos fu
      by linarith
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  have reach: \<open>vec_nth (z 0) iU * exp (- T) \<le> vec_nth (z T) iU\<close>
    using REACH_lyapunov[where V = \<open>\<lambda>w. - vec_nth w iU\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
  have \<open>0 \<le> vec_nth (z 0) iU * exp (- T)\<close>
    by (rule mult_nonneg_nonneg) (simp_all add: u0_nn)
  then show ?thesis
    using reach
    by linarith
qed

lemma pulse_v_nonneg:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes v0_nn: \<open>0 \<le> vec_nth (z 0) iV\<close>
  shows \<open>0 \<le> vec_nth (z T) iV\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = -v, the Lie derivative
     v - alpha_base/(1 + u^2) is at most v = -1 * V *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. - vec_nth w iV) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (- vec_nth (z \<tau>) iV)\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. - vec_nth w iV\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. - vec_nth h iV\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (- vec_nth (z \<tau>) iV)\<close> and T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. - vec_nth w iV) has_derivative (\<lambda>h. - vec_nth h iV)) (at (z \<tau>))\<close>
      by (rule has_derivative_minus[OF has_derivative_vec_nth])
  next
    fix \<tau> assume \<open>\<tau> \<in> {0..T}\<close>
    have pos: \<open>0 \<le> \<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2)\<close>
    proof (rule divide_nonneg_pos)
      show \<open>0 \<le> \<alpha>_base\<close>
        using \<alpha>_base_above_threshold
        by linarith
      show \<open>0 < 1 + (vec_nth (z \<tau>) iU)^2\<close>
        by (rule add_pos_nonneg) simp_all
    qed
    have fv: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV =
              \<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2) - vec_nth (z \<tau>) iV\<close>
      by (rule pulse_field_v)
    show \<open>- vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV \<le>
            - 1 * (- vec_nth (z \<tau>) iV)\<close>
      using pos fv
      by linarith
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  have reach: \<open>vec_nth (z 0) iV * exp (- T) \<le> vec_nth (z T) iV\<close>
    using REACH_lyapunov[where V = \<open>\<lambda>w. - vec_nth w iV\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
  have \<open>0 \<le> vec_nth (z 0) iV * exp (- T)\<close>
    by (rule mult_nonneg_nonneg) (simp_all add: v0_nn)
  then show ?thesis
    using reach
    by linarith
qed

text \<open>
  The four exponential approach bounds.  Each one is REACH\_lyapunov with
  decay rate 1 for an affine function of a single coordinate.
\<close>

lemma pulse_u_upper:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T vl :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes vl_nn: \<open>0 \<le> vl\<close>
  assumes v_ge: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vl \<le> vec_nth (z \<tau>) iV\<close>
  shows \<open>vec_nth (z T) iU - \<alpha>_low / (1 + vl^2) \<le>
           (vec_nth (z 0) iU - \<alpha>_low / (1 + vl^2)) * exp (- T)\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = u - alpha_low/(1 + vl^2),
     the Lie derivative alpha_low/(1 + v^2) - u is at most -1 * V,
     because v >= vl >= 0 *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. vec_nth w iU - \<alpha>_low / (1 + vl^2)) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (vec_nth (z \<tau>) iU - \<alpha>_low / (1 + vl^2))\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. vec_nth w iU - \<alpha>_low / (1 + vl^2)\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. vec_nth h iU - 0\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (vec_nth (z \<tau>) iU - \<alpha>_low / (1 + vl^2))\<close> and
                                       T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. vec_nth w iU - \<alpha>_low / (1 + vl^2)) has_derivative (\<lambda>h. vec_nth h iU - 0))
             (at (z \<tau>))\<close>
      by (rule has_derivative_diff[OF has_derivative_vec_nth has_derivative_const])
  next
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    have sq: \<open>vl^2 \<le> (vec_nth (z \<tau>) iV)^2\<close>
      by (rule power_mono[OF v_ge[OF \<tau>_in] vl_nn])
    have frac: \<open>\<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2) \<le> \<alpha>_low / (1 + vl^2)\<close>
    proof (rule frac_le)
      show \<open>0 \<le> \<alpha>_low\<close>
        using \<alpha>_low_pos
        by linarith
      show \<open>\<alpha>_low \<le> \<alpha>_low\<close>
        by simp
      show \<open>0 < 1 + vl^2\<close>
        by (rule add_pos_nonneg) simp_all
      show \<open>1 + vl^2 \<le> 1 + (vec_nth (z \<tau>) iV)^2\<close>
        using sq
        by simp
    qed
    have fu: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU =
              \<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2) - vec_nth (z \<tau>) iU\<close>
      by (rule pulse_field_u)
    show \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU - 0 \<le>
            - 1 * (vec_nth (z \<tau>) iU - \<alpha>_low / (1 + vl^2))\<close>
      using frac fu 
      by auto 
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  show ?thesis
    using REACH_lyapunov[where V = \<open>\<lambda>w. vec_nth w iU - \<alpha>_low / (1 + vl^2)\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
qed

lemma pulse_u_lower:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T vh :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes v_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 0 \<le> vec_nth (z \<tau>) iV\<close>
  assumes v_le: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (z \<tau>) iV \<le> vh\<close>
  shows \<open>\<alpha>_low / (1 + vh^2) - vec_nth (z T) iU \<le>
           (\<alpha>_low / (1 + vh^2) - vec_nth (z 0) iU) * exp (- T)\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = alpha_low/(1 + vh^2) - u,
     the Lie derivative u - alpha_low/(1 + v^2) is at most -1 * V,
     because 0 <= v <= vh *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. \<alpha>_low / (1 + vh^2) - vec_nth w iU) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (\<alpha>_low / (1 + vh^2) - vec_nth (z \<tau>) iU)\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. \<alpha>_low / (1 + vh^2) - vec_nth w iU\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. 0 - vec_nth h iU\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (\<alpha>_low / (1 + vh^2) - vec_nth (z \<tau>) iU)\<close> and
                                       T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. \<alpha>_low / (1 + vh^2) - vec_nth w iU) has_derivative (\<lambda>h. 0 - vec_nth h iU))
             (at (z \<tau>))\<close>
      by (rule has_derivative_diff[OF has_derivative_const has_derivative_vec_nth])
  next
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    have sq: \<open>(vec_nth (z \<tau>) iV)^2 \<le> vh^2\<close>
      by (rule power_mono[OF v_le[OF \<tau>_in] v_nn[OF \<tau>_in]])
    have frac: \<open>\<alpha>_low / (1 + vh^2) \<le> \<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2)\<close>
    proof (rule frac_le)
      show \<open>0 \<le> \<alpha>_low\<close>
        using \<alpha>_low_pos
        by linarith
      show \<open>\<alpha>_low \<le> \<alpha>_low\<close>
        by simp
      show \<open>0 < 1 + (vec_nth (z \<tau>) iV)^2\<close>
        by (rule add_pos_nonneg) simp_all
      show \<open>1 + (vec_nth (z \<tau>) iV)^2 \<le> 1 + vh^2\<close>
        using sq
        by simp
    qed
    have fu: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU =
              \<alpha>_low / (1 + (vec_nth (z \<tau>) iV)^2) - vec_nth (z \<tau>) iU\<close>
      by (rule pulse_field_u)
    show \<open>0 - vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iU \<le>
            - 1 * (\<alpha>_low / (1 + vh^2) - vec_nth (z \<tau>) iU)\<close>
      using frac fu 
      by auto
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  show ?thesis
    using REACH_lyapunov[where V = \<open>\<lambda>w. \<alpha>_low / (1 + vh^2) - vec_nth w iU\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
qed

lemma pulse_v_upper:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T ul :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes ul_nn: \<open>0 \<le> ul\<close>
  assumes u_ge: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> ul \<le> vec_nth (z \<tau>) iU\<close>
  shows \<open>vec_nth (z T) iV - \<alpha>_base / (1 + ul^2) \<le>
           (vec_nth (z 0) iV - \<alpha>_base / (1 + ul^2)) * exp (- T)\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = v - alpha_base/(1 + ul^2),
     the Lie derivative alpha_base/(1 + u^2) - v is at most -1 * V,
     because u >= ul >= 0 *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. vec_nth w iV - \<alpha>_base / (1 + ul^2)) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (vec_nth (z \<tau>) iV - \<alpha>_base / (1 + ul^2))\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. vec_nth w iV - \<alpha>_base / (1 + ul^2)\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. vec_nth h iV - 0\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (vec_nth (z \<tau>) iV - \<alpha>_base / (1 + ul^2))\<close> and
                                       T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. vec_nth w iV - \<alpha>_base / (1 + ul^2)) has_derivative (\<lambda>h. vec_nth h iV - 0))
             (at (z \<tau>))\<close>
      by (rule has_derivative_diff[OF has_derivative_vec_nth has_derivative_const])
  next
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    have sq: \<open>ul^2 \<le> (vec_nth (z \<tau>) iU)^2\<close>
      by (rule power_mono[OF u_ge[OF \<tau>_in] ul_nn])
    have frac: \<open>\<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2) \<le> \<alpha>_base / (1 + ul^2)\<close>
    proof (rule frac_le)
      show \<open>0 \<le> \<alpha>_base\<close>
        using \<alpha>_base_above_threshold
        by linarith
      show \<open>\<alpha>_base \<le> \<alpha>_base\<close>
        by simp
      show \<open>0 < 1 + ul^2\<close>
        by (rule add_pos_nonneg) simp_all
      show \<open>1 + ul^2 \<le> 1 + (vec_nth (z \<tau>) iU)^2\<close>
        using sq
        by simp
    qed
    have fv: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV =
              \<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2) - vec_nth (z \<tau>) iV\<close>
      by (rule pulse_field_v)
    show \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV - 0 \<le>
            - 1 * (vec_nth (z \<tau>) iV - \<alpha>_base / (1 + ul^2))\<close>
      using frac fv 
      by auto
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  show ?thesis
    using REACH_lyapunov[where V = \<open>\<lambda>w. vec_nth w iV - \<alpha>_base / (1 + ul^2)\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
qed

lemma pulse_v_lower:
  fixes z :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T uh :: real
  assumes z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 0 \<le> vec_nth (z \<tau>) iU\<close>
  assumes u_le: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (z \<tau>) iU \<le> uh\<close>
  shows \<open>\<alpha>_base / (1 + uh^2) - vec_nth (z T) iV \<le>
           (\<alpha>_base / (1 + uh^2) - vec_nth (z 0) iV) * exp (- T)\<close>
proof -
  (* PROOF OBLIGATION (induct_step): with V(w) = alpha_base/(1 + uh^2) - v,
     the Lie derivative v - alpha_base/(1 + u^2) is at most -1 * V,
     because 0 <= u <= uh *)
  have lie: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              \<exists>DV. ((\<lambda>w. \<alpha>_base / (1 + uh^2) - vec_nth w iV) has_derivative DV) (at (z \<tau>)) \<and>
                   DV (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) \<le>
                     - 1 * (\<alpha>_base / (1 + uh^2) - vec_nth (z \<tau>) iV)\<close>
  proof (rule induct_step_from_lie[where V = \<open>\<lambda>w. \<alpha>_base / (1 + uh^2) - vec_nth w iV\<close> and
                                       f = \<open>gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>\<close> and
                                       y = z and lin = \<open>\<lambda>\<tau> h. 0 - vec_nth h iV\<close> and
                                       bnd = \<open>\<lambda>\<tau>. - 1 * (\<alpha>_base / (1 + uh^2) - vec_nth (z \<tau>) iV)\<close> and
                                       T = T])
    show \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
           ((\<lambda>w. \<alpha>_base / (1 + uh^2) - vec_nth w iV) has_derivative (\<lambda>h. 0 - vec_nth h iV))
             (at (z \<tau>))\<close>
      by (rule has_derivative_diff[OF has_derivative_const has_derivative_vec_nth])
  next
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    have sq: \<open>(vec_nth (z \<tau>) iU)^2 \<le> uh^2\<close>
      by (rule power_mono[OF u_le[OF \<tau>_in] u_nn[OF \<tau>_in]])
    have frac: \<open>\<alpha>_base / (1 + uh^2) \<le> \<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2)\<close>
    proof (rule frac_le)
      show \<open>0 \<le> \<alpha>_base\<close>
        using \<alpha>_base_above_threshold
        by linarith
      show \<open>\<alpha>_base \<le> \<alpha>_base\<close>
        by simp
      show \<open>0 < 1 + (vec_nth (z \<tau>) iU)^2\<close>
        by (rule add_pos_nonneg) simp_all
      show \<open>1 + (vec_nth (z \<tau>) iU)^2 \<le> 1 + uh^2\<close>
        using sq
        by simp
    qed
    have fv: \<open>vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV =
              \<alpha>_base / (1 + (vec_nth (z \<tau>) iU)^2) - vec_nth (z \<tau>) iV\<close>
      by (rule pulse_field_v)
    show \<open>0 - vec_nth (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma> \<tau> (z \<tau>)) iV \<le>
            - 1 * (\<alpha>_base / (1 + uh^2) - vec_nth (z \<tau>) iV)\<close>
      using frac fv 
      by auto
  qed
  (* APPLY REACH_lyapunov with delta = 1 *)
  show ?thesis
    using REACH_lyapunov[where V = \<open>\<lambda>w. \<alpha>_base / (1 + uh^2) - vec_nth w iV\<close> and \<delta> = 1,
                         OF z_sol T_nn lie]
    by simp
qed

text \<open>
  The first box.  A trajectory that starts in the box
  [ul0, uh0] x [vl0, vh0] with non-negative lower corner stays in the
  larger box [ul, uh] x [vl, vh] during the whole pulse, provided that the
  larger box contains the starting box, its upper corner lies above
  (alpha\_low, alpha\_base), and its lower corner lies below the values that
  the Hill terms take at that upper corner.
\<close>

lemma pulse_box_initial:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes D ul0 uh0 vl0 vh0 ul uh vl vh :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..D} UNIV\<close>
  assumes start: \<open>ul0 \<le> vec_nth (y 0) iU\<close> \<open>vec_nth (y 0) iU \<le> uh0\<close>
                 \<open>vl0 \<le> vec_nth (y 0) iV\<close> \<open>vec_nth (y 0) iV \<le> vh0\<close>
  assumes ul0_nn: \<open>0 \<le> ul0\<close>
  assumes vl0_nn: \<open>0 \<le> vl0\<close>
  assumes uh_ok: \<open>uh0 \<le> uh\<close> \<open>\<alpha>_low \<le> uh\<close>
  assumes vh_ok: \<open>vh0 \<le> vh\<close> \<open>\<alpha>_base \<le> vh\<close>
  assumes ul_ok: \<open>ul \<le> ul0\<close> \<open>ul \<le> \<alpha>_low / (1 + vh^2)\<close>
  assumes vl_ok: \<open>vl \<le> vl0\<close> \<open>vl \<le> \<alpha>_base / (1 + uh^2)\<close>
  shows \<open>\<forall>\<tau>\<in>{0..D}. in_box ul uh vl vh (y \<tau>)\<close>
proof -
  have sub: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow>
               (y solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..s} UNIV\<close>
    by (rule solves_ode_subset_ivl[OF y_sol])
  have y0_u_nn: \<open>0 \<le> vec_nth (y 0) iU\<close>
    using start(1) ul0_nn
    by linarith
  have y0_v_nn: \<open>0 \<le> vec_nth (y 0) iV\<close>
    using start(3) vl0_nn
    by linarith

  (* STEP 1: both coordinates stay non-negative *)
  have u_nn: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> 0 \<le> vec_nth (y s) iU\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    show \<open>0 \<le> vec_nth (y s) iU\<close>
      by (rule pulse_u_nonneg[OF sub[OF s_in] s_nn y0_u_nn])
  qed
  have v_nn: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> 0 \<le> vec_nth (y s) iV\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    show \<open>0 \<le> vec_nth (y s) iV\<close>
      by (rule pulse_v_nonneg[OF sub[OF s_in] s_nn y0_v_nn])
  qed

  (* STEP 2: upper bounds; each one only needs the other coordinate to be
     non-negative, so the Hill term is at most alpha_low or alpha_base *)
  have u_le: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> vec_nth (y s) iU \<le> uh\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    have v_nn_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iV\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>0 \<le> vec_nth (y \<tau>) iV\<close>
        by (rule v_nn)
    qed
    have rate: \<open>vec_nth (y s) iU - \<alpha>_low / (1 + 0^2) \<le>
                  (vec_nth (y 0) iU - \<alpha>_low / (1 + 0^2)) * exp (- s)\<close>
      by (rule pulse_u_upper[OF sub[OF s_in] s_nn order_refl v_nn_s])
    have e_nn: \<open>0 \<le> exp (- s)\<close>
      by simp
    have e_le: \<open>exp (- s) \<le> 1\<close>
      using s_nn
      by simp
    have c_le: \<open>\<alpha>_low / (1 + 0^2) \<le> uh\<close>
      using uh_ok(2)
      by simp
    have b_le: \<open>\<alpha>_low / (1 + 0^2) + (uh0 - \<alpha>_low / (1 + 0^2)) * 1 \<le> uh\<close>
      using uh_ok(1)
      by simp
    show \<open>vec_nth (y s) iU \<le> uh\<close>
      by (rule exp_approach_upper[OF rate e_nn e_le start(2) c_le b_le])
  qed
  have v_le: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> vec_nth (y s) iV \<le> vh\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    have u_nn_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iU\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>0 \<le> vec_nth (y \<tau>) iU\<close>
        by (rule u_nn)
    qed
    have rate: \<open>vec_nth (y s) iV - \<alpha>_base / (1 + 0^2) \<le>
                  (vec_nth (y 0) iV - \<alpha>_base / (1 + 0^2)) * exp (- s)\<close>
      by (rule pulse_v_upper[OF sub[OF s_in] s_nn order_refl u_nn_s])
    have e_nn: \<open>0 \<le> exp (- s)\<close>
      by simp
    have e_le: \<open>exp (- s) \<le> 1\<close>
      using s_nn
      by simp
    have c_le: \<open>\<alpha>_base / (1 + 0^2) \<le> vh\<close>
      using vh_ok(2)
      by simp
    have b_le: \<open>\<alpha>_base / (1 + 0^2) + (vh0 - \<alpha>_base / (1 + 0^2)) * 1 \<le> vh\<close>
      using vh_ok(1)
      by simp
    show \<open>vec_nth (y s) iV \<le> vh\<close>
      by (rule exp_approach_upper[OF rate e_nn e_le start(4) c_le b_le])
  qed

  (* STEP 3: lower bounds; each one uses the upper bound of the other
     coordinate from STEP 2 *)
  have u_ge: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> ul \<le> vec_nth (y s) iU\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    have v_nn_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iV\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>0 \<le> vec_nth (y \<tau>) iV\<close>
        by (rule v_nn)
    qed
    have v_le_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> vec_nth (y \<tau>) iV \<le> vh\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>vec_nth (y \<tau>) iV \<le> vh\<close>
        by (rule v_le)
    qed
    have rate: \<open>\<alpha>_low / (1 + vh^2) - vec_nth (y s) iU \<le>
                  (\<alpha>_low / (1 + vh^2) - vec_nth (y 0) iU) * exp (- s)\<close>
      by (rule pulse_u_lower[OF sub[OF s_in] s_nn v_nn_s v_le_s])
    have e_nn: \<open>0 \<le> exp (- s)\<close>
      by simp
    have e_le: \<open>exp (- s) \<le> 1\<close>
      using s_nn
      by simp
    have b_ge: \<open>ul \<le> \<alpha>_low / (1 + vh^2) - (\<alpha>_low / (1 + vh^2) - ul0) * 1\<close>
      using ul_ok(1)
      by simp
    show \<open>ul \<le> vec_nth (y s) iU\<close>
      by (rule exp_approach_lower[OF rate e_nn e_le start(1) ul_ok(2) b_ge])
  qed
  have v_ge: \<open>\<And>s. s \<in> {0..D} \<Longrightarrow> vl \<le> vec_nth (y s) iV\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..D}\<close>
    have s_nn: \<open>0 \<le> s\<close>
      using s_in
      by simp
    have u_nn_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iU\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>0 \<le> vec_nth (y \<tau>) iU\<close>
        by (rule u_nn)
    qed
    have u_le_s: \<open>\<And>\<tau>. \<tau> \<in> {0..s} \<Longrightarrow> vec_nth (y \<tau>) iU \<le> uh\<close>
    proof -
      fix \<tau> assume \<open>\<tau> \<in> {0..s}\<close>
      then have \<open>\<tau> \<in> {0..D}\<close>
        using s_in
        by auto
      then show \<open>vec_nth (y \<tau>) iU \<le> uh\<close>
        by (rule u_le)
    qed
    have rate: \<open>\<alpha>_base / (1 + uh^2) - vec_nth (y s) iV \<le>
                  (\<alpha>_base / (1 + uh^2) - vec_nth (y 0) iV) * exp (- s)\<close>
      by (rule pulse_v_lower[OF sub[OF s_in] s_nn u_nn_s u_le_s])
    have e_nn: \<open>0 \<le> exp (- s)\<close>
      by simp
    have e_le: \<open>exp (- s) \<le> 1\<close>
      using s_nn
      by simp
    have b_ge: \<open>vl \<le> \<alpha>_base / (1 + uh^2) - (\<alpha>_base / (1 + uh^2) - vl0) * 1\<close>
      using vl_ok(1)
      by simp
    show \<open>vl \<le> vec_nth (y s) iV\<close>
      by (rule exp_approach_lower[OF rate e_nn e_le start(3) vl_ok(2) b_ge])
  qed

  show ?thesis
  proof
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..D}\<close>
    show \<open>in_box ul uh vl vh (y \<tau>)\<close>
      unfolding in_box_def
      using u_ge[OF \<tau>_in] u_le[OF \<tau>_in] v_ge[OF \<tau>_in] v_le[OF \<tau>_in]
      by simp
  qed
qed

text \<open>
  One step of the chain.  If the trajectory is in the box
  [ul, uh] x [vl, vh] from time S on, then it is in the box
  [ul', uh'] x [vl', vh'] from time S' >= S + h on.  The new bounds only
  have to dominate the exponential approach estimates over a time step of
  length h, with exp(-h) <= rho.  For instance the new upper bound uh' of u
  must lie above alpha\_low/(1 + vl\textasciicircum{}2), the value that pulls
  u while v >= vl, and above that value plus rho times the remaining gap
  to uh.
\<close>

lemma pulse_box_step:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes D S S' h \<rho> ul uh vl vh ul' uh' vl' vh' :: real
  assumes y_sol: \<open>(y solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..D} UNIV\<close>
  assumes S_nn: \<open>0 \<le> S\<close>
  assumes h_nn: \<open>0 \<le> h\<close>
  assumes S'_ge: \<open>S + h \<le> S'\<close>
  assumes rho: \<open>exp (- h) \<le> \<rho>\<close>
  assumes ul_nn: \<open>0 \<le> ul\<close>
  assumes vl_nn: \<open>0 \<le> vl\<close>
  assumes box: \<open>\<forall>\<tau>\<in>{S..D}. in_box ul uh vl vh (y \<tau>)\<close>
  assumes uh_new: \<open>\<alpha>_low / (1 + vl^2) \<le> uh'\<close>
                  \<open>\<alpha>_low / (1 + vl^2) + (uh - \<alpha>_low / (1 + vl^2)) * \<rho> \<le> uh'\<close>
  assumes ul_new: \<open>ul' \<le> \<alpha>_low / (1 + vh^2)\<close>
                  \<open>ul' \<le> \<alpha>_low / (1 + vh^2) - (\<alpha>_low / (1 + vh^2) - ul) * \<rho>\<close>
  assumes vh_new: \<open>\<alpha>_base / (1 + ul^2) \<le> vh'\<close>
                  \<open>\<alpha>_base / (1 + ul^2) + (vh - \<alpha>_base / (1 + ul^2)) * \<rho> \<le> vh'\<close>
  assumes vl_new: \<open>vl' \<le> \<alpha>_base / (1 + uh^2)\<close>
                  \<open>vl' \<le> \<alpha>_base / (1 + uh^2) - (\<alpha>_base / (1 + uh^2) - vl) * \<rho>\<close>
  shows \<open>\<forall>\<tau>\<in>{S'..D}. in_box ul' uh' vl' vh' (y \<tau>)\<close>
proof
  fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {S'..D}\<close>

  (* STEP 1: restart the trajectory at time s0 = tau - h, so that the
     restarted trajectory z reaches y tau at time h *)
  define s0 where \<open>s0 = \<tau> - h\<close>
  have s0_ge: \<open>S \<le> s0\<close>
    using \<tau>_in S'_ge
    unfolding s0_def
    by auto
  have s0_nn: \<open>0 \<le> s0\<close>
    using s0_ge S_nn
    by linarith
  have s0_le: \<open>s0 \<le> D\<close>
    using \<tau>_in h_nn
    unfolding s0_def
    by auto
  have h_in: \<open>h \<in> {0..(D - s0)}\<close>
    using \<tau>_in h_nn
    unfolding s0_def
    by auto
  define z where \<open>z = (\<lambda>s. y (s0 + s))\<close>
  have z_sol_long: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>))
                      {0..(D - s0)} UNIV\<close>
    unfolding z_def
    by (rule solves_ode_shift[OF y_sol s0_nn s0_le pulse_field_time_invariant])
  have z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) {0..h} UNIV\<close>
    by (rule solves_ode_subset_ivl[OF z_sol_long h_in])
  have z_h: \<open>z h = y \<tau>\<close>
    unfolding z_def s0_def
    by simp

  (* STEP 2: the restarted trajectory stays in the old box *)
  have z_box: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> in_box ul uh vl vh (z s)\<close>
  proof -
    fix s assume s_in: \<open>s \<in> {0..h}\<close>
    have \<open>s0 + s \<in> {S..D}\<close>
      using s_in s0_ge \<tau>_in
      unfolding s0_def
      by auto
    then show \<open>in_box ul uh vl vh (z s)\<close>
      using box
      unfolding z_def
      by blast
  qed
  have z_u_ge: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> ul \<le> vec_nth (z s) iU\<close>
    using z_box
    unfolding in_box_def
    by blast
  have z_u_le: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> vec_nth (z s) iU \<le> uh\<close>
    using z_box
    unfolding in_box_def
    by blast
  have z_v_ge: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> vl \<le> vec_nth (z s) iV\<close>
    using z_box
    unfolding in_box_def
    by blast
  have z_v_le: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> vec_nth (z s) iV \<le> vh\<close>
    using z_box
    unfolding in_box_def
    by blast
  have z_u_nn: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> 0 \<le> vec_nth (z s) iU\<close>
  proof -
    fix s assume \<open>s \<in> {0..h}\<close>
    then have \<open>ul \<le> vec_nth (z s) iU\<close>
      by (rule z_u_ge)
    then show \<open>0 \<le> vec_nth (z s) iU\<close>
      using ul_nn
      by linarith
  qed
  have z_v_nn: \<open>\<And>s. s \<in> {0..h} \<Longrightarrow> 0 \<le> vec_nth (z s) iV\<close>
  proof -
    fix s assume \<open>s \<in> {0..h}\<close>
    then have \<open>vl \<le> vec_nth (z s) iV\<close>
      by (rule z_v_ge)
    then show \<open>0 \<le> vec_nth (z s) iV\<close>
      using vl_nn
      by linarith
  qed
  have h0: \<open>(0::real) \<in> {0..h}\<close>
    using h_nn
    by simp
  have z0: \<open>ul \<le> vec_nth (z 0) iU\<close> \<open>vec_nth (z 0) iU \<le> uh\<close>
           \<open>vl \<le> vec_nth (z 0) iV\<close> \<open>vec_nth (z 0) iV \<le> vh\<close>
    using z_box[OF h0]
    unfolding in_box_def
    by simp_all

  (* STEP 3: the four exponential approach estimates over [0..h] *)
  have u_up: \<open>vec_nth (z h) iU - \<alpha>_low / (1 + vl^2) \<le>
                (vec_nth (z 0) iU - \<alpha>_low / (1 + vl^2)) * exp (- h)\<close>
    by (rule pulse_u_upper[OF z_sol h_nn vl_nn z_v_ge])
  have u_lo: \<open>\<alpha>_low / (1 + vh^2) - vec_nth (z h) iU \<le>
                (\<alpha>_low / (1 + vh^2) - vec_nth (z 0) iU) * exp (- h)\<close>
    by (rule pulse_u_lower[OF z_sol h_nn z_v_nn z_v_le])
  have v_up: \<open>vec_nth (z h) iV - \<alpha>_base / (1 + ul^2) \<le>
                (vec_nth (z 0) iV - \<alpha>_base / (1 + ul^2)) * exp (- h)\<close>
    by (rule pulse_v_upper[OF z_sol h_nn ul_nn z_u_ge])
  have v_lo: \<open>\<alpha>_base / (1 + uh^2) - vec_nth (z h) iV \<le>
                (\<alpha>_base / (1 + uh^2) - vec_nth (z 0) iV) * exp (- h)\<close>
    by (rule pulse_v_lower[OF z_sol h_nn z_u_nn z_u_le])

  (* STEP 4: the new bounds dominate the estimates *)
  have e_nn: \<open>0 \<le> exp (- h)\<close>
    by simp
  have new_uh: \<open>vec_nth (z h) iU \<le> uh'\<close>
    by (rule exp_approach_upper[OF u_up e_nn rho z0(2) uh_new(1) uh_new(2)])
  have new_ul: \<open>ul' \<le> vec_nth (z h) iU\<close>
    by (rule exp_approach_lower[OF u_lo e_nn rho z0(1) ul_new(1) ul_new(2)])
  have new_vh: \<open>vec_nth (z h) iV \<le> vh'\<close>
    by (rule exp_approach_upper[OF v_up e_nn rho z0(4) vh_new(1) vh_new(2)])
  have new_vl: \<open>vl' \<le> vec_nth (z h) iV\<close>
    by (rule exp_approach_lower[OF v_lo e_nn rho z0(3) vl_new(1) vl_new(2)])
  show \<open>in_box ul' uh' vl' vh' (y \<tau>)\<close>
    using new_ul new_uh new_vl new_vh
    unfolding in_box_def z_h
    by simp
qed

end  (* gardner_pulse_lyapunov *)


subsection \<open>Final induced switching theorem\<close>

text \<open>
  The pulse is split into two phases.  During the approach phase
  [0, T\_app] the trajectory travels from R\_A into the region where the
  Lyapunov estimate holds; during the Lyapunov phase
  [T\_app, t\_end - t\_start] V\_pulse decays until the trajectory lies in
  the sublevel set where V\_pulse <= L\_target, which is inside R\_B.  The
  theorem takes the approach phase as a hypothesis about pulse trajectories
  that start in R\_A.  The concrete instance below discharges it with the
  shrinking boxes of pulse\_box\_initial and pulse\_box\_step.
\<close>

locale gardner_induced_switching = 
  gardner_R_A_params + gardner_R_B_params + gardner_pulse_lyapunov +
  fixes L_target :: real
  assumes sublevel_in_R_B: 
    \<open>\<And>v :: (real, 'a) vec. V_pulse v \<le> L_target \<Longrightarrow> in_R_B v\<close>
begin

theorem induced_switching:
  fixes y1 y2 y3 :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes t_start t_end T T_app :: real
  assumes y1_sol: \<open>(y1 solves_ode (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma>)) 
                     {0..t_start} UNIV\<close>
  assumes y2_sol: \<open>(y2 solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) 
                     {0..(t_end - t_start)} UNIV\<close>
  assumes y3_sol: \<open>(y3 solves_ode (gardner_baseline_field iU iV \<alpha>_base \<beta> \<gamma>)) 
                     {0..(T - t_end)} UNIV\<close>
  assumes glue1: \<open>y2 0 = y1 t_start\<close>
  assumes glue2: \<open>y3 0 = y2 (t_end - t_start)\<close>
  assumes t_start_nn: \<open>0 \<le> t_start\<close>
  assumes T_app_nn: \<open>0 \<le> T_app\<close>
  assumes T_app_le: \<open>T_app \<le> t_end - t_start\<close>
  assumes T_after_end: \<open>t_end \<le> T\<close>
  assumes y1_starts_in_R_A: \<open>in_R_A (y1 0)\<close>
  \<comment> \<open>Approach phase: a pulse trajectory that starts in R\_A is inside the
      Lyapunov region from time T\_app until the end of the pulse.\<close>
  assumes approach_from_R_A:
    \<open>in_R_A (y2 0) \<Longrightarrow>
       \<forall>\<tau>\<in>{T_app..(t_end - t_start)}.
         u_min \<le> vec_nth (y2 \<tau>) iU \<and> vec_nth (y2 \<tau>) iU \<le> u_max \<and>
         v_min \<le> vec_nth (y2 \<tau>) iV \<and> vec_nth (y2 \<tau>) iV \<le> v_max\<close>
  \<comment> \<open>Lyapunov phase: the rest of the pulse is long enough for V\_pulse to
      decay below L\_target.\<close>
  assumes pulse_long_enough: 
    \<open>V_pulse (y2 T_app) * exp (-\<delta> * (t_end - t_start - T_app)) \<le> L_target\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> in_R_B (y3 \<tau>)\<close>
proof -
  (* STAGE 1: baseline dynamics, the trajectory stays in R_A *)
  have y1_in_R_A: \<open>\<And>\<tau>. \<tau> \<in> {0..t_start} \<Longrightarrow> in_R_A (y1 \<tau>)\<close>
    using R_A_forward_invariant[OF y1_sol t_start_nn y1_starts_in_R_A] .

  have y1_end_in_R_A: \<open>in_R_A (y1 t_start)\<close>
    using y1_in_R_A[of t_start] t_start_nn
    by simp

  have y2_starts_in_R_A: \<open>in_R_A (y2 0)\<close>
    using glue1 y1_end_in_R_A
    by simp

  (* STAGE 2a: approach phase, from R_A into the Lyapunov region *)
  have region: \<open>\<forall>\<tau>\<in>{T_app..(t_end - t_start)}.
                  u_min \<le> vec_nth (y2 \<tau>) iU \<and> vec_nth (y2 \<tau>) iU \<le> u_max \<and>
                  v_min \<le> vec_nth (y2 \<tau>) iV \<and> vec_nth (y2 \<tau>) iV \<le> v_max\<close>
    by (rule approach_from_R_A[OF y2_starts_in_R_A])

  (* STAGE 2b: Lyapunov phase, restart the pulse trajectory at T_app *)
  define z where \<open>z = (\<lambda>s. y2 (T_app + s))\<close>

  have z_sol: \<open>(z solves_ode (gardner_pulse_field iU iV \<alpha>_base \<alpha>_low \<beta> \<gamma>)) 
                 {0..(t_end - t_start - T_app)} UNIV\<close>
    unfolding z_def
    by (rule solves_ode_shift[OF y2_sol T_app_nn T_app_le pulse_field_time_invariant])

  have \<Delta>_nn: \<open>0 \<le> t_end - t_start - T_app\<close>
    using T_app_le
    by simp

  have z_region: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..(t_end - t_start - T_app)} \<Longrightarrow>
         u_min \<le> vec_nth (z \<tau>) iU \<and> vec_nth (z \<tau>) iU \<le> u_max \<and>
         v_min \<le> vec_nth (z \<tau>) iV \<and> vec_nth (z \<tau>) iV \<le> v_max\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..(t_end - t_start - T_app)}\<close>
    have \<open>T_app + \<tau> \<in> {T_app..(t_end - t_start)}\<close>
      using \<tau>_in
      by auto
    then show \<open>u_min \<le> vec_nth (z \<tau>) iU \<and> vec_nth (z \<tau>) iU \<le> u_max \<and>
               v_min \<le> vec_nth (z \<tau>) iV \<and> vec_nth (z \<tau>) iV \<le> v_max\<close>
      using region
      unfolding z_def
      by blast
  qed

  have L_reached: \<open>V_pulse (z 0) * exp (-\<delta> * (t_end - t_start - T_app)) \<le> L_target\<close>
    using pulse_long_enough
    unfolding z_def
    by simp

  have z_reaches_sublevel: \<open>V_pulse (z (t_end - t_start - T_app)) \<le> L_target\<close>
    by (rule pulse_trajectory_reaches_sublevel[OF z_sol \<Delta>_nn z_region L_reached])

  have z_end: \<open>z (t_end - t_start - T_app) = y2 (t_end - t_start)\<close>
  proof -
    have shift: \<open>T_app + (t_end - t_start - T_app) = t_end - t_start\<close>
      by simp
    show ?thesis
      unfolding z_def
      using shift
      by (rule arg_cong[where f = y2])
  qed

  have y2_reaches_sublevel: \<open>V_pulse (y2 (t_end - t_start)) \<le> L_target\<close>
    using z_reaches_sublevel
    unfolding z_end .

  have y2_end_in_R_B: \<open>in_R_B (y2 (t_end - t_start))\<close>
    using sublevel_in_R_B[OF y2_reaches_sublevel] .

  (* STAGE 3: baseline dynamics again, the trajectory stays in R_B *)
  have y3_starts_in_R_B: \<open>in_R_B (y3 0)\<close>
    using glue2 y2_end_in_R_B
    by simp

  have T_end_nn: \<open>0 \<le> T - t_end\<close>
    using T_after_end
    by simp

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
  rate delta used by the pulse Lyapunov argument; the sublevel target
  L\_target for containment in R\_B; and the pulse length T\_pulse that
  takes every trajectory from R\_A to R\_B.  Every definition is collected
  in gardner\_conc\_defs.
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

definition u_min_val :: real where [gardner_conc_defs]: \<open>u_min_val = 1/5\<close>
definition u_max_val :: real where [gardner_conc_defs]: \<open>u_max_val = 5/16\<close>
definition v_min_val :: real where [gardner_conc_defs]: \<open>v_min_val = 5/2\<close>
definition v_max_val :: real where [gardner_conc_defs]:\<open>v_max_val = 7/2\<close>
definition \<delta>_val :: real where [gardner_conc_defs]: \<open>\<delta>_val = 1/8\<close>

definition L_target_val :: real where [gardner_conc_defs]: \<open>L_target_val = 1/100\<close>
definition T_pulse_val :: real where [gardner_conc_defs]: \<open>T_pulse_val = 57\<close>


subsubsection \<open>Coordinates of the concrete instance\<close>

text \<open>
  The concrete instance keeps the state space general: u and v sit at two
  distinct coordinates iU and iV of an arbitrary finite index type.  The
  results of this block are exported with iU and iV generalised and with
  their distinctness as a premise.  The corollary at the end of the theory
  instantiates them in R\textasciicircum{}2.
\<close>

context
  fixes iU iV :: \<open>'a::finite\<close>
  assumes coords: \<open>iU \<noteq> iV\<close>
begin

subsubsection \<open>Baseline parameters interpretation\<close>

interpretation concrete_baseline:
  gardner_baseline_params iU iV \<alpha>_base_val \<beta>_val \<gamma>_val
proof
  show \<open>iU \<noteq> iV\<close>
    by (rule coords)
  show \<open>2 < \<alpha>_base_val\<close>
    unfolding \<alpha>_base_val_def
    by simp
  show \<open>1 \<le> \<beta>_val\<close>
    unfolding \<beta>_val_def
    by simp
  show \<open>1 \<le> \<gamma>_val\<close>
    unfolding \<gamma>_val_def
    by simp
qed


subsubsection \<open>Pulse parameters interpretation\<close>

interpretation concrete_pulse:
  gardner_pulse_params iU iV \<alpha>_base_val \<beta>_val \<gamma>_val \<alpha>_low_val u_pulse_val v_pulse_val
proof 
 
  show \<open>0 < \<alpha>_low_val\<close>
    unfolding \<alpha>_low_val_def
    by simp
  show \<open>\<alpha>_low_val < \<alpha>_base_val\<close>
    unfolding \<alpha>_low_val_def \<alpha>_base_val_def
    by simp
  show \<open>0 < u_pulse_val\<close>
    unfolding u_pulse_val_def
    by simp
  show \<open>0 < v_pulse_val\<close>
    unfolding v_pulse_val_def
    by simp
  show \<open>\<alpha>_low_val / (1 + v_pulse_val ^ \<beta>_val) = u_pulse_val\<close>
    unfolding \<alpha>_low_val_def v_pulse_val_def \<beta>_val_def u_pulse_val_def
    by simp
  show \<open>\<alpha>_base_val / (1 + u_pulse_val ^ \<gamma>_val) = v_pulse_val\<close>
    unfolding \<alpha>_base_val_def u_pulse_val_def \<gamma>_val_def v_pulse_val_def 
    by (simp add: power2_eq_square)
qed

subsubsection \<open>R\_A trapping region interpretation\<close>

interpretation concrete_R_A:
  gardner_R_A_params iU iV \<alpha>_base_val \<beta>_val \<gamma>_val 
                     u_A_lo_val u_A_hi_val v_A_lo_val v_A_hi_val
proof
  show \<open>u_A_lo_val < u_A_hi_val\<close>
    unfolding u_A_lo_val_def u_A_hi_val_def
    by simp
  show \<open>v_A_lo_val < v_A_hi_val\<close>
    unfolding v_A_lo_val_def v_A_hi_val_def
    by simp
  show \<open>0 < u_A_lo_val\<close>
    unfolding u_A_lo_val_def
    by simp
  show \<open>0 < v_A_lo_val\<close>
    unfolding v_A_lo_val_def
    by simp

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
      using v_lo
      unfolding v_A_lo_val_def
      by simp
    have v_min_nn: \<open>0 \<le> v_A_lo_val\<close>
      unfolding v_A_lo_val_def
      by simp
    have \<open>\<alpha>_base_val / (1 + v_A_hi_val^2) \<le> \<alpha>_base_val / (1 + v_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_A_lo_val and x_max = v_A_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>u_A_lo_val < \<alpha>_base_val / (1 + v_A_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def v_A_hi_val_def u_A_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_lo_val\<close>
      unfolding \<beta>_val_def
      by simp
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
      unfolding v_A_lo_val_def
      by simp
    have \<open>\<alpha>_base_val / (1 + v_val^2) \<le> \<alpha>_base_val / (1 + v_A_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_A_lo_val and x_max = v_A_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + v_A_lo_val^2) < u_A_hi_val\<close>
      unfolding \<alpha>_base_val_def v_A_lo_val_def u_A_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + v_val^\<beta>_val) - u_A_hi_val < 0\<close>
      unfolding \<beta>_val_def
      by simp
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
      unfolding u_A_lo_val_def
      by simp
    have \<open>\<alpha>_base_val / (1 + u_A_hi_val^2) \<le> \<alpha>_base_val / (1 + u_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_A_lo_val and x_max = u_A_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>v_A_lo_val < \<alpha>_base_val / (1 + u_A_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def u_A_hi_val_def v_A_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_lo_val\<close>
      unfolding \<gamma>_val_def
      by simp
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
      unfolding u_A_lo_val_def
      by simp
    have \<open>\<alpha>_base_val / (1 + u_val^2) \<le> \<alpha>_base_val / (1 + u_A_lo_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = u_val 
                                    and x_min = u_A_lo_val and x_max = u_A_hi_val]
            u_lo u_hi u_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>\<alpha>_base_val / (1 + u_A_lo_val^2) < v_A_hi_val\<close>
      unfolding \<alpha>_base_val_def u_A_lo_val_def v_A_hi_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>\<alpha>_base_val / (1 + u_val^\<gamma>_val) - v_A_hi_val < 0\<close>
      unfolding \<gamma>_val_def
      by simp
  qed
qed


subsubsection \<open>R\_B trapping region interpretation\<close>

interpretation concrete_R_B:
  gardner_R_B_params iU iV \<alpha>_base_val \<beta>_val \<gamma>_val 
                     u_B_lo_val u_B_hi_val v_B_lo_val v_B_hi_val
proof
  show \<open>u_B_lo_val < u_B_hi_val\<close>
    unfolding u_B_lo_val_def u_B_hi_val_def
    by simp
  show \<open>v_B_lo_val < v_B_hi_val\<close>
    unfolding v_B_lo_val_def v_B_hi_val_def
    by simp
  show \<open>0 < u_B_lo_val\<close>
    unfolding u_B_lo_val_def
    by simp
  show \<open>0 < v_B_lo_val\<close>
    unfolding v_B_lo_val_def
    by simp

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
      unfolding v_B_lo_val_def
      by simp
    have \<open>\<alpha>_base_val / (1 + v_B_hi_val^2) \<le> \<alpha>_base_val / (1 + v_val^2)\<close>
      using hill_monotonic_bound[where a = \<alpha>_base_val and x = v_val 
                                    and x_min = v_B_lo_val and x_max = v_B_hi_val]
            v_lo v_hi v_min_nn
      by (simp add: \<alpha>_base_val_def)
    moreover have \<open>u_B_lo_val < \<alpha>_base_val / (1 + v_B_hi_val^2)\<close>
      unfolding \<alpha>_base_val_def v_B_hi_val_def u_B_lo_val_def
      by (simp add: power2_eq_square)
    ultimately show \<open>0 < \<alpha>_base_val / (1 + v_val^\<beta>_val) - u_B_lo_val\<close>
      unfolding \<beta>_val_def
      by simp
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
      unfolding v_B_lo_val_def
      by simp
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
     1/8 <= 2 - M\_sharp(1/5, 5/16, 5/2, 7/2)

   Computing M\_sharp:
     M\_sharp = u\_pulse*(v\_max+v\_pulse)/(1+v\_min\textasciicircum{}2) +
               v\_pulse*(u\_max+u\_pulse)/(1+u\_min\textasciicircum{}2)
             = (1/4)*(7/2+3)/(1+25/4) + 3*(5/16+1/4)/(1+1/25)
             = (1/4)*(13/2)/(29/4) + 3*(9/16)/(26/25)
             = 13/58 + 675/416
             = 2704/12064 + 19575/12064
             = 22279/12064

   So 2 - M\_sharp = 1849/12064.
   Check: 1/8 <= 1849/12064 <=> 12064 <= 8*1849 = 14792

   The lower bound u\_min = 1/5 lies below u\_pulse = 1/4, so that the
   region contains the last box of the approach chain in the concrete
   switching theorem below.
\<close>


subsubsection \<open>Pulse Lyapunov interpretation\<close>

interpretation concrete_pulse_lyapunov:
  gardner_pulse_lyapunov iU iV \<alpha>_base_val \<beta>_val \<gamma>_val \<alpha>_low_val u_pulse_val v_pulse_val
                        u_min_val u_max_val v_min_val v_max_val \<delta>_val
proof
  show \<open>u_min_val < u_max_val\<close>
    unfolding u_min_val_def u_max_val_def
    by simp
  show \<open>v_min_val < v_max_val\<close>
    unfolding v_min_val_def v_max_val_def
    by simp
  show \<open>u_min_val \<le> u_pulse_val\<close>
    unfolding u_min_val_def u_pulse_val_def
    by simp
  show \<open>u_pulse_val \<le> u_max_val\<close>
    unfolding u_pulse_val_def u_max_val_def
    by simp
  show \<open>v_min_val \<le> v_pulse_val\<close>
    unfolding v_min_val_def v_pulse_val_def
    by simp
  show \<open>v_pulse_val \<le> v_max_val\<close>
    unfolding v_pulse_val_def v_max_val_def
    by simp
  show \<open>0 \<le> u_min_val\<close>
    unfolding u_min_val_def
    by simp
  show \<open>0 \<le> v_min_val\<close>
    unfolding v_min_val_def
    by simp
  show \<open>0 < \<delta>_val\<close>
    unfolding \<delta>_val_def
    by simp

  (* The arithmetic check: \<delta>_val = 1/8 \<le> 2 - M_sharp *)
  show \<open>\<delta>_val \<le> 2 - M_sharp_scalar u_pulse_val v_pulse_val 
                                   u_min_val u_max_val v_min_val v_max_val\<close>
    unfolding \<delta>_val_def M_sharp_scalar_def 
              u_pulse_val_def v_pulse_val_def 
              u_min_val_def u_max_val_def v_min_val_def v_max_val_def
    by (simp add: power2_eq_square field_simps)
  show \<open>\<beta>_val = 2\<close>
    unfolding \<beta>_val_def
    by simp
  show \<open>\<gamma>_val = 2\<close>
    unfolding \<gamma>_val_def
    by simp
qed

text \<open>
   Stage 4: gardner\_induced\_switching interpretation.

   Instantiates the top-level induced
   switching theorem with the concrete Gardner parameters.

   The substantive obligation is sublevel\_in\_R\_B:
     V\_pulse v <= 1/100  ==>  in\_R\_B v

   Outline of proof:
\begin{itemize}
\item V\_pulse v = (1/2)((u - 1/4)\textasciicircum{}2 + (v - 3)\textasciicircum{}2) <= 1/100
  gives (u - 1/4)\textasciicircum{}2 <= 1/50 and (v - 3)\textasciicircum{}2 <= 1/50.
\item From x\textasciicircum{}2 <= 1/50, deduce |x| <= 1/7 (since (1/7)\textasciicircum{}2 = 1/49 > 1/50;
  if |x| > 1/7 then x\textasciicircum{}2 > 1/49 > 1/50, contradiction).
\item So u in [1/4 - 1/7, 1/4 + 1/7] = [3/28, 11/28] <= [1/10, 7/10].
\item And v in [3 - 1/7, 3 + 1/7] = [20/7, 22/7] <= [2, 7/2].
\end{itemize}
\<close>


subsubsection \<open>Induced switching interpretation\<close>

text \<open>Helper: sublevel containment for the concrete parameters.\<close>

lemma concrete_sublevel_in_R_B:
  fixes v :: \<open>(real, 'a) vec\<close>
  assumes V_le: \<open>concrete_pulse.V_pulse v \<le> L_target_val\<close>
  shows \<open>concrete_R_B.in_R_B v\<close>
proof -
  define u where \<open>u = vec_nth v iU\<close>
  define w where \<open>w = vec_nth v iV\<close>

  (* Unfold V_pulse *)
  have V_expand: \<open>concrete_pulse.V_pulse v = 
                 (1/2) * ((u - u_pulse_val)^2 + (w - v_pulse_val)^2)\<close>
    unfolding concrete_pulse.V_pulse_def u_def w_def
    by simp

  from V_le V_expand have V_ineq:
    \<open>(u - u_pulse_val)^2 + (w - v_pulse_val)^2 \<le> 2 * L_target_val\<close>
    by simp

  (* Both squared terms bounded by 2\<sqdot>L_target = 1/50 *)
  have sq_u_bound: \<open>(u - u_pulse_val)^2 \<le> 2 * L_target_val\<close>
  proof -
    have \<open>0 \<le> (w - v_pulse_val)^2\<close>
      by simp
    with V_ineq show ?thesis
      by linarith
  qed
  have sq_w_bound: \<open>(w - v_pulse_val)^2 \<le> 2 * L_target_val\<close>
  proof -
    have \<open>0 \<le> (u - u_pulse_val)^2\<close>
      by simp
    with V_ineq show ?thesis
      by linarith
  qed

  (* From x^2 \<le> 1/50, deduce |x| \<le> 1/7 *)
  have abs_u_bound: \<open>\<bar>u - u_pulse_val\<bar> \<le> 1/7\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<bar>u - u_pulse_val\<bar> \<le> 1/7\<close>
    hence gt: \<open>1/7 < \<bar>u - u_pulse_val\<bar>\<close>
      by simp
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
    hence gt: \<open>1/7 < \<bar>w - v_pulse_val\<bar>\<close>
      by simp
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
      using sq_w_bound
      by linarith
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
      unfolding u_B_lo_val_def u_pulse_val_def
      by simp
    with u_range show ?thesis 
      by linarith
  qed
  have u_hi: \<open>u \<le> u_B_hi_val\<close>
  proof -
    have \<open>u_pulse_val + 1/7 \<le> u_B_hi_val\<close>
      unfolding u_pulse_val_def u_B_hi_val_def
      by simp
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


interpretation concrete_switching:
  gardner_induced_switching iU iV \<alpha>_base_val \<beta>_val \<gamma>_val
                            u_A_lo_val u_A_hi_val v_A_lo_val v_A_hi_val
                            u_B_lo_val u_B_hi_val v_B_lo_val v_B_hi_val
                            \<alpha>_low_val u_pulse_val v_pulse_val
                            u_min_val u_max_val v_min_val v_max_val \<delta>_val
                            L_target_val
proof
  fix v :: \<open>(real, 'a) vec\<close>
  assume \<open>concrete_pulse.V_pulse v \<le> L_target_val\<close>
  then show \<open>concrete_R_B.in_R_B v\<close>
    by (simp add: concrete_sublevel_in_R_B)
qed

text \<open>
   The concrete parameters satisfy the top locale gardner\_induced\_switching.
   The theorem below states this with the concrete values as arguments; its
   proof is the locale predicate established by the interpretation
   concrete\_switching.

   Parameter order (from thm gardner\_induced\_switching\_def):
     iU iV
     alpha\_base beta gamma
     u\_A\_lo u\_A\_hi v\_A\_lo v\_A\_hi
     u\_B\_lo u\_B\_hi v\_B\_lo v\_B\_hi
     alpha\_low u\_pulse v\_pulse
     u\_min u\_max v\_min v\_max delta
     L\_target
\<close>

theorem gardner_induced_switching_concrete:
  \<open>gardner_induced_switching
     iU iV
     \<alpha>_base_val \<beta>_val \<gamma>_val
     u_A_lo_val u_A_hi_val v_A_lo_val v_A_hi_val
     u_B_lo_val u_B_hi_val v_B_lo_val v_B_hi_val
     \<alpha>_low_val u_pulse_val v_pulse_val
     u_min_val u_max_val v_min_val v_max_val \<delta>_val
     L_target_val\<close>
  using concrete_switching.gardner_induced_switching_axioms .


subsubsection \<open>Concrete switching theorem\<close>

text \<open>
   Concrete Gardner switching theorem.

   We prove the switching property for the concrete parameter values
   as a top-level theorem.  It is polymorphic in the index type 'a
   and holds at any two distinct coordinates iU and iV.  The corollary at
   the end of this theory instantiates it in R\textasciicircum{}2.

   The theorem instantiates induced\_switching through the interpretation
   concrete\_switching, which rests on the concrete interpretations
   (concrete\_baseline, concrete\_pulse, concrete\_R\_A, concrete\_R\_B,
   concrete\_pulse\_lyapunov) and on concrete\_sublevel\_in\_R\_B, the proof
   of sublevel\_in\_R\_B for our concrete numerical values.  It discharges
   the two pulse hypotheses of induced\_switching itself: the approach phase
   with a chain of shrinking boxes, and the Lyapunov phase with a bound on
   V\_pulse at the end of the chain.  Its only hypothesis on the pulse is
   the length t\_end - t\_start >= T\_pulse = 57.
\<close>


text \<open>
  From R\_A to the Lyapunov region.  The Lyapunov estimate of
  gardner\_pulse\_lyapunov holds in the region [1/5, 5/16] x [5/2, 7/2]
  around the pulsed equilibrium (1/4, 3), but the pulse starts in
  R\_A = [2, 7/2] x [1/10, 7/10].  The proof below bridges the gap with 29
  nested boxes B0, ..., B28 in the (u, v) plane.  The pulse trajectory is
  in B0 = [1/10, 7/2] x [1/10, 7/2] during the whole pulse
  (pulse\_box\_initial), and it is in Bk from time 2k on (pulse\_box\_step
  with step length h = 2 and rho = 1/4, using exp(-2) <= 1/4).  The last
  box B28 = [6/25, 3/10] x [143/50, 151/50] lies inside the Lyapunov
  region, so the approach phase ends at T\_app = 56.  On B28, V\_pulse is at
  most 221/20000.  A Lyapunov phase of length at least 1 multiplies this
  bound by exp(-1/8) <= 8/9, which brings V\_pulse below L\_target = 1/100.
  Hence a pulse of length T\_pulse = 57 suffices.  The box bounds were
  computed with exact rational arithmetic and rounded outwards to
  multiples of 1/100; simp checks the conditions of each step.
\<close>

text \<open>Top-level concrete switching theorem.\<close>

theorem gardner_concrete_switching:
  fixes y1 y2 y3 :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes t_start t_end T :: real
  assumes y1_sol: \<open>(y1 solves_ode (gardner_baseline_field iU iV \<alpha>_base_val \<beta>_val \<gamma>_val)) 
                     {0..t_start} UNIV\<close>
  assumes y2_sol: \<open>(y2 solves_ode 
                     (gardner_pulse_field iU iV \<alpha>_base_val \<alpha>_low_val \<beta>_val \<gamma>_val)) 
                     {0..(t_end - t_start)} UNIV\<close>
  assumes y3_sol: \<open>(y3 solves_ode (gardner_baseline_field iU iV \<alpha>_base_val \<beta>_val \<gamma>_val)) 
                     {0..(T - t_end)} UNIV\<close>
  assumes glue1: \<open>y2 0 = y1 t_start\<close>
  assumes glue2: \<open>y3 0 = y2 (t_end - t_start)\<close>
  assumes t_start_nn: \<open>0 \<le> t_start\<close>
  assumes pulse_long_enough: \<open>T_pulse_val \<le> t_end - t_start\<close>
  assumes T_after_end: \<open>t_end \<le> T\<close>
  assumes y1_starts_in_R_A: \<open>concrete_R_A.in_R_A (y1 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> concrete_R_B.in_R_B (y3 \<tau>)\<close>
proof -
  (* STAGE 1: the trajectory is still in R_A when the pulse starts *)
  have y1_in_R_A: \<open>\<And>\<tau>. \<tau> \<in> {0..t_start} \<Longrightarrow> concrete_R_A.in_R_A (y1 \<tau>)\<close>
    using concrete_R_A.R_A_forward_invariant[OF y1_sol t_start_nn y1_starts_in_R_A] .

  have y1_end_in_R_A: \<open>concrete_R_A.in_R_A (y1 t_start)\<close>
    using y1_in_R_A[of t_start] t_start_nn 
    by simp

  have y2_starts_in_R_A: \<open>concrete_R_A.in_R_A (y2 0)\<close>
    using glue1 y1_end_in_R_A 
    by simp

  have start: \<open>2 \<le> vec_nth (y2 0) iU\<close> \<open>vec_nth (y2 0) iU \<le> 7/2\<close>
              \<open>1/10 \<le> vec_nth (y2 0) iV\<close> \<open>vec_nth (y2 0) iV \<le> 7/10\<close>
    using y2_starts_in_R_A
     concrete_R_A.in_R_A_def u_A_lo_val_def u_A_hi_val_def 
              v_A_lo_val_def v_A_hi_val_def
    by auto

  have \<Delta>_ge: \<open>57 \<le> t_end - t_start\<close>
    using pulse_long_enough
    unfolding T_pulse_val_def .

  (* STAGE 2a: approach phase.  Every step of the chain lasts h = 2, and
     exp(-2) <= 1/4 bounds the contraction factor rho of one step *)
  have exp_two: \<open>(4::real) \<le> exp 2\<close>
  proof -
    have e1: \<open>(2::real) \<le> exp 1\<close>
      using exp_ge_add_one_self[of \<open>1::real\<close>]
      by linarith
    have \<open>(2::real) * 2 \<le> exp 1 * exp 1\<close>
      by (rule mult_mono[OF e1 e1]) simp_all
    also have \<open>exp 1 * exp 1 = exp (2::real)\<close>
      by (simp add: exp_add[symmetric])
    finally show ?thesis 
      by simp
  qed

  have rho: \<open>exp (- 2) \<le> (1/4::real)\<close>
  proof -
    have \<open>exp (- 2) = 1 / exp (2::real)\<close>
      by (rule exp_minus')
    also have \<open>\<dots> \<le> 1 / 4\<close>
    proof (rule frac_le)
      show \<open>(0::real) \<le> 1\<close>
        by simp
      show \<open>(1::real) \<le> 1\<close>
        by simp
      show \<open>(0::real) < 4\<close>
        by simp
      show \<open>4 \<le> exp (2::real)\<close>
        by (rule exp_two)
    qed
    finally show ?thesis .
  qed

  (* The chain: Bk holds from time 2k until the end of the pulse *)
  have B0: \<open>\<forall>\<tau>\<in>{0..(t_end - t_start)}.
              concrete_baseline.in_box (1/10) (7/2) (1/10) (7/2) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_initial[OF y2_sol start])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B1: \<open>\<forall>\<tau>\<in>{2..(t_end - t_start)}.
              concrete_baseline.in_box (4/25) (137/50) (1/5) (13/4) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B0])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B2: \<open>\<forall>\<tau>\<in>{4..(t_end - t_start)}.
              concrete_baseline.in_box (1/5) (249/100) (33/100) (63/20) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B1])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B3: \<open>\<forall>\<tau>\<in>{6..(t_end - t_start)}.
              concrete_baseline.in_box (11/50) (58/25) (41/100) (309/100) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B2])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B4: \<open>\<forall>\<tau>\<in>{8..(t_end - t_start)}.
              concrete_baseline.in_box (23/100) (219/100) (47/100) (153/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B3])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B5: \<open>\<forall>\<tau>\<in>{10..(t_end - t_start)}.
              concrete_baseline.in_box (23/100) (209/100) (13/25) (76/25) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B4])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B6: \<open>\<forall>\<tau>\<in>{12..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (2) (57/100) (76/25) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B5])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B7: \<open>\<forall>\<tau>\<in>{14..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (48/25) (31/50) (303/100) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B6])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B8: \<open>\<forall>\<tau>\<in>{16..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (46/25) (33/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B7])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B9: \<open>\<forall>\<tau>\<in>{18..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (177/100) (71/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B8])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B10: \<open>\<forall>\<tau>\<in>{20..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (169/100) (3/4) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B9])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B11: \<open>\<forall>\<tau>\<in>{22..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (163/100) (4/5) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B10])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B12: \<open>\<forall>\<tau>\<in>{24..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (39/25) (17/20) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B11])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B13: \<open>\<forall>\<tau>\<in>{26..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (37/25) (9/10) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B12])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B14: \<open>\<forall>\<tau>\<in>{28..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (141/100) (97/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B13])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B15: \<open>\<forall>\<tau>\<in>{30..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (33/25) (26/25) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B14])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B16: \<open>\<forall>\<tau>\<in>{32..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (31/25) (113/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B15])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B17: \<open>\<forall>\<tau>\<in>{34..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (57/50) (61/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B16])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B18: \<open>\<forall>\<tau>\<in>{36..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (26/25) (67/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B17])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B19: \<open>\<forall>\<tau>\<in>{38..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (47/50) (37/25) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B18])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B20: \<open>\<forall>\<tau>\<in>{40..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (83/100) (163/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B19])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B21: \<open>\<forall>\<tau>\<in>{42..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (73/100) (91/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B20])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B22: \<open>\<forall>\<tau>\<in>{44..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (31/50) (201/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B21])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B23: \<open>\<forall>\<tau>\<in>{46..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (53/100) (111/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B22])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B24: \<open>\<forall>\<tau>\<in>{48..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (9/20) (121/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B23])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B25: \<open>\<forall>\<tau>\<in>{50..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (39/100) (259/100) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B24])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B26: \<open>\<forall>\<tau>\<in>{52..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (7/20) (68/25) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B25])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B27: \<open>\<forall>\<tau>\<in>{54..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (8/25) (14/5) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B26])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)
  have B28: \<open>\<forall>\<tau>\<in>{56..(t_end - t_start)}.
              concrete_baseline.in_box (6/25) (3/10) (143/50) (151/50) (y2 \<tau>)\<close>
    by (rule concrete_pulse_lyapunov.pulse_box_step[OF y2_sol _ _ _ rho _ _ B27])
       (simp_all add: \<alpha>_low_val_def \<alpha>_base_val_def power2_eq_square field_simps)

  (* The last box lies in the Lyapunov region *)
  have region: \<open>\<forall>\<tau>\<in>{56..(t_end - t_start)}.
                  u_min_val \<le> vec_nth (y2 \<tau>) iU \<and> vec_nth (y2 \<tau>) iU \<le> u_max_val \<and>
                  v_min_val \<le> vec_nth (y2 \<tau>) iV \<and> vec_nth (y2 \<tau>) iV \<le> v_max_val\<close>
  proof
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {56..(t_end - t_start)}\<close>
    have b\<tau>: \<open>concrete_baseline.in_box (6/25) (3/10) (143/50) (151/50) (y2 \<tau>)\<close>
      using B28 \<tau>_in
      by blast
    have b: \<open>6/25 \<le> vec_nth (y2 \<tau>) iU\<close> \<open>vec_nth (y2 \<tau>) iU \<le> 3/10\<close>
            \<open>143/50 \<le> vec_nth (y2 \<tau>) iV\<close> \<open>vec_nth (y2 \<tau>) iV \<le> 151/50\<close>
      using b\<tau>
      unfolding concrete_baseline.in_box_def
      by simp_all
    show \<open>u_min_val \<le> vec_nth (y2 \<tau>) iU \<and> vec_nth (y2 \<tau>) iU \<le> u_max_val \<and>
          v_min_val \<le> vec_nth (y2 \<tau>) iV \<and> vec_nth (y2 \<tau>) iV \<le> v_max_val\<close>
      unfolding u_min_val_def u_max_val_def v_min_val_def v_max_val_def
    proof (intro conjI)
      show \<open>1/5 \<le> vec_nth (y2 \<tau>) iU\<close>
        using b(1)
        by linarith
      show \<open>vec_nth (y2 \<tau>) iU \<le> 5/16\<close>
        using b(2)
        by linarith
      show \<open>5/2 \<le> vec_nth (y2 \<tau>) iV\<close>
        using b(3)
        by linarith
      show \<open>vec_nth (y2 \<tau>) iV \<le> 7/2\<close>
        using b(4)
        by linarith
    qed
  qed

  have approach: 
    \<open>concrete_R_A.in_R_A (y2 0) \<Longrightarrow>
       \<forall>\<tau>\<in>{56..(t_end - t_start)}.
         u_min_val \<le> vec_nth (y2 \<tau>) iU \<and> vec_nth (y2 \<tau>) iU \<le> u_max_val \<and>
         v_min_val \<le> vec_nth (y2 \<tau>) iV \<and> vec_nth (y2 \<tau>) iV \<le> v_max_val\<close>
    by (rule region)

  (* STAGE 2b: Lyapunov phase.  At time 56 the trajectory is in B28, where
     V_pulse <= ((1/20)^2 + (7/50)^2)/2 = 221/20000 *)
  have b56: \<open>concrete_baseline.in_box (6/25) (3/10) (143/50) (151/50) (y2 56)\<close>
  proof -
    have \<open>(56::real) \<in> {56..(t_end - t_start)}\<close>
      using \<Delta>_ge
      by simp
    then show ?thesis 
      using B28
      by blast
  qed
  have b56u: \<open>6/25 \<le> vec_nth (y2 56) iU\<close> \<open>vec_nth (y2 56) iU \<le> 3/10\<close>
    using b56
    unfolding concrete_baseline.in_box_def
    by simp_all
  have b56v: \<open>143/50 \<le> vec_nth (y2 56) iV\<close> \<open>vec_nth (y2 56) iV \<le> 151/50\<close>
    using b56
    unfolding concrete_baseline.in_box_def
    by simp_all

  have du: \<open>\<bar>vec_nth (y2 56) iU - 1/4\<bar> \<le> 1/20\<close>
  proof (rule abs_leI)
    show \<open>vec_nth (y2 56) iU - 1/4 \<le> 1/20\<close>
      using b56u(2)
      by linarith
    show \<open>- (vec_nth (y2 56) iU - 1/4) \<le> 1/20\<close>
      using b56u(1)
      by linarith
  qed
  have dv: \<open>\<bar>vec_nth (y2 56) iV - 3\<bar> \<le> 7/50\<close>
  proof (rule abs_leI)
    show \<open>vec_nth (y2 56) iV - 3 \<le> 7/50\<close>
      using b56v(2)
      by linarith
    show \<open>- (vec_nth (y2 56) iV - 3) \<le> 7/50\<close>
      using b56v(1)
      by linarith
  qed

  have sq_u: \<open>(vec_nth (y2 56) iU - 1/4)^2 \<le> 1/400\<close>
  proof -
    have nn: \<open>(0::real) \<le> 1/20\<close>
      by simp
    have \<open>(vec_nth (y2 56) iU - 1/4)^2 \<le> (1/20)^2\<close>
      by (rule iffD2[OF power2_le_iff_abs_le[OF nn] du])
    moreover have \<open>(1/20::real)^2 = 1/400\<close>
      by (simp add: power2_eq_square)
    ultimately show ?thesis 
      by linarith
  qed
  have sq_v: \<open>(vec_nth (y2 56) iV - 3)^2 \<le> 49/2500\<close>
  proof -
    have nn: \<open>(0::real) \<le> 7/50\<close>
      by simp
    have \<open>(vec_nth (y2 56) iV - 3)^2 \<le> (7/50)^2\<close>
      by (rule iffD2[OF power2_le_iff_abs_le[OF nn] dv])
    moreover have \<open>(7/50::real)^2 = 49/2500\<close>
      by (simp add: power2_eq_square)
    ultimately show ?thesis 
      by linarith
  qed

  have V56: \<open>concrete_pulse.V_pulse (y2 56) \<le> 221/20000\<close>
    unfolding concrete_pulse.V_pulse_def
    unfolding u_pulse_val_def v_pulse_val_def
    using sq_u sq_v
    by linarith

  (* The rest of the pulse lasts at least 1, so V_pulse decays by at least
     the factor exp(-1/8) <= 8/9 *)
  have d_ge: \<open>1/8 \<le> \<delta>_val * (t_end - t_start - 56)\<close>
    unfolding \<delta>_val_def
    using \<Delta>_ge
    by auto
  have exp_shift: \<open>exp (- \<delta>_val * (t_end - t_start - 56)) \<le> exp (- (1/8))\<close>
    using d_ge
    by simp
  have e18: \<open>9/8 \<le> exp (1/8::real)\<close>
    using exp_ge_add_one_self[of \<open>1/8::real\<close>]
    by linarith
  have exp18: \<open>exp (- (1/8::real)) \<le> 8/9\<close>
  proof -
    have \<open>exp (- (1/8::real)) = 1 / exp (1/8)\<close>
      by (rule exp_minus')
    also have \<open>\<dots> \<le> 1 / (9/8)\<close>
    proof (rule frac_le)
      show \<open>(0::real) \<le> 1\<close>
        by simp
      show \<open>(1::real) \<le> 1\<close>
        by simp
      show \<open>(0::real) < 9/8\<close>
        by simp
      show \<open>9/8 \<le> exp (1/8::real)\<close>
        by (rule e18)
    qed
    also have \<open>\<dots> = 8/9\<close> 
      by simp
    finally show ?thesis .
  qed
  have exp_le: \<open>exp (- \<delta>_val * (t_end - t_start - 56)) \<le> 8/9\<close>
    using exp_shift exp18
    by linarith

  have prod: \<open>concrete_pulse.V_pulse (y2 56) * exp (- \<delta>_val * (t_end - t_start - 56)) \<le>
                221/20000 * (8/9)\<close>
  proof (rule mult_mono)
    show \<open>concrete_pulse.V_pulse (y2 56) \<le> 221/20000\<close>
      by (rule V56)
    show \<open>exp (- \<delta>_val * (t_end - t_start - 56)) \<le> 8/9\<close>
      by (rule exp_le)
    show \<open>(0::real) \<le> 221/20000\<close>
      by simp
    show \<open>0 \<le> exp (- \<delta>_val * (t_end - t_start - 56))\<close>
      by simp
  qed
  have L_ok: \<open>221/20000 * (8/9) \<le> L_target_val\<close>
    unfolding L_target_val_def
    by simp
  have pulse_long: 
    \<open>concrete_pulse.V_pulse (y2 56) * exp (- \<delta>_val * (t_end - t_start - 56)) \<le> L_target_val\<close>
    by (rule order_trans[OF prod L_ok])

  (* STAGE 3: the abstract theorem with T_app = 56 *)
  have T_app_nn: \<open>(0::real) \<le> 56\<close> 
    by simp
  have T_app_le: \<open>56 \<le> t_end - t_start\<close> 
    using \<Delta>_ge
    by linarith

  show \<open>\<And>\<tau>. \<tau> \<in> {0..(T - t_end)} \<Longrightarrow> concrete_R_B.in_R_B (y3 \<tau>)\<close>
    using concrete_switching.induced_switching[OF y1_sol y2_sol y3_sol glue1 glue2
            t_start_nn T_app_nn T_app_le T_after_end y1_starts_in_R_A approach pulse_long] .
qed

end


text \<open>
  The concrete switching theorem in the state space R\textasciicircum{}2, i.e., at the
  numeral type 2, whose coordinates 0 and 1 carry u and v.
\<close>

lemmas gardner_concrete_switching_R2 =
  gardner_concrete_switching[where 'a = 2, OF zero_neq_one]

end