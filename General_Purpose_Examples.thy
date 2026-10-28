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
theory General_Purpose_Examples

imports Differential_Dynamic_Logic

begin

section \<open>General purpose examples\<close>

subsection \<open>Examples for application of DI\<close>

lemma Example1_via_DI:
  assumes y: \<open>\<And>t. (y solves_ode f) {0 .. t} UNIV\<close>
    and iv: \<open>((vec_nth (y 0) x)::real) \<ge> 0\<close>
    and f': \<open>\<forall>t vect. t \<in> {0..t} \<longrightarrow> vec_nth (f t vect) x \<ge> 0\<close>
    and t: \<open>t \<ge> 0\<close>
  shows \<open>0 \<le> vec_nth (y t) x\<close>
  apply (rule DI_Vect[where  h = \<open>\<lambda>v. 0\<close> and g = \<open>\<lambda>v. vec_nth v x\<close>])
     apply (simp add: iv)
    apply (rule y)
  apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
   apply (intro  exI[where x=\<open>\<lambda>v. vec_nth v x\<close>] conjI)
     apply (rule has_derivative_const)
  apply (rule has_derivative_vec_nth)
    apply (simp add: f')
  apply (rule t)
  done

lemma circular_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes iX iY :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close>
  assumes y_sol: \<open>(y solves_ode 
                    (\<lambda>t v. vec_lambda 
                           ((\<lambda>i. 0)(iX := -(\<omega>::real) * (vec_nth v iY), 
                                    iY := \<omega> * (vec_nth v iX))))) 
                  {0..t} UNIV\<close>
  assumes iv: \<open>(vec_nth (y 0) iX)^2 + (vec_nth (y 0) iY)^2 = r0^2\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>(vec_nth (y t) iX)^2 + (vec_nth (y t) iY)^2 = r0^2\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* Helper: Fréchet derivative of the squared-sum (v1² + v2²) *)
  have g_has_derivative:
   \<open>((\<lambda>v. (vec_nth v i)^2 + (vec_nth v j)^2) has_derivative 
    (\<lambda>v. 2 * (vec_nth (p::(real,'p) vec) i) * (vec_nth v i) + 
         2 * (vec_nth p j) * (vec_nth v j))) (at p)\<close>
   for i j p
    apply (rule has_derivative_add)
     apply (rule component_sq_has_derivative)
    apply (rule component_sq_has_derivative)
    done

  (* ------------------------------------------------------------------------
     SUB-PART 1: r0² \<le> x(t)² + y(t)²
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition r0² \<le> x(0)² + y(0)² *)
  have iv_ge: \<open>r0^2 \<le> (vec_nth (y 0) iX)^2 + (vec_nth (y 0) iY)^2\<close>
    using iv by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. r0^2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -\<omega> * (vec_nth v iY),
                       iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -\<omega> * (vec_nth v iY),
                       iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. r0^2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -\<omega> * (vec_nth v iY),
                        iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>))
                  \<le> Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -\<omega> * (vec_nth v iY),
                        iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 2 * (vec_nth (y \<tau>) iX) * (vec_nth v iX) +
                                     2 * (vec_nth (y \<tau>) iY) * (vec_nth v iY)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule g_has_derivative)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: x(t)² + y(t)² \<le> r0²
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition x(0)² + y(0)² \<le> r0² *)
  have iv_le: \<open>(vec_nth (y 0) iX)^2 + (vec_nth (y 0) iY)^2 \<le> r0^2\<close>
    using iv by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. r0^2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (iX := -\<omega> * (vec_nth v iY),
                                         iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (iX := -\<omega> * (vec_nth v iY),
                                         iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. r0^2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -\<omega> * (vec_nth v iY),
                        iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -\<omega> * (vec_nth v iY),
                       iY :=  \<omega> * (vec_nth v iX)))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 2 * (vec_nth (y \<tau>) iX) * (vec_nth v iX) +
                                     2 * (vec_nth (y \<tau>) iY) * (vec_nth v iY)\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule g_has_derivative)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     APPLY DI_Vect twice after antisym. It is antisym which generate SUB-PART 1 and 2 
     ------------------------------------------------------------------------ *)
  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2\<close> and g = \<open>\<lambda>v. r0^2\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. r0^2\<close> and g = \<open>\<lambda>v. (vec_nth v iX)^2 + (vec_nth v iY)^2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

subsection \<open>Examples for application of DG\<close>

subsubsection \<open>Example: exponential decay via DG and DI\_Vect\<close>

text \<open>
  ODE:        x' = -x  (at coordinate iX)
  Proof Goal: x(t) > 0 given x(0) > 0
  Ghost:      g' = 1/2*g  (at coordinate iG, distinct from iX)
  Invariant:  x*g\textasciicircum{}2 >= 1  (using DI\_Vect with h = lambdav. 1, g = lambdav. x*g\textasciicircum{}2)
\<close>
lemma exponential_decay:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes iX iG :: 'p
      \<comment> \<open>iX holds x; iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iX \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iX := -((vec_nth v iX)::real))))) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (x 0) iX > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>0 < vec_nth (x t) iX\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iX)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the velocity vector's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(iX := -((vec_nth v iX)::real)))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iX := -((vec_nth v iX)::real)))) \<tau> v =
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iX := -((vec_nth v iX)::real)))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v iX = vec_nth w iX\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iX := -((vec_nth v iX)::real)))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iX := -((vec_nth v iX)::real)))) \<tau> w\<close>
      using v0 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = iG,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))\<close>

  (* Helper: Fréchet derivative of x \<sqdot> y² (product rule) *)
  have xg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iX * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iX * (vec_nth p iG)^2 + 
           vec_nth p iX * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iX) has_derivative (\<lambda>v. vec_nth v iX)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: Apply DI_Vect to prove the invariant 1 \<le> x \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> x(0) \<sqdot> y(0)² *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) iX * (vec_nth (?z 0) iG)^2\<close>
    using iv
    by (simp add: y0_def y_init field_simps power2_eq_square fun_upd_def)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>  
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iX * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                            vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))
                 \<le> Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                              vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iX * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                             vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))
                  \<le> Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iX := -(vec_nth v iX))) +
                               vec_lambda ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iX * (vec_nth (?z \<tau>) iG)^2 + 
                                      vec_nth (?z \<tau>) iX * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule xg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      done
  qed

  (* APPLY DI_Vect: we get the invariant 1 \<le> x \<sqdot> y² at time t *)
  have ineq: \<open>1 \<le> vec_nth (?z t) iX * (vec_nth (?z t) iG)^2\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iX * (vec_nth v iG)^2\<close>,
                  OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From x(t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude x(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iX\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iX = vec_nth (x t) iX\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iX * (vec_nth (?z t) iG)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iX \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

end