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
theory Real_Analysis_More

imports "Ordinary_Differential_Equations.ODE_Analysis"
begin

section \<open>Algebraic and Calculus Helpers\<close>

subsection \<open>Vectors Algebra\<close>

lemma has_derivative_vec_nth:
  \<open>((\<lambda>v. vec_nth v x) has_derivative (\<lambda>v. vec_nth v x)) (at y)\<close>
  by (auto simp add: has_derivative_def)

lemma vec_lambda_mk_ode_eq: 
  \<open>(\<chi> i. if i = pos then val else f) = vec_lambda ((\<lambda>k. f)(pos := val))\<close>
  by auto

lemma vec_lambda_mk_ode_eq':
  \<open>(\<chi> i. if i = pos then val else f i) = vec_lambda ((\<lambda>k. f k)(pos := val))\<close>
  by auto

subsection \<open>ODE solution manipulation\<close>

lemma solves_ode_subset_ivl:
  assumes \<open>(y solves_ode f) {0..t} Q\<close>
  assumes \<open>\<tau> \<in> {0..t}\<close> 
    shows \<open>(y solves_ode f) {0..\<tau>} Q\<close>
  by (meson assms(1) assms(2) atLeastAtMost_iff atLeastatMost_subset_iff order_refl 
            solves_ode_on_subset)

text \<open>
  HELPER: Time-shift of a solution to a time-invariant ODE
  GRN: Gene Regulatory Network.
  If y solves the ODE on [a..b] and the vector field is time-invariant
  (i.e., f tau v depends only on v, not on tau), then the shifted trajectory
  y'(s) := y(t0 + s) solves the same ODE on [0..(b - t0)] for any
  t0 in [a..b].

  This lemma is needed for "monotonicity in both directions":
  to prove an invariant about y(t1) vs y(t2) for t1 < t2, we shift the
  trajectory by t1 and then apply existing invariant lemmas (which are
  stated for [0..t]) to the shifted trajectory.

  TIME-INVARIANCE: most CRN/GRN ODEs in our development have the form
  lambdat v. <expression in v alone>, with no dependence on t. The hypothesis
  `time\_inv` captures this property.
\<close>

lemma solves_ode_shift:
  fixes y :: \<open>real \<Rightarrow> (real, 'a::finite) vec\<close>
  fixes f :: \<open>real \<Rightarrow> (real, 'a) vec \<Rightarrow> (real, 'a) vec\<close>
  assumes y_sol: \<open>(y solves_ode f) {0..b} Q\<close>
  assumes t0_in: \<open>0 \<le> t0\<close> 
  assumes t0_le_b: \<open>t0 \<le> b\<close>
  assumes time_inv: \<open>\<And>\<tau>1 \<tau>2 v. f \<tau>1 v = f \<tau>2 v\<close>
  shows \<open>((\<lambda>s. y (t0 + s)) solves_ode f) {0..(b - t0)} Q\<close>
proof -
  let ?y' = \<open>\<lambda>s. y (t0 + s)\<close>
  
  (* Step 1: y has vderiv on [0..b] *)
  have y_vderiv: \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) {0..b}\<close>
    using y_sol by (simp add: solves_ode_def)

  (* Step 2: The shift map s \<mapsto> t0 + s sends [0..(b-t0)] into [0..b] *)
  have shift_image: \<open>(\<lambda>s. t0 + s) ` {0..(b - t0)} \<subseteq> {0..b}\<close>
    using t0_in t0_le_b by auto

  (* Step 3: Apply the chain rule via has_vderiv_on_compose.
     The "inner" function is (\<lambda>s. t0 + s), with derivative 1.
     The "outer" function is y, with derivative (\<lambda>\<tau>. f \<tau> (y \<tau>)).
     The composition has derivative (\<lambda>s. f (t0 + s) (y (t0 + s))). *)
  have shift_vderiv: \<open>((\<lambda>s. t0 + s) has_vderiv_on (\<lambda>s. 1)) {0..(b - t0)}\<close>
    using has_vderiv_on_add has_vderiv_on_const has_vderiv_on_id 
    by fastforce
  have y'_vderiv: \<open>(?y' has_vderiv_on (\<lambda>s. f (t0 + s) (y (t0 + s)))) {0..(b - t0)}\<close>
  proof -
    (* Restrict y_vderiv to the image (\<lambda>s. t0 + s) ` {0..(b-t0)} *)
    have y_vderiv_on_image: 
      \<open>(y has_vderiv_on (\<lambda>\<tau>. f \<tau> (y \<tau>))) ((\<lambda>s. t0 + s) ` {0..(b - t0)})\<close>
      using y_vderiv shift_image
      by (rule has_vderiv_on_subset)
    
    (* Apply the chain rule *)
    have \<open>((y \<circ> (\<lambda>s. t0 + s)) has_vderiv_on 
           (\<lambda>s. 1 *\<^sub>R (f (t0 + s) (y (t0 + s))))) {0..(b - t0)}\<close>
      using has_vderiv_on_compose[OF y_vderiv_on_image shift_vderiv]
      by (simp add: comp_def)
    thus ?thesis
      by (simp add: comp_def)
  qed
  (* Step 4: Use time-invariance to rewrite f (t0 + s) as f s *)
  have rewrite: \<open>\<And>s. f (t0 + s) (y (t0 + s)) = f s (?y' s)\<close>
    using time_inv by simp

  have y'_vderiv': \<open>(?y' has_vderiv_on (\<lambda>s. f s (?y' s))) {0..(b - t0)}\<close>
    using y'_vderiv rewrite
    by (simp cong: has_vderiv_on_cong)

  (* Step 5: Membership in Q *)
  have y_in_Q: \<open>\<And>\<tau>. \<tau> \<in> {0..b} \<Longrightarrow> y \<tau> \<in> Q\<close>
    using y_sol by (simp add: solves_ode_def Pi_def)
  have y'_in_Q: \<open>\<And>s. s \<in> {0..(b - t0)} \<Longrightarrow> ?y' s \<in> Q\<close>
    using y_in_Q t0_in t0_le_b by auto

  (* Step 6: Reassemble solves_ode *)
  show ?thesis
    using y'_vderiv' y'_in_Q
    by (intro solves_odeI) (auto simp: Pi_def)
qed

subsection \<open>Scalar derivative helpers\<close>

lemma has_real_derivative_pos_inc_right_within:
  fixes g :: \<open>real \<Rightarrow> real\<close>
  assumes g_deriv: \<open>(g has_real_derivative l) (at \<tau> within {\<tau>..s})\<close>
  assumes \<tau>_lt_s: \<open>\<tau> < s\<close>
  assumes l_pos: \<open>0 < l\<close>
  shows \<open>\<exists>d > 0. \<forall>h. 0 < h \<and> h < d \<longrightarrow> g \<tau> < g (\<tau> + h)\<close>
proof -
  (* Unfold has_real_derivative at within {\<tau>..s} into its limit form *)
  have \<open>((\<lambda>y. (g y - g \<tau>) / (y - \<tau>)) \<longlongrightarrow> l) (at \<tau> within {\<tau>..s})\<close>
    using g_deriv
    by (simp add: has_field_derivative_iff)
  (* From the limit, extract \<epsilon> = l (a specific choice) *)
  hence \<open>\<forall>\<epsilon> > 0. \<exists>d > 0. \<forall>y \<in> {\<tau>..s}. y \<noteq> \<tau> \<and> dist y \<tau> < d 
                          \<longrightarrow> dist ((g y - g \<tau>)/(y - \<tau>)) l < \<epsilon>\<close>
    by (simp add: tendsto_iff eventually_at)
  from this[rule_format, OF l_pos]
  obtain d0 where d0_pos: \<open>0 < d0\<close> and
    d0_prop: \<open>\<forall>y \<in> {\<tau>..s}. y \<noteq> \<tau> \<and> dist y \<tau> < d0 
                  \<longrightarrow> dist ((g y - g \<tau>)/(y - \<tau>)) l < l\<close>
    by blast
  (* Choose d = min(d0, s - \<tau>) so that \<tau> + h stays in (\<tau>, s] \<subseteq> {\<tau>..s} *)
  define d where \<open>d = min d0 (s - \<tau>)\<close>
  have d_pos: \<open>0 < d\<close>
    using d0_pos \<tau>_lt_s by (simp add: d_def)
  show ?thesis
  proof (intro exI[where x=d] conjI allI impI)
    show \<open>0 < d\<close> using d_pos .
    fix h assume h: \<open>0 < h \<and> h < d\<close>
    hence h_pos: \<open>0 < h\<close> and h_lt_d: \<open>h < d\<close> by auto
    let ?y = \<open>\<tau> + h\<close>
    have y_in: \<open>?y \<in> {\<tau>..s}\<close>
      using h_pos h_lt_d by (auto simp: d_def)
    have y_ne: \<open>?y \<noteq> \<tau>\<close> using h_pos by simp
    have y_dist: \<open>dist ?y \<tau> < d0\<close>
      using h_lt_d d_def dist_real_def h by auto
    have \<open>dist ((g ?y - g \<tau>)/(?y - \<tau>)) l < l\<close>
      using d0_prop y_in y_ne y_dist by blast
    hence \<open>(g ?y - g \<tau>)/(?y - \<tau>) > 0\<close>
      using dist_real_def 
      by force
    moreover have \<open>?y - \<tau> > 0\<close> using h_pos by simp
    ultimately have \<open>g ?y - g \<tau> > 0\<close>
      by (simp add: zero_less_divide_iff)
    thus \<open>g \<tau> < g ?y\<close> by simp
  qed
qed

text \<open>
  Part 1: Auxiliary lemma , strict positive derivative implies right neighborhood

  This is the key real-analysis fact: if g'(tau*) > 0, then g is strictly
  greater than g(tau*) on a right neighborhood of tau*.

  HOL provides DERIV\_left\_inc which states:
    DERIV f x :> l ==> 0 < l ==> EXd > 0. ALLh > 0. h < d --> f(x) < f(x + h)

  We restate it in the modern has\_real\_derivative form for convenience.
\<close>

lemma deriv_pos_right_strict:
  fixes g :: \<open>real \<Rightarrow> real\<close>
  assumes g_deriv: \<open>(g has_real_derivative l) (at \<tau>)\<close>
  assumes l_pos: \<open>0 < l\<close>
  shows \<open>\<exists>d > 0. \<forall>h. 0 < h \<and> h < d \<longrightarrow> g \<tau> < g (\<tau> + h)\<close>
proof -
  have \<open>DERIV g \<tau> :> l\<close>
    using g_deriv by simp
  thus ?thesis
    using DERIV_pos_inc_right[OF _ l_pos]
    by blast
qed

lemma has_vderiv_on_zero_imp_constant:
  fixes \<phi> :: \<open>real \<Rightarrow> real\<close>
  assumes vderiv: \<open>(\<phi> has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
  shows \<open>\<phi> \<tau> = \<phi> 0\<close>
proof -
  have \<open>\<And>x. x \<in> {0..t} \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. h *\<^sub>R 0)) (at x within {0..t})\<close>
    using vderiv unfolding has_vderiv_on_def has_vector_derivative_def by blast
  hence \<open>\<And>x. x \<in> {0..t} \<Longrightarrow> (\<phi> has_derivative (\<lambda>h. 0)) (at x within {0..t})\<close>
    by simp
    hence \<open>\<exists>c. \<forall>x\<in>{0..t}. \<phi> x = c\<close>
    by (rule has_derivative_zero_constant[rotated]) auto
  thus ?thesis
    using \<tau>_in t_nn by fastforce
qed

subsection \<open>Vector component derivatives\<close>
text \<open>
   Generic chain rule: scalar function composed with vector
   component extraction.

   This is the abstract pattern behind component\_sq\_has\_derivative
   and all the Hill vector derivative lemmas.  Any differentiable
   scalar function f composed with vec\_nth \_ i gives a
   differentiable function on vectors, with derivative
   f'(vec\_nth p i) * vec\_nth w i.
\<close>

lemma scalar_comp_vec_nth_has_derivative:
  fixes f :: \<open>real \<Rightarrow> real\<close> 
  fixes f' :: \<open>real \<Rightarrow> real\<close>
  fixes p :: \<open>(real, 'a::finite) vec\<close> 
  fixes i :: 'a
  assumes f_deriv: \<open>(f has_derivative (\<lambda>h. h * f' (vec_nth p i))) (at (vec_nth p i))\<close>
  shows \<open>((\<lambda>v. f (vec_nth v i)) has_derivative 
          (\<lambda>w. f' (vec_nth p i) * vec_nth w i)) (at p)\<close>
proof -
  have nth_deriv: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>w. vec_nth w i)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have \<open>((f \<circ> (\<lambda>v. vec_nth v i)) has_derivative 
         ((\<lambda>h. h * f' (vec_nth p i)) \<circ> (\<lambda>w. vec_nth w i))) (at p)\<close>
    using has_derivative_compose[OF nth_deriv f_deriv] 
    by (simp add: assms diff_chain_at nth_deriv)
  thus ?thesis
    by (simp add: comp_def algebra_simps)
qed


text \<open>
   Corollary of scalar\_comp\_vec\_nth\_has\_derivative:
   component\_sq\_has\_derivative from the general lemma.

   textbook: f(x) = x\textasciicircum{}2, f'(x) = 2x.
   Our formalism:
   (lambdav. 2*(vec\_nth x i)*(vec\_nth v i))
   is the Fr?chet derivative of (lambdav. (vec\_nth v i)\textasciicircum{}2) at x.
\<close>


corollary component_sq_has_derivative:
  fixes i :: \<open>'a::finite\<close>
  shows \<open>((\<lambda>v. (vec_nth v i)^2) has_derivative 
          (\<lambda>v. 2*(vec_nth (p::(real,'a) vec) i)*(vec_nth v i))) (at p)\<close>
proof -
  have fderiv:
    \<open>((\<lambda>x. x^2) has_derivative (\<lambda>h. h * (2 * vec_nth p i))) (at (vec_nth p i))\<close>
    using DERIV_pow[where n=2 and x=\<open>vec_nth p i\<close>]
    unfolding has_field_derivative_def has_vector_derivative_def
    by (simp add: mult_commute_abs)
  from scalar_comp_vec_nth_has_derivative
  show ?thesis using fderiv by blast
qed

text \<open>Helper: derivative of the sum of two components.\<close>
lemma sum2_components_has_derivative:
  \<open>((\<lambda>v. vec_nth v i + vec_nth v j) has_derivative 
    (\<lambda>w. vec_nth w i + vec_nth w j)) (at p)\<close>
  for i j and p :: \<open>(real, 'a::finite) vec\<close>
  by (intro has_derivative_add has_derivative_vec_nth)


text \<open>Helper: the Fr\'{e}chet derivative of the sum of three vector
  components is the sum itself, since the sum is linear.
  This is the Dg supplied to DI\_Vect.\<close>
lemma sum3_components_has_derivative:
  \<open>((\<lambda>v. vec_nth v i + vec_nth v j + vec_nth v k) has_derivative 
    (\<lambda>w. vec_nth w i + vec_nth w j + vec_nth w k)) (at p)\<close>
  for i j k and p :: \<open>(real, 'a::finite) vec\<close>
  by (intro has_derivative_add has_derivative_vec_nth)

text \<open>Helper: derivative of vec\_nth v i + 2 * vec\_nth v j as a function of v.\<close>
lemma weighted_sum_has_derivative:
  \<open>((\<lambda>v. vec_nth v i + 2 * vec_nth v j) has_derivative 
    (\<lambda>w. vec_nth w i + 2 * vec_nth w j)) (at p)\<close>
  for i j and p :: \<open>(real, 'a::finite) vec\<close>
proof -
  have \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>w. vec_nth w i)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  moreover have \<open>((\<lambda>v. 2 * vec_nth v j) has_derivative (\<lambda>w. 2 * vec_nth w j)) (at p)\<close>
    using has_derivative_vec_nth[where x=j]
    using has_derivative_mult_right by blast
  ultimately show ?thesis
    by (intro has_derivative_add)
qed

subsection \<open>Hill function calculus\<close>
text \<open>
   Generalized Hill function calculus.

   These four lemmas generalize the existing Hill derivative and
   monotonicity lemmas.  The key insight: the only property of
   the exponent n that matters is that the denominator 1 + x\textasciicircum{}n
   is strictly positive.  This holds when x >= 0 (any n >= 1),
   or when n is even (any x).
\<close>

subsubsection \<open>Scalar field derivative, general version\<close>
text \<open>
  Hill function derivatives for EVEN Hill coefficients

  The existing hill\_repressive\_scalar\_has\_derivative requires x >= 0 to
  ensure 1 + x\textasciicircum{}n > 0. For the unconditional Gardner theorem, we need
  the derivative of the Hill function WITHOUT assuming the regulator
  concentration is non-negative (because we're about to PROVE it's
  non-negative).

  The trick: if n is EVEN, then x\textasciicircum{}n >= 0 for all real x, so
  1 + x\textasciicircum{}n >= 1 > 0 automatically, without any sign assumption.

  Biological justification: Hill coefficients for dimerizing repressors
  (the standard mechanism in the Gardner toggle switch) are typically
  n = 2, which is even. More generally, n = 2k for k-mer binding.
\<close>

lemma hill_repressive_scalar_has_derivative_general:
  fixes x \<alpha> :: real 
  fixes n   :: nat
  assumes denom_pos: \<open>0 < 1 + x^n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_field_derivative 
          (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2)) (at x)\<close>
proof -
  have denom_nz: \<open>1 + x^n \<noteq> 0\<close> using denom_pos by simp

  have pow_deriv: \<open>((\<lambda>y. y^n) has_field_derivative (real n * x^(n-1))) (at x)\<close>
    by (simp add: DERIV_pow)

  have denom_deriv: \<open>((\<lambda>y. 1 + y^n) has_field_derivative (real n * x^(n-1))) (at x)\<close>
    using pow_deriv DERIV_const[where k=1]
    using DERIV_add by fastforce

  have \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_field_derivative 
         ((0 * (1 + x^n) - \<alpha> * (real n * x^(n-1))) / (1 + x^n)^2)) (at x)\<close>
  proof -
    have \<open>((\<lambda>r. \<alpha> / (1 + r^n)) has_real_derivative 
           (0 * (1 + x^n) - \<alpha> * (real n * x^(n-1))) / ((1 + x^n) * (1 + x^n))) (at x)\<close>
      using DERIV_const DERIV_divide denom_deriv denom_nz by blast
    then show ?thesis
      by (simp add: power2_eq_square)
  qed
  moreover have \<open>(0 * (1 + x^n) - \<alpha> * (real n * x^(n-1))) / (1 + x^n)^2 
                = - \<alpha> * real n * x^(n-1) / (1 + x^n)^2\<close>
    by (simp add: field_simps)
  ultimately show ?thesis 
    by argo
qed

subsubsection \<open>Scalar Fr\'{e}chet derivative, general version\<close>

lemma hill_repressive_scalar_has_frechet_derivative_general:
  fixes x \<alpha> :: real 
  fixes n :: nat
  assumes denom_pos: \<open>0 < 1 + x^n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2))) (at x)\<close>
  using hill_repressive_scalar_has_derivative_general[OF denom_pos n_pos]
  by (metis (full_types) has_field_derivative_imp_has_derivative mult_commute_abs)

subsubsection \<open>Vector derivative, general version\<close>

lemma hill_repressive_vector_has_derivative_general:
  fixes p :: \<open>(real, 'a::finite) vec\<close> 
  fixes \<alpha> :: real 
  fixes n :: nat 
  fixes i :: 'a
  assumes denom_pos: \<open>0 < 1 + (vec_nth p i)^n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>((\<lambda>v. \<alpha> / (1 + (vec_nth v i)^n)) has_derivative 
          (\<lambda>w. (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2) 
                * vec_nth w i)) (at p)\<close>
proof -
  have nth_deriv: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>w. vec_nth w i)) (at p)\<close>
    by (rule has_derivative_vec_nth)

  have hill_deriv: \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2))) 
          (at (vec_nth p i))\<close>
    using hill_repressive_scalar_has_frechet_derivative_general[OF denom_pos n_pos] .

  have \<open>(((\<lambda>y. \<alpha> / (1 + y^n)) \<circ> (\<lambda>v. vec_nth v i)) has_derivative 
         ((\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2)) 
          \<circ> (\<lambda>w. vec_nth w i))) (at p)\<close>
    using has_derivative_compose[OF nth_deriv hill_deriv]
          diff_chain_at hill_deriv nth_deriv 
    by blast
  thus ?thesis
    by (simp add: comp_def algebra_simps)
qed


subsubsection \<open>Monotonicity bound, general version for arbitrary n\<close>

text \<open>
   Hill-function monotonicity helper.

   For a > 0 and 0 <= x\_min <= x <= x\_max, 1 <= n, the Hill-style expression
   a / (1 + x\textasciicircum{}n) is bounded above by a / (1 + x\_min\textasciicircum{}n) and below
   by a / (1 + x\_max\textasciicircum{}n).
\<close>
lemma hill_monotonic_bound_general:
  fixes a x x_min x_max :: real 
  fixes n :: nat
  assumes a_pos: \<open>0 < a\<close>
  assumes x_min_nn: \<open>0 \<le> x_min\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  assumes x_bounds: \<open>x_min \<le> x\<close> \<open>x \<le> x_max\<close>
  shows \<open>a / (1 + x_max^n) \<le> a / (1 + x^n) \<and> 
         a / (1 + x^n) \<le> a / (1 + x_min^n)\<close>
proof -
  have x_nn: \<open>0 \<le> x\<close> using x_min_nn x_bounds(1) by linarith
  have x_max_nn: \<open>0 \<le> x_max\<close> using x_nn x_bounds(2) by linarith

  have sq_mono_lo: \<open>x_min^n \<le> x^n\<close>
    using x_min_nn x_bounds(1) n_pos 
    by (simp add: power_mono)
  
  have sq_mono_hi: \<open>x^n \<le> x_max^n\<close>
    using x_nn x_bounds(2) n_pos 
    by (simp add: power_mono)

  have denom_min_le: \<open>1 + x_min^n \<le> 1 + x^n\<close>
    using sq_mono_lo by simp
  have denom_x_le: \<open>1 + x^n \<le> 1 + x_max^n\<close>
    using sq_mono_hi by simp

  have denom_min_pos: \<open>0 < 1 + x_min^n\<close>
    using x_min_nn n_pos 
    by (simp add: add_pos_nonneg)
  have denom_x_pos: \<open>0 < 1 + x^n\<close>
    using x_nn n_pos 
    by (simp add: add_pos_nonneg)
  have denom_max_pos: \<open>0 < 1 + x_max^n\<close>
    using x_max_nn n_pos 
    by (simp add: add_pos_nonneg)

  have lower: \<open>a / (1 + x_max^n) \<le> a / (1 + x^n)\<close>
    using a_pos denom_x_le denom_x_pos denom_max_pos
    by (simp add: frac_le)

  have upper: \<open>a / (1 + x^n) \<le> a / (1 + x_min^n)\<close>
    using a_pos denom_min_le denom_min_pos denom_x_pos
    by (simp add: frac_le)

  from lower upper show ?thesis by blast
qed


text \<open>
   Corollary proofs: existing lemmas from general versions

   These show how the existing special-case lemmas follow from
   the general versions.
\<close>

text \<open>hill\_repressive\_scalar\_has\_derivative as a corollary.\<close>

corollary hill_repressive_scalar_has_derivative:
  fixes x \<alpha> :: real 
  fixes n :: nat
  assumes x_nn: \<open>x \<ge> 0\<close> 
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_field_derivative 
          (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2)) (at x)\<close>
proof -
  have \<open>0 < 1 + x^n\<close>
    using x_nn n_pos 
    by (simp add: add_pos_nonneg)
  thus ?thesis 
    using hill_repressive_scalar_has_derivative_general n_pos 
    by blast
qed

text \<open>hill\_repressive\_scalar\_has\_derivative\_even as a corollary.\<close>

corollary hill_repressive_scalar_has_derivative_even:
  fixes x \<alpha> :: real  
  fixes n :: nat
  assumes n_even: \<open>even n\<close> and n_pos: \<open>n \<ge> 1\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_field_derivative 
          (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2)) (at x)\<close>
proof -
  have \<open>0 < 1 + x^n\<close>
    using n_even by (simp add: zero_le_even_power add_pos_nonneg)
  thus ?thesis using hill_repressive_scalar_has_derivative_general n_pos by blast
qed

text \<open>hill\_monotonic\_bound as a corollary (case n = 2).\<close>

corollary hill_monotonic_bound:
  fixes a x x_min x_max :: real
  assumes a_pos: \<open>0 < a\<close> 
  assumes x_min_nn: \<open>0 \<le> x_min\<close>
  assumes x_bounds: \<open>x_min \<le> x\<close> \<open>x \<le> x_max\<close>
  shows \<open>a / (1 + x_max^2) \<le> a / (1 + x^2) \<and> 
         a / (1 + x^2) \<le> a / (1 + x_min^2)\<close>
  using hill_monotonic_bound_general[OF a_pos x_min_nn _ x_bounds, where n = 2]
  by simp


text \<open>
          Convert to has\_derivative form (Fr?chet derivative)

  DI\_Vect uses `has\_derivative` (Fr?chet) rather than `has\_field\_derivative`.
  We use `has\_field\_derivative\_imp\_has\_derivative` (or whatever the actual
  conversion lemma is called) to bridge.

  For real-valued functions of a real variable, the Fr?chet derivative
  Df at x is the linear map (lambdah. h * f'(x)).
\<close>

lemma hill_repressive_scalar_has_frechet_derivative:
  fixes x :: real 
  fixes \<alpha> :: real 
  fixes n :: nat
  assumes x_nn: \<open>x \<ge> 0\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2))) (at x)\<close>
  using hill_repressive_scalar_has_derivative[OF x_nn n_pos]
  by (metis (full_types) has_field_derivative_imp_has_derivative mult_commute_abs)

text \<open>
       Vector version

  For DI\_Vect we need the function over vectors:
    H\_i(v) = alpha / (1 + (vec\_nth v i)\textasciicircum{}n)

  Strategy: compose the scalar Hill function with `(lambdav. vec\_nth v i)`.

  The chain rule gives us:
    DH\_i(v)(w) = (-alpha * n * (vec\_nth v i)\textasciicircum{}\{n-1\} / (1 + (vec\_nth v i)\textasciicircum{}n)\textasciicircum{}2) * vec\_nth w i

  i.e., the derivative is a linear functional on increment vectors `w`,
  which extracts the i-th component and multiplies by the scalar Hill
  derivative evaluated at vec\_nth v i.
\<close>

lemma hill_repressive_vector_has_derivative:
  fixes p :: \<open>(real, 'a::finite) vec\<close> 
  fixes \<alpha> :: real 
  fixes n :: nat 
  fixes i :: 'a
  assumes p_i_nn: \<open>vec_nth p i \<ge> 0\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows 
    \<open>((\<lambda>v. \<alpha> / (1 + (vec_nth v i)^n)) has_derivative 
      (\<lambda>w. (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2) * vec_nth w i)) (at p)\<close>
proof -
  (* Step 1: (\<lambda>v. vec_nth v i) has derivative (\<lambda>w. vec_nth w i) (it's linear) *)
  have nth_deriv: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>w. vec_nth w i)) (at p)\<close>
    by (rule has_derivative_vec_nth)

  (* Step 2: Scalar Hill function has derivative at vec_nth p i *)
  have hill_deriv: \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2))) 
          (at (vec_nth p i))\<close>
    using hill_repressive_scalar_has_frechet_derivative[OF p_i_nn n_pos] .

  (* Step 3: Chain rule *)
  have \<open>(((\<lambda>y. \<alpha> / (1 + y^n)) \<circ> (\<lambda>v. vec_nth v i)) has_derivative 
         ((\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2)) 
          \<circ> (\<lambda>w. vec_nth w i))) (at p)\<close>
    using has_derivative_compose[OF nth_deriv hill_deriv]
          diff_chain_at hill_deriv nth_deriv 
    by blast
  thus ?thesis
    by (simp add: comp_def algebra_simps)
qed

text \<open>Fr\'{e}chet-derivative version for even Hill coefficients.\<close>
lemma hill_repressive_scalar_has_frechet_derivative_even:
  fixes x \<alpha> :: real  
  fixes n :: nat
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * x^(n-1) / (1 + x^n)^2))) (at x)\<close>
  using hill_repressive_scalar_has_derivative_even[OF n_even n_pos]
  by (metis (full_types) has_field_derivative_imp_has_derivative mult_commute_abs)

text \<open>Vector version for even Hill coefficients.\<close>
lemma hill_repressive_vector_has_derivative_even:
  fixes p :: \<open>(real, 'a::finite) vec\<close> 
  fixes \<alpha> :: real 
  fixes n :: nat 
  fixes i :: 'a
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows 
    \<open>((\<lambda>v. \<alpha> / (1 + (vec_nth v i)^n)) has_derivative 
      (\<lambda>w. (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2) * vec_nth w i)) (at p)\<close>
proof -
  have nth_deriv: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>w. vec_nth w i)) (at p)\<close>
    by (rule has_derivative_vec_nth)

  have hill_deriv: \<open>((\<lambda>y. \<alpha> / (1 + y^n)) has_derivative 
          (\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2))) 
          (at (vec_nth p i))\<close>
    using hill_repressive_scalar_has_frechet_derivative_even[OF n_even n_pos] .

  have \<open>(((\<lambda>y. \<alpha> / (1 + y^n)) \<circ> (\<lambda>v. vec_nth v i)) has_derivative 
         ((\<lambda>h. h * (- \<alpha> * real n * (vec_nth p i)^(n-1) / (1 + (vec_nth p i)^n)^2)) \<circ> 
          (\<lambda>w. vec_nth w i))) (at p)\<close>
    using has_derivative_compose[OF nth_deriv hill_deriv]
          diff_chain_at hill_deriv nth_deriv 
    by blast
  thus ?thesis
    by (simp add: comp_def algebra_simps)
qed

subsection \<open>Lie derivative helpers\<close>
lemma induct_step_from_lie:
  fixes V :: \<open>(real,'a::finite) vec \<Rightarrow> real\<close>
  fixes f :: \<open>real \<Rightarrow> (real,'a) vec \<Rightarrow> (real,'a) vec\<close>
  fixes y :: \<open>real \<Rightarrow> (real,'a) vec\<close>
  fixes lin :: \<open>real \<Rightarrow> (real,'a) vec \<Rightarrow> real\<close>
  fixes bnd :: \<open>real \<Rightarrow> real\<close>
  fixes T :: real
  assumes V_deriv: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> (V has_derivative (lin \<tau>)) (at (y \<tau>))\<close>
  assumes rate_le: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> lin \<tau> (f \<tau> (y \<tau>)) \<le> bnd \<tau>\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
          \<exists>DV. (V has_derivative DV) (at (y \<tau>)) \<and> DV (f \<tau> (y \<tau>)) \<le> bnd \<tau>\<close>
proof -
  fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
  show \<open>\<exists>DV. (V has_derivative DV) (at (y \<tau>)) \<and> DV (f \<tau> (y \<tau>)) \<le> bnd \<tau>\<close>
    using V_deriv[OF h\<tau>] rate_le[OF h\<tau>] by blast
qed
end