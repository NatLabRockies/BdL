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
theory Bioreactor_Safety_Proof

imports Differential_Dynamic_Logic

begin
section \<open>Case study: bioreactor safety proof\<close>

text \<open>
  We formalize an engineered microorganism for biofuel production.
  The substrate S is consumed by biomass X via Monod kinetics.  
  Biomass growth produces a toxic intermediate Z, which is removed 
  by an engineered enzymatic degradation pathway (Michaelis-Menten 
  kinetics).  Growth is inhibited by high Z.
  
  The central design question: for what regime of feed rate u, 
  degradation rate k, and initial conditions does the intermediate 
  Z stay below its toxicity threshold?  This is a bioreactor 
  safety guarantee that cannot be obtained by simulation alone.\<close>


subsection \<open>Vector field\<close>

text \<open>
  The dynamics are:
    dS/dt = u - (mu\_max * S / (K\_S + S)) * X
    dX/dt = Y * (mu\_max * S / (K\_S + S)) * X * (K\_I / (K\_I + Z)) - d * X
    dZ/dt = alpha * (mu\_max * S / (K\_S + S)) * X - k * Z / (K\_Z + Z)
  
  The input u is a constant feed rate (one instance of the vector 
  field for each value of u).  Time-varying u can be handled by a 
  monotonicity argument; we leave that for future work.\<close>

definition metabolic_field ::
  \<open>'a::finite \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>
   real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   real \<Rightarrow> (real, 'a) vec \<Rightarrow>
   (real, 'a) vec\<close>
where
  \<open>metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z =
    (\<lambda>t v.
      vec_lambda ((\<lambda>k_idx. 0)(
        iS := u - (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX,
        iX := Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
               * (K_I / (K_I + vec_nth v iZ)) -
             d * vec_nth v iX,
        iZ := \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX -
             k * vec_nth v iZ / (K_Z + vec_nth v iZ))))\<close>

text \<open>Coordinates: iS holds S (substrate), iX holds X (biomass) and iZ holds Z
  (intermediate).  They are three pairwise distinct elements of an arbitrary
  finite index type 'a.\<close>


subsection \<open>Baseline parameter regime\<close>

text \<open>
  The baseline locale fixes the biological/physical constants and 
  imposes the minimum structural assumptions needed for the vector 
  field to make sense: positivity of rates, Michaelis constants, and 
  yields.  Design constraints (that specific parameter combinations 
  give a safe trapping region) are imposed in a downstream locale.\<close>

locale metabolic_baseline_params =
  fixes iS iX iZ :: \<open>'a::finite\<close>
    \<comment> \<open>the coordinates of S, X and Z in the state vector\<close>
  fixes \<mu>_max :: real
  fixes K_S :: real
  fixes Y :: real
  fixes d :: real
  fixes K_I :: real
  fixes \<alpha> :: real
  fixes k :: real
  fixes K_Z :: real
  assumes coords: \<open>iS \<noteq> iX\<close> \<open>iS \<noteq> iZ\<close> \<open>iX \<noteq> iZ\<close>
  assumes \<mu>_max_pos: \<open>0 < \<mu>_max\<close>
  assumes K_S_pos: \<open>0 < K_S\<close>
  assumes Y_pos: \<open>0 < Y\<close>
  assumes Y_bounded: \<open>Y \<le> 1\<close>
  assumes d_pos: \<open>0 < d\<close>
  assumes K_I_pos: \<open>0 < K_I\<close>
  assumes \<alpha>_pos: \<open>0 < \<alpha>\<close>
  assumes k_pos: \<open>0 < k\<close>
  assumes K_Z_pos: \<open>0 < K_Z\<close>
begin

lemmas coords_neq [simp] = coords coords[THEN not_sym]

text \<open>Basic helper facts: denominators strictly positive on the 
      non-negative orthant.\<close>

lemma K_S_plus_S_pos:
  fixes S :: real
  assumes S_nn: \<open>0 \<le> S\<close>
  shows \<open>0 < K_S + S\<close>
  using K_S_pos S_nn 
  by simp

lemma K_I_plus_Z_pos:
  fixes Z :: real
  assumes Z_nn: \<open>0 \<le> Z\<close>
  shows \<open>0 < K_I + Z\<close>
  using K_I_pos Z_nn 
  by simp

lemma K_Z_plus_Z_pos:
  fixes Z :: real
  assumes Z_nn: \<open>0 \<le> Z\<close>
  shows \<open>0 < K_Z + Z\<close>
  using K_Z_pos Z_nn 
  by simp

text \<open>Monod consumption rate is bounded above by mu\_max * X.
      (The "rate" here is the per-cell intrinsic term, without the 
       biomass multiplier; the bound matters because we'll need to 
       bound the flux into Z from above when proving the safety box.)\<close>

lemma monod_consumption_bound:
  fixes S X :: real
  assumes S_nn: \<open>0 \<le> S\<close>
  assumes X_nn: \<open>0 \<le> X\<close>
  shows \<open>(\<mu>_max * S / (K_S + S)) * X \<le> \<mu>_max * X\<close>
proof -
  have denom_pos: \<open>0 < K_S + S\<close> using K_S_plus_S_pos[OF S_nn] .
  have frac_bound: \<open>S / (K_S + S) \<le> 1\<close>
  proof -
    have \<open>S \<le> K_S + S\<close> using K_S_pos by simp
    thus ?thesis using denom_pos by (simp add: divide_le_eq)
  qed
  have \<open>\<mu>_max * S / (K_S + S) \<le> \<mu>_max\<close>
    using \<mu>_max_pos frac_bound
    by (metis K_S_pos denom_pos less_eq_real_def mult_le_cancel_left_pos pos_divide_le_eq zero_compare_simps(3))
  hence \<open>(\<mu>_max * S / (K_S + S)) * X \<le> \<mu>_max * X\<close>
    using X_nn 
    using mult_right_mono 
    by blast
  thus ?thesis .
qed

lemma monod_consumption_nn:
  fixes S X :: real
  assumes S_nn: \<open>0 \<le> S\<close>
  assumes X_nn: \<open>0 \<le> X\<close>
  shows \<open>0 \<le> (\<mu>_max * S / (K_S + S)) * X\<close>
proof -
  have denom_pos: \<open>0 < K_S + S\<close> using K_S_plus_S_pos[OF S_nn] .
  have num_nn: \<open>0 \<le> \<mu>_max * S\<close> using \<mu>_max_pos S_nn by simp
  have \<open>0 \<le> \<mu>_max * S / (K_S + S)\<close>
    using num_nn denom_pos by (simp add: divide_nonneg_pos)
  thus ?thesis 
    using X_nn  mult_sign_intros(1)
    by blast
qed

text \<open>The growth-inhibition factor K\_I/(K\_I + Z) is bounded in [0, 1].
      At Z = 0 it is 1 (full growth); as Z increases it decreases 
      toward 0 (growth shuts off).\<close>

lemma growth_inhibition_bounds:
  fixes Z :: real
  assumes Z_nn: \<open>0 \<le> Z\<close>
  shows \<open>0 \<le> K_I / (K_I + Z) \<and> K_I / (K_I + Z) \<le> 1\<close>
proof -
  have denom_pos: \<open>0 < K_I + Z\<close> using K_I_plus_Z_pos[OF Z_nn] .
  have num_nn: \<open>0 \<le> K_I\<close> using K_I_pos by simp
  have lb: \<open>0 \<le> K_I / (K_I + Z)\<close>
    using num_nn denom_pos by (simp add: divide_nonneg_pos)
  have \<open>K_I \<le> K_I + Z\<close> using Z_nn by simp
  hence ub: \<open>K_I / (K_I + Z) \<le> 1\<close> 
    using denom_pos by (simp add: divide_le_eq)
  from lb ub show ?thesis by blast
qed

text \<open>The Michaelis-Menten degradation rate k*Z/(K\_Z+Z) is bounded 
      above by k (saturation).  At Z = 0 it is 0; as Z grows it 
      approaches k.\<close>

lemma mm_degradation_bounds:
  fixes Z :: real
  assumes Z_nn: \<open>0 \<le> Z\<close>
  shows \<open>0 \<le> k * Z / (K_Z + Z) \<and> k * Z / (K_Z + Z) \<le> k\<close>
proof -
  have denom_pos: \<open>0 < K_Z + Z\<close> using K_Z_plus_Z_pos[OF Z_nn] .
  have num_nn: \<open>0 \<le> k * Z\<close> using k_pos Z_nn by simp
  have lb: \<open>0 \<le> k * Z / (K_Z + Z)\<close>
    using num_nn denom_pos by (simp add: divide_nonneg_pos)
  have \<open>Z \<le> K_Z + Z\<close> using K_Z_pos by simp
  hence \<open>Z / (K_Z + Z) \<le> 1\<close> using denom_pos by (simp add: divide_le_eq)
  hence \<open>k * (Z / (K_Z + Z)) \<le> k\<close> 
    using k_pos mult_left_le 
    by fastforce
  hence ub: \<open>k * Z / (K_Z + Z) \<le> k\<close> by simp
  from lb ub show ?thesis by blast
qed

text \<open>MM degradation is monotone in Z: larger Z means faster degradation 
      (up to saturation).  This is the key property that makes k/(K\_Z+Z) 
      pointing inward at Z = Z\_tox.\<close>

lemma mm_degradation_monotone:
  fixes Z1 Z2 :: real
  assumes Z1_nn: \<open>0 \<le> Z1\<close>
  assumes Z1_le_Z2: \<open>Z1 \<le> Z2\<close>
  shows \<open>k * Z1 / (K_Z + Z1) \<le> k * Z2 / (K_Z + Z2)\<close>
proof -
  have Z2_nn: \<open>0 \<le> Z2\<close> using Z1_nn Z1_le_Z2 by linarith
  have d1_pos: \<open>0 < K_Z + Z1\<close> using K_Z_plus_Z_pos[OF Z1_nn] .
  have d2_pos: \<open>0 < K_Z + Z2\<close> using K_Z_plus_Z_pos[OF Z2_nn] .
  have d12: \<open>K_Z + Z1 \<le> K_Z + Z2\<close> using Z1_le_Z2 by simp
  (* k\<sqdot>Z/(K_Z+Z) = k - k\<sqdot>K_Z/(K_Z+Z); latter is decreasing in Z *)
  have rewrite1: \<open>k * Z1 / (K_Z + Z1) = k - k * K_Z / (K_Z + Z1)\<close>
    using d1_pos K_Z_pos by (simp add: field_simps)
  have rewrite2: \<open>k * Z2 / (K_Z + Z2) = k - k * K_Z / (K_Z + Z2)\<close>
    using d2_pos K_Z_pos by (simp add: field_simps)
  have kKZ_pos: \<open>0 < k * K_Z\<close> using k_pos K_Z_pos by simp
  have \<open>k * K_Z / (K_Z + Z2) \<le> k * K_Z / (K_Z + Z1)\<close>
    using kKZ_pos d12 d1_pos d2_pos by (simp add: frac_le)
  thus ?thesis using rewrite1 rewrite2 by linarith
qed

text \<open>Monod uptake is monotone in S (at fixed X): larger substrate gives 
      faster consumption. This is the key property that makes 
      mu\_max*S/(K\_S+S) pointing inward at S = S\_max.\<close>

lemma monod_uptake_monotone_in_S:
  fixes S1 S2 X :: real
  assumes S1_nn: \<open>0 \<le> S1\<close>
  assumes S1_le_S2: \<open>S1 \<le> S2\<close>
  assumes X_nn: \<open>0 \<le> X\<close>
  shows \<open>(\<mu>_max * S1 / (K_S + S1)) * X \<le> (\<mu>_max * S2 / (K_S + S2)) * X\<close>
proof -
  have S2_nn: \<open>0 \<le> S2\<close> using S1_nn S1_le_S2 by linarith
  have d1_pos: \<open>0 < K_S + S1\<close> using K_S_plus_S_pos[OF S1_nn] .
  have d2_pos: \<open>0 < K_S + S2\<close> using K_S_plus_S_pos[OF S2_nn] .
  have d12: \<open>K_S + S1 \<le> K_S + S2\<close> using S1_le_S2 by simp
  have rewrite1: \<open>\<mu>_max * S1 / (K_S + S1) = \<mu>_max - \<mu>_max * K_S / (K_S + S1)\<close>
    using d1_pos K_S_pos by (simp add: field_simps)
  have rewrite2: \<open>\<mu>_max * S2 / (K_S + S2) = \<mu>_max - \<mu>_max * K_S / (K_S + S2)\<close>
    using d2_pos K_S_pos by (simp add: field_simps)
  have \<mu>KS_pos: \<open>0 < \<mu>_max * K_S\<close> using \<mu>_max_pos K_S_pos by simp
  have \<open>\<mu>_max * K_S / (K_S + S2) \<le> \<mu>_max * K_S / (K_S + S1)\<close>
    using \<mu>KS_pos d12 d1_pos d2_pos by (simp add: frac_le)
  hence \<open>\<mu>_max * S1 / (K_S + S1) \<le> \<mu>_max * S2 / (K_S + S2)\<close>
    using rewrite1 rewrite2 by linarith
  thus ?thesis using X_nn mult_right_mono 
    by blast
qed

end  (* metabolic_baseline_params *)


subsection \<open>Safety region with design constraints (a failed attempt)\<close>

text \<open>
  This section records a first attempt at a safety guarantee.  It fails,
  and we keep it to document why.  The safety region is an axis-aligned
  bounded box in (S, X, Z) space.  For the box to be forward-invariant,
  the vector field must point strictly inward at each face.  This imposes
  design constraints on the feed rate u, the degradation rate k, and the
  box boundaries.

  We use strictly positive lower bounds on all three components because
  DI\_Frame\_Rule\_partial requires strict inequalities at the edges; Z
  cannot touch 0 because then dZ/dt could become non-strictly positive.

  The attempt fails at the two X faces.  The X equation has the form
  dX/dt = X * r(S, Z), where the net growth rate
  r(S, Z) = Y * (mu\_max * S / (K\_S + S)) * (K\_I / (K\_I + Z)) - d
  does not depend on X.  For given S and Z, the field therefore points the
  same way on both X faces, so it cannot point inward on both.  In the
  locale below this shows up as two design constraints that contradict
  each other: X\_lower\_growth\_exceeds\_decay asks for r > 0 at the
  slowest growth in the box (S = S\_min, Z = Z\_max), and
  X\_upper\_growth\_below\_decay asks for r < 0 at the fastest growth
  (S = S\_max, Z = Z\_min).  Growth increases with S and decreases with Z,
  so the slowest growth is at most the fastest one, and the two
  constraints together would give d < d.  No parameter values satisfy the
  locale, so its invariance theorem holds only vacuously.  The locale
  metabolic\_z\_clearance\_params replaces this attempt: it takes the
  bounds on S and X from the bioreactor's controllers and proves that Z is
  cleared.\<close>

locale metabolic_safety_region_params = metabolic_baseline_params +
  fixes u :: real                          \<comment> \<open>constant feed rate\<close>
  fixes S_min S_max X_min X_max Z_min Z_max :: real
  assumes u_pos: \<open>0 < u\<close>
  \<comment> \<open>Box ordering and positivity.\<close>
  assumes S_ordered: \<open>S_min < S_max\<close>
  assumes X_ordered: \<open>X_min < X_max\<close>
  assumes Z_ordered: \<open>Z_min < Z_max\<close>
  assumes S_min_pos: \<open>0 < S_min\<close>
  assumes X_min_pos: \<open>0 < X_min\<close>
  assumes Z_min_pos: \<open>0 < Z_min\<close>
  \<comment> \<open>S-face design constraints (feed rate balanced against uptake).\<close>
  assumes S_lower_inward: 
    \<open>(\<mu>_max * S_min / (K_S + S_min)) * X_max < u\<close>
  assumes S_upper_inward:
    \<open>u < (\<mu>_max * S_max / (K_S + S_max)) * X_min\<close>
  \<comment> \<open>X-face design constraints (growth vs. decay).\<close>
  assumes X_lower_growth_exceeds_decay:
    \<open>d < Y * (\<mu>_max * S_min / (K_S + S_min)) * (K_I / (K_I + Z_max))\<close>
  assumes X_upper_growth_below_decay:
    \<open>Y * (\<mu>_max * S_max / (K_S + S_max)) * (K_I / (K_I + Z_min)) < d\<close>
  \<comment> \<open>Z-face design constraints (degradation outpaces production).\<close>
  assumes Z_lower_production_exceeds_degradation:
    \<open>k * Z_min / (K_Z + Z_min) < \<alpha> * (\<mu>_max * S_min / (K_S + S_min)) * X_min\<close>
  assumes Z_upper_degradation_exceeds_production:
    \<open>\<alpha> * (\<mu>_max * S_max / (K_S + S_max)) * X_max < k * Z_max / (K_Z + Z_max)\<close>
begin

text \<open> Predicate for the safety region, in terms of the components
  vec\_nth v iS, vec\_nth v iX and vec\_nth v iZ.\<close>

definition in_safety_region :: 
  \<open>(real, 'a) vec \<Rightarrow> bool\<close> where
  \<open>in_safety_region v \<longleftrightarrow> 
     S_min \<le> vec_nth v iS \<and> vec_nth v iS \<le> S_max \<and>
     X_min \<le> vec_nth v iX \<and> vec_nth v iX \<le> X_max \<and>
     Z_min \<le> vec_nth v iZ \<and> vec_nth v iZ \<le> Z_max\<close>


subsection \<open>Forward invariance of the safety region\<close>

text \<open>
  Forward invariance of the box under the design constraints: a
  trajectory that starts in the safety region and evolves under the
  metabolic ODE with constant feed rate u stays in the safety region.
  The derivation is correct, but its premises include the two
  contradictory X-face constraints explained above, so the theorem says
  nothing about any actual bioreactor.  It is kept to document the
  attempt.\<close>

lemma safety_region_forward_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes t :: real
  assumes y_sol: \<open>(y solves_ode 
                   (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z)) 
                   {0..t} UNIV\<close>
  assumes t_nn: \<open>0 \<le> t\<close>
  assumes y0_in_safety: \<open>in_safety_region (y 0)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_safety_region (y \<tau>)\<close>
proof -
  define lo :: \<open>'a \<Rightarrow> real\<close> where
    \<open>lo = (\<lambda>i. if i = iS then S_min 
               else if i = iX then X_min
               else if i = iZ then Z_min
               else vec_nth (y 0) i)\<close>
  define hi :: \<open>'a \<Rightarrow> real\<close> where
    \<open>hi = (\<lambda>i. if i = iS then S_max 
               else if i = iX then X_max
               else if i = iZ then Z_max
               else vec_nth (y 0) i)\<close>
  define active :: \<open>'a set\<close> where
    \<open>active = {iS, iX, iZ}\<close>

  \<comment> \<open>Initial values lie in [lo, hi].\<close>
  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'a
    show \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof (cases \<open>i = iS\<close>)
      case True
      with y0_in_safety show ?thesis 
        unfolding in_safety_region_def lo_def hi_def by simp
    next
      case False
      show ?thesis
      proof (cases \<open>i = iX\<close>)
        case True
        with y0_in_safety \<open>i \<noteq> iS\<close> show ?thesis 
          unfolding in_safety_region_def lo_def hi_def by simp
      next
        case False
        show ?thesis
        proof (cases \<open>i = iZ\<close>)
          case True
          with y0_in_safety \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> show ?thesis 
            unfolding in_safety_region_def lo_def hi_def by simp
        next
          case False
          with \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> show ?thesis 
            unfolding lo_def hi_def by simp
        qed
      qed
    qed
  qed

  \<comment> \<open>Active components have lo < hi.\<close>
  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'a assume \<open>i \<in> active\<close>
    hence \<open>i = iS \<or> i = iX \<or> i = iZ\<close> unfolding active_def by blast
    thus \<open>lo i < hi i\<close>
    proof (elim disjE)
      assume \<open>i = iS\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using S_ordered by simp
    next
      assume \<open>i = iX\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using X_ordered by simp
    next
      assume \<open>i = iZ\<close>
      thus \<open>lo i < hi i\<close> unfolding lo_def hi_def using Z_ordered by simp
    qed
  qed

  \<comment> \<open>Lower-edge condition: at v\_i = lo i (with other components in 
      box), the i-th component of the field is strictly positive.\<close>
  have lower_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = lo i \<Longrightarrow> 
             0 < vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>

    \<comment> \<open>we extract scalar component bounds.\<close>
    have S_bounds: \<open>S_min \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_max\<close>
      using bounds[of iS] unfolding lo_def hi_def by simp_all
    have X_bounds: \<open>X_min \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_max\<close>
      using bounds[of iX] unfolding lo_def hi_def by simp_all
    have Z_bounds: \<open>Z_min \<le> vec_nth v iZ\<close> \<open>vec_nth v iZ \<le> Z_max\<close>
      using bounds[of iZ] unfolding lo_def hi_def by simp_all
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> using S_bounds(1) S_min_pos by linarith
    have X_nn: \<open>0 \<le> vec_nth v iX\<close> using X_bounds(1) X_min_pos by linarith
    have Z_nn: \<open>0 \<le> vec_nth v iZ\<close> using Z_bounds(1) Z_min_pos by linarith

    from i_act have \<open>i = iS \<or> i = iX \<or> i = iZ\<close> unfolding active_def by blast
    thus \<open>0 < vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
    proof (elim disjE)
      \<comment> \<open>Case i = iS: S-lower edge.\<close>
      assume i_eq: \<open>i = iS\<close>
      have S_at_min: \<open>vec_nth v iS = S_min\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iS = 
         u - (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
        unfolding metabolic_field_def by (simp add: fun_upd_def)
      also have \<open>... = u - (\<mu>_max * S_min / (K_S + S_min)) * vec_nth v iX\<close>
        using S_at_min by simp
      finally have field_val: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iS = 
         u - (\<mu>_max * S_min / (K_S + S_min)) * vec_nth v iX\<close> .
      \<comment> \<open>At X = X\_max we get the design bound; for X <= X\_max use monotonicity.\<close>
      have consumption_le: 
        \<open>(\<mu>_max * S_min / (K_S + S_min)) * vec_nth v iX \<le> 
         (\<mu>_max * S_min / (K_S + S_min)) * X_max\<close>
      proof -
        have denom_pos: \<open>0 < K_S + S_min\<close> 
          using K_S_plus_S_pos S_min_pos by simp
        have rate_nn: \<open>0 \<le> \<mu>_max * S_min / (K_S + S_min)\<close>
          using \<mu>_max_pos S_min_pos denom_pos by (simp add: divide_nonneg_pos)
        show ?thesis
          using rate_nn X_bounds(2) mult_left_mono by blast
      qed
      have \<open>(\<mu>_max * S_min / (K_S + S_min)) * vec_nth v iX < u\<close>
        using consumption_le S_lower_inward by linarith
      thus \<open>0 < vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
        using field_val i_eq by simp
    next
      \<comment> \<open>Case i = iX: X-lower edge.\<close>
      assume i_eq: \<open>i = iX\<close>
      have X_at_min: \<open>vec_nth v iX = X_min\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iX = 
         Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
             * (K_I / (K_I + vec_nth v iZ)) 
           - d * vec_nth v iX\<close>
        unfolding metabolic_field_def by (simp add: fun_upd_def)
      \<comment> \<open>Factoring X\_min from the expression using X\_at\_min.\<close>
      also have \<open>... = X_min * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
                                  * (K_I / (K_I + vec_nth v iZ)) - d)\<close>
        using X_at_min by (simp add: algebra_simps)
      finally have field_val: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iX = 
         X_min * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
                    * (K_I / (K_I + vec_nth v iZ)) - d)\<close> .

      \<comment> \<open>Key: Y*(mu\_max*S/(K\_S+S))*(K\_I/(K\_I+Z)) > d for any S in [S\_min, S\_max], Z in [Z\_min, Z\_max].
          The worst-case (minimum growth) is at S = S\_min, Z = Z\_max.\<close>
      have growth_rate_bound:
        \<open>Y * (\<mu>_max * S_min / (K_S + S_min)) * (K_I / (K_I + Z_max)) \<le>
         Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + vec_nth v iZ))\<close>
      proof -
        \<comment> \<open>Monotonicity in S.\<close>
        have uptake_mono: \<open>\<mu>_max * S_min / (K_S + S_min) \<le> 
                           \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
        proof -
          have \<open>(\<mu>_max * S_min / (K_S + S_min)) * 1 \<le> 
                (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1\<close>
            using S_bounds(1) S_min_pos less_imp_le monod_uptake_monotone_in_S rel_simps(44) 
            by blast
          thus ?thesis 
            by simp
        qed
        \<comment> \<open>Anti-monotonicity in Z: K\_I/(K\_I+Z) decreases as Z increases.\<close>
        have inhibition_mono:
          \<open>K_I / (K_I + Z_max) \<le> K_I / (K_I + vec_nth v iZ)\<close>
        proof -
          have dmax_pos: \<open>0 < K_I + Z_max\<close> 
            using K_I_pos Z_bounds(2) Z_nn by linarith
          have dv_pos: \<open>0 < K_I + vec_nth v iZ\<close> 
            using K_I_plus_Z_pos[OF Z_nn] .
          have d_le: \<open>K_I + vec_nth v iZ \<le> K_I + Z_max\<close>
            using Z_bounds(2) by simp
          show ?thesis
            using K_I_pos d_le dv_pos dmax_pos by (simp add: frac_le)
        qed
        \<comment> \<open>Combine both.\<close>
        have uptake_nn: \<open>0 \<le> \<mu>_max * S_min / (K_S + S_min)\<close>
        proof -
          have \<open>0 < K_S + S_min\<close> using K_S_plus_S_pos S_min_pos by simp
          thus ?thesis using \<mu>_max_pos S_min_pos by (simp add: divide_nonneg_pos)
        qed
        have uptake_at_v_nn: \<open>0 \<le> \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
        proof -
          have \<open>0 < K_S + vec_nth v iS\<close> using K_S_plus_S_pos[OF S_nn] .
          thus ?thesis using \<mu>_max_pos S_nn by (simp add: divide_nonneg_pos)
        qed
        have inh_at_v_nn: \<open>0 \<le> K_I / (K_I + vec_nth v iZ)\<close>
          using growth_inhibition_bounds[OF Z_nn] by simp
        have Y_nn: \<open>0 \<le> Y\<close> using Y_pos by simp
        \<comment> \<open>Step 1: Y * (uptake at S\_min) * (inhibition at Z\_max) <= Y * (uptake at v) * (inhibition at Z\_max).\<close>
        have step1: 
          \<open>Y * (\<mu>_max * S_min / (K_S + S_min)) * (K_I / (K_I + Z_max)) \<le>
           Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + Z_max))\<close>
        proof -
          have Y_uptake_mono: 
            \<open>Y * (\<mu>_max * S_min / (K_S + S_min)) \<le> 
             Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS))\<close>
            using uptake_mono Y_nn Y_pos mult_le_cancel_left_pos 
            by blast
          have inh_max_nn: \<open>0 \<le> K_I / (K_I + Z_max)\<close>
            using K_I_pos Z_bounds(2) Z_nn by (simp add: divide_nonneg_pos)
          show ?thesis
            using Y_uptake_mono inh_max_nn 
            using landau_omega.R_mult_right_mono 
            by blast
        qed
        \<comment> \<open>Step 2: Y * (uptake at v) * (inhibition at Z\_max) <= Y * (uptake at v) * (inhibition at v).\<close>
        have step2: 
          \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + Z_max)) \<le>
           Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + vec_nth v iZ))\<close>
        proof -
          have prod_nn: \<open>0 \<le> Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS))\<close>
            using Y_nn uptake_at_v_nn split_mult_pos_le 
            by blast
          show ?thesis
            using prod_nn inhibition_mono landau_omega.R_mult_left_mono 
            by blast
        qed
        from step1 step2 show ?thesis by linarith
      qed

      \<comment> \<open>The design constraint X\_lower\_growth\_exceeds\_decay gives us d < Y*...\<close>
      have growth_gt_decay: 
        \<open>d < Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
             * (K_I / (K_I + vec_nth v iZ))\<close>
        using X_lower_growth_exceeds_decay growth_rate_bound by linarith

      \<comment> \<open>Multiplied by X\_min > 0, gives us the strict positivity.\<close>
      have \<open>0 < X_min * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
                           * (K_I / (K_I + vec_nth v iZ)) - d)\<close>
        using X_min_pos growth_gt_decay by simp 
      thus \<open>0 < vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
        using field_val i_eq by simp
    next
      \<comment> \<open>Case i = iZ: Z-lower edge.\<close>
      assume i_eq: \<open>i = iZ\<close>
      have Z_at_min: \<open>vec_nth v iZ = Z_min\<close>
        using eq_lo i_eq unfolding lo_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ = 
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
         - k * vec_nth v iZ / (K_Z + vec_nth v iZ)\<close>
        unfolding metabolic_field_def by (simp add: fun_upd_def)
      also have \<open>... = \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
                       - k * Z_min / (K_Z + Z_min)\<close>
        using Z_at_min by simp
      finally have field_val: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ = 
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
         - k * Z_min / (K_Z + Z_min)\<close> .

      \<comment> \<open>Production at (v\_0, v\_1) >= production at (S\_min, X\_min) by monotonicity.\<close>
      have production_ge:
        \<open>\<alpha> * (\<mu>_max * S_min / (K_S + S_min)) * X_min \<le> 
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
      proof -
        have uptake_mono: \<open>\<mu>_max * S_min / (K_S + S_min) \<le> 
                           \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
        proof -
          have \<open>(\<mu>_max * S_min / (K_S + S_min)) * 1 \<le> 
                (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1\<close>
            using S_bounds(1) S_min_pos less_imp_le
                  monod_uptake_monotone_in_S rel_simps(44) 
            by blast
          thus ?thesis by simp
        qed
        have uptake_at_v_nn: \<open>0 \<le> \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
        proof -
          have \<open>0 < K_S + vec_nth v iS\<close> using K_S_plus_S_pos[OF S_nn] .
          thus ?thesis using \<mu>_max_pos S_nn by (simp add: divide_nonneg_pos)
        qed
        have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> using \<alpha>_pos by simp
        have \<alpha>_uptake_mono: 
          \<open>\<alpha> * (\<mu>_max * S_min / (K_S + S_min)) \<le> 
           \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS))\<close>
          using uptake_mono \<alpha>_nn 
          using mult_left_mono 
          by blast
        have step1:
          \<open>\<alpha> * (\<mu>_max * S_min / (K_S + S_min)) * X_min \<le>
           \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * X_min\<close>
          using \<alpha>_uptake_mono X_min_pos mult_right_mono
          by fastforce
        have \<alpha>u_v_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS))\<close>
          using \<alpha>_nn uptake_at_v_nn split_mult_pos_le 
          by blast
        have step2:
          \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * X_min \<le>
           \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
          using \<alpha>u_v_nn X_bounds(1)
                ordered_comm_semiring_class.comm_mult_left_mono 
          by blast
        from step1 step2 show ?thesis by linarith
      qed
      have \<open>k * Z_min / (K_Z + Z_min) < 
            \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
        using Z_lower_production_exceeds_degradation production_ge by linarith
      thus \<open>0 < vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
        using field_val i_eq by simp
    qed
  qed

  \<comment> \<open>Upper-edge condition: at v\_i = hi i, the i-th component of the 
      field is strictly negative.  Symmetric to lower\_edge.\<close>
  have upper_edge: 
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
             (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow> 
             vec_nth v i = hi i \<Longrightarrow> 
             vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    assume bounds: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>

    have S_bounds: \<open>S_min \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_max\<close>
      using bounds[of iS] unfolding lo_def hi_def by simp_all
    have X_bounds: \<open>X_min \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_max\<close>
      using bounds[of iX] unfolding lo_def hi_def by simp_all
    have Z_bounds: \<open>Z_min \<le> vec_nth v iZ\<close> \<open>vec_nth v iZ \<le> Z_max\<close>
      using bounds[of iZ] unfolding lo_def hi_def by simp_all
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> using S_bounds(1) S_min_pos by linarith
    have X_nn: \<open>0 \<le> vec_nth v iX\<close> using X_bounds(1) X_min_pos by linarith
    have Z_nn: \<open>0 \<le> vec_nth v iZ\<close> using Z_bounds(1) Z_min_pos by linarith

    from i_act have \<open>i = iS \<or> i = iX \<or> i = iZ\<close> unfolding active_def by blast
    thus \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
    proof (elim disjE)
      \<comment> \<open>Case i = iS: S-upper edge.\<close>
      assume i_eq: \<open>i = iS\<close>
      have S_at_max: \<open>vec_nth v iS = S_max\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iS = 
         u - (\<mu>_max * S_max / (K_S + S_max)) * vec_nth v iX\<close>
        unfolding metabolic_field_def using S_at_max 
        by (simp add: fun_upd_def)

      \<comment> \<open>At X >= X\_min we have (mu\_max*S\_max/(K\_S+S\_max))*X >= ... * X\_min > u.\<close>
      have consumption_ge:
        \<open>(\<mu>_max * S_max / (K_S + S_max)) * X_min \<le> 
         (\<mu>_max * S_max / (K_S + S_max)) * vec_nth v iX\<close>
      proof -
        have denom_pos: \<open>0 < K_S + S_max\<close> 
          using K_S_plus_S_pos S_bounds S_nn by simp
        have rate_nn: \<open>0 \<le> \<mu>_max * S_max / (K_S + S_max)\<close>
          using \<mu>_max_pos S_bounds S_nn denom_pos 
          by (simp add: divide_nonneg_pos)
        show ?thesis 
          using rate_nn X_bounds(1) landau_omega.R_mult_left_mono 
          by blast
      qed
      have \<open>u < (\<mu>_max * S_max / (K_S + S_max)) * vec_nth v iX\<close>
        using S_upper_inward consumption_ge by linarith
      thus \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
        using field_eq i_eq by simp
    next
      \<comment> \<open>Case i = iX: X-upper edge.\<close>
      assume i_eq: \<open>i = iX\<close>
      have X_at_max: \<open>vec_nth v iX = X_max\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iX = 
         X_max * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
                    * (K_I / (K_I + vec_nth v iZ)) - d)\<close>
      proof -
        have \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iX = 
              Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
                  * (K_I / (K_I + vec_nth v iZ)) 
                - d * vec_nth v iX\<close>
          unfolding metabolic_field_def by (simp add: fun_upd_def)
        also have \<open>... = X_max * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) 
                                    * (K_I / (K_I + vec_nth v iZ)) - d)\<close>
          using X_at_max by (simp add: algebra_simps)
        finally show ?thesis .
      qed

      \<comment> \<open>Growth rate at (S, Z) <= growth rate at (S\_max, Z\_min) by monotonicity.\<close>
      have growth_rate_bound:
        \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + vec_nth v iZ)) \<le>
         Y * (\<mu>_max * S_max / (K_S + S_max)) * (K_I / (K_I + Z_min))\<close>
      proof -
        have uptake_mono: \<open>\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS) \<le> 
                           \<mu>_max * S_max / (K_S + S_max)\<close>
        proof -
          have \<open>(\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1 \<le> 
                (\<mu>_max * S_max / (K_S + S_max)) * 1\<close>
            using monod_uptake_monotone_in_S[OF S_nn S_bounds(2), of 1] by simp
          thus ?thesis 
            by simp
        qed
        have inhibition_mono:
          \<open>K_I / (K_I + vec_nth v iZ) \<le> K_I / (K_I + Z_min)\<close>
        proof -
          have dmin_pos: \<open>0 < K_I + Z_min\<close> 
            using K_I_pos Z_min_pos by simp
          have dv_pos: \<open>0 < K_I + vec_nth v iZ\<close> 
            using K_I_plus_Z_pos[OF Z_nn] .
          have d_le: \<open>K_I + Z_min \<le> K_I + vec_nth v iZ\<close>
            using Z_bounds(1) by simp
          show ?thesis
            using K_I_pos d_le dmin_pos dv_pos 
            by (simp add: frac_le)
        qed
        have uptake_max_nn: \<open>0 \<le> \<mu>_max * S_max / (K_S + S_max)\<close>
        proof -
          have \<open>0 < K_S + S_max\<close> using K_S_plus_S_pos S_bounds S_nn by simp
          thus ?thesis using \<mu>_max_pos S_bounds S_nn 
            by (simp add: divide_nonneg_pos)
        qed
        have inh_at_v_nn: \<open>0 \<le> K_I / (K_I + vec_nth v iZ)\<close>
          using growth_inhibition_bounds[OF Z_nn] by simp
        have Y_nn: \<open>0 \<le> Y\<close> 
          using Y_pos 
          by simp
        have step1: 
          \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + vec_nth v iZ)) \<le>
           Y * (\<mu>_max * S_max / (K_S + S_max)) * (K_I / (K_I + vec_nth v iZ))\<close>
        proof -
          have Y_uptake_mono: 
            \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) \<le> 
             Y * (\<mu>_max * S_max / (K_S + S_max))\<close>
            using uptake_mono Y_nn  landau_omega.R_mult_left_mono 
            by blast
          show ?thesis
            using Y_uptake_mono inh_at_v_nn  landau_omega.R_mult_right_mono 
            by blast
        qed
        have step2:
          \<open>Y * (\<mu>_max * S_max / (K_S + S_max)) * (K_I / (K_I + vec_nth v iZ)) \<le>
           Y * (\<mu>_max * S_max / (K_S + S_max)) * (K_I / (K_I + Z_min))\<close>
        proof -
          have prod_nn: \<open>0 \<le> Y * (\<mu>_max * S_max / (K_S + S_max))\<close>
            using Y_nn uptake_max_nn  mult_sign_intros(1) 
            by blast
          show ?thesis
            using prod_nn inhibition_mono 
                  landau_o.R_mult_left_mono 
            by blast
        qed
        from step1 step2 show ?thesis by linarith
      qed

      have growth_lt_decay: 
        \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * (K_I / (K_I + vec_nth v iZ)) < d\<close>
        using X_upper_growth_below_decay growth_rate_bound 
        by linarith

      have \<open>X_max * (Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 
            (K_I / (K_I + vec_nth v iZ)) - d) < 0\<close>
      proof -
        have X_max_pos: \<open>0 < X_max\<close> using X_min_pos X_ordered by linarith
        have \<open>Y * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 
              (K_I / (K_I + vec_nth v iZ)) - d < 0\<close>
          using growth_lt_decay 
          by simp
        thus ?thesis 
          using X_max_pos 
          by (simp add: mult_pos_neg)
      qed
      thus \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
        using field_eq i_eq 
        by simp
    next
      \<comment> \<open>Case i = iZ: Z-upper edge.\<close>
      assume i_eq: \<open>i = iZ\<close>
      have Z_at_max: \<open>vec_nth v iZ = Z_max\<close>
        using eq_hi i_eq unfolding hi_def by simp
      have field_eq: 
        \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ = 
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
         - k * Z_max / (K_Z + Z_max)\<close>
        unfolding metabolic_field_def using Z_at_max 
        by (simp add: fun_upd_def)

      \<comment> \<open>Production at (v\_0, v\_1) <= production at (S\_max, X\_max) by monotonicity.\<close>
      have production_le:
        \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * S_max / (K_S + S_max)) * X_max\<close>
      proof -
        have uptake_mono: \<open>\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS) \<le> 
                           \<mu>_max * S_max / (K_S + S_max)\<close>
        proof -
          have \<open>(\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1 \<le> 
                (\<mu>_max * S_max / (K_S + S_max)) * 1\<close>
            using monod_uptake_monotone_in_S[OF S_nn S_bounds(2), of 1] 
            by simp
          thus ?thesis 
            by simp
        qed
        have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> 
          using \<alpha>_pos 
          by simp
        have uptake_max_nn: \<open>0 \<le> \<mu>_max * S_max / (K_S + S_max)\<close>
        proof -
          have \<open>0 < K_S + S_max\<close> 
            using K_S_plus_S_pos S_bounds S_nn 
            by simp
          thus ?thesis 
            using \<mu>_max_pos S_bounds S_nn 
            by (simp add: divide_nonneg_pos)
        qed
        have \<alpha>_uptake_mono: 
          \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) \<le> 
           \<alpha> * (\<mu>_max * S_max / (K_S + S_max))\<close>
          using uptake_mono \<alpha>_nn landau_omega.R_mult_left_mono 
          by blast
        have step1:
          \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
           \<alpha> * (\<mu>_max * S_max / (K_S + S_max)) * vec_nth v iX\<close>
          using \<alpha>_uptake_mono X_nn mult_right_mono 
          by blast
        have \<alpha>u_max_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_max / (K_S + S_max))\<close>
          using \<alpha>_nn uptake_max_nn split_mult_pos_le 
          by blast
        have step2:
          \<open>\<alpha> * (\<mu>_max * S_max / (K_S + S_max)) * vec_nth v iX \<le>
           \<alpha> * (\<mu>_max * S_max / (K_S + S_max)) * X_max\<close>
          using \<alpha>u_max_nn X_bounds(2) landau_omega.R_mult_left_mono 
          by blast
        from step1 step2 
        show ?thesis 
          by linarith
      qed

      have \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
            < k * Z_max / (K_Z + Z_max)\<close>
        using Z_upper_degradation_exceeds_production production_le 
        by linarith
      thus \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
        using field_eq i_eq 
        by simp
    qed
  qed

  \<comment> \<open>Inactive components: for i notin \{iS, iX, iZ\}, the vector field is identically 
      zero (because the ODE only updates the components iS, iX and iZ).\<close>
  have inactive_maint: 
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..t} \<Longrightarrow> 
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'a and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    from i_inact 
    have i_ne: \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> \<open>i \<noteq> iZ\<close> 
      unfolding active_def 
      by auto

    have field_zero: \<open>\<And>\<tau>' v. vec_nth 
                     (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
    proof -
      fix \<tau>' :: real and v :: \<open>(real, 'a) vec\<close>
      show \<open>vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
        unfolding metabolic_field_def 
        using i_ne 
        by (simp add: fun_upd_def)
    qed

    have y_vderiv: \<open>(y has_vderiv_on 
                     (\<lambda>\<tau>. metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>))) 
                    {0..t}\<close>
      using y_sol 
      by (simp add: solves_ode_def)

    have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..t}\<close>
    proof -
      have \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on 
             (\<lambda>\<tau>. vec_nth (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) i)) 
            {0..t}\<close>
      proof -
        have step1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_vector_derivative 
              (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using y_vderiv 
          unfolding has_vderiv_on_def 
          by blast
        have step2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             (y has_derivative 
              (\<lambda>h. h *\<^sub>R metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>'))) 
               (at \<tau>' within {0..t})\<close>
          using step1 
          unfolding has_vector_derivative_def 
          by blast
        have step3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..t} \<Longrightarrow> 
             ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
              (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i)) 
               (at \<tau>' within {0..t})\<close>
        proof -
          fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..t}\<close>
          have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
            by (rule has_derivative_vec_nth)
          show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative 
                 (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i)) 
                   (at \<tau>' within {0..t})\<close>
            using has_derivative_compose[OF step2[OF \<tau>'_in] proj] by simp
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

  \<comment> \<open>Apply DI\_Frame\_Rule\_partial.\<close>
  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..t} \<Longrightarrow> 
                     lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF t_nn y_sol iv active_ord 
                                       lower_edge upper_edge inactive_maint]
    by blast

  show \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> in_safety_region (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have h0: \<open>lo iS \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> hi iS\<close>
      using main[OF \<tau>_in, of iS] .
    have h1: \<open>lo iX \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> hi iX\<close>
      using main[OF \<tau>_in, of iX] .
    have h2: \<open>lo iZ \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> hi iZ\<close>
      using main[OF \<tau>_in, of iZ] .
    show \<open>in_safety_region (y \<tau>)\<close>
      using h0 h1 h2 
      unfolding in_safety_region_def lo_def hi_def 
      by simp
  qed
qed

end  (* metabolic_safety_region_params *)

subsection \<open>Z-clearance under operational bounds\<close>

text \<open>
  The bioreactor operator maintains substrate S and biomass X 
  within known operational limits.  We do not require these 
  limits to arise from box invariance (the attempt above shows that a
  box cannot point inward on both X faces); they come from 
  the bioreactor's feed controller and dilution rate management.
  
  Given these operational bounds, we prove the engineered 
  degradation pathway clears the toxic intermediate Z 
  exponentially, from any initial Z above the alarm threshold 
  down to the target operating level.  The clearance time is 
  explicitly computable from the decay rate delta\_Z.\<close>

locale metabolic_z_clearance_params = metabolic_baseline_params +
  \<comment> \<open>Operational bounds on S and X (maintained by bioreactor control).\<close>
  fixes S_lo S_hi X_lo X_hi :: real
  assumes S_lo_pos: \<open>0 < S_lo\<close>
  assumes S_ordered: \<open>S_lo < S_hi\<close>
  assumes X_lo_pos: \<open>0 < X_lo\<close>
  assumes X_ordered: \<open>X_lo < X_hi\<close>
  \<comment> \<open>Z equilibrium target and alarm threshold.\<close>
  fixes Z_eq  Z_alarm Z_max :: real
  assumes Z_eq_pos: \<open>0 < Z_eq\<close>
  assumes Z_alarm_above_eq: \<open>Z_eq < Z_alarm\<close>
  assumes Z_max_above_alarm: \<open>Z_alarm \<le> Z_max\<close>
  \<comment> \<open>Engineering band-width constraint: the alarm zone 
      [Z\_alarm, Z\_max] is no wider than [Z\_eq, Z\_alarm].\<close>
  assumes Z_band_width: \<open>Z_max - Z_eq \<le> 2 * (Z_alarm - Z_eq)\<close>
  \<comment> \<open>Lower bound below which production strictly exceeds degradation.
      Sits below the operating point Z\_eq.  Together with Z\_max this makes
      [Z\_min, Z\_max] a forward-invariant box for the Z component.\<close>
  fixes Z_min :: real
  assumes Z_min_pos: \<open>0 < Z_min\<close>
  \<comment> \<open>Ordering w.r.t. operating point.  Derivable (from
      Z\_lower\_production\_exceeds\_degradation, equilibrium\_condition, and
      strict monotonicity of MM degradation) in \textasciitilde{}25 lines; added as
      assumption here for proof brevity.\<close>
  assumes Z_min_below_eq: \<open>Z_min \<le> Z_eq\<close>
  \<comment> \<open>Decay rate and design gap.\<close>
  fixes \<delta>_Z :: real
  assumes \<delta>_Z_pos: \<open>0 < \<delta>_Z\<close>
  \<comment> \<open>At Z\_alarm, degradation exceeds maximum possible production 
      by enough margin to guarantee decay at rate delta\_Z.\<close>
  assumes degradation_exceeds_production:
    \<open>\<delta>_Z * (Z_alarm - Z_eq) \<le> 
     k * Z_alarm / (K_Z + Z_alarm) - \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
\<comment> \<open>Equilibrium condition: at the operating point Z = Z\_eq, the engineered
      degradation pathway exceeds the worst-case production rate.  Required
      for the lower-band Lyapunov decrease (Z below the alarm threshold).\<close>
  assumes equilibrium_condition:
    \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi \<le> k * Z_eq / (K_Z + Z_eq)\<close>

  \<comment> \<open>Lower-band decay-rate compatibility.  Algebraic identity
        f(Z) - f(Z\_eq) = k*K\_Z*(Z - Z\_eq) / ((K\_Z + Z)(K\_Z + Z\_eq))
      combined with (K\_Z + Z) <= (K\_Z + Z\_alarm) on the lower band gives a
      slope beta = k*K\_Z / ((K\_Z + Z\_alarm)(K\_Z + Z\_eq)); to drive V\_Z decay at
      rate delta\_Z requires delta\_Z <= 2*beta, which cleared of denominators is:\<close>
  assumes lower_band_decay_rate:
    \<open>\<delta>_Z * (K_Z + Z_alarm) * (K_Z + Z_eq) \<le> 2 * k * K_Z\<close>
\<comment> \<open>At Z = Z\_min, minimum production (at S\_lo, X\_lo) strictly exceeds
      degradation.  This is the lower-face inward condition that drives
      Z\_lower\_bound\_invariant.\<close>
  assumes Z_lower_production_exceeds_degradation:
    \<open>k * Z_min / (K_Z + Z_min) < \<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) * X_lo\<close>
begin

text \<open>
  Production-degradation gap is non-negative at Z\_alarm.  This 
  is an immediate consequence of delta\_Z > 0 and 
  degradation\_exceeds\_production.\<close>

lemma gap_at_alarm_nn:
  \<open>0 \<le> k * Z_alarm / (K_Z + Z_alarm) 
       - \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
proof -
  have \<open>0 < \<delta>_Z * (Z_alarm - Z_eq)\<close>
    using \<delta>_Z_pos Z_alarm_above_eq by simp
  thus ?thesis 
    using degradation_exceeds_production 
    by linarith
qed


text \<open>The Lyapunov function for Z-clearance.\<close>
 
definition V_Z :: 
  \<open>(real, 'a) vec \<Rightarrow> real\<close> where
  \<open>V_Z v = (vec_nth v iZ - Z_eq)^2 / 2\<close>

lemma V_Z_has_derivative:
  fixes p :: \<open>(real, 'a) vec\<close>
  shows \<open>(V_Z has_derivative (\<lambda>w. (vec_nth p iZ - Z_eq) * vec_nth w iZ)) (at p)\<close>
proof -
  have proj: \<open>((\<lambda>v::(real,'a) vec. vec_nth v iZ)
                 has_derivative (\<lambda>w. vec_nth w iZ)) (at p)\<close>
    by (rule has_derivative_vec_nth)
  have sq: \<open>((\<lambda>z::real. (z - Z_eq)^2 / 2)
              has_derivative (\<lambda>h. (vec_nth p iZ - Z_eq) * h))
            (at (vec_nth p iZ))\<close>
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    unfolding V_Z_def
    using has_derivative_compose[OF proj sq] 
    by (simp add: comp_def)
qed

lemma V_Z_induct_step:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T u :: real
  assumes rate_bound:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         (vec_nth (y \<tau>) iZ - Z_eq) *
         (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS))
            * vec_nth (y \<tau>) iX
          - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ))
         \<le> -\<delta>_Z * V_Z (y \<tau>)\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         \<exists>DV. (V_Z has_derivative DV) (at (y \<tau>)) \<and>
              DV (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) \<le>
                 -\<delta>_Z * V_Z (y \<tau>)\<close>
proof -
  fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>
  \<comment> \<open>Applying the derivative to the field picks out the Z-component,
      giving exactly the left-hand side of rate\_bound.\<close>
  have lie: \<open>(\<lambda>w. (vec_nth (y \<tau>) iZ - Z_eq) * vec_nth w iZ)
               (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) =
              (vec_nth (y \<tau>) iZ - Z_eq) *
               (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS))
                  * vec_nth (y \<tau>) iX - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ))\<close>
    unfolding metabolic_field_def by (simp add: fun_upd_def)
  show \<open>\<exists>DV. (V_Z has_derivative DV) (at (y \<tau>)) \<and>
             DV (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) \<le> -\<delta>_Z * V_Z (y \<tau>)\<close>
    using V_Z_has_derivative[of \<open>y \<tau>\<close>] rate_bound[OF h\<tau>] lie 
    by auto
qed

lemma V_Z_nn:
  fixes v :: \<open>(real, 'a) vec\<close>
  shows \<open>0 \<le> V_Z v\<close>
  unfolding V_Z_def 
  by simp


text \<open>
  Pointwise Lyapunov decrease.  If S in [S\_lo, S\_hi] and 
  X in [X\_lo, X\_hi] and Z in [Z\_alarm, Z\_max], then the Lie 
  derivative of V\_Z is bounded by -delta\_Z * V\_Z.
  
  The proof combines three ingredients:
\begin{enumerate}
\item Production is bounded above by its value at (S\_hi, X\_hi).
\item Degradation is bounded below by its value at Z\_alarm.
\item The engineering band-width constraint gives
  (Z - Z\_eq)\textasciicircum{}2 / 2 <= (Z - Z\_eq) * (Z\_alarm - Z\_eq).
\end{enumerate}\<close>

lemma V_Z_Lie_decrease:
  fixes v :: \<open>(real, 'a) vec\<close>
  assumes S_bounds: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
  assumes X_bounds: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
  assumes Z_above_alarm: \<open>Z_alarm \<le> vec_nth v iZ\<close>
  assumes Z_below_max: \<open>vec_nth v iZ \<le> Z_max\<close>
  shows \<open>(vec_nth v iZ - Z_eq) * 
         (\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX 
          - k * vec_nth v iZ / (K_Z + vec_nth v iZ)) \<le> -\<delta>_Z * V_Z v\<close>
proof -
  define S where \<open>S = vec_nth v iS\<close>
  define X where \<open>X = vec_nth v iX\<close>
  define Z where \<open>Z = vec_nth v iZ\<close>

  have S_in: \<open>S_lo \<le> S\<close> \<open>S \<le> S_hi\<close> 
    using S_bounds 
    unfolding S_def 
    by simp_all
  have X_in: \<open>X_lo \<le> X\<close> \<open>X \<le> X_hi\<close> 
    using X_bounds 
    unfolding X_def 
    by simp_all
  have Z_in: \<open>Z_alarm \<le> Z\<close> \<open>Z \<le> Z_max\<close> 
    using Z_above_alarm Z_below_max 
    unfolding Z_def 
    by simp_all

  have S_nn: \<open>0 \<le> S\<close> using S_in(1) S_lo_pos by linarith
  have X_nn: \<open>0 \<le> X\<close> using X_in(1) X_lo_pos by linarith
  have Z_nn: \<open>0 \<le> Z\<close> using Z_in(1) Z_alarm_above_eq Z_eq_pos by linarith

  have Z_minus_eq_pos: \<open>0 < Z - Z_eq\<close>
    using Z_in(1) Z_alarm_above_eq by linarith
  have Z_minus_eq_nn: \<open>0 \<le> Z - Z_eq\<close> using Z_minus_eq_pos by linarith

  \<comment> \<open>(i) Production bound: P(S, X) <= P(S\_hi, X\_hi).\<close>
  have P_bound: 
    \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
  proof -
    have uptake_mono: 
      \<open>\<mu>_max * S / (K_S + S) \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
    proof -
      have \<open>(\<mu>_max * S / (K_S + S)) * 1 \<le> (\<mu>_max * S_hi / (K_S + S_hi)) * 1\<close>
        using monod_uptake_monotone_in_S[OF S_nn S_in(2), of 1] by simp
      thus ?thesis 
        by simp
    qed
    have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> using \<alpha>_pos by simp
    have \<alpha>_uptake_mono:
      \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
      using uptake_mono \<alpha>_nn mult_left_mono 
      by blast
    have uptake_hi_nn: \<open>0 \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
    proof -
      have \<open>0 < K_S + S_hi\<close> using K_S_plus_S_pos S_in(2) S_nn by simp
      thus ?thesis 
        using \<mu>_max_pos S_in(2) S_nn 
        by (simp add: divide_nonneg_pos)
    qed
    have \<alpha>u_hi_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
      using \<alpha>_nn uptake_hi_nn mult_sign_intros(1)
      by blast
    have step1:
      \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X\<close>
      using \<alpha>_uptake_mono X_nn mult_right_mono 
      by blast
    have step2:
      \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X \<le> 
       \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
      using \<alpha>u_hi_nn X_in(2) mult_left_mono
      by blast
    from step1 step2 
    show ?thesis 
      by linarith
  qed

  \<comment> \<open>(ii) Degradation bound: f(Z) >= f(Z\_alarm).\<close>
  have f_bound: \<open>k * Z_alarm / (K_Z + Z_alarm) \<le> k * Z / (K_Z + Z)\<close>
  proof -
    have Z_alarm_nn: \<open>0 \<le> Z_alarm\<close> 
      using Z_alarm_above_eq Z_eq_pos 
      by linarith
    show ?thesis
      using mm_degradation_monotone[OF Z_alarm_nn Z_in(1)] .
  qed

  \<comment> \<open>Production minus degradation at (S, X, Z) is bounded above 
      by production minus degradation at (S\_hi, X\_hi, Z\_alarm).\<close>
  have gap_bound: 
    \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z) \<le>
     \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi - k * Z_alarm / (K_Z + Z_alarm)\<close>
    using P_bound f_bound 
    by linarith

  \<comment> \<open>The design gap is at most -delta\_Z * (Z\_alarm - Z\_eq).\<close>
  have gap_at_Z_bound:
    \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z) \<le>
      -(\<delta>_Z * (Z_alarm - Z_eq))\<close>
    using gap_bound degradation_exceeds_production 
    by linarith

  \<comment> \<open>Multiply by (Z - Z\_eq) >= 0.\<close>
  have lhs_bound:
    \<open>(Z - Z_eq) * (\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z)) \<le>
     (Z - Z_eq) * (-(\<delta>_Z * (Z_alarm - Z_eq)))\<close>
    using gap_at_Z_bound Z_minus_eq_nn mult_left_mono  
    by blast

  \<comment> \<open>(iii) Band-width: (Z - Z\_eq)\textasciicircum{}2/2 <= (Z - Z\_eq) * (Z\_alarm - Z\_eq).\<close>
  have bandwidth_bound:
    \<open>(Z - Z_eq)^2 / 2 \<le> (Z - Z_eq) * (Z_alarm - Z_eq)\<close>
  proof -
    have Z_diff_bound: \<open>Z - Z_eq \<le> 2 * (Z_alarm - Z_eq)\<close>
    proof -
      have \<open>Z - Z_eq \<le> Z_max - Z_eq\<close> 
        using Z_in(2) 
        by linarith
      thus ?thesis 
        using Z_band_width 
        by linarith
    qed
    have \<open>(Z - Z_eq) * (Z - Z_eq) \<le> (Z - Z_eq) * (2 * (Z_alarm - Z_eq))\<close>
      using Z_diff_bound Z_minus_eq_nn 
      by (simp add: mult_left_mono)
    hence \<open>(Z - Z_eq)^2 \<le> 2 * ((Z - Z_eq) * (Z_alarm - Z_eq))\<close>
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis 
      by simp
  qed

  \<comment> \<open>Combine: Lie derivative <= -delta\_Z * V\_Z.\<close>
  have scale_bandwidth:
    \<open>\<delta>_Z * ((Z - Z_eq)^2 / 2) \<le> \<delta>_Z * ((Z - Z_eq) * (Z_alarm - Z_eq))\<close>
  proof -
    have \<delta>_Z_nn: \<open>0 \<le> \<delta>_Z\<close> 
      using \<delta>_Z_pos 
      by simp
    show ?thesis
      using bandwidth_bound \<delta>_Z_nn mult_left_mono  
      by blast
  qed

  have \<open>(Z - Z_eq) * (\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z)) \<le>
         -(\<delta>_Z * ((Z - Z_eq) * (Z_alarm - Z_eq)))\<close>
  proof -
    have \<open>(Z - Z_eq) * (-(\<delta>_Z * (Z_alarm - Z_eq))) =
           -(\<delta>_Z * ((Z - Z_eq) * (Z_alarm - Z_eq)))\<close>
      by (simp add: algebra_simps)
    thus ?thesis 
      using lhs_bound 
      by linarith
  qed
  moreover have \<open>-(\<delta>_Z * ((Z - Z_eq) * (Z_alarm - Z_eq))) \<le> 
                 -(\<delta>_Z * ((Z - Z_eq)^2 / 2))\<close>
    using scale_bandwidth 
    by linarith
  ultimately have main_bound:
    \<open>(Z - Z_eq) * (\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z)) \<le>
      -(\<delta>_Z * ((Z - Z_eq)^2 / 2))\<close>
    by linarith

  have V_Z_eq: \<open>V_Z v = (Z - Z_eq)^2 / 2\<close>
    unfolding V_Z_def Z_def by simp

  have \<open>-(\<delta>_Z * ((Z - Z_eq)^2 / 2)) = -\<delta>_Z * V_Z v\<close>
    unfolding V_Z_eq by simp

  with main_bound show ?thesis
    unfolding S_def X_def Z_def 
    by linarith
qed


text \<open>
  Exponential decay of V\_Z while the trajectory stays in the 
  alarm zone.  This is the main REACH\_lyapunov application.\<close>

lemma V_Z_exponential_decay:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T :: real
  assumes y_sol: \<open>(y solves_ode 
                   (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z)) 
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_val: \<open>0 < u\<close>
  assumes state_in_alarm_zone:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
         Z_alarm \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  shows \<open>V_Z (y T) \<le> V_Z (y 0) * exp (-\<delta>_Z * T)\<close>
proof -
  \<comment> \<open>Rate bound from pointwise Lyapunov estimate.\<close>
  have rate_bound: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 
         (vec_nth (y \<tau>) iZ - Z_eq) * 
         (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS)) 
            * vec_nth (y \<tau>) iX 
          - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ)) \<le>
          -\<delta>_Z * V_Z (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    from state_in_alarm_zone[OF \<tau>_in] have 
      \<open>S_lo \<le> vec_nth (y \<tau>) iS\<close> \<open>vec_nth (y \<tau>) iS \<le> S_hi\<close>
      \<open>X_lo \<le> vec_nth (y \<tau>) iX\<close> \<open>vec_nth (y \<tau>) iX \<le> X_hi\<close>
      \<open>Z_alarm \<le> vec_nth (y \<tau>) iZ\<close> \<open>vec_nth (y \<tau>) iZ \<le> Z_max\<close>
      by auto
    show \<open>(vec_nth (y \<tau>) iZ - Z_eq) * 
          (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS)) 
             * vec_nth (y \<tau>) iX 
           - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ)) \<le> 
           -\<delta>_Z * V_Z (y \<tau>)\<close>
      using V_Z_Lie_decrease[OF \<open>S_lo \<le> _\<close> \<open>_ \<le> S_hi\<close> \<open>X_lo \<le> _\<close> \<open>_ \<le> X_hi\<close>
                                \<open>Z_alarm \<le> _\<close> \<open>_ \<le> Z_max\<close>] .
  qed

 \<comment> \<open>Pointwise obligation: V\_Z is differentiable at each trajectory point and
      its Lie derivative along the metabolic field is at most -delta\_Z * V\_Z.
      REACH\_lyapunov now derives the composed time-derivative itself, from
      y\_sol - the old V\_Z\_vderiv block is no longer needed.\<close>
  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
                     \<exists>DV. (V_Z has_derivative DV) (at (y \<tau>)) \<and>
                          DV (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) \<le> 
                          -\<delta>_Z * V_Z (y \<tau>)\<close>
   using V_Z_induct_step[OF rate_bound] .
  show ?thesis
    using REACH_lyapunov[where V = V_Z and \<delta> = \<delta>_Z,
                         OF y_sol T_nn induct_step]
    by simp
qed


text \<open>
  Clearance time corollary.  If V\_Z starts at some level 
  V\_0 and the trajectory stays in the alarm zone for time T, 
  then V\_Z(T) <= L for any level L >= V\_0 * exp(-delta\_Z * T).
  
  The bio-engineer reads this as: "To get Z within epsilon of Z\_eq, 
  wait T >= ln(V\_0 / (epsilon\textasciicircum{}2/2)) / delta\_Z hours."\<close>

lemma V_Z_reaches_sublevel:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T L :: real
  assumes y_sol: \<open>(y solves_ode 
                   (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z)) 
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_val: \<open>0 < u\<close>
  assumes state_in_alarm_zone:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
         Z_alarm \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  assumes L_reached: \<open>V_Z (y 0) * exp (-\<delta>_Z * T) \<le> L\<close>
  shows \<open>V_Z (y T) \<le> L\<close>
proof -
  have \<open>V_Z (y T) \<le> V_Z (y 0) * exp (-\<delta>_Z * T)\<close>
    using V_Z_exponential_decay[OF y_sol T_nn u_val state_in_alarm_zone] .
  also have \<open>... \<le> L\<close>
    using L_reached .
  finally show ?thesis .
qed

text \<open>
   BIOREACTOR SAFETY THEOREM (inside metabolic\_z\_clearance\_params)

   This theorem is the paper-facing statement that separates the
   bioreactor controller's responsibility (maintaining S and X)
   from the engineered pathway's guarantee (clearing Z).
\<close>


text \<open>
  Bioreactor safety theorem.  This is the headline result of the 
  metabolic case study, stated in terms a bio-engineer would use.
  
  The theorem separates two concerns:
\begin{enumerate}
\item Controller guarantees: the bioreactor operator maintains
  substrate S in [S\_lo, S\_hi] via feed pump control, and
  biomass X in [X\_lo, X\_hi] via dilution rate management.
  These are standard operating practices in modern bioreactors
  and require routine instrumentation (flow meters, OD sensors).
\item Pathway guarantee: the engineered enzymatic degradation
  pathway clears the toxic intermediate Z exponentially,
  from any initial level in the alarm zone [Z\_alarm, Z\_max]
  toward the designed operating point Z\_eq.
\end{enumerate}
  The bio-engineer controls (1); the theorem formally verifies (2).
  This separation mirrors how real bioprocess engineering works: 
  the operator manages macroscopic variables (feed, dilution); 
  the genetic design determines internal metabolic behavior.
  
  The formal guarantee covers ALL trajectories consistent with 
  the controller bounds, an uncountable family of scenarios that 
  no finite simulation campaign can exhaust.  This is the value 
  of formal verification over simulation.\<close>

theorem bioreactor_safety:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T L :: real
  fixes u_feed :: real
  \<comment> \<open>The trajectory solves the metabolic ODE with some feed rate.\<close>
  assumes y_sol: \<open>(y solves_ode 
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z)) 
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  \<comment> \<open>CONTROLLER GUARANTEES: the bioreactor operator maintains 
      S and X within operational bounds throughout [0, T].\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  \<comment> \<open>Z is in the alarm zone throughout [0, T].\<close>
  assumes Z_in_alarm_zone:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> Z_alarm \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  \<comment> \<open>PATHWAY GUARANTEE: Z clears to sublevel L within time T.\<close>
  assumes sufficient_time: \<open>V_Z (y 0) * exp (-\<delta>_Z * T) \<le> L\<close>
  shows \<open>V_Z (y T) \<le> L\<close>
proof -
  have state_combined: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> 
       S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
       X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
       Z_alarm \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using substrate_controlled biomass_controlled Z_in_alarm_zone 
    by auto
  show ?thesis
    using V_Z_reaches_sublevel[OF y_sol T_nn u_feed_pos 
                                  state_combined sufficient_time] .
qed

text \<open>
  Lower-band Lyapunov decrease.  For Z in [Z\_eq, Z\_alarm] with S, X within
  controller bounds, the Lie derivative of V\_Z is bounded above by -delta\_Z * V\_Z.

  The proof mirrors V\_Z\_Lie\_decrease but replaces ingredient (ii)
  (degradation lower bound at Z\_alarm) with a slope bound:
    f(Z) - f(Z\_eq) >= beta*(Z - Z\_eq)
  where beta = k*K\_Z / ((K\_Z + Z\_alarm)*(K\_Z + Z\_eq)) comes from the algebraic
  identity
    f(Z) - f(Z\_eq) = k*K\_Z*(Z - Z\_eq) / ((K\_Z + Z)*(K\_Z + Z\_eq))
  and the bound (K\_Z + Z) <= (K\_Z + Z\_alarm) for Z <= Z\_alarm.

  The equilibrium\_condition gives P\_max <= f(Z\_eq), and lower\_band\_decay\_rate
  gives delta\_Z <= 2*beta.\<close>

lemma V_Z_Lie_decrease_lower:
  fixes v :: \<open>(real, 'a) vec\<close>
  assumes S_bounds: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
  assumes X_bounds: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
  assumes Z_above_eq:    \<open>Z_eq \<le> vec_nth v iZ\<close>
  assumes Z_below_alarm: \<open>vec_nth v iZ \<le> Z_alarm\<close>
  shows \<open>(vec_nth v iZ - Z_eq) *
         (\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX
          - k * vec_nth v iZ / (K_Z + vec_nth v iZ)) \<le>
          -\<delta>_Z * V_Z v\<close>
proof -
  define S where \<open>S = vec_nth v iS\<close>
  define X where \<open>X = vec_nth v iX\<close>
  define Z where \<open>Z = vec_nth v iZ\<close>

  have S_in: \<open>S_lo \<le> S\<close> \<open>S \<le> S_hi\<close> 
    using S_bounds 
    unfolding S_def 
    by simp_all
  have X_in: \<open>X_lo \<le> X\<close> \<open>X \<le> X_hi\<close> 
    using X_bounds 
    unfolding X_def 
    by simp_all
  have Z_in: \<open>Z_eq \<le> Z\<close> \<open>Z \<le> Z_alarm\<close>
    using Z_above_eq Z_below_alarm 
    unfolding Z_def 
    by simp_all

  have S_nn: \<open>0 \<le> S\<close> using S_in(1) S_lo_pos by linarith
  have X_nn: \<open>0 \<le> X\<close> using X_in(1) X_lo_pos by linarith
  have Z_nn: \<open>0 \<le> Z\<close> using Z_in(1) Z_eq_pos by linarith
  have Z_minus_eq_nn: \<open>0 \<le> Z - Z_eq\<close> using Z_in(1) by linarith

  \<comment> \<open>(i) Production bound: P(S, X) <= P(S\_hi, X\_hi).  (Identical to the
      upper-band proof.)\<close>
  have P_bound:
    \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
  proof -
    have uptake_mono: \<open>\<mu>_max * S / (K_S + S) \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
    proof -
      have \<open>(\<mu>_max * S / (K_S + S)) * 1 \<le> (\<mu>_max * S_hi / (K_S + S_hi)) * 1\<close>
        using monod_uptake_monotone_in_S[OF S_nn S_in(2), of 1] 
        by simp
      thus ?thesis 
        by simp
    qed
    have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> 
      using \<alpha>_pos 
      by simp
    have \<alpha>_uptake_mono:
      \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
      using uptake_mono \<alpha>_nn mult_left_mono 
      by blast
    have uptake_hi_nn: \<open>0 \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
    proof -
      have \<open>0 < K_S + S_hi\<close> 
        using K_S_plus_S_pos S_in(2) S_nn 
        by simp
      thus ?thesis 
        using \<mu>_max_pos S_in(2) S_nn 
        by (simp add: divide_nonneg_pos)
    qed
    have \<alpha>u_hi_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
      using \<alpha>_nn uptake_hi_nn mult_sign_intros(1) 
      by blast
    have step1:
      \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X\<close>
      using \<alpha>_uptake_mono X_nn mult_right_mono 
      by blast
    have step2:
      \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
      using \<alpha>u_hi_nn X_in(2) mult_left_mono 
      by blast
    from step1 step2 
    show ?thesis 
      by linarith
  qed

  \<comment> \<open>Denominator positivity.\<close>
  have K_Z_Z_pos: \<open>0 < K_Z + Z\<close>       
    using Z_nn K_Z_pos 
    by simp
  have K_Z_Z_eq_pos: \<open>0 < K_Z + Z_eq\<close>    
    using Z_eq_pos K_Z_pos 
    by simp
  have K_Z_Z_alarm_pos: \<open>0 < K_Z + Z_alarm\<close>
    using Z_alarm_above_eq Z_eq_pos K_Z_pos 
    by linarith

  \<comment> \<open>(ii.a) Algebraic identity for f(Z) - f(Z\_eq).\<close>
  have f_identity:
    \<open>k * Z / (K_Z + Z) - k * Z_eq / (K_Z + Z_eq) =
     k * K_Z * (Z - Z_eq) / ((K_Z + Z) * (K_Z + Z_eq))\<close>
  proof -
    have \<open>k * Z / (K_Z + Z) - k * Z_eq / (K_Z + Z_eq)
          = (k * Z * (K_Z + Z_eq) - k * Z_eq * (K_Z + Z))
            / ((K_Z + Z) * (K_Z + Z_eq))\<close>
      using K_Z_Z_pos K_Z_Z_eq_pos 
      by (simp add: field_simps)
    also have \<open>... = k * K_Z * (Z - Z_eq) / ((K_Z + Z) * (K_Z + Z_eq))\<close>
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  \<comment> \<open>(ii.b) Denominator bound on the lower band.\<close>
  have denom_bound: \<open>(K_Z + Z) * (K_Z + Z_eq) \<le> (K_Z + Z_alarm) * (K_Z + Z_eq)\<close>
    using Z_in(2) K_Z_Z_eq_pos 
    by (simp add: mult_right_mono)

  \<comment> \<open>(ii.c) Slope bound: f(Z) - f(Z\_eq) >= beta*(Z - Z\_eq).\<close>
  have num_nn: \<open>0 \<le> k * K_Z * (Z - Z_eq)\<close>
    using k_pos K_Z_pos Z_minus_eq_nn 
    by simp
  have den_pos1: \<open>0 < (K_Z + Z) * (K_Z + Z_eq)\<close>
    using K_Z_Z_pos K_Z_Z_eq_pos 
    by simp
  have den_pos2: \<open>0 < (K_Z + Z_alarm) * (K_Z + Z_eq)\<close>
    using K_Z_Z_alarm_pos K_Z_Z_eq_pos 
    by simp

  have slope_bound:
    \<open>k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq))
     \<le> k * Z / (K_Z + Z) - k * Z_eq / (K_Z + Z_eq)\<close>
  proof -
    have \<open>k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq))
          \<le> k * K_Z * (Z - Z_eq) / ((K_Z + Z) * (K_Z + Z_eq))\<close>
    proof (rule frac_le)
      show \<open>0 \<le> k * K_Z * (Z - Z_eq)\<close> using num_nn .
      show \<open>k * K_Z * (Z - Z_eq) \<le> k * K_Z * (Z - Z_eq)\<close> by simp
      show \<open>0 < (K_Z + Z) * (K_Z + Z_eq)\<close> using den_pos1 .
      show \<open>(K_Z + Z) * (K_Z + Z_eq) \<le> (K_Z + Z_alarm) * (K_Z + Z_eq)\<close>
        using denom_bound .
    qed
    thus ?thesis 
      using f_identity 
      by simp
  qed

  \<comment> \<open>Equilibrium condition: P\_max <= f(Z\_eq).\<close>
  have eq_cond:
    \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi \<le> k * Z_eq / (K_Z + Z_eq)\<close>
    using equilibrium_condition .

  \<comment> \<open>Combine: P - f(Z) <= -beta*(Z - Z\_eq).\<close>
  have P_minus_f_bound:
    \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z) \<le>
     - (k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq)))\<close>
  proof -
    have a:
      \<open>\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z) \<le>
       \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi - k * Z / (K_Z + Z)\<close>
      using P_bound 
      by linarith
    have b:
      \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi - k * Z / (K_Z + Z)
       \<le> k * Z_eq / (K_Z + Z_eq) - k * Z / (K_Z + Z)\<close>
      using eq_cond by linarith
    have c:
      \<open>k * Z_eq / (K_Z + Z_eq) - k * Z / (K_Z + Z)
       = - (k * Z / (K_Z + Z) - k * Z_eq / (K_Z + Z_eq))\<close>
      by simp
    have d:
      \<open>- (k * Z / (K_Z + Z) - k * Z_eq / (K_Z + Z_eq)) \<le>
       - (k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq)))\<close>
      using slope_bound 
      by linarith
    from a b c d 
    show ?thesis 
      by linarith
  qed

  \<comment> \<open>Multiply by (Z - Z\_eq) >= 0.\<close>
  have lhs_bound:
    \<open>(Z - Z_eq) * (\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z)) \<le>
      (Z - Z_eq) * (- (k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq))))\<close>
    using P_minus_f_bound Z_minus_eq_nn mult_left_mono 
    by blast

  have rhs_eq:
    \<open>(Z - Z_eq) * (- (k * K_Z * (Z - Z_eq) / ((K_Z + Z_alarm) * (K_Z + Z_eq)))) =
     - (k * K_Z * (Z - Z_eq)^2 / ((K_Z + Z_alarm) * (K_Z + Z_eq)))\<close>
    by (simp add: power2_eq_square algebra_simps)

  \<comment> \<open>(iii) Convert slope rate beta = k*K\_Z / ((K\_Z+Z\_alarm)*(K\_Z+Z\_eq))
      into Lyapunov rate via delta\_Z <= 2*beta.\<close>
  have rate_bound:
    \<open>\<delta>_Z * (Z - Z_eq)^2 / 2 \<le>
     k * K_Z * (Z - Z_eq)^2 / ((K_Z + Z_alarm) * (K_Z + Z_eq))\<close>
  proof -
    have sq_nn: \<open>0 \<le> (Z - Z_eq)^2\<close> by simp
    have step_assoc: \<open>\<delta>_Z * ((K_Z + Z_alarm) * (K_Z + Z_eq)) \<le> 2 * (k * K_Z)\<close>
      using lower_band_decay_rate by (simp add: mult.assoc)
    have step_div: \<open>\<delta>_Z \<le> 2 * (k * K_Z) / ((K_Z + Z_alarm) * (K_Z + Z_eq))\<close>
      using step_assoc den_pos2 by (simp add: pos_le_divide_eq)
    have step_half: \<open>\<delta>_Z / 2 \<le> k * K_Z / ((K_Z + Z_alarm) * (K_Z + Z_eq))\<close>
      using step_div 
      by linarith
    have \<open>(\<delta>_Z / 2) * (Z - Z_eq)^2 \<le>
          (k * K_Z / ((K_Z + Z_alarm) * (K_Z + Z_eq))) * (Z - Z_eq)^2\<close>
      using step_half sq_nn mult_right_mono 
      by blast
    thus ?thesis 
      by (simp add: field_simps)
  qed

  have V_Z_eq: \<open>V_Z v = (Z - Z_eq)^2 / 2\<close>
    unfolding V_Z_def Z_def 
    by simp

  \<comment> \<open>Combine everything.\<close>
  have \<open>(Z - Z_eq) * (\<alpha> * (\<mu>_max * S / (K_S + S)) * X - k * Z / (K_Z + Z)) \<le>
         - (k * K_Z * (Z - Z_eq)^2 / ((K_Z + Z_alarm) * (K_Z + Z_eq)))\<close>
    using lhs_bound rhs_eq 
    by linarith
  also have \<open>- (k * K_Z * (Z - Z_eq)^2 / ((K_Z + Z_alarm) * (K_Z + Z_eq))) \<le>
              - (\<delta>_Z * (Z - Z_eq)^2 / 2)\<close>
    using rate_bound 
    by linarith
  also have \<open>- (\<delta>_Z * (Z - Z_eq)^2 / 2) = -\<delta>_Z * V_Z v\<close>
    unfolding V_Z_eq 
    by simp
  finally show ?thesis
    unfolding S_def X_def Z_def 
    by simp
qed


text \<open>
  Combined Lyapunov decrease for the full Z range [Z\_eq, Z\_max].
  Case-split on whether Z >= Z\_alarm (upper band, V\_Z\_Lie\_decrease) or
  Z <= Z\_alarm (lower band, V\_Z\_Lie\_decrease\_lower).\<close>

lemma V_Z_Lie_decrease_full:
  fixes v :: \<open>(real, 'a) vec\<close>
  assumes S_bounds: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
  assumes X_bounds: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
  assumes Z_above_eq:  \<open>Z_eq \<le> vec_nth v iZ\<close>
  assumes Z_below_max: \<open>vec_nth v iZ \<le> Z_max\<close>
  shows \<open>(vec_nth v iZ - Z_eq) *
         (\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX
          - k * vec_nth v iZ / (K_Z + vec_nth v iZ)) \<le>
          -\<delta>_Z * V_Z v\<close>
proof (cases \<open>Z_alarm \<le> vec_nth v iZ\<close>)
  case True
  show ?thesis
    using V_Z_Lie_decrease[OF S_bounds X_bounds True Z_below_max] .
next
  case False
  hence \<open>vec_nth v iZ \<le> Z_alarm\<close> by linarith
  show ?thesis
    using V_Z_Lie_decrease_lower[OF S_bounds X_bounds Z_above_eq \<open>vec_nth v iZ \<le> Z_alarm\<close>]
    by blast
qed


text \<open>
  Exponential decay of V\_Z over the full Z range [Z\_eq, Z\_max].

  This is the rigorous statement of the bound shown in the metabolic
  Z-clearance figure: |Z(t) - Z\_eq| <= |Z(0) - Z\_eq| * exp(-delta\_Z*t/2),
  which is the envelope plotted across BOTH Phase 1 (alarm) and Phase 2
  (safe) without case-splitting on the trajectory.\<close>

lemma V_Z_exponential_decay_full:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_val: \<open>0 < u\<close>
  assumes state_in_full_band:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
         Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  shows \<open>V_Z (y T) \<le> V_Z (y 0) * exp (-\<delta>_Z * T)\<close>
proof -
  \<comment> \<open>Pointwise rate bound - now over the FULL band [Z\_eq, Z\_max].\<close>
  have rate_bound:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         (vec_nth (y \<tau>) iZ - Z_eq) *
         (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS))
            * vec_nth (y \<tau>) iX
          - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ)) \<le>
          -\<delta>_Z * V_Z (y \<tau>)\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    from state_in_full_band[OF \<tau>_in] have
      \<open>S_lo \<le> vec_nth (y \<tau>) iS\<close> \<open>vec_nth (y \<tau>) iS \<le> S_hi\<close>
      \<open>X_lo \<le> vec_nth (y \<tau>) iX\<close> \<open>vec_nth (y \<tau>) iX \<le> X_hi\<close>
      \<open>Z_eq \<le> vec_nth (y \<tau>) iZ\<close> \<open>vec_nth (y \<tau>) iZ \<le> Z_max\<close>
      by auto
    show \<open>(vec_nth (y \<tau>) iZ - Z_eq) *
          (\<alpha> * (\<mu>_max * vec_nth (y \<tau>) iS / (K_S + vec_nth (y \<tau>) iS))
             * vec_nth (y \<tau>) iX
           - k * vec_nth (y \<tau>) iZ / (K_Z + vec_nth (y \<tau>) iZ)) \<le>
           -\<delta>_Z * V_Z (y \<tau>)\<close>
      using V_Z_Lie_decrease V_Z_Lie_decrease_lower 
             \<open>S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and> X_lo \<le> vec_nth (y \<tau>) iX \<and> 
              vec_nth (y \<tau>) iX \<le> X_hi \<and> Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close> 
      by fastforce
  qed

  \<comment> \<open>Pointwise obligation: V\_Z is differentiable at each trajectory point and
      its Lie derivative along the metabolic field is at most -delta\_Z * V\_Z.
      REACH\_lyapunov now derives the composed time-derivative itself, from
      y\_sol - the old V\_Z\_vderiv block is no longer needed.\<close>
  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
                     \<exists>DV. (V_Z has_derivative DV) (at (y \<tau>)) \<and>
                          DV (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) \<le> 
                          -\<delta>_Z * V_Z (y \<tau>)\<close>
   using V_Z_induct_step[OF rate_bound] .

  show ?thesis
    using REACH_lyapunov[where V = V_Z and \<delta> = \<delta>_Z,
                         OF y_sol T_nn induct_step]
    by simp
qed


text \<open>Full-band corollary: V\_Z reaches any prescribed sublevel L within
  time T provided the design budget is met.\<close>

lemma V_Z_reaches_sublevel_full:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T L :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_val: \<open>0 < u\<close>
  assumes state_in_full_band:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
         Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  assumes L_reached: \<open>V_Z (y 0) * exp (-\<delta>_Z * T) \<le> L\<close>
  shows \<open>V_Z (y T) \<le> L\<close>
proof -
  have \<open>V_Z (y T) \<le> V_Z (y 0) * exp (-\<delta>_Z * T)\<close>
    using V_Z_exponential_decay_full[OF y_sol T_nn u_val state_in_full_band] .
  also have \<open>... \<le> L\<close> using L_reached .
  finally show ?thesis .
qed


text \<open>
  Full-band bioreactor safety.  Mirrors `bioreactor\_safety` but admits
  trajectories that pass through both the alarm zone and the safe zone
  -- the single exponential envelope from the figure.\<close>

theorem bioreactor_safety_full:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T L :: real
  fixes u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z_in_full_band:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
  assumes sufficient_time: \<open>V_Z (y 0) * exp (-\<delta>_Z * T) \<le> L\<close>
  shows \<open>V_Z (y T) \<le> L\<close>
proof -
  have state_combined: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
       S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
       X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
       Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using substrate_controlled biomass_controlled Z_in_full_band by auto
  show ?thesis
    using V_Z_reaches_sublevel_full[OF y_sol T_nn u_feed_pos
                                       state_combined sufficient_time] .
qed

text \<open>
   BIOREACTOR SAFETY -- Unconditional formulation.

   Adds three results to `metabolic\_z\_clearance\_params` that together upgrade
   `bioreactor\_safety\_full` from a conditional theorem (assuming
   `Z\_in\_full\_band`) to an unconditional one for the upper bound, with the
   Z >= Z\_eq part isolated as a "controller-supplied invariant for the safe
   phase" -- i.e., explicitly conditional and honest.

   Three new results:
\begin{enumerate}
\item `Z\_upper\_bound\_invariant` -- forward-invariance of Z <= Z\_max
  (using DI\_Frame\_Rule\_partial with active = \{iZ\}, lo iZ = 0).
\item `Z\_exits\_alarm\_zone`     -- Z drops below Z\_alarm by T\_clear
  (using V\_Z\_exponential\_decay\_full + arithmetic on T\_clear).
\item `bioreactor\_safety\_unconditional` -- composes (1) and (2).
\end{enumerate}

   Piece C (Z >= Z\_eq forward-invariance) is provably INCOMPATIBLE with
   `equilibrium\_condition`:
       equilibrium\_condition: P\_max <= D(Z\_eq)
   means at Z = Z\_eq the field points DOWNWARD, i.e., outward relative to
   \{Z >= Z\_eq\}.  Hence Z\_above\_eq\_post\_clearance is left as a controller-
   supplied hypothesis in the unconditional theorem.
\<close>


subsubsection \<open>Piece A: forward invariance of Z <= Z\_max\<close>

text \<open>
  Upper-bound forward-invariance for Z.  Uses `DI\_Frame\_Rule\_partial`
  with active = \{iZ\}, lo iZ = 0, hi iZ = Z\_max.  At the lower face Z = 0:
  the field reduces to P(S, X) > 0 (production with S, X strictly
  positive from the controllers).  At the upper face Z = Z\_max:
  production is bounded above by P\_max, and by `degradation\_exceeds\_production`
  combined with monotonicity of MM degradation, D(Z\_max) > P\_max strictly.

  We add `Z0\_nn` (Z(0) >= 0) as a natural biological assumption.  In the
  unconditional theorem below this is derived from `Z0\_in\_alarm`.\<close>

lemma Z_upper_bound_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z0_nn:        \<open>0 \<le> vec_nth (y 0) iZ\<close>
  assumes Z0_below_max: \<open>vec_nth (y 0) iZ \<le> Z_max\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
proof -
  define lo where
    \<open>lo = (\<lambda>i::'a.
      if i = iS then S_lo
      else if i = iX then X_lo
      else if i = iZ then (0::real)
      else vec_nth (y 0) i)\<close>
  define hi where
    \<open>hi = (\<lambda>i::'a.
      if i = iS then S_hi
      else if i = iX then X_hi
      else if i = iZ then Z_max
      else vec_nth (y 0) i)\<close>
  define active :: \<open>'a set\<close> where \<open>active = {iZ}\<close>

  have lo_S: \<open>lo iS = S_lo\<close> unfolding lo_def by simp
  have lo_X: \<open>lo iX = X_lo\<close> unfolding lo_def by simp
  have lo_Z: \<open>lo iZ = 0\<close>    unfolding lo_def by simp
  have hi_S: \<open>hi iS = S_hi\<close> unfolding hi_def by simp
  have hi_X: \<open>hi iX = X_hi\<close> unfolding hi_def by simp
  have hi_Z: \<open>hi iZ = Z_max\<close> unfolding hi_def by simp

  have T_in: \<open>0 \<in> {0..T}\<close> using T_nn by simp

  \<comment> \<open>Initial-value condition.\<close>
  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'a
    consider (S) \<open>i = iS\<close> | (X) \<open>i = iX\<close> | (Z) \<open>i = iZ\<close>
      | (other) \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> \<open>i \<noteq> iZ\<close>
      by blast
    thus \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof cases
      case S
      thus ?thesis
        using substrate_controlled[OF T_in] lo_S hi_S 
        by simp
    next
      case X
      thus ?thesis
        using biomass_controlled[OF T_in] lo_X hi_X 
        by simp
    next
      case Z
      thus ?thesis using Z0_nn Z0_below_max lo_Z hi_Z 
        by simp
    next
      case other
      thus ?thesis unfolding lo_def hi_def 
        by simp
    qed
  qed

  \<comment> \<open>The single active component has lo < hi (Z\_max > 0).\<close>
  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'a
    assume \<open>i \<in> active\<close>
    hence i_2: \<open>i = iZ\<close> unfolding active_def 
      by simp
    have \<open>0 < Z_max\<close>
      using Z_eq_pos Z_alarm_above_eq Z_max_above_alarm 
      by linarith
    thus \<open>lo i < hi i\<close> using i_2 lo_Z hi_Z 
      by simp
  qed

  \<comment> \<open>Lower face Z = 0: alpha * (mu\_max * S / (K\_S + S)) * X > 0.\<close>
  have lower_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
            (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
            vec_nth v i = lo i \<Longrightarrow>
            0 < vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    assume v_box: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>

    from i_act have i_2: \<open>i = iZ\<close> 
      unfolding active_def 
      by simp
    have Z_eq_zero: \<open>vec_nth v iZ = 0\<close> 
      using eq_lo i_2 lo_Z 
      by simp

    have S_pos: \<open>0 < vec_nth v iS\<close>
      using v_box[of iS] lo_S S_lo_pos 
      by linarith
    have X_pos: \<open>0 < vec_nth v iX\<close>
      using v_box[of iX] lo_X X_lo_pos 
      by linarith
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> 
      using S_pos 
      by simp

    have field_eq:
      \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ =
       \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
      unfolding metabolic_field_def 
      using Z_eq_zero
      by (simp add: fun_upd_def)

    have uptake_pos: \<open>0 < \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
    proof -
      have \<open>0 < K_S + vec_nth v iS\<close> using K_S_plus_S_pos S_nn by simp
      thus ?thesis 
        using \<mu>_max_pos S_pos 
        by simp
    qed

    have \<open>0 < \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
      using \<alpha>_pos uptake_pos X_pos
      by (meson mult_sign_intros(5))
    thus \<open>0 < vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
      using field_eq i_2 
      by simp
  qed

  \<comment> \<open>Upper face Z = Z\_max: production bounded by P\_max, degradation
      monotone in Z, gap strict by degradation\_exceeds\_production.\<close>
  have upper_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
            (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
            vec_nth v i = hi i \<Longrightarrow>
            vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    assume v_box: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>

    from i_act have i_2: \<open>i = iZ\<close> 
      unfolding active_def 
      by simp
    have Z_at_max: \<open>vec_nth v iZ = Z_max\<close> 
      using eq_hi i_2 hi_Z 
      by simp

    have S_in: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
      using v_box[of iS] lo_S hi_S 
      by simp_all
    have X_in: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
      using v_box[of iX] lo_X hi_X 
      by simp_all
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> 
      using S_in(1) S_lo_pos 
      by linarith
    have X_nn: \<open>0 \<le> vec_nth v iX\<close> 
      using X_in(1) X_lo_pos 
      by linarith

    have field_eq:
      \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ =
       \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX
       - k * Z_max / (K_Z + Z_max)\<close>
      unfolding metabolic_field_def 
      using Z_at_max
      by (simp add: fun_upd_def)

    \<comment> \<open>P(S,X) <= P\_max.\<close>
    have prod_bound:
      \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
        \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
    proof -
      have uptake_mono:
        \<open>\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS) \<le>
          \<mu>_max * S_hi / (K_S + S_hi)\<close>
      proof -
        have \<open>(\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1 \<le>
               (\<mu>_max * S_hi / (K_S + S_hi)) * 1\<close>
          using monod_uptake_monotone_in_S[OF S_nn S_in(2), of 1] 
          by simp
        thus ?thesis 
          by simp
      qed
      have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> using \<alpha>_pos by simp
      have \<alpha>_up_mono:
        \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) \<le>
          \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
        using uptake_mono \<alpha>_nn mult_left_mono 
        by blast
      have up_hi_nn: \<open>0 \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
      proof -
        have \<open>0 < K_S + S_hi\<close> 
          using K_S_plus_S_pos S_in(2) S_nn 
          by simp
        thus ?thesis 
          using \<mu>_max_pos S_in(2) S_nn 
          by (simp add: divide_nonneg_pos)
      qed
      have \<alpha>u_hi_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
        using \<alpha>_nn up_hi_nn mult_sign_intros(1) 
        by blast
      have step1:
        \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * vec_nth v iX\<close>
        using \<alpha>_up_mono X_nn mult_right_mono 
        by blast
      have step2:
        \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
        using \<alpha>u_hi_nn X_in(2) mult_left_mono 
        by blast
      from step1 step2 
      show ?thesis 
        by linarith
    qed

    \<comment> \<open>D(Z\_max) >= D(Z\_alarm) by MM monotonicity.\<close>
    have deg_mono: \<open>k * Z_alarm / (K_Z + Z_alarm) \<le> k * Z_max / (K_Z + Z_max)\<close>
    proof -
      have Z_alarm_nn: \<open>0 \<le> Z_alarm\<close>
        using Z_alarm_above_eq Z_eq_pos 
        by linarith
      show ?thesis
        using mm_degradation_monotone[OF Z_alarm_nn Z_max_above_alarm] .
    qed

    \<comment> \<open>Gap strict: D(Z\_max) - P\_max > 0.\<close>
    have gap_pos:
      \<open>0 < k * Z_max / (K_Z + Z_max) - \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
    proof -
      have \<open>0 < \<delta>_Z * (Z_alarm - Z_eq)\<close>
        using \<delta>_Z_pos Z_alarm_above_eq 
        by simp
      hence \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi
             < k * Z_alarm / (K_Z + Z_alarm)\<close>
        using degradation_exceeds_production 
        by linarith
      thus ?thesis 
        using deg_mono 
        by linarith
    qed

    have \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX < 
          k * Z_max / (K_Z + Z_max)\<close>
      using prod_bound gap_pos 
      by linarith
    thus \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
      using field_eq i_2 
      by simp
  qed

  \<comment> \<open>Inactive components: i=0 (S) and i=1 (X) from controllers;
      i not in \{iS, iX, iZ\} from field-is-zero implying y is constant.\<close>
  have inactive_maint:
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'a and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    from i_inact 
    have i_ne_2: \<open>i \<noteq> iZ\<close> 
      unfolding active_def 
      by simp

    consider (S) \<open>i = iS\<close> | (X) \<open>i = iX\<close>
      | (other) \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> \<open>i \<noteq> iZ\<close>
      using i_ne_2 
      by blast
    thus \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof cases
      case S
      thus ?thesis
        using substrate_controlled[OF \<tau>_in] lo_S hi_S 
        by simp
    next
      case X
      thus ?thesis
        using biomass_controlled[OF \<tau>_in] lo_X hi_X 
        by simp
    next
      case other
      \<comment> \<open>Returns zero on these indices, hence y constant.\<close>
      have field_zero:
        \<open>\<And>\<tau>' v. vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
      proof -
        fix \<tau>' :: real and v :: \<open>(real, 'a) vec\<close>
        show \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
          unfolding metabolic_field_def 
          using other 
          by (simp add: fun_upd_def)
      qed

      have y_vderiv: \<open>(y has_vderiv_on
                       (\<lambda>\<tau>. metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)))
                      {0..T}\<close>
        using y_sol 
        by (simp add: solves_ode_def)

      have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..T}\<close>
      proof -
        have inner: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on
                     (\<lambda>\<tau>. vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) i))
                    {0..T}\<close>
        proof -
          have s1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               (y has_vector_derivative
                (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')))
                 (at \<tau>' within {0..T})\<close>
            using y_vderiv 
            unfolding has_vderiv_on_def 
            by blast
          have s2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               (y has_derivative
                (\<lambda>h. h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')))
                 (at \<tau>' within {0..T})\<close>
            using s1 
            unfolding has_vector_derivative_def 
            by blast
          have s3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative
                (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i))
                 (at \<tau>' within {0..T})\<close>
          proof -
            fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..T}\<close>
            have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
              by (rule has_derivative_vec_nth)
            show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative
                   (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i))
                  (at \<tau>' within {0..T})\<close>
              using has_derivative_compose[OF s2[OF \<tau>'_in] proj] 
              by simp
          qed
          show ?thesis
            unfolding has_vderiv_on_def has_vector_derivative_def
            using s3 
            by simp
        qed
        thus ?thesis 
          using field_zero 
          by simp
      qed

      have y_const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
        using has_vderiv_on_zero_imp_constant[OF yi_vderiv T_nn \<tau>_in] .

      have lo_eq: \<open>lo i = vec_nth (y 0) i\<close> using other unfolding lo_def by simp
      have hi_eq: \<open>hi i = vec_nth (y 0) i\<close> using other unfolding hi_def by simp
      show ?thesis 
        using y_const lo_eq hi_eq 
        by simp
    qed
  qed

  \<comment> \<open>Apply DI\_Frame\_Rule\_partial.\<close>
  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..T} \<Longrightarrow>
                    lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF T_nn y_sol iv active_ord
                                      lower_inward upper_inward inactive_maint]
    by blast

  fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
  have \<open>lo iZ \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> hi iZ\<close>
    using main[OF \<tau>_in, of iZ] .
  thus \<open>vec_nth (y \<tau>) iZ \<le> Z_max\<close> 
    using hi_Z 
    by simp
qed

text \<open>
  Lower-bound forward-invariance for Z.  Uses DI\_Frame\_Rule\_partial
  with active = \{iZ\}, lo iZ = Z\_min, hi iZ = Z\_max.  At the lower face
  Z = Z\_min: production at the worst-case (S\_lo, X\_lo) is supplied by
  Z\_lower\_production\_exceeds\_degradation, then monotonicity in S and X
  lifts this to the full controller band.  At the upper face Z = Z\_max:
  same argument as in Z\_upper\_bound\_invariant.\<close>

lemma Z_lower_bound_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z0_above_min: \<open>Z_min \<le> vec_nth (y 0) iZ\<close>
  assumes Z0_below_max: \<open>vec_nth (y 0) iZ \<le> Z_max\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> Z_min \<le> vec_nth (y \<tau>) iZ\<close>
proof -
  define lo where
    \<open>lo = (\<lambda>i::'a.
      if i = iS then S_lo
      else if i = iX then X_lo
      else if i = iZ then Z_min
      else vec_nth (y 0) i)\<close>
  define hi where
    \<open>hi = (\<lambda>i::'a.
      if i = iS then S_hi
      else if i = iX then X_hi
      else if i = iZ then Z_max
      else vec_nth (y 0) i)\<close>
  define active :: \<open>'a set\<close> where \<open>active = {iZ}\<close>

  have lo_S: \<open>lo iS = S_lo\<close>  unfolding lo_def by simp
  have lo_X: \<open>lo iX = X_lo\<close>  unfolding lo_def by simp
  have lo_Z: \<open>lo iZ = Z_min\<close> unfolding lo_def by simp
  have hi_S: \<open>hi iS = S_hi\<close>  unfolding hi_def by simp
  have hi_X: \<open>hi iX = X_hi\<close>  unfolding hi_def by simp
  have hi_Z: \<open>hi iZ = Z_max\<close> unfolding hi_def by simp

  have T_in: \<open>0 \<in> {0..T}\<close> using T_nn by simp

  \<comment> \<open>iv obligation: initial state in [lo, hi] componentwise.\<close>
  have iv: \<open>\<And>i. lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
  proof -
    fix i :: 'a
    consider (S) \<open>i = iS\<close> | (X) \<open>i = iX\<close> | (Z) \<open>i = iZ\<close>
      | (other) \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> \<open>i \<noteq> iZ\<close>
      by blast
    thus \<open>lo i \<le> vec_nth (y 0) i \<and> vec_nth (y 0) i \<le> hi i\<close>
    proof cases
      case S
      thus ?thesis using substrate_controlled[OF T_in] lo_S hi_S by simp
    next
      case X
      thus ?thesis using biomass_controlled[OF T_in] lo_X hi_X by simp
    next
      case Z
      thus ?thesis using Z0_above_min Z0_below_max lo_Z hi_Z by simp
    next
      case other
      thus ?thesis unfolding lo_def hi_def by simp
    qed
  qed

  \<comment> \<open>active\_ordered: Z\_min < Z\_max.  From Z\_min <= Z\_eq < Z\_alarm <= Z\_max.\<close>
  have active_ord: \<open>\<And>i. i \<in> active \<Longrightarrow> lo i < hi i\<close>
  proof -
    fix i :: 'a
    assume \<open>i \<in> active\<close>
    hence i_2: \<open>i = iZ\<close> 
      unfolding active_def 
      by simp
    have \<open>Z_min < Z_max\<close>
      using Z_min_below_eq Z_alarm_above_eq Z_max_above_alarm 
      by linarith
    thus \<open>lo i < hi i\<close> 
      using i_2 lo_Z hi_Z 
      by simp
  qed

  \<comment> \<open>Lower face Z = Z\_min: dZ/dt strictly > 0 by
      Z\_lower\_production\_exceeds\_degradation plus monotonicity.\<close>
  have lower_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
            (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
            vec_nth v i = lo i \<Longrightarrow>
            0 < vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    assume v_box: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_lo: \<open>vec_nth v i = lo i\<close>

    from i_act have i_2: \<open>i = iZ\<close> 
      unfolding active_def 
      by simp
    have Z_at_min: 
      \<open>vec_nth v iZ = Z_min\<close> 
      using eq_lo i_2 lo_Z 
      by simp

    have S_in: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
      using v_box[of iS] lo_S hi_S 
      by simp_all
    have X_in: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
      using v_box[of iX] lo_X hi_X 
      by simp_all
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> 
      using S_in(1) S_lo_pos 
      by linarith
    have X_nn: \<open>0 \<le> vec_nth v iX\<close> 
      using X_in(1) X_lo_pos 
      by linarith
    have S_lo_nn: \<open>0 \<le> S_lo\<close>          
      using S_lo_pos 
      by simp
    have X_lo_nn: \<open>0 \<le> X_lo\<close>          
      using X_lo_pos 
      by simp

    have field_eq:
      \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ =
       \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX - k * Z_min / (K_Z + Z_min)\<close>
      unfolding metabolic_field_def 
      using Z_at_min
      by (simp add: fun_upd_def)

    \<comment> \<open>P(S, X) >= P\_min = P(S\_lo, X\_lo).\<close>
    have prod_bound:
      \<open>\<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) * X_lo \<le>
       \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
    proof -
      have uptake_mono:
        \<open>\<mu>_max * S_lo / (K_S + S_lo) \<le>
         \<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)\<close>
      proof -
        have \<open>(\<mu>_max * S_lo / (K_S + S_lo)) * 1
              \<le> (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1\<close>
          using monod_uptake_monotone_in_S[OF S_lo_nn S_in(1), of 1] 
          by simp
        thus ?thesis 
          by simp
      qed
      have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> 
        using \<alpha>_pos 
        by simp
      have \<alpha>_up_mono:
        \<open>\<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) \<le>
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS))\<close>
        using uptake_mono \<alpha>_nn mult_left_mono 
        by blast
      have up_lo_nn: \<open>0 \<le> \<mu>_max * S_lo / (K_S + S_lo)\<close>
      proof -
        have \<open>0 < K_S + S_lo\<close> 
          using K_S_plus_S_pos S_lo_nn 
          by simp
        thus ?thesis 
          using \<mu>_max_pos S_lo_nn 
          by (simp add: divide_nonneg_pos)
      qed
      have \<alpha>u_lo_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_lo / (K_S + S_lo))\<close>
        using \<alpha>_nn up_lo_nn mult_sign_intros(1) 
        by blast
      have step1:
        \<open>\<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) * X_lo \<le>
         \<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) * vec_nth v iX\<close>
        using \<alpha>u_lo_nn X_in(1) mult_left_mono 
        by blast
      have step2:
        \<open>\<alpha> * (\<mu>_max * S_lo / (K_S + S_lo)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
        using \<alpha>_up_mono X_nn mult_right_mono 
        by blast
      from step1 step2 
      show ?thesis 
        by linarith
    qed

    \<comment> \<open>D(Z\_min) < P\_min <= P(S, X), hence dZ/dt > 0.\<close>
    have \<open>k * Z_min / (K_Z + Z_min) <
          \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX\<close>
      using Z_lower_production_exceeds_degradation prod_bound 
      by linarith
    thus \<open>0 < vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i\<close>
      using field_eq i_2 
      by simp
  qed

  \<comment> \<open>Upper face Z = Z\_max: same argument as Z\_upper\_bound\_invariant.\<close>
  have upper_inward:
    \<open>\<And>i v \<tau>. i \<in> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
            (\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j) \<Longrightarrow>
            vec_nth v i = hi i \<Longrightarrow>
            vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
  proof -
    fix i :: 'a and v :: \<open>(real, 'a) vec\<close> and \<tau> :: real
    assume i_act: \<open>i \<in> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    assume v_box: \<open>\<And>j. lo j \<le> vec_nth v j \<and> vec_nth v j \<le> hi j\<close>
    assume eq_hi: \<open>vec_nth v i = hi i\<close>

    from i_act have i_2: \<open>i = iZ\<close> 
      unfolding active_def 
      by simp
    have Z_at_max: \<open>vec_nth v iZ = Z_max\<close> 
      using eq_hi i_2 hi_Z 
      by simp

    have S_in: \<open>S_lo \<le> vec_nth v iS\<close> \<open>vec_nth v iS \<le> S_hi\<close>
      using v_box[of iS] lo_S hi_S 
      by simp_all
    have X_in: \<open>X_lo \<le> vec_nth v iX\<close> \<open>vec_nth v iX \<le> X_hi\<close>
      using v_box[of iX] lo_X hi_X 
      by simp_all
    have S_nn: \<open>0 \<le> vec_nth v iS\<close> 
      using S_in(1) S_lo_pos 
      by linarith
    have X_nn: \<open>0 \<le> vec_nth v iX\<close> 
      using X_in(1) X_lo_pos 
      by linarith

    have field_eq:
      \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) iZ =
       \<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX
       - k * Z_max / (K_Z + Z_max)\<close>
      unfolding metabolic_field_def 
      using Z_at_max
      by (simp add: fun_upd_def)

    have prod_bound:
      \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
       \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
    proof -
      have uptake_mono:
        \<open>\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS) \<le>
         \<mu>_max * S_hi / (K_S + S_hi)\<close>
      proof -
        have \<open>(\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * 1 \<le>
              (\<mu>_max * S_hi / (K_S + S_hi)) * 1\<close>
          using monod_uptake_monotone_in_S[OF S_nn S_in(2), of 1] 
          by simp
        thus ?thesis 
          by simp
      qed
      have \<alpha>_nn: \<open>0 \<le> \<alpha>\<close> using \<alpha>_pos by simp
      have \<alpha>_up_mono:
        \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) \<le>
         \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
        using uptake_mono \<alpha>_nn mult_left_mono 
        by blast
      have up_hi_nn: \<open>0 \<le> \<mu>_max * S_hi / (K_S + S_hi)\<close>
      proof -
        have \<open>0 < K_S + S_hi\<close> 
          using K_S_plus_S_pos S_in(2) S_nn 
          by simp
        thus ?thesis 
          using \<mu>_max_pos S_in(2) S_nn 
          by (simp add: divide_nonneg_pos)
      qed
      have \<alpha>u_hi_nn: \<open>0 \<le> \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi))\<close>
        using \<alpha>_nn up_hi_nn mult_sign_intros(1) 
        by blast
      have step1:
        \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * vec_nth v iX\<close>
        using \<alpha>_up_mono X_nn mult_right_mono 
        by blast
      have step2:
        \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * vec_nth v iX \<le>
         \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
        using \<alpha>u_hi_nn X_in(2) mult_left_mono 
        by blast
      from step1 step2 
      show ?thesis 
        by linarith
    qed

    have deg_mono: \<open>k * Z_alarm / (K_Z + Z_alarm) \<le> k * Z_max / (K_Z + Z_max)\<close>
    proof -
      have Z_alarm_nn: \<open>0 \<le> Z_alarm\<close>
        using Z_alarm_above_eq Z_eq_pos 
        by linarith
      show ?thesis
        using mm_degradation_monotone[OF Z_alarm_nn Z_max_above_alarm] .
    qed

    have gap_pos:
      \<open>0 < k * Z_max / (K_Z + Z_max) - \<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi\<close>
    proof -
      have \<open>0 < \<delta>_Z * (Z_alarm - Z_eq)\<close>
        using \<delta>_Z_pos Z_alarm_above_eq by simp
      hence \<open>\<alpha> * (\<mu>_max * S_hi / (K_S + S_hi)) * X_hi < k * Z_alarm / (K_Z + Z_alarm)\<close>
        using degradation_exceeds_production 
        by linarith
      thus ?thesis using deg_mono 
        by linarith
    qed

    have \<open>\<alpha> * (\<mu>_max * vec_nth v iS / (K_S + vec_nth v iS)) * vec_nth v iX < k * Z_max / (K_Z + Z_max)\<close>
      using prod_bound gap_pos 
      by linarith
    thus \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> v) i < 0\<close>
      using field_eq i_2 
      by simp
  qed

  \<comment> \<open>Inactive components: i=0 (S) and i=1 (X) from controllers;
      i not in \{iS, iX, iZ\} via field-is-zero argument.  Same as in
      Z\_upper\_bound\_invariant.\<close>
  have inactive_maint:
    \<open>\<And>i \<tau>. i \<notin> active \<Longrightarrow> \<tau> \<in> {0..T} \<Longrightarrow>
           lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
  proof -
    fix i :: 'a and \<tau> :: real
    assume i_inact: \<open>i \<notin> active\<close>
    assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
    from i_inact 
    have i_ne_2: \<open>i \<noteq> iZ\<close> 
      unfolding active_def 
      by simp

    consider (S) \<open>i = iS\<close> | (X) \<open>i = iX\<close>
      | (other) \<open>i \<noteq> iS\<close> \<open>i \<noteq> iX\<close> \<open>i \<noteq> iZ\<close>
      using i_ne_2 by blast
    thus \<open>lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    proof cases
      case S
      thus ?thesis 
        using substrate_controlled[OF \<tau>_in] lo_S hi_S 
        by simp
    next
      case X
      thus ?thesis 
        using biomass_controlled[OF \<tau>_in] lo_X hi_X 
        by simp
    next
      case other
      have field_zero:
        \<open>\<And>\<tau>' v. vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
      proof -
        fix \<tau>' :: real and v :: \<open>(real, 'a) vec\<close>
        show \<open>vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' v) i = 0\<close>
          unfolding metabolic_field_def 
          using other 
          by (simp add: fun_upd_def)
      qed

      have y_vderiv: \<open>(y has_vderiv_on
                       (\<lambda>\<tau>. metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)))
                      {0..T}\<close>
        using y_sol 
        by (simp add: solves_ode_def)

      have yi_vderiv: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on (\<lambda>\<tau>. 0)) {0..T}\<close>
      proof -
        have inner: \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_vderiv_on
                     (\<lambda>\<tau>. vec_nth (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau> (y \<tau>)) i))
                    {0..T}\<close>
        proof -
          have s1: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               (y has_vector_derivative
                (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')))
                 (at \<tau>' within {0..T})\<close>
            using y_vderiv 
            unfolding has_vderiv_on_def 
            by blast
          have s2: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               (y has_derivative
                (\<lambda>h. h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')))
                 (at \<tau>' within {0..T})\<close>
            using s1 
            unfolding has_vector_derivative_def 
            by blast
          have s3: \<open>\<And>\<tau>'. \<tau>' \<in> {0..T} \<Longrightarrow>
               ((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative
                (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i))
                 (at \<tau>' within {0..T})\<close>
          proof -
            fix \<tau>' assume \<tau>'_in: \<open>\<tau>' \<in> {0..T}\<close>
            have proj: \<open>((\<lambda>v. vec_nth v i) has_derivative (\<lambda>v. vec_nth v i)) (at (y \<tau>'))\<close>
              by (rule has_derivative_vec_nth)
            show \<open>((\<lambda>\<tau>. vec_nth (y \<tau>) i) has_derivative
                   (\<lambda>h. vec_nth (h *\<^sub>R metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z \<tau>' (y \<tau>')) i))
                  (at \<tau>' within {0..T})\<close>
              using has_derivative_compose[OF s2[OF \<tau>'_in] proj] 
              by simp
          qed
          show ?thesis
            unfolding has_vderiv_on_def has_vector_derivative_def
            using s3 
            by simp
        qed
        thus ?thesis 
          using field_zero 
          by simp
      qed

      have y_const: \<open>vec_nth (y \<tau>) i = vec_nth (y 0) i\<close>
        using has_vderiv_on_zero_imp_constant[OF yi_vderiv T_nn \<tau>_in] .

      have lo_eq: \<open>lo i = vec_nth (y 0) i\<close> using other unfolding lo_def by simp
      have hi_eq: \<open>hi i = vec_nth (y 0) i\<close> using other unfolding hi_def by simp
      show ?thesis 
        using y_const lo_eq hi_eq 
        by simp
    qed
  qed

  \<comment> \<open>Apply DI\_Frame\_Rule\_partial and project to the lower bound.\<close>
  have main: \<open>\<And>\<tau> i. \<tau> \<in> {0..T} \<Longrightarrow>
                    lo i \<le> vec_nth (y \<tau>) i \<and> vec_nth (y \<tau>) i \<le> hi i\<close>
    using DI_Frame_Rule_partial[OF T_nn y_sol iv active_ord
                                   lower_inward upper_inward inactive_maint]
    by blast

  fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
  have \<open>lo iZ \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> hi iZ\<close>
    using main[OF \<tau>_in, of iZ] .
  thus \<open>Z_min \<le> vec_nth (y \<tau>) iZ\<close> 
    using lo_Z 
    by simp
qed

text \<open>
  Unconditional box invariance for Z.  Composes Z\_upper\_bound\_invariant
  (Round 1) with Z\_lower\_bound\_invariant (above).  The Z\_upper precondition
  Z(0) >= 0 follows from Z\_min\_pos + Z0\_above\_min.\<close>

lemma Z_in_box_invariant:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z0_in_box:
    \<open>Z_min \<le> vec_nth (y 0) iZ \<and> vec_nth (y 0) iZ \<le> Z_max\<close>
  shows \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
              Z_min \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
proof -
  have Z0_above_min: \<open>Z_min \<le> vec_nth (y 0) iZ\<close> 
    using Z0_in_box 
    by simp
  have Z0_below_max: \<open>vec_nth (y 0) iZ \<le> Z_max\<close> 
    using Z0_in_box 
    by simp
  have Z0_nn: \<open>0 \<le> vec_nth (y 0) iZ\<close>
    using Z0_above_min Z_min_pos 
    by linarith

  fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
  have lower: \<open>Z_min \<le> vec_nth (y \<tau>) iZ\<close>
    using Z_lower_bound_invariant[OF y_sol T_nn u_feed_pos
                                     substrate_controlled biomass_controlled
                                     Z0_above_min Z0_below_max \<tau>_in] .
  have upper: \<open>vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using Z_upper_bound_invariant[OF y_sol T_nn u_feed_pos
                                     substrate_controlled biomass_controlled
                                     Z0_nn Z0_below_max \<tau>_in] .
  show \<open>Z_min \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using lower upper 
    by simp
qed

subsubsection \<open>Piece B: Phase 1 exit-time theorem\<close>

text \<open>
  Z drops below Z\_alarm by time T\_clear = (2/delta\_Z)*ln((Z\_max-Z\_eq)/
  (Z\_alarm-Z\_eq)).  Proof: from V\_Z\_exponential\_decay\_full at time T\_clear,
  V\_Z bound at endpoint equals (Z\_alarm - Z\_eq)\textasciicircum{}2 / 2; with Z(T\_clear) >= Z\_eq,
  this unfolds to Z(T\_clear) <= Z\_alarm.

  IMPORTANT: this theorem still ASSUMES Z\_above\_eq\_throughout -- that's
  Piece C, which is provably incompatible with equilibrium\_condition.
  We leave it as a controller-supplied invariant.\<close>

theorem Z_exits_alarm_zone:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T_cl u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T_cl} UNIV\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T_cl} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T_cl} \<Longrightarrow>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z0_alarm:     \<open>Z_alarm \<le> vec_nth (y 0) iZ\<close>
  assumes Z0_below_max: \<open>vec_nth (y 0) iZ \<le> Z_max\<close>
  assumes Z_above_eq_throughout:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T_cl} \<Longrightarrow> Z_eq \<le> vec_nth (y \<tau>) iZ\<close>
  assumes T_cl_def: \<open>T_cl = (2 / \<delta>_Z) * ln ((Z_max - Z_eq) / (Z_alarm - Z_eq))\<close>
  shows \<open>\<exists>\<tau>\<in>{0..T_cl}. vec_nth (y \<tau>) iZ \<le> Z_alarm\<close>
proof -
  have eq_pos:   \<open>0 < Z_alarm - Z_eq\<close> using Z_alarm_above_eq by simp
  have max_pos:  \<open>0 < Z_max - Z_eq\<close>
    using Z_eq_pos Z_alarm_above_eq Z_max_above_alarm 
    by linarith
  have max_geq:  \<open>Z_alarm - Z_eq \<le> Z_max - Z_eq\<close>
    using Z_max_above_alarm 
    by simp
  have ratio_pos: \<open>0 < (Z_max - Z_eq) / (Z_alarm - Z_eq)\<close>
    using max_pos eq_pos 
    by simp
  have ratio_geq_1: \<open>1 \<le> (Z_max - Z_eq) / (Z_alarm - Z_eq)\<close>
    using max_geq eq_pos 
    by simp
  have ln_ratio_nn: \<open>0 \<le> ln ((Z_max - Z_eq) / (Z_alarm - Z_eq))\<close>
    using ratio_geq_1 
    by simp

  have T_cl_nn: \<open>0 \<le> T_cl\<close>
    using T_cl_def \<delta>_Z_pos ln_ratio_nn 
    by simp

  \<comment> \<open>Deriving Z0\_nn from Z0\_alarm (Z\_alarm > 0).\<close>
  have Z0_nn: \<open>0 \<le> vec_nth (y 0) iZ\<close>
    using Z0_alarm Z_alarm_above_eq Z_eq_pos 
    by linarith

  \<comment> \<open>Upper bound throughout via Piece A.\<close>
  have Z_upper: \<open>\<And>\<tau>. \<tau> \<in> {0..T_cl} \<Longrightarrow> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using Z_upper_bound_invariant[OF y_sol T_cl_nn u_feed_pos
                                     substrate_controlled biomass_controlled
                                     Z0_nn Z0_below_max] .

  \<comment> \<open>State in full band [Z\_eq, Z\_max].\<close>
  have state_in_full_band: \<open>\<And>\<tau>. \<tau> \<in> {0..T_cl} \<Longrightarrow>
       S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi \<and>
       X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi \<and>
       Z_eq \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using substrate_controlled biomass_controlled Z_above_eq_throughout Z_upper
    by auto

  \<comment> \<open>Applying Lyapunov decay at endpoint T\_cl.\<close>
  have V_Z_decay: \<open>V_Z (y T_cl) \<le> V_Z (y 0) * exp (-\<delta>_Z * T_cl)\<close>
    using V_Z_exponential_decay_full[OF y_sol T_cl_nn u_feed_pos state_in_full_band] .

  \<comment> \<open>V\_Z(y(0)) <= (Z\_max - Z\_eq)\textasciicircum{}2 / 2.\<close>
  have V_Z0_bound: \<open>V_Z (y 0) \<le> (Z_max - Z_eq)^2 / 2\<close>
  proof -
    have z0_diff_nn: \<open>0 \<le> vec_nth (y 0) iZ - Z_eq\<close>
      using Z0_alarm Z_alarm_above_eq 
      by linarith
    have z0_diff_le: \<open>vec_nth (y 0) iZ - Z_eq \<le> Z_max - Z_eq\<close>
      using Z0_below_max 
      by simp
    have \<open>(vec_nth (y 0) iZ - Z_eq)^2 \<le> (Z_max - Z_eq)^2\<close>
      using z0_diff_nn z0_diff_le 
      by (simp add: power_mono)
    thus ?thesis unfolding V_Z_def 
      by simp
  qed

  \<comment> \<open>exp(-delta\_Z * T\_cl) = ((Z\_alarm-Z\_eq)/(Z\_max-Z\_eq))\textasciicircum{}2.\<close>
  have exp_T_cl:
  \<open>exp (-\<delta>_Z * T_cl) = ((Z_alarm - Z_eq) / (Z_max - Z_eq))^2\<close>
  proof -
    have step1: \<open>-\<delta>_Z * T_cl = -2 * ln ((Z_max - Z_eq) / (Z_alarm - Z_eq))\<close>
      using T_cl_def \<delta>_Z_pos 
      by simp
    have step2: \<open>exp (-2 * ln ((Z_max - Z_eq) / (Z_alarm - Z_eq))) =
               ((Z_max - Z_eq) / (Z_alarm - Z_eq)) powr (-2)\<close>
      using ratio_pos 
      by (metis eq_pos le_divide_eq_1_pos le_numeral_extra(2) max_geq powr_def) 
    have step3: \<open>((Z_max - Z_eq) / (Z_alarm - Z_eq)) powr (-2) =
               ((Z_alarm - Z_eq) / (Z_max - Z_eq))^2\<close>
      using ratio_pos max_pos eq_pos
      by (simp add: powr_minus_divide power2_eq_square field_simps)
    show ?thesis using step1 step2 step3 
      by simp
  qed   

  \<comment> \<open>Combine: V\_Z(y(T\_cl)) <= (Z\_alarm - Z\_eq)\textasciicircum{}2 / 2.\<close>
  have V_Z_T_cl_bound: \<open>V_Z (y T_cl) \<le> (Z_alarm - Z_eq)^2 / 2\<close>
  proof -
    have exp_nn: \<open>0 \<le> exp (-\<delta>_Z * T_cl)\<close> 
      by simp
    have v0_nn: \<open>0 \<le> V_Z (y 0)\<close> using V_Z_nn .
    have prod_bound: \<open>V_Z (y 0) * exp (-\<delta>_Z * T_cl) \<le>
                      ((Z_max - Z_eq)^2 / 2) * exp (-\<delta>_Z * T_cl)\<close>
      using V_Z0_bound exp_nn mult_right_mono 
      by blast
    have arith: \<open>((Z_max - Z_eq)^2 / 2) * ((Z_alarm - Z_eq) / (Z_max - Z_eq))^2 =
                  (Z_alarm - Z_eq)^2 / 2\<close>
      using max_pos
      by (simp add: power2_eq_square)
    show ?thesis
      using V_Z_decay prod_bound exp_T_cl arith 
      by (metis (no_types, opaque_lifting) landau_o.R_trans)
  qed

  \<comment> \<open>Unfolding V\_Z and use Z(T\_cl) >= Z\_eq to conclude Z(T\_cl) <= Z\_alarm.\<close>
  have T_cl_in: \<open>T_cl \<in> {0..T_cl}\<close> 
    using T_cl_nn 
    by simp
  have Z_T_cl_geq_eq: \<open>Z_eq \<le> vec_nth (y T_cl) iZ\<close>
    using Z_above_eq_throughout[OF T_cl_in] .
  have diff_nn: \<open>0 \<le> vec_nth (y T_cl) iZ - Z_eq\<close>
    using Z_T_cl_geq_eq 
    by simp

  have sq_bound: \<open>(vec_nth (y T_cl) iZ - Z_eq)^2 \<le> (Z_alarm - Z_eq)^2\<close>
    using V_Z_T_cl_bound 
    unfolding V_Z_def 
    by simp
  have alarm_minus_eq_nn: \<open>0 \<le> Z_alarm - Z_eq\<close> 
    using eq_pos 
    by simp
  have \<open>vec_nth (y T_cl) iZ - Z_eq \<le> Z_alarm - Z_eq\<close>
    using sq_bound diff_nn alarm_minus_eq_nn power2_le_imp_le 
    by blast
  hence Z_T_cl_le_alarm: \<open>vec_nth (y T_cl) iZ \<le> Z_alarm\<close> 
    by linarith
  show ?thesis 
    using T_cl_in Z_T_cl_le_alarm 
    by blast
qed


text \<open>
  Unconditional safety with the interval-invariant conjunct.

  \textbf{WHAT'S UNCONDITIONAL:}\\
- Z(t) in [Z\_min, Z\_max] for all t in [0,T]  (forward-invariant box,
  from Z\_in\_box\_invariant -- derived purely from the dynamics).

  WHAT'S CONDITIONAL (controller-supplied invariant):
- Z(t) >= Z\_eq for all t in [0,T].  Structurally incompatible with
  equilibrium\_condition.

  \textbf{WHAT WE CONCLUDE GIVEN BOTH:}
    - exists t* in [0,T] with Z(t*) <= Z\_alarm  (alarm-zone exit by T\_clear).\<close>

theorem bioreactor_safety_unconditional:
  fixes y :: \<open>real \<Rightarrow> (real, 'a) vec\<close>
  fixes T u_feed :: real
  assumes y_sol: \<open>(y solves_ode
                   (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                   {0..T} UNIV\<close>
  assumes T_nn: \<open>0 \<le> T\<close>
  assumes u_feed_pos: \<open>0 < u_feed\<close>
  assumes substrate_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
  assumes biomass_controlled:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
         X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
  assumes Z0_in_alarm:  \<open>Z_alarm \<le> vec_nth (y 0) iZ\<close>
  assumes Z0_below_max: \<open>vec_nth (y 0) iZ \<le> Z_max\<close>
  \<comment> \<open>Conditional operating-regime hypothesis: required for Lyapunov decay,
     NOT removable.\<close>
  assumes Z_above_eq_post_clearance:
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> Z_eq \<le> vec_nth (y \<tau>) iZ\<close>
  assumes T_geq_clear:
    \<open>(2 / \<delta>_Z) * ln ((Z_max - Z_eq) / (Z_alarm - Z_eq)) \<le> T\<close>
  shows \<open>(\<forall>\<tau>\<in>{0..T}. Z_min \<le> vec_nth (y \<tau>) iZ \<and>
                     vec_nth (y \<tau>) iZ \<le> Z_max) \<and>
         (\<exists>\<tau>\<in>{0..T}. vec_nth (y \<tau>) iZ \<le> Z_alarm)\<close>
proof -
  define T_clear where
    \<open>T_clear = (2 / \<delta>_Z) * ln ((Z_max - Z_eq) / (Z_alarm - Z_eq))\<close>

  \<comment> \<open>Initial Z is in [Z\_min, Z\_max]: from Z\_alarm > Z\_eq >= Z\_min and Z0\_in\_alarm.\<close>
  have Z0_above_min: \<open>Z_min \<le> vec_nth (y 0) iZ\<close>
    using Z0_in_alarm Z_alarm_above_eq Z_min_below_eq 
    by linarith
  have Z0_in_box: \<open>Z_min \<le> vec_nth (y 0) iZ \<and> vec_nth (y 0) iZ \<le> Z_max\<close>
    using Z0_above_min Z0_below_max 
    by simp

  \<comment> \<open>Box invariance via Z\_in\_box\_invariant.\<close>
  have box_inv: \<open>\<forall>\<tau>\<in>{0..T}. Z_min \<le> vec_nth (y \<tau>) iZ \<and> vec_nth (y \<tau>) iZ \<le> Z_max\<close>
    using Z_in_box_invariant[OF y_sol T_nn u_feed_pos
                                substrate_controlled biomass_controlled Z0_in_box]
    by blast

  \<comment> \<open>Alarm-zone exit by T\_clear.\<close>
  have eq_pos:  \<open>0 < Z_alarm - Z_eq\<close> 
    using Z_alarm_above_eq 
    by simp
  have max_pos: \<open>0 < Z_max - Z_eq\<close>
    using Z_eq_pos Z_alarm_above_eq Z_max_above_alarm 
    by linarith
  have max_geq: \<open>Z_alarm - Z_eq \<le> Z_max - Z_eq\<close>
    using Z_max_above_alarm 
    by simp
  have ratio_geq_1: \<open>1 \<le> (Z_max - Z_eq) / (Z_alarm - Z_eq)\<close>
    using max_geq eq_pos 
    by simp
  have T_clear_nn: \<open>0 \<le> T_clear\<close>
    unfolding T_clear_def 
    using \<delta>_Z_pos ratio_geq_1 
    by simp
  have T_clear_le_T: \<open>T_clear \<le> T\<close>
    unfolding T_clear_def 
    using T_geq_clear 
    by simp
  have T_clear_in: \<open>T_clear \<in> {0..T}\<close>
    using T_clear_nn T_clear_le_T 
    by simp

  have y_sol_T_clear: \<open>(y solves_ode
                        (metabolic_field iS iX iZ u_feed \<mu>_max K_S Y d K_I \<alpha> k K_Z))
                        {0..T_clear} UNIV\<close>
    using solves_ode_subset_ivl[OF y_sol T_clear_in] .

  have sub_S: \<open>\<And>\<tau>. \<tau> \<in> {0..T_clear} \<Longrightarrow>
                  S_lo \<le> vec_nth (y \<tau>) iS \<and> vec_nth (y \<tau>) iS \<le> S_hi\<close>
    using substrate_controlled T_clear_le_T 
    by auto
  have sub_X: \<open>\<And>\<tau>. \<tau> \<in> {0..T_clear} \<Longrightarrow>
                  X_lo \<le> vec_nth (y \<tau>) iX \<and> vec_nth (y \<tau>) iX \<le> X_hi\<close>
    using biomass_controlled T_clear_le_T 
    by auto
  have sub_Z_eq: \<open>\<And>\<tau>. \<tau> \<in> {0..T_clear} \<Longrightarrow> Z_eq \<le> vec_nth (y \<tau>) iZ\<close>
    using Z_above_eq_post_clearance T_clear_le_T 
    by auto

  have exit_window: \<open>\<exists>\<tau>\<in>{0..T_clear}. vec_nth (y \<tau>) iZ \<le> Z_alarm\<close>
    using Z_exits_alarm_zone[OF y_sol_T_clear u_feed_pos sub_S sub_X
                                Z0_in_alarm Z0_below_max sub_Z_eq
                                T_clear_def] .

  have exit: \<open>\<exists>\<tau>\<in>{0..T}. vec_nth (y \<tau>) iZ \<le> Z_alarm\<close>
  proof -
    from exit_window obtain \<tau>_e where
      \<tau>_e_in:    \<open>\<tau>_e \<in> {0..T_clear}\<close> and
      \<tau>_e_alarm: \<open>vec_nth (y \<tau>_e) iZ \<le> Z_alarm\<close>
      by blast
    have \<open>\<tau>_e \<in> {0..T}\<close> using \<tau>_e_in T_clear_le_T 
      by auto
    thus ?thesis 
      using \<tau>_e_alarm 
      by blast
  qed

  show ?thesis 
    using box_inv exit 
    by blast
qed

end  (* metabolic_z_clearance_params *)

subsection \<open>Concrete metabolic instantiation\<close>

text \<open>
  Parameter values for an engineered E. coli biofuel strain.
  
  Kinetic parameters (textbook-realistic):
    mu\_max = 1/2 hr\textasciicircum{}-\textasciicircum{}1     (maximum Monod growth rate)
    K\_S   = 1/2 g/L       (Monod half-saturation constant)
    Y     = 2/5            (biomass yield per substrate)
    d     = 1/10 hr\textasciicircum{}-\textasciicircum{}1     (biomass decay/dilution rate)
    K\_I   = 5 mM           (Z-inhibition constant)
    alpha     = 1/10           (intermediate production yield)
    k     = 1 mM/hr        (engineered degradation V\_max)
    K\_Z   = 1 mM           (degradation Michaelis constant)
  
  Operational bounds (bioreactor controller):
    S in [1/10, 1] g/L     (substrate maintained by feed pump)
    X in [1/10, 2] g/L     (biomass managed by dilution)
  
  Z-clearance parameters:
    Z\_eq    = 1/4 mM       (designed operating point for Z)
    Z\_alarm = 1 mM         (alarm threshold)
    Z\_max   = 7/4 mM       (maximum Z in alarm zone)
    delta\_Z     = 1/2 hr\textasciicircum{}-\textasciicircum{}1    (exponential decay rate)
  
  The design theorem: after a substrate spike pushes Z above 
  the alarm threshold, the engineered degradation pathway clears 
  Z below the alarm level with a half-life of ln(2)/delta\_Z approx 1.4 hr.\<close>

subsubsection \<open>Parameter values\<close>

named_theorems metabolic_conc_defs 

definition \<mu>_max_val :: real where [metabolic_conc_defs]:\<open>\<mu>_max_val = 1/2\<close>
definition K_S_val :: real where [metabolic_conc_defs]: \<open>K_S_val = 1/2\<close>
definition Y_val :: real where [metabolic_conc_defs]: \<open>Y_val = 2/5\<close>
definition d_val :: real where [metabolic_conc_defs]: \<open>d_val = 1/10\<close>
definition K_I_val :: real where [metabolic_conc_defs]: \<open>K_I_val = 5\<close>
definition \<alpha>_met_val :: real where [metabolic_conc_defs]: \<open>\<alpha>_met_val = 1/10\<close>
definition k_met_val :: real where [metabolic_conc_defs]: \<open>k_met_val = 1\<close>
definition K_Z_val :: real where [metabolic_conc_defs]: \<open>K_Z_val = 1\<close>

definition S_lo_val :: real where [metabolic_conc_defs]: \<open>S_lo_val = 1/10\<close>
definition S_hi_val :: real where [metabolic_conc_defs]: \<open>S_hi_val = 1\<close>
definition X_lo_val :: real where [metabolic_conc_defs]: \<open>X_lo_val = 1/10\<close>
definition X_hi_val :: real where [metabolic_conc_defs]: \<open>X_hi_val = 2\<close>

definition Z_eq_val :: real where [metabolic_conc_defs]: \<open>Z_eq_val = 1/4\<close>
definition Z_alarm_val :: real where [metabolic_conc_defs]: \<open>Z_alarm_val = 1\<close>
definition Z_max_met_val :: real where [metabolic_conc_defs]: \<open>Z_max_met_val = 7/4\<close>
definition \<delta>_Z_val :: real where [metabolic_conc_defs]: \<open>\<delta>_Z_val = 1/2\<close>
definition Z_min_val :: real where  [metabolic_conc_defs]: \<open>Z_min_val = 1/2000\<close>


subsubsection \<open>Coordinates of the concrete instance\<close>

text \<open>
  As in the Gardner case study, the concrete instance keeps the state space
  general: S, X and Z sit at three pairwise distinct coordinates iS, iX
  and iZ of an arbitrary finite index type.  The results of this block are
  exported with the coordinates generalised and their distinctness as
  premises.
\<close>

context
  fixes iS iX iZ :: \<open>'a::finite\<close>
  assumes coords: \<open>iS \<noteq> iX\<close> \<open>iS \<noteq> iZ\<close> \<open>iX \<noteq> iZ\<close>
begin

subsubsection \<open>Baseline parameters interpretation\<close>

interpretation met_baseline:
  metabolic_baseline_params iS iX iZ
    \<mu>_max_val K_S_val Y_val d_val K_I_val \<alpha>_met_val k_met_val K_Z_val
proof
  show \<open>iS \<noteq> iX\<close> \<open>iS \<noteq> iZ\<close> \<open>iX \<noteq> iZ\<close>
    by (simp_all add: coords)
  show \<open>0 < \<mu>_max_val\<close> unfolding \<mu>_max_val_def by simp
  show \<open>0 < K_S_val\<close> unfolding K_S_val_def by simp
  show \<open>0 < Y_val\<close> unfolding Y_val_def by simp
  show \<open>Y_val \<le> 1\<close> unfolding Y_val_def by simp
  show \<open>0 < d_val\<close> unfolding d_val_def by simp
  show \<open>0 < K_I_val\<close> unfolding K_I_val_def by simp
  show \<open>0 < \<alpha>_met_val\<close> unfolding \<alpha>_met_val_def by simp
  show \<open>0 < k_met_val\<close> unfolding k_met_val_def by simp
  show \<open>0 < K_Z_val\<close> unfolding K_Z_val_def by simp
qed


subsubsection \<open>Z-clearance interpretation\<close>

interpretation met_z_clearance:
  metabolic_z_clearance_params iS iX iZ
    \<mu>_max_val K_S_val Y_val d_val K_I_val \<alpha>_met_val k_met_val K_Z_val
    S_lo_val S_hi_val X_lo_val X_hi_val
    Z_eq_val Z_alarm_val Z_max_met_val Z_min_val \<delta>_Z_val
proof
  show \<open>0 < S_lo_val\<close> unfolding S_lo_val_def by simp
  show \<open>S_lo_val < S_hi_val\<close> unfolding S_lo_val_def S_hi_val_def by simp
  show \<open>0 < X_lo_val\<close> unfolding X_lo_val_def by simp
  show \<open>X_lo_val < X_hi_val\<close> unfolding X_lo_val_def X_hi_val_def by simp
  show \<open>0 < Z_eq_val\<close> unfolding Z_eq_val_def by simp
  show \<open>Z_eq_val < Z_alarm_val\<close> unfolding Z_eq_val_def Z_alarm_val_def by simp
  show \<open>Z_alarm_val \<le> Z_max_met_val\<close> 
    unfolding Z_alarm_val_def Z_max_met_val_def by simp

  (* Band-width: 7/4 - 1/4 = 3/2 \<le> 2\<sqdot>(1 - 1/4) = 3/2 *)
  show \<open>Z_max_met_val - Z_eq_val \<le> 2 * (Z_alarm_val - Z_eq_val)\<close>
    unfolding Z_max_met_val_def Z_eq_val_def Z_alarm_val_def by simp
  show \<open>0 < Z_min_val\<close>
    unfolding Z_min_val_def by simp

  show \<open>Z_min_val \<le> Z_eq_val\<close>
    unfolding Z_min_val_def Z_eq_val_def by simp
  show \<open>0 < \<delta>_Z_val\<close> unfolding \<delta>_Z_val_def by simp

  (* Design gap: \<delta>_Z \<sqdot> (Z_alarm - Z_eq) = 1/2 \<sqdot> 3/4 = 3/8
     Degradation at Z_alarm: k \<sqdot> 1/(1+1) = 1/2
     Production max: \<alpha> \<sqdot> \<mu> \<sqdot> S_hi/(K_S + S_hi) \<sqdot> X_hi 
                   = 1/10 \<sqdot> 1/2 \<sqdot> 1/(1/2 + 1) \<sqdot> 2 = 1/15
     Gap: 1/2 - 1/15 = 13/30
     Check: 3/8 \<le> 13/30, i.e. 90 \<le> 104 *)
  show \<open>\<delta>_Z_val * (Z_alarm_val - Z_eq_val) \<le> 
        k_met_val * Z_alarm_val / (K_Z_val + Z_alarm_val) 
        - \<alpha>_met_val * (\<mu>_max_val * S_hi_val / (K_S_val + S_hi_val)) * X_hi_val\<close>
    unfolding \<delta>_Z_val_def Z_alarm_val_def Z_eq_val_def 
              k_met_val_def K_Z_val_def \<alpha>_met_val_def \<mu>_max_val_def 
              S_hi_val_def K_S_val_def X_hi_val_def
    by (simp add: field_simps)
  \<comment> \<open>Equilibrium condition.
        P\_max = alpha*mu*S\_hi/(K\_S+S\_hi)*X\_hi
              = 1/10*1/2*1/(3/2)*2  =  1/15
        f(Z\_eq) = k*Z\_eq/(K\_Z+Z\_eq)
                = 1*(1/4)/(5/4)       =  1/5
        Check: 1/15 <= 1/5  i.e. 3/15 >= 1/15\<close>
  show \<open>\<alpha>_met_val * (\<mu>_max_val * S_hi_val / (K_S_val + S_hi_val)) * X_hi_val
        \<le> k_met_val * Z_eq_val / (K_Z_val + Z_eq_val)\<close>
    unfolding \<alpha>_met_val_def \<mu>_max_val_def S_hi_val_def K_S_val_def X_hi_val_def
              k_met_val_def Z_eq_val_def K_Z_val_def
    by (simp add: field_simps)

  \<comment> \<open>Lower-band decay-rate compatibility.
        LHS = delta\_Z*(K\_Z+Z\_alarm)*(K\_Z+Z\_eq) = 1/2 * 2 * 5/4 = 5/4
        RHS = 2*k*K\_Z                         = 2*1*1     = 2
        Check: 5/4 <= 2\<close>
  show \<open>\<delta>_Z_val * (K_Z_val + Z_alarm_val) * (K_Z_val + Z_eq_val)
        \<le> 2 * k_met_val * K_Z_val\<close>
    unfolding \<delta>_Z_val_def K_Z_val_def Z_alarm_val_def Z_eq_val_def k_met_val_def
    by simp
 \<comment> \<open>Lower production exceeds degradation at Z\_min.
        LHS = k*Z\_min/(K\_Z + Z\_min) = (1/2000)/(1+1/2000) = 1/2001
        RHS = alpha*mu*S\_lo/(K\_S+S\_lo)*X\_lo
            = (1/10)*(1/2)*(1/10)/(1/2+1/10)*(1/10)
            = (1/10)*(1/12)*(1/10) = 1/1200
        Check: 1/2001 < 1/1200 <=> 1200 < 2001\<close>
  show \<open>k_met_val * Z_min_val / (K_Z_val + Z_min_val)
        < \<alpha>_met_val * (\<mu>_max_val * S_lo_val / (K_S_val + S_lo_val)) * X_lo_val\<close>
    unfolding k_met_val_def Z_min_val_def K_Z_val_def
              \<alpha>_met_val_def \<mu>_max_val_def S_lo_val_def K_S_val_def X_lo_val_def
    by (simp add: field_simps)
qed


subsubsection \<open>Concrete Z-clearance theorem\<close>

text \<open>
  The locale metabolic\_z\_clearance\_params is satisfied by our 
  concrete E. coli biofuel parameters.  This unlocks 
  V\_Z\_exponential\_decay and V\_Z\_reaches\_sublevel as concrete 
  theorems about this specific engineered organism.
  
  In particular, met\_z\_clearance.V\_Z\_exponential\_decay gives:
  for any trajectory with S in [0.1, 1] g/L, X in [0.1, 2] g/L, 
  and Z in [1, 1.75] mM throughout [0, T], the Lyapunov function 
  V\_Z = (Z - 0.25)\textasciicircum{}2/2 satisfies 
    V\_Z(y(T)) <= V\_Z(y(0)) * exp(-T/2).
  
  A bio-engineer reads this as: "Z clears with a half-life of 
  about 1.4 hours."\<close>

thm met_z_clearance.V_Z_exponential_decay
thm met_z_clearance.V_Z_reaches_sublevel


theorem metabolic_z_clearance_concrete:
  \<open>metabolic_z_clearance_params iS iX iZ
     \<mu>_max_val K_S_val Y_val d_val K_I_val \<alpha>_met_val k_met_val K_Z_val
     S_lo_val S_hi_val X_lo_val X_hi_val
     Z_eq_val Z_alarm_val Z_max_met_val Z_min_val \<delta>_Z_val\<close>
  using met_z_clearance.metabolic_z_clearance_params_axioms .

end

end