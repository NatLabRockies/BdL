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
theory Biological_Computing_Benchmark_Proofs

imports Differential_Dynamic_Logic

begin
section \<open>Biological computing examples\<close>
subsection \<open>CRNs benchmark\<close>
subsubsection \<open>Autocatalytic chemical oscillator: conservation law\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  We consider an autocatalytic oscillator, a chemical reaction network (CRN)
  that exhibits oscillatory behavior - concentrations of chemical species
  rise and fall periodically over time, similar to a biological clock.

  This particular oscillator appears in the DNA strand displacement
  computing literature (Srinivas et al., 2015; Badelt et al., DNA 2017)
  as a benchmark for compiling abstract chemical programs into physical
  DNA-based implementations.

  \textbf{THE CHEMICAL REACTIONS}\\
  The system consists of three chemical species A, B, C undergoing three
  autocatalytic reactions:

    Reaction 1:  A + B  ->  2B    (rate k1)
    Reaction 2:  B + C  ->  2C    (rate k2)
    Reaction 3:  C + A  ->  2A    (rate k3)

  In each reaction, one species "converts" another into a copy of itself:
\begin{itemize}
\item A converts B into more B (A is consumed, B doubles)
\item B converts C into more C (B is consumed, C doubles)
\item C converts A into more A (C is consumed, A doubles)
\end{itemize}

  This creates a cyclic predator-prey dynamic: A feeds B, B feeds C,
  C feeds A - leading to oscillations.

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics (the standard model for well-mixed chemical
  systems), the concentrations [A], [B], [C] evolve according to:

    d[A]/dt = -k1*[A]*[B] + k3*[C]*[A]
    d[B]/dt =  k1*[A]*[B] - k2*[B]*[C]
    d[C]/dt =  k2*[B]*[C] - k3*[C]*[A]

  Each equation has two terms:
\begin{itemize}
\item A negative term: the species is consumed by one reaction
\item A positive term: the species is produced by another reaction
\end{itemize}

  This is a nonlinear system (products of concentrations appear on the
  right-hand side), which generally cannot be solved in closed form.

  \textbf{WHAT WE VERIFY}\\
  We formally prove the CONSERVATION LAW:

    [A](t) + [B](t) + [C](t) = [A](0) + [B](0) + [C](0)    for all t >= 0

  This states that the TOTAL concentration of all species is preserved
  over time. Although individual concentrations oscillate, their sum
  remains constant. Physically, this means no matter is created or
  destroyed - every molecule of A consumed in a reaction produces exactly
  one molecule of B (or C), maintaining the total count.

  \textbf{WHY THIS MATTERS}\\
1. CORRECTNESS OF THE MODEL: Conservation of mass is a fundamental
  physical law. If the ODE model violates it, the model is wrong.
  Our proof certifies the model is physically consistent.

1. COMPILATION VERIFICATION: When compiling this CRN to DNA strand
  displacement circuits (as in the Nuskell compiler), the compiled
  implementation should also satisfy conservation. Our proof
  methodology can verify this.

1. SAFETY PROPERTY: The conservation law implies that concentrations
  stay bounded: no species can exceed the total initial concentration.
  This is a safety property - the system cannot "blow up."

  \textbf{HOW WE VERIFY IT}\\
  We use DIFFERENTIAL INDUCTION (DI), a proof technique from Andre
  Platzer's Differential Dynamic Logic (dDL). The key idea:

  Instead of solving the ODE (which is impossible in closed form for
  this nonlinear system), we show that the DERIVATIVE of the invariant
  quantity [A]+[B]+[C] along the vector field is ZERO:

    d([A]+[B]+[C])/dt = d[A]/dt + d[B]/dt + d[C]/dt
                       = (-k1*A*B + k3*C*A) + (k1*A*B - k2*B*C) + (k2*B*C - k3*C*A)
                       = 0

  Every term appears once with + and once with -, so they cancel perfectly.
  Since the derivative is zero and the quantity starts at total0, it
  remains at total0 forever. This is proved WITHOUT solving the ODE.

  ASSUMPTIONS
  The proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [A](0) + [B](0) + [C](0) = total0
\item The time t >= 0
\item The rate constants k1, k2, k3 are arbitrary real numbers
  (the conservation law holds regardless of their values)
\end{enumerate}

  FORMALIZATION
  We represent the three species as components of a 3-dimensional vector:
\begin{itemize}
\item Position 0: concentration of A, i.e., [A]
\item Position 1: concentration of B, i.e., [B]
\item Position 2: concentration of C, i.e., [C]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
    vec\_lambda ((lambdak. 0)(0 := d[A]/dt, 1 := d[B]/dt, 2 := d[C]/dt))

  The proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>


text \<open>Main theorem: conservation of the total concentration.\<close>
lemma crn_oscillator_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
      \<comment> \<open>y(t) = ([A](t), [B](t), [C](t))\<close>
  fixes k1 k2 k3 :: real
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v. 
                       vec_lambda ((\<lambda>k. 0)(
                         0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                         1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                         2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Oscillator ODE:
           d[A]/dt = -k1*[A]*[B] + k3*[C]*[A];
           d[B]/dt = k1*[A]*[B] - k2*[B]*[C];
           d[C]/dt = k2*[B]*[C] - k3*[C]*[A]\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2 = total0\<close>
      \<comment> \<open>Initially: [A](0) + [B](0) + [C](0) = total0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + vec_nth (y t) 1 + vec_nth (y t) 2 = total0\<close>
      \<comment> \<open>Conclusion: [A](t) + [B](t) + [C](t) = total0 for all t >= 0\<close>
proof -
   have sum_deriv:
    \<open>((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 0 + vec_nth w 1 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: total0 \<le> [A](t) + [B](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>total0 \<le> vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2\<close>
    using iv by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                       1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                       2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                      \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                       1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                       2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                      \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                        1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                        2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                      \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                        1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                        2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                      \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + [B](t) + [C](t) \<le> total0₀
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2 \<le> total0\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                       1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                       2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                     \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                        1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                        2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                       \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                        1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                        2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                       \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + k3 * vec_nth v 2 * vec_nth v 0,
                        1 :=  k1 * vec_nth v 0 * vec_nth v 1 - k2 * vec_nth v 1 * vec_nth v 2,
                        2 :=  k2 * vec_nth v 1 * vec_nth v 2 - k3 * vec_nth v 2 * vec_nth v 0))) 
                       \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close> and 
                                   g = \<open>\<lambda>v. total0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. total0\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

text \<open>
 We formally proved that the total concentration in an autocatalytic chemical oscillator
   is conserved, using differential induction, a technique that verifies properties of nonlinear
    ODE systems without solving them. This is the first step toward formally certified
   compilation of chemical reaction networks.
  Chemical Reaction Network: Autocatalytic Oscillator

 Reactions:
    A + B -> 2B    (rate k1)
    B + C -> 2C    (rate k2)
    C + A -> 2A    (rate k3)
  Mass-action ODEs:
    d[A]/dt = -k1*[A]*[B] + k3*[C]*[A]
    d[B]/dt =  k1*[A]*[B] - k2*[B]*[C]
    d[C]/dt =  k2*[B]*[C] - k3*[C]*[A]
  Conservation law: [A](t) + [B](t) + [C](t) = [A](0) + [B](0) + [C](0)

  Proof method: DI\_Vect via antisymmetry (same structure as circular\_invariant)
  The Lie derivative of [A]+[B]+[C] along the vector field is:
    (-k1*A*B + k3*C*A) + (k1*A*B - k2*B*C) + (k2*B*C - k3*C*A) = 0
\<close>

subsubsection \<open>Michaelis-Menten enzyme kinetics: conservation laws\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  Michaelis-Menten kinetics is the most fundamental model in enzymology,
  describing how enzymes catalyze biochemical reactions. Proposed by
  Leonor Michaelis and Maud Menten in 1913, it is the foundation for
  understanding drug metabolism, cellular signaling, and metabolic pathways.

  \textbf{THE BIOCHEMICAL REACTION}\\
  An enzyme E binds reversibly to a substrate S to form an enzyme-substrate
  complex ES, which then irreversibly produces a product P and releases
  the enzyme:

           k1      k2
    E + S  <=>  ES  ->  E + P
           k-1

  Where:
    k1  = binding rate (enzyme + substrate -> complex)
    km1 = unbinding rate (complex -> enzyme + substrate)
    k2  = catalytic rate (complex -> enzyme + product)

  The enzyme acts as a catalyst: it facilitates the reaction but is
  regenerated at the end. The substrate is consumed and transformed
  into product.

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics, the concentrations evolve according to:

    d[E]/dt  = -k1*[E]*[S] + (km1 + k2)*[ES]
    d[S]/dt  = -k1*[E]*[S] + km1*[ES]
    d[ES]/dt =  k1*[E]*[S] - (km1 + k2)*[ES]
    d[P]/dt  =  k2*[ES]

  This is a 4-species, nonlinear system (due to the k?*[E]*[S] terms).

  \textbf{WHAT WE VERIFY}\\
  We formally prove TWO conservation laws:

1. ENZYME CONSERVATION:
  [E](t) + [ES](t) = [E](0) + [ES](0)    for all t >= 0

     The total enzyme (free + bound) is constant. The enzyme is a
     catalyst , it participates in the reaction but is never consumed
     or created. This is the fundamental property that makes enzymes
     reusable.

1. SUBSTRATE CONSERVATION (mass balance):
  [S](t) + [ES](t) + [P](t) = [S](0) + [ES](0) + [P](0)    for all t >= 0

     The total amount of substrate-derived material is constant.
     Substrate is either free [S], bound in the complex [ES], or
     converted to product [P]. No matter is created or destroyed.

  \textbf{WHY THESE MATTER}\\
1. ENZYME CONSERVATION is the key assumption that enables deriving
  the Michaelis-Menten equation V = Vmax*[S]/(Km + [S]).
  Without it, the standard derivation is invalid.

1. SUBSTRATE CONSERVATION ensures the model respects physical law
  (conservation of mass). It also implies boundedness: no species
  concentration can exceed the total initial amount.

1. Both properties are assumed (often implicitly) in every textbook
  treatment of enzyme kinetics. Here we PROVE them from the ODEs.

  \textbf{PROOF METHOD}\\
  Both conservation laws are proved using Differential Induction (DI),
  the same technique used for the CRN oscillator conservation law.

  For enzyme conservation [E]+[ES]:
    d([E]+[ES])/dt = d[E]/dt + d[ES]/dt
                   = (-k1*E*S + (km1+k2)*ES) + (k1*E*S - (km1+k2)*ES)
                   = 0
  For substrate conservation [S]+[ES]+[P]:
    d([S]+[ES]+[P])/dt = d[S]/dt + d[ES]/dt + d[P]/dt
                       = (-k1*E*S + km1*ES) + (k1*E*S - (km1+k2)*ES) + k2*ES
                       = 0

  FORMALIZATION
  We represent the four species as components of a 4-dimensional vector:
    Position 0: [E]   (free enzyme)
    Position 1: [S]   (free substrate)
    Position 2: [ES]  (enzyme-substrate complex)
    Position 3: [P]   (product)
\<close>



paragraph \<open>Conservation law 1: enzyme conservation, [E](t) + [ES](t) = E\_total\<close>

text \<open>
  The enzyme is a catalyst: it is neither created nor destroyed.
  The total enzyme concentration [E] + [ES] remains constant.

  Lie derivative calculation:
      d([E]+[ES])/dt = (-k1*[E]*[S] + (km1+k2)*[ES]) + (k1*[E]*[S] - (km1+k2)*[ES])
                     = -k1*E*S + (km1+k2)*ES + k1*E*S - (km1+k2)*ES
                     = 0
\<close>

lemma michaelis_menten_enzyme_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
      \<comment> \<open>y(t) = ([E](t), [S](t), [ES](t), [P](t))\<close>
  fixes k1 km1 k2 :: real
      \<comment> \<open>k1: binding rate, km1: unbinding rate, k2: catalytic rate\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                         1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                         2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                         3 :=  k2 * vec_nth v 2))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Michaelis-Menten ODE:
           d[E]/dt = -k1*[E]*[S] + (km1 + k2)*[ES];
           d[S]/dt = -k1*[E]*[S] + km1*[ES];
           d[ES]/dt = k1*[E]*[S] - (km1 + k2)*[ES];
           d[P]/dt = k2*[ES]\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = E_total\<close>
      \<comment> \<open>Initially: [E](0) + [ES](0) = E\_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = E_total\<close>
      \<comment> \<open>Conclusion: [E](t) + [ES](t) = E\_total for all t >= 0\<close>
proof -
   have enz_deriv:
    \<open>((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 0 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: E_total \<le> [E](t) + [ES](t)
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition E_total \<le> [E](0) + [ES](0) *)
  have iv_ge: \<open>E_total \<le> vec_nth (y 0) 0 + vec_nth (y 0) 2\<close>
    using iv by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. E_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. E_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                      0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                      1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                      2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                      3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule enz_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [E](t) + [ES](t) \<le> E_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 \<le> E_total\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. E_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. E_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule enz_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close> and g = \<open>\<lambda>v. E_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. E_total\<close> and g = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

paragraph \<open>Conservation law 2: substrate conservation, [S](t) + [ES](t) + [P](t) = S\_total\<close>

text \<open>
  The substrate is transformed but not destroyed: it is either free [S],
  bound in the complex [ES], or converted to product [P].

  Lie derivative calculation:
    d([S]+[ES]+[P])/dt = d[S]/dt + d[ES]/dt + d[P]/dt
      = (-k*E*S + km1*ES) + (k*E*S - (km1+k1)*ES) + k2*ES
      = -k*E*S + km1*ES + k*E*S - km1*ES - k2*ES + k2*ES
      = 0
\<close>
lemma michaelis_menten_substrate_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k1 km1 k2 :: real
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                         1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                         2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                         3 :=  k2 * vec_nth v 2))
                       )) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 + vec_nth (y 0) 3 = S_total\<close>
      \<comment> \<open>Initially: [S](0) + [ES](0) + [P](0) = S\_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 1 + vec_nth (y t) 2 + vec_nth (y t) 3 = S_total\<close>
      \<comment> \<open>Conclusion: [S](t) + [ES](t) + [P](t) = S\_total for all t >= 0\<close>
proof -
   have sub_deriv:
    \<open>((\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3) has_derivative 
      (\<lambda>w. vec_nth w 1 + vec_nth w 2 + vec_nth w 3)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: S_total \<le> [S](t) + [ES](t) + [P](t)
     ------------------------------------------------------------------------ *)

  (*PROOF OBLIGATION 1.1 (iv): initial condition S_total \<le> [S](0) + [ES](0) + [P](0) *)
  have iv_ge: \<open>S_total \<le> vec_nth (y 0) 1 + vec_nth (y 0) 2 + vec_nth (y 0) 3\<close>
    using iv by simp

  (*PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. S_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. S_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sub_deriv)
      apply (auto simp: fun_upd_def)
      apply argo
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [S](t) + [ES](t) + [P](t) \<le> S_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 + vec_nth (y 0) 3 \<le> S_total\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. S_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                      0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                      1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                      2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                      3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. S_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                        3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + (km1 + k2) * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - (km1 + k2) * vec_nth v 2,
                       3 :=  k2 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sub_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      apply argo
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3\<close> and 
                                   g = \<open>\<lambda>v. S_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. S_total\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2 + vec_nth v 3\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed
subsubsection \<open>SIR epidemic model: population conservation\<close>

text \<open>
  CONTEXT
  The SIR model is one of the most fundamental models in epidemiology,
  proposed by Kermack and McKendrick in 1927. It divides a population
  into three compartments:
    S = Susceptible (healthy, can become infected)
    I = Infected (can spread the disease)
    R = Recovered (immune, no longer infectious)

  \textbf{THE REACTIONS}\\
    S + I -> 2I    (infection: susceptible meets infected, becomes infected)
    I -> R         (recovery: infected individual recovers)

  Under mass-action kinetics:
    d[S]/dt = -beta*[S]*[I]
    d[I]/dt =  beta*[S]*[I] - gamma*[I]
    d[R]/dt =  gamma*[I]

  Where beta = infection rate, gamma = recovery rate.

  \textbf{WHAT WE VERIFY}\\
  Population conservation: [S](t) + [I](t) + [R](t) = N  for all t >= 0

  The total population is constant , people move between compartments
  but are neither created nor destroyed.

  Lie derivative:
    d([S]+[I]+[R])/dt = (-beta*S*I) + (beta*S*I - gamma*I) + (gamma*I)
                      = -beta*S*I + beta*S*I - gamma*I + gamma*I
                      = 0
\<close>
lemma sir_population_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes beta gamma :: real
      \<comment> \<open>beta: infection rate, gamma: recovery rate\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         0 := -beta * vec_nth v 0 * vec_nth v 1,
                         1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                         2 :=  gamma * vec_nth v 1))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: [S], position 1: [I], position 2: [R]\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2 = N\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + vec_nth (y t) 1 + vec_nth (y t) 2 = N\<close>
proof -
   have sum_deriv:
    \<open>((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 0 + vec_nth w 1 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: N \<le> [S](t) + [I](t) + [R](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>N \<le> vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2\<close>
    using iv by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. N) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -beta * vec_nth v 0 * vec_nth v 1,
                       1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                       2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -beta * vec_nth v 0 * vec_nth v 1,
                       1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                       2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. N) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -beta * vec_nth v 0 * vec_nth v 1,
                        1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                        2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -beta * vec_nth v 0 * vec_nth v 1,
                        1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                        2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [S](t) + [I](t) + [R](t) \<le> N
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 1 + vec_nth (y 0) 2 \<le> N\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. N) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -beta * vec_nth v 0 * vec_nth v 1,
                       1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                       2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -beta * vec_nth v 0 * vec_nth v 1,
                       1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                       2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. N) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -beta * vec_nth v 0 * vec_nth v 1,
                        1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                        2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -beta * vec_nth v 0 * vec_nth v 1,
                        1 :=  beta * vec_nth v 0 * vec_nth v 1 - gamma * vec_nth v 1,
                        2 :=  gamma * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close> and 
                                   g = \<open>\<lambda>v. N\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. N\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 1 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

subsubsection \<open>Reversible binding: two conservation laws\<close>

text \<open>
  CONTEXT
  Reversible binding is the most basic reaction in chemistry and biology.
  A ligand A binds to a receptor B to form a complex C, and the complex
  can dissociate back:

    A + B <=> C     (k forward, km1 reverse)

  This models:
\begin{itemize}
\item Drug-receptor binding in pharmacology
\item Antibody-antigen interactions in immunology
\item Transcription factor-DNA binding in gene regulation
\item Protein-protein interactions in cell signaling
\end{itemize}

  \textbf{THE ODE MODEL}\\
    d[A]/dt = -k*[A]*[B] + km1*[C]
    d[B]/dt = -k*[A]*[B] + km1*[C]
    d[C]/dt =  k*[A]*[B] - km1*[C]

  \textbf{WHAT WE VERIFY}\\
  Two conservation laws:

1. [A](t) + [C](t) = A\_total   (total A-containing material)
  Lie derivative: (-kAB + km1*C) + (kAB - km1*C) = 0

1. [B](t) + [C](t) = B\_total   (total B-containing material)
  Lie derivative: (-kAB + km1*C) + (kAB - km1*C) = 0

  These express that A and B are conserved moieties: they change form
  (free vs bound) but are never created or destroyed.
\<close>

text \<open>Conservation law 1: [A] + [C] = A\_total.\<close>
lemma reversible_binding_A_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k1 km1 :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                                      1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                                      2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: [A], position 1: [B], position 2: [C]\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = A_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = A_total\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [A](t) + [C](t) at A_total via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([A]+[C])/dt = (-k\<sqdot>A\<sqdot>B + km1\<sqdot>C) + (k\<sqdot>A\<sqdot>B - km1\<sqdot>C) = 0
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v₀ + v₂ *)
  have deriv:
    \<open>((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 0 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: A_total \<le> [A](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>A_total \<le> vec_nth (y 0) 0 + vec_nth (y 0) 2\<close>
    using iv by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. A_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. A_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + [C](t) \<le> A_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 \<le> A_total\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. A_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. A_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close> and g = \<open>\<lambda>v. A_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. A_total\<close> and g = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

text \<open>Conservation law 2: [B] + [C] = B\_total.\<close>
lemma reversible_binding_B_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k1 km1 :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                                      1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                                      2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: [A], position 1: [B], position 2: [C]\<close>
  assumes iv: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = B_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 1 + vec_nth (y t) 2 = B_total\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [B](t) + [C](t) at B_total via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([B]+[C])/dt = (-k1\<sqdot>A\<sqdot>B + km1\<sqdot>C) + (k1\<sqdot>A\<sqdot>B - km1\<sqdot>C) = 0
     ========================================================================== *)

  (* Helper: Fr\<eacute>chet derivative of the sum \<lambda>v. v\<^sub>1 + v\<^sub>2*)
  have deriv:
    \<open>((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 1 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: B_total \<le> [B](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>B_total \<le> vec_nth (y 0) 1 + vec_nth (y 0) 2\<close>
    using iv by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. B_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. B_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [B](t) + [C](t) \<le> B_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 \<le> B_total\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. B_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                       2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. B_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        1 := -k1 * vec_nth v 0 * vec_nth v 1 + km1 * vec_nth v 2,
                        2 :=  k1 * vec_nth v 0 * vec_nth v 1 - km1 * vec_nth v 2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close> and g = \<open>\<lambda>v. B_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. B_total\<close> and g = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


subsubsection \<open>Dimerization: weighted conservation law\<close>

text \<open>
  CONTEXT
  Dimerization is when two identical molecules combine to form a dimer:

 2A  <=>  A2     (k1 forward, k-1 reverse)

  This is fundamental in:
\begin{itemize}
\item Protein dimerization (many transcription factors function as dimers)
\item Receptor dimerization (e.g., EGFR signaling)
\item Hemoglobin assembly
\end{itemize}

  \textbf{THE ODE MODEL}\\
    d[A]/dt  = -2*k1*[A]\textasciicircum{}2 + 2*km1*[A2]
    d[A2]/dt =    k1*[A]\textasciicircum{}2 -    km1*[A2]

  \textbf{WHAT WE VERIFY}\\
  Weighted conservation: [A](t) + 2*[A2](t) = total

  Each dimer contains 2 monomers, so the total monomer count is
  [A] + 2*[A?]. The factor of 2 in the stoichiometry is crucial.

  Lie derivative:
    d([A] + 2*[A2])/dt = (-2*k1*A\textasciicircum{}2 + 2*km1*A2) + 2*(k1*A\textasciicircum{}2 - km1*A2)
                        = -2*k1*A\textasciicircum{}2 + 2*km1*A2+ 2*k1*A\textasciicircum{}2 - 2*km1*A2
                        = 0
\<close>

lemma dimerization_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k1 km1 :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                                      1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: [A] (monomer), position 1: [A2] (dimer)\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + 2 * vec_nth (y 0) 1 = total0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + 2 * vec_nth (y t) 1 = total0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [A](t) + 2\<sqdot>[A\<^sub>2](t) at total0 via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([A] + 2\<sqdot>[A\<^sub>2])/dt = (-2\<sqdot>k1\<sqdot>A² + 2\<sqdot>km1₁\<sqdot>A\<^sub>2) + 2\<sqdot>(k1\<sqdot>A² - km1\<sqdot>A\<^sub>2)
                            = -2\<sqdot>k1\<sqdot>A² + 2\<sqdot>km1\<sqdot>A\<^sub>2+ 2\<sqdot>k1\<sqdot>A² - 2\<sqdot>km1\<sqdot>A\<^sub>2
                            = 0
     
     Each dimer contains 2 monomers, so the total monomer count is 
     [A] + 2\<sqdot>[A\<^sub>2].  The factor of 2 in the stoichiometry is crucial.
     ========================================================================== *)

  (* ------------------------------------------------------------------------
     SUB-PART 1: total0 \<le> [A](t) + 2\<sqdot>[A\<^sub>2](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>total0 \<le> vec_nth (y 0) 0 + 2 * vec_nth (y 0) 1\<close>
    using iv by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                       1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>))\<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                       1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                        1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                        1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule weighted_sum_has_derivative)
      apply (auto simp: power2_eq_square algebra_simps fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + 2\<sqdot>[A₂](t) \<le> total0
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) 0 + 2 * vec_nth (y 0) 1 \<le> total0\<close>
    using iv by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                       1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                       1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                        1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := -2 * k1 * (vec_nth v 0)^2 + 2 * km1 * vec_nth v 1,
                        1 :=      k1 * (vec_nth v 0)^2 -     km1 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule weighted_sum_has_derivative)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: power2_eq_square algebra_simps fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1\<close> and g = \<open>\<lambda>v. total0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. total0\<close> and g = \<open>\<lambda>v. vec_nth v 0 + 2 * vec_nth v 1\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


subsubsection \<open>Simple decay: positivity via DG\<close>

text \<open>
  CONTEXT
  The simplest irreversible reaction: a species decays at a rate
  proportional to its concentration.

  A  ->  \{\}     (rate k)

  This models:
\begin{itemize}
\item Radioactive decay
\item mRNA degradation in cells
\item Drug clearance from the body
\item Protein turnover
\end{itemize}

  \textbf{THE ODE}\\
    d[A]/dt = -k*[A]

  \textbf{WHAT WE VERIFY}\\
  If [A](0) > 0, then [A](t) > 0 for all t >= 0.

  The species decays but never reaches zero in finite time.
  (The exact solution is [A](t) = [A](0)*e\textasciicircum{}\{-kt\} > 0.)

  \textbf{WHY DG IS NEEDED}\\
  DI alone fails: the Lie derivative of [A] >= 0 is -k*[A],
  which requires [A] <= 0 , the opposite of what we want.

  The ghost trick: add g' = (k/2)*g with g(0) = 1/surd[A](0).
  Then [A]*g\textasciicircum{}2 is invariant (Lie derivative = 0) and [A]*g\textasciicircum{}2 = 1,
  so [A] = 1/g\textasciicircum{}2 > 0.

  NOTE: This is exactly our exponential\_decay example with the
  ODE written in CRN notation. We state it here for completeness
  of the benchmark suite.
\<close>

subsubsection \<open>CRN benchmark summary\<close>

text \<open>
  | \#  | System                | Property              | Method | Species |
  |----|-----------------------|-----------------------|--------|---------|
  | 1  | CRN Oscillator        | A+B+C = const         | DI     | 3       |
  | 2  | Michaelis-Menten      | E+ES = const          | DI     | 4       |
  | 3  | Michaelis-Menten      | S+ES+P = const        | DI     | 4       |
  | 4  | Exponential decay     | x > 0                 | DG+DI  | 1+ghost |
  | 5  | Circular dynamics     | x\textasciicircum{}2+y\textasciicircum{}2 = r?\textasciicircum{}2          | DI     | 2       |
  | 6  | SIR Epidemic          | S+I+R = N             | DI     | 3       |
  | 7a | Reversible binding    | A+C = A\_total         | DI     | 3       |
  | 7b | Reversible binding    | B+C = B\_total         | DI     | 3       |
  | 8  | Dimerization          | A+2*A? = total        | DI     | 2       |
  | 9  | Simple decay A->\{\}      | [A] > 0               | DG+DI  | 1+ghost |

  All properties verified WITHOUT solving the ODEs , purely from
  local derivative analysis using differential induction (DI) and
  differential ghosts (DG).
\<close>
subsubsection \<open>CRN properties requiring differential ghosts\<close>

text \<open>
  These examples demonstrate properties that CANNOT be proved by
  Differential Induction (DI) alone. The Lie derivative has the
  "wrong sign", so a ghost variable must be introduced to create
  an invariant that implies the desired property.

  General pattern:
\begin{itemize}
\item Want to prove: [X](t) > 0
\item ODE has form: d[X]/dt = -k*[X] + (other terms)
\item DI fails: Lie derivative of [X] >= 0 gives -k*[X] + ... which is not >= 0
\item DG fix: Add ghost g' = (k/2)*g, prove [X]*g\textasciicircum{}2 >= 1 is invariant
\item Conclude: [X]*g\textasciicircum{}2 >= 1 and g\textasciicircum{}2 >= 0 implies [X] > 0
\end{itemize}
\<close>


paragraph \<open>Simple decay: the DG proof\<close>

text \<open>
  \textbf{THE CRN}\\
    A ->(k) \{\}        (first-order degradation)

  ODE:  d[A]/dt = -k*[A]

  This models: radioactive decay, mRNA degradation, drug clearance,
  protein turnover.

  PROPERTY: [A](0) > 0 ==> [A](t) > 0

  \textbf{WHY DI FAILS:}\\
    Lie derivative of [A] along -k*[A] is -k*[A].
    For [A] >= 0, need -k*[A] >= 0, which requires [A] <= 0. Contradiction!

  \textbf{DG STRATEGY:}\\
    Ghost: g' = (k/2)*g,  g(0) = 1/surd[A](0)
    Invariant: [A]*g\textasciicircum{}2 = 1
    Lie derivative: (-k*A)*g\textasciicircum{}2 + A*2g*(k/2*g) = -kAg\textasciicircum{}2 + kAg\textasciicircum{}2 = 0
    Initial: A?*(1/surdA?)\textasciicircum{}2 = 1
    Conclude: A*g\textasciicircum{}2 >= 1 and g\textasciicircum{}2 >= 0 ==> A > 0
\<close>
lemma crn_simple_decay_positivity:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k :: real
  assumes x_sol: \<open>(x solves_ode 
                    (\<lambda>t v. 
                      vec_lambda ((\<lambda>k. 0)(0 := -k * (vec_nth v 0))))) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (x 0) 0 > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes k_pos: \<open>0 < k\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove [A](t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): Introduce a ghost species y at position 1 satisfying 
                     dy/dt = (k/2)\<sqdot>y with initial value y(0) = 1/sqrt([A](0)). 
                     The combined trajectory ?z = x extended at index 1 
                     with y solves the extended ODE.
       
       STAGE 2 (DI): Prove the invariant 1 \<le> [A] \<sqdot> y² along the combined 
                     trajectory, via DI_Vect with h = 1 and g = [A] \<sqdot> y².
                     
                     Lie derivative:
                       d([A]\<sqdot>y²)/dt = (-k\<sqdot>A)\<sqdot>y² + A\<sqdot>2y\<sqdot>(k/2\<sqdot>y)
                                    = -k\<sqdot>A\<sqdot>y² + k\<sqdot>A\<sqdot>y²
                                    = 0
       
       STAGE 3 (algebra): Since [A] \<sqdot> y² \<ge> 1 and y² \<ge> 0, we get [A] > 0.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 0)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. k/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. k/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 1 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::4. 0)(0 := -k * (vec_nth v 0)))) \<tau> v) 1 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 1 \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(0 := -k * (vec_nth v 0)))) \<tau> v = 
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(0 := -k * (vec_nth v 0)))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 1 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(0 := -k * (vec_nth v 0)))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(0 := -k * (vec_nth v 0)))) \<tau> w\<close>
      using v0 
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: obtain a ghost trajectory y satisfying dy/dt = (k/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(1 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. k/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = 1,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(1 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(1 := y \<tau>))\<close>

  (* Helper: Fréchet derivative of [A] \<sqdot> y² (product rule) *)
  have xg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative 
      (\<lambda>v. vec_nth v 0 * (vec_nth p 1)^2 + 
           vec_nth p 0 * (2 * vec_nth p 1 * vec_nth v 1))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 1)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 1 * vec_nth v 1)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: Apply DI_Vect to prove the invariant 1 \<le> [A] \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> [A](0) \<sqdot> y(0)² *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) 0 * (vec_nth (?z 0) 1)^2\<close>
    using iv
    by (simp add: y0_def y_init field_simps power2_eq_square fun_upd_def)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                            vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                            vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                             vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(0 := -k * (vec_nth v 0))) +
                             vec_lambda ((\<lambda>i. 0)(1 := (k/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 * (vec_nth (?z \<tau>) 1)^2 + 
                                     vec_nth (?z \<tau>) 0 * (2 * vec_nth (?z \<tau>) 1 * vec_nth v 1)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule xg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      done
  qed

  (* APPLY DI_Vect: we get the invariant 1 \<le> [A] \<sqdot> y² at time t *)
  have ineq: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 1)^2\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2\<close>,
                  OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From [A](t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude [A](t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 0 = vec_nth (x t) 0\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 1)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 1)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 0 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

subsubsection \<open>Computing CRN min(x, y): conservation laws\<close>

text \<open>
  CONTEXT
  This is the first example where we verify a property of a CRN that
  performs COMPUTATION - not just a natural biochemical process, but a
  deliberately designed chemical program.
  The CRN computes the minimum of two non-negative integers x and y
  (Bridger 2019, "Computing with chemical reaction networks: a tutorial").
  This is referenced in Section 2.1.1 of "A Survey of Existing Paradigms
  in Biological Computing" (Nag et al., 2026).
  \textbf{THE CHEMICAL REACTION}\\
    X + Y -> Z     (rate k)
  Starting from initial concentrations [X](0) = x0 and [Y](0) = y0
  (with [Z](0) = 0), the reaction consumes equal amounts of X and Y
  to produce Z. When the minority species is exhausted, the reaction
  stops, and [Z] = min(x0, y0).
  \textbf{THE MASS-ACTION ODE MODEL}\\
    d[X]/dt = -k*[X]*[Y]
    d[Y]/dt = -k*[X]*[Y]
    d[Z]/dt =  k*[X]*[Y]
  \textbf{WHAT WE VERIFY}\\
  Two conservation laws that together ensure computational correctness:
\begin{enumerate}
\item INPUT-OUTPUT BALANCE FOR X:
  [X](t) + [Z](t) = x0     for all t >= 0
  Every molecule of X consumed produces exactly one molecule of Z.
  At completion (when X or Y is exhausted):
  if x0 <= y0, then [X] -> 0, so [Z] -> x0
  if x0 > y0, then [X] -> x0 - y0, and [Z] -> y0
\item INPUT-OUTPUT BALANCE FOR Y:
  [Y](t) + [Z](t) = y0     for all t >= 0
  Every molecule of Y consumed produces exactly one molecule of Z.
\end{enumerate}
  Together these imply:
\begin{itemize}
\item [X](t) - [Y](t) = x0 - y0 (the difference is preserved)
\item [Z](t) = x0 - [X](t) = y0 - [Y](t)
\item At steady state: [Z] = min(x0, y0)
\end{itemize}
  \textbf{WHY THIS MATTERS FOR BIOLOGICAL COMPUTING}\\
  This CRN is a PROGRAM - it takes inputs (initial concentrations of X, Y)
  and produces an output (final concentration of Z = min(x0, y0)).
  Our conservation laws prove that the program is CORRECT in the sense
  that it maintains the right "balance" throughout its execution:
  no molecules are lost or created spuriously.
  This is analogous to proving loop invariants in software verification:
  the conservation laws are invariants of the chemical "loop" that hold
  at every time step.
  \textbf{PROOF METHOD}\\
  Differential Induction (DI). Both Lie derivatives cancel to zero:
  For [X]+[Z]:
    d([X]+[Z])/dt = (-k*X*Y) + (k*X*Y) = 0
  For [Y]+[Z]:
    d([Y]+[Z])/dt = (-k*X*Y) + (k*X*Y) = 0
\<close>


lemma crn_min_X_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)
                                               (0 := -k * vec_nth v 0 * vec_nth v 1,
                                                1 := -k * vec_nth v 0 * vec_nth v 1,
                                                2 :=  k * vec_nth v 0 * vec_nth v 1))
                                   )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: [X], position 1: [Y], position 2: [Z].
         d[X]/dt = -k*[X]*[Y];
         d[Y]/dt = -k*[X]*[Y];
         d[Z]/dt = k*[X]*[Y]\<close>
  assumes iv: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
      \<comment> \<open>Initially: [X](0) + [Z](0) = x0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = x0\<close>
      \<comment> \<open>Conclusion: [X](t) + [Z](t) = x0 for all t >= 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [X](t) + [Z](t) at x0 via TWO DI_Vect applications.
     
     To prove A = B, we prove A \<le> B and B \<le> A (antisymmetry).  Each direction 
     uses DI_Vect with a constant lower/upper bound.  The Lie derivative of 
     [X] + [Z] cancels:
     
         d([X]+[Z])/dt = -k\<sqdot>X\<sqdot>Y + k\<sqdot>X\<sqdot>Y = 0
     
     so both directions hold with the same derivative check.
     
     We discharge each DI_Vect obligation as a separate `have` statement, 
     then apply both axiom instances via forward reasoning combined with 
     antisym in the final show.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v\<^sub>1+ v\<^sub>2*)
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 0 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: x0 \<le> [X](t) + [Z](t) via DI_Vect with h = x0, g = [X] + [Z]
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition x0 \<le> [X](0) + [Z](0) *)
  have iv_ge: \<open>x0 \<le> vec_nth (y 0) 0 + vec_nth (y 0) 2\<close>
    using iv by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. x0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. 
                         vec_lambda ((\<lambda>i. 0)
                                     (0 := -k * vec_nth v 0 * vec_nth v 1,
                                      1 := -k * vec_nth v 0 * vec_nth v 1,
                                      2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (0 := -k * vec_nth v 0 * vec_nth v 1,
                                         1 := -k * vec_nth v 0 * vec_nth v 1,
                                         2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. x0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [X](t) + [Z](t) \<le> x0 via DI_Vect with h = [X] + [Z], g = x0
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition [X](0) + [Z](0) \<le> x0 *)
  have iv_le: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 \<le> x0\<close>
    using iv by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. x0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (0 := -k * vec_nth v 0 * vec_nth v 1,
                                         1 := -k * vec_nth v 0 * vec_nth v 1,
                                         2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (0 := -k * vec_nth v 0 * vec_nth v 1,
                                         1 := -k * vec_nth v 0 * vec_nth v 1,
                                         2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. x0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     APPLY DI_Vect twice via antisym
     ------------------------------------------------------------------------ *)
  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close> and g = \<open>\<lambda>v. x0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. x0\<close> and g = \<open>\<lambda>v. vec_nth v 0 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


text \<open>Conservation law 2: [Y](t) + [Z](t) = y0.\<close>
lemma crn_min_Y_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)(
                                     0 := -k * vec_nth v 0 * vec_nth v 1,
                                     1 := -k * vec_nth v 0 * vec_nth v 1,
                                     2 :=  k * vec_nth v 0 * vec_nth v 1))
                                   )) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
      \<comment> \<open>Initially: [Y](0) + [Z](0) = y0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 1 + vec_nth (y t) 2 = y0\<close>
      \<comment> \<open>Conclusion: [Y](t) + [Z](t) = y0 for all t >= 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [Y](t) + [Z](t) at y0 via two DI_Vect applications.
     
     The Lie derivative of [Y] + [Z] cancels:
     
         d([Y]+[Z])/dt = -k\<sqdot>X\<sqdot>Y + k\<sqdot>X\<sqdot>Y = 0
     
     so both directions hold with the same derivative check.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v\<^sub>1+ v\<^sub>2*)
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative 
      (\<lambda>w. vec_nth w 1 + vec_nth w 2)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: y0 \<le> [Y](t) + [Z](t) via DI_Vect with h = y₀, g = [Y] + [Z]
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition y0 \<le> [Y](0) + [Z](0) *)
  have iv_ge: \<open>y0 \<le> vec_nth (y 0) 1 + vec_nth (y 0) 2\<close>
    using iv by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. y0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       0 := -k * vec_nth v 0 * vec_nth v 1,
                       1 := -k * vec_nth v 0 * vec_nth v 1,
                       2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       0 := -k * vec_nth v 0 * vec_nth v 1,
                       1 := -k * vec_nth v 0 * vec_nth v 1,
                       2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. y0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [Y](t) + [Z](t) \<le> y0 via DI_Vect with h = [Y] + [Z], g = y0
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition [Y](0) + [Z](0) \<le> y0 *)
  have iv_le: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 \<le> y0\<close>
    using iv by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. y0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 1 + vec_nth v 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. y0) has_derivative Dg) (at (y \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                         0 := -k * vec_nth v 0 * vec_nth v 1,
                         1 := -k * vec_nth v 0 * vec_nth v 1,
                         2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                         0 := -k * vec_nth v 0 * vec_nth v 1,
                         1 := -k * vec_nth v 0 * vec_nth v 1,
                         2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     APPLY DI_Vect twice via antisym
     ------------------------------------------------------------------------ *)
  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close> and g = \<open>\<lambda>v. y0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. y0\<close> and g = \<open>\<lambda>v. vec_nth v 1 + vec_nth v 2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

lemma crn_min_difference_preserved:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)(
                                     0 := -k * vec_nth v 0 * vec_nth v 1,
                                     1 := -k * vec_nth v 0 * vec_nth v 1,
                                     2 :=  k * vec_nth v 0 * vec_nth v 1))
                                   )) {0..t} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 - vec_nth (y t) 1 = x0 - y0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Compose the two conservation lemmas.
     
     From crn_min_X_conservation:  [X](t) + [Z](t) = x0
     From crn_min_Y_conservation:  [Y](t) + [Z](t) = y0
     Subtracting:                  [X](t) - [Y](t) = x0 - y0
     
     This lemma needs no DI_Vect application of its own; it's a pure 
     forward composition of the two established conservation laws, 
     finished by linarith.
     ========================================================================== *)

  have x_conservation: \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = x0\<close>
    using crn_min_X_conservation[OF y_sol iv_x t] .
  have y_conservation: \<open>vec_nth (y t) 1 + vec_nth (y t) 2 = y0\<close>
    using crn_min_Y_conservation[OF y_sol iv_y t] .
  show ?thesis
    using x_conservation y_conservation 
    by linarith
qed

subsection \<open>GRN benchmark\<close>

subsubsection \<open>Simplified genetic toggle switch, mass-action form\<close>

text \<open>
  CONTEXT-------
  The genetic toggle switch was constructed by Gardner, Cantor, and
  Collins in E. coli (Nature, 2000), the first synthetic, bistable
  gene-regulatory network. It is referenced in Section 3.4.5 of the
  biological computing survey (Nag et al., 2026).

  \textbf{THE CIRCUIT}\\
  Two repressors that mutually inhibit each other:

    Gene 1 -> Protein 1 -| Gene 2
    Gene 2 -> Protein 2 -| Gene 1

  The full Hill-function model used by Gardner et al. is:
    du/dt = alpha1/(1 + v\textasciicircum{}beta) - u
    dv/dt = alpha2/(1 + u\textasciicircum{}gamma) - v

  This involves rational functions, requiring `has\_derivative` for
  Hill functions, which we leave for future work. Instead, here we
  formalize the SIMPLIFIED LINEAR REPRESSION version:

    du/dt = alpha1 - beta*u*v - delta*u
    dv/dt = alpha2 - beta*u*v - delta*v

  Where:
    alpha1, alpha2 = constitutive production rates of proteins 1 and 2
    beta     = mutual repression rate (each protein degrades the other)
    delta     = degradation rate (basal turnover)

  Each protein represses the other through a bimolecular destruction
  reaction (beta*u*v term). This is the "annihilation" form of repression,
  often used in synthetic biology and specifically in antithetic feedback
  controllers (Briat et al. 2016).

  \textbf{PROPERTY TO VERIFY}\\
  REGIONAL INVARIANCE: If u(0) >= 0 and v(0) >= 0 and the parameters are
  positive, then u(t) >= 0 and v(t) >= 0 for all t >= 0.

  In other words: protein concentrations stay non-negative.

  \textbf{WHY THIS NEEDS DC}\\
  Direct DI proof of u >= 0 fails:
    Lie derivative of u along the field is alpha1 - beta*u*v - delta*u
    For u >= 0 invariance, we need alpha1 - beta*u*v - delta*u >= 0 when u = 0
    At u = 0: alpha1 - 0 - 0 = alpha1 >= 0  (since alpha1 > 0)

  Actually, for THIS specific simplified version, the standard DI
  approach for u >= 0 only requires evaluating the derivative at the
  BOUNDARY u = 0. Since at u = 0 we have du/dt = alpha1 >= 0, the boundary
  is repelling and u stays >= 0.

  But DI as we've formalized it (DI\_Vect) checks the derivative
  EVERYWHERE in the trajectory, not just at the boundary. So we need
  the global condition: 0 <= alpha1 - beta*u*v - delta*u for ALL u, v reachable.
  This is NOT true everywhere - it can fail when u is large.

  THIS is where DC helps:
\begin{enumerate}
\item First, we prove u >= 0 directly is hard with DI alone
\item Better strategy: we cut on a region where DI works
\end{enumerate}

  Even better: we use DC to incrementally build up an invariant region.

  \textbf{PROOF STRATEGY}\\
  We use DC sequentially:
    Step 1: Prove u >= 0 is invariant (using DI on a strong assumption:
            we need v >= 0 to be in the picture, but at u = 0 the
            argument works regardless of v as long as alpha? >= 0)
    Step 2: Cut: domain becomes UNIV Int \{u >= 0\}
    Step 3: Prove v >= 0 is invariant (symmetric)
    Step 4: Cut again: domain becomes \{u >= 0 and v >= 0\}


  As a first DC example, we instead prove a TRUE conservation-style
  property where DI works directly under a domain restriction:

  \textbf{CONSERVATION-STYLE PROPERTY:}\\
  Consider the ODE WITHOUT degradation (delta = 0):
   du/dt = alpha1 - beta*u*v
    dv/dt = alpha2 - beta*u*v

  Then alpha2*u - alpha1*v is conserved (Lie derivative cancels).

  We use DC to first establish the invariant alpha?*u - alpha?*v = c,
  then strengthen the domain to use this invariant in subsequent reasoning.
\<close>


paragraph \<open>Toggle switch: conservation in degradation-free form\<close>
text \<open>
  ODE:
    du/dt = alpha1 - beta*u*v
    dv/dt = alpha2 - beta*u*v

  CONSERVATION LAW (Lie derivative argument):
    d(alpha2*u - alpha1*v)/dt = alpha2*(alpha1 - beta*u*v) - alpha1*(alpha2 - beta*u*v)
                        = alpha2*alpha1 - alpha2*beta*u*v - alpha1*alpha2 + alpha1*beta*u*v
                        = (alpha1 - alpha2)*beta*u*v

  In the symmetric case alpha1 = alpha2 = alpha, the conservation is:
    d(u - v)/dt = (alpha - beta*u*v) - (alpha - beta*u*v) = 0

  So u(t) - v(t) = u(0) - v(0)  (the difference is preserved)
\<close>

lemma toggle_switch_difference_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> \<beta> :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                                      1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Symmetric toggle switch without degradation, u at position 0 and v at position 1:
         du/dt = alpha - beta*u*v;
         dv/dt = alpha - beta*u*v\<close>
  assumes iv: \<open>vec_nth (y 0) 0 - vec_nth (y 0) 1 = c\<close>
      \<comment> \<open>Initial difference: c = u(0) - v(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) 0 - vec_nth (y t) 1 = c\<close>
      \<comment> \<open>Conclusion: the difference u(t) - v(t) is preserved\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Sandwich u(t) - v(t) at c via two DI_Vect applications.
     
     The Lie derivative of u - v cancels:
     
         d(u - v)/dt = (\<alpha> - \<beta>\<sqdot>u\<sqdot>v) - (\<alpha> - \<beta>\<sqdot>u\<sqdot>v) = 0
     
     so both directions hold with the same derivative check.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the difference \<lambda>v. v₀ - v₁ *)
  have diff_deriv:
    \<open>((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative 
      (\<lambda>w. vec_nth w 0 - vec_nth w 1)) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
    by (intro has_derivative_diff has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: c \<le> u(t) - v(t)
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition c \<le> u(0) - v(0) *)
  have iv_ge: \<open>c \<le> vec_nth (y 0) 0 - vec_nth (y 0) 1\<close>
    using iv by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                       1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                       1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                        1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                        1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule diff_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: u(t) - v(t) \<le> c
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition u(0) - v(0) \<le> c *)
  have iv_le: \<open>vec_nth (y 0) 0 - vec_nth (y 0) 1 \<le> c\<close>
    using iv by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. c) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                       1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                       1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. c) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                        1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                        1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule diff_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     APPLY DI_Vect twice via antisym
     ------------------------------------------------------------------------ *)
  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close> and g = \<open>\<lambda>v. c\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. c\<close> and g = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


text \<open>
  Part 4: Using DC to derive a stronger invariant

  Now we demonstrate the DC pattern: USE the conservation law as a
  CUT to strengthen the domain, then derive further consequences.

  Suppose we additionally have the standing assumption u(0) = v(0) = u?.
  Then by the conservation law, u(t) = v(t) for all t (the difference
  c = 0 stays 0).

  Using DC, we strengthen the domain to \{(u,v). u = v\}, and within
  this domain the ODE simplifies to a 1-D system:
    du/dt = alpha - beta*u\textasciicircum{}2

  Now we can prove further invariants on this restricted system.
\<close>

text \<open>DC application: strengthen the domain to include the conservation invariant.\<close>
lemma toggle_switch_DC_strengthened_domain:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> \<beta> :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
                                      1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))
                                    )) {0..t} UNIV\<close>
  assumes iv_eq: \<open>vec_nth (y 0) 0 = vec_nth (y 0) 1\<close>
      \<comment> \<open>Symmetric initial condition: u(0) = v(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>(y solves_ode (\<lambda>t v.
            vec_lambda ((\<lambda>k. 0)(
              0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
              1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))
          )) {0..t} (UNIV \<inter> {v. vec_nth v 0 = vec_nth v 1})\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Apply DC with cut-formula C v \<equiv> (v₀ = v₁).
     
     DC requires two obligations:
       1. (y_sol) The trajectory solves the ODE on the original domain.
          This is passed directly from our assumption.
       2. (C_inv) For every \<tau> \<in> [0..t], the cut-formula holds at y(\<tau>), 
          i.e., vec_nth (y \<tau>) 0 = vec_nth (y \<tau>) 1.
     
     The C_inv obligation is discharged using 
     toggle_switch_difference_conservation: since u(0) = v(0) gives 
     initial difference c = 0, the preserved difference u(\<tau>) - v(\<tau>) 
     is also 0 for all \<tau>, i.e., u(\<tau>) = v(\<tau>).
     ========================================================================== *)

  (* PROOF OBLIGATION DC.1 (y_sol): passed directly from assumption *)

  (* PROOF OBLIGATION DC.2 (C_inv): u(\<tau>) = v(\<tau>) for all \<tau> \<in> [0..t].
     Proved by restricting y to {0..\<tau>} and invoking the difference 
     conservation lemma with initial difference c = 0. *)
  have C_inv: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) 0 = vec_nth (y \<tau>) 1\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>

    (* Restrict the ODE to {0..\<tau>} *)
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
        vec_lambda ((\<lambda>k. 0)(
          0 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1,
          1 := \<alpha> - \<beta> * vec_nth v 0 * vec_nth v 1))
        )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol h\<tau>] .

    (* Initial difference is 0 (from the symmetric initial condition) *)
    have iv0: \<open>vec_nth (y 0) 0 - vec_nth (y 0) 1 = 0\<close>
      using iv_eq by simp

    (* Apply the difference conservation lemma at time \<tau> *)
    have \<open>vec_nth (y \<tau>) 0 - vec_nth (y \<tau>) 1 = 0\<close>
      using h\<tau> toggle_switch_difference_conservation[OF y_sol_\<tau> iv0 ] by simp
    thus \<open>vec_nth (y \<tau>) 0 = vec_nth (y \<tau>) 1\<close> 
      by simp
  qed

  (* APPLY DC via forward reasoning *)
  show ?thesis
    using DC[OF y_sol _] C_inv 
    by auto
qed

                    

text \<open>
  SUMMARY: What we have achieved with DC

  We have:
\begin{enumerate}
\item Formalized the Differential Cut (DC) axiom of dDL in Isabelle/HOL
\item Demonstrated DC application on the symmetric toggle switch:
  - Used DI to prove the conservation law u(t) - v(t) = c
  - Used DC to strengthen the domain with this invariant
\item The strengthened solves\_ode predicate now carries the conservation
  law as part of the domain constraint, enabling further reasoning.
\end{enumerate}
\<close>


subsubsection \<open>Gardner genetic toggle switch\<close>

text \<open>
  CONTEXT
  The genetic toggle switch (Gardner, Cantor \& Collins, Nature 2000) is a
  landmark device in synthetic biology: the first synthetic, bistable,
  gene-regulatory network constructed in a living organism (E. coli). It
  is referenced in Section 3.4.5 of our biological computing survey and
  is considered a foundational primitive for cellular memory.

  The toggle switch consists of two genes encoding proteins that
  mutually repress each other's expression:

      Gene 1 -> Protein u stileturn Gene 2
      Gene 2 -> Protein v stileturn Gene 1

  Gardner et al. modeled the dynamics using Hill functions, which capture
  the cooperative nature of transcription-factor binding:

      du/dt = alpha1 / (1 + v\textasciicircum{}beta) - u
      dv/dt = alpha2 / (1 + u\textasciicircum{}gamma) - v
  where:
    alpha1, alpha2 are the maximal production rates of each protein
    beta, gamma   are the Hill coefficients (cooperativity exponents)
    u, v   are protein concentrations

  Each Hill term is a DECREASING function of the repressor concentration,
  capturing the fact that as repressor levels rise, target gene expression
  falls. The `1` term in the numerator represents linear degradation.

  \textbf{WHAT WE PROVE FORMALLY IN THIS FILE}\\
  THEOREM (Conditional Positivity of Protein u):

    If u(0) > 0, and the concentration v(tau) stays non-negative throughout
    the time interval [0, t], then u(t) > 0.

  In words: under mild assumptions, the concentration of protein u remains
  strictly positive , it never vanishes. This is a fundamental SAFETY
  PROPERTY of any chemical model: concentrations of existing species
  cannot become negative or zero in finite time.

  \textbf{WHY THIS MATTERS}\\
1. MODEL VALIDITY: For the Hill function alpha?/(1+v\textasciicircum{}beta) to be well-defined
  and well-behaved, we need v >= 0 (so that v\textasciicircum{}beta is non-negative and
  the denominator stays strictly positive). Proving that u stays
  positive given that v is non-negative is a building block for
  proving that BOTH concentrations stay positive , which certifies
  that the entire ODE model remains physically meaningful over time.

1. CORRECTNESS OF THE CIRCUIT: In the toggle switch, the two proteins
  represent two distinct stable states ("on" for u, "off" for v, or
  vice versa). If either protein concentration could reach zero,
  the circuit would lose information. Strict positivity means the
  system retains its state indefinitely.

1. FIRST FORMAL PROOF OF A HILL-FUNCTION PROPERTY: To the best of our
  knowledge, this is the first formally verified property of the
  Gardner et al. toggle switch using interactive theorem proving. It
  demonstrates that our dDL tooling scales from simple mass-action CRN
  examples to realistic gene regulatory network models involving
  rational functions.

  \textbf{PROOF METHOD , DIFFERENTIAL GHOST (DG)}\\
  We cannot prove u(t) > 0 by Differential Induction (DI) alone: the Lie
  derivative of u along the vector field includes the `-u` term, which
  is negative when u is positive. DI requires this derivative to be
  non-negative along the trajectory, which fails.

  Instead, we use the DIFFERENTIAL GHOST technique. We introduce a ghost
  variable g satisfying the linear ODE:

      g' = g / 2,    g(0) = 1 / surdu(0)

  (This is the same ghost trick we use for exponential decay and for
  CRN simple decay.) The key insight: consider the combined quantity

      I(u, g) = u * g\textasciicircum{}2

  Its Lie derivative along the EXTENDED vector field (u-dynamics plus
    g-dynamics) is:
        dI/dt = (du/dt) * g2 + u * 2g * (dg/dt)
              = (alpha1/(1+v\textasciicircum{}beta) - u) * g2 + u * 2g * (g/2)
              = alpha1/(1+v\textasciicircum{}beta) * g2 - u*g2 + u*g2
              = alpha1/(1+v\textasciicircum{}beta) * g2
    The `-u*g2` from the ODE and the `+u*g2` from the ghost CANCEL
    perfectly (this is DG magic!). The residual is:
        alpha1/(1+v\textasciicircum{}beta) * g2
    which is >= 0 provided:
      (a) alpha1 >= 0 (the production rate is non-negative - physically natural)
      (b) 1 + v\textasciicircum{}beta > 0 (the Hill denominator is positive)
      (c) g2 >= 0 (always true for real g)

  Condition (b) holds whenever v >= 0 and beta is a positive integer , which
  is exactly our assumption.

  Given that dI/dt >= 0 and I(0) = u(0) * g(0)\textasciicircum{}2 = u(0) * (1/surdu(0))\textasciicircum{}2 = 1,
  we conclude I(t) >= 1 for all t in [0, T]. Since g\textasciicircum{}2 >= 0, this means u*g\textasciicircum{}2 >= 1
  forces u > 0 (because if u <= 0, the product u*g\textasciicircum{}2 could not be >= 1).

   LIMITATION

  This theorem is CONDITIONAL: we require v(tau) >= 0 as an assumption. A
  fully unconditional theorem would instead prove:

      "If u(0) > 0 and v(0) >= 0, then u(t) > 0 for all t >= 0"

  The gap is that we cannot YET prove `v >= 0` is invariant using our
  current dDL tooling. Here is why, and what we plan to do about it:

  \textbf{THE TECHNICAL OBSTACLE}\\
  Our `DI\_Generic` (and its vector counterpart `DI\_Vect`) faithfully
  formalizes the STANDARD differential induction axiom of dDL. This axiom
  requires the Lie derivative of the candidate invariant to be >= 0
  EVERYWHERE ALONG THE TRAJECTORY, not just at the boundary.

  For the invariant `v >= 0`, the Lie derivative is:
      d(v - 0)/dt = alpha2/(1+u\textasciicircum{}gamma) - v
  This expression is NOT globally non-negative: when v is large, it
  becomes negative. Hence, standard DI cannot discharge the inductive
  step. The property `v >= 0` is only at risk on the BOUNDARY `v = 0`,
  where the Lie derivative reduces to `alpha2/(1+u\textasciicircum{}gamma) >= 0`, which IS
  non-negative. But standard DI cannot exploit this boundary structure.

  This is a well-known limitation in the original formulation of DI,
  not a defect of our formalization.
\<close>
lemma gardner_toggle_switch_u_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                      1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: u (protein 1), position 1: v (protein 2).
         Gardner toggle switch:
           du/dt = alpha1/(1 + v\textasciicircum{}beta) - u;
           dv/dt = alpha2/(1 + u\textasciicircum{}gamma) - v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) 0 > (0::real)\<close>
      \<comment> \<open>Initial condition: u(0) > 0 (protein 1 is initially present)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn: \<open>0 \<le> \<alpha>1\<close>
      \<comment> \<open>The production rate is non-negative, as is physically natural\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
      \<comment> \<open>The Hill coefficient is a positive integer\<close>
  \<comment> \<open>The conditional assumption, explained in the text above the lemma:\<close>
  assumes v_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) 1\<close>
      \<comment> \<open>Protein v stays non-negative along the trajectory.
         This assumption is discharged in
         gardner\_toggle\_switch\_u\_positive\_unconditional by applying
         gardner\_toggle\_switch\_v\_nonneg, which uses DI\_boundary.\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
    \<comment> \<open>Conclusion: protein u remains strictly positive at time t\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the apply-DG-then-apply-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y at position 2 satisfying 
                     dy/dt = (1/2)\<sqdot>y with initial value y(0) = 1/sqrt(u(0)). 
                     The combined trajectory ?z = x extended at index 2 
                     with y solves the extended ODE.
       
       STAGE 2 (DI): We prove the invariant 1 \<le> u \<sqdot> y² along the combined 
                     trajectory, via DI_Vect with h = 1 and g = u \<sqdot> y².
                     
                    Lie derivative:
                       d(u\<cdot>y\<^sup>2)/dt = (\<alpha>\<^sub>1/(1+v^\<beta>) - u)\<cdot>y\<^sup>2 + u\<cdot>2y\<cdot>(1/2\<cdot>y)
                                  = \<alpha>\<^sub>1/(1+v^\<beta>)\<cdot>y\<^sup>2 - u\<cdot>y\<^sup>2 + u\<cdot>y\<^sup>2
                                  = \<alpha>\<^sub>1/(1+v^\<beta>)\<cdot>y\<^sup>2
                                  \<ge> 0   (\<alpha>\<^sub>1 \<ge> 0, 1+v^\<beta> > 0 since v \<ge> 0)
                     
                     Note: the non-negativity of 1 + v^\<beta> requires v \<ge> 0, 
                     which is the conditional assumption v_nn.
       
       STAGE 3 (algebra): Since u \<sqdot> y² \<ge> 1 and y² \<ge> 0, we get u > 0.

     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 0)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.1 (x_sol): passed directly from assumption *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 2 is zero *)
  have gi_zero: 
   \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
          vec_lambda ((\<lambda>k::4. 0)(
                       0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                       1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v) 2 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 2 \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                  1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v =
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                  1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 2 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The vector field reads indices 0 and 1; neither is 2 *)
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    have v1: \<open>vec_nth v 1 = vec_nth w 1\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
            1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
            1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> w\<close>
      using v0 v1 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(2 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                   1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (2 := (1/2) * vec_nth v 2 + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = 2,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(2 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                   1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                vec_lambda
                 ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (2 := y \<tau>))\<close>

  (* Helper: Fréchet derivative of u \<sqdot> y² (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative 
      (\<lambda>v. vec_nth v 0 * (vec_nth p 2)^2 + 
           vec_nth p 0 * (2 * vec_nth p 2 * vec_nth v 2))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 2)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 2 * vec_nth v 2)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: Apply DI_Vect to prove the invariant 1 \<le> u \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> u(0) \<sqdot> y(0)² *)
  (* Since y(0) = 1/sqrt(u(0)), we have y(0)² = 1/u(0), so u(0)\<sqdot>y(0)² = 1 *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) 0 * (vec_nth (?z 0) 2)^2\<close>
    unfolding fun_upd_def
    using u0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(vectorfield) \<le> Dg(vectorfield).
     
     Here Dh = 0 and Dg (via product rule) evaluated at the extended vector field 
     gives, after cancellation of \<plusminus>u\<sqdot>y² terms, \<alpha>₁/(1 + v^\<beta>) \<sqdot> y² \<ge> 0 
     (using \<alpha>\<^sub>1\<ge> 0, v \<ge> 0 from v_nn, and y² \<ge> 0). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                           1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                        vec_lambda
                         ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                           1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                        vec_lambda
                         ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have v_nn_\<tau>: \<open>0 \<le> vec_nth (x \<tau>) 1\<close> using v_nn[OF \<tau>_in] .
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                            1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                         vec_lambda
                          ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha>1 / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                            1 := \<alpha>2 / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                         vec_lambda
                          ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 * (vec_nth (?z \<tau>) 2)^2 + 
                                      vec_nth (?z \<tau>) 0 * (2 * vec_nth (?z \<tau>) 2 * vec_nth v 2)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      using \<alpha>1_nn v_nn_\<tau>
      apply (metis comm_semiring_class.distrib diff_add_cancel 
                   mult_nonneg_nonneg zero_compare_simps(3) zero_le_divide_iff 
                   zero_le_power zero_le_square zero_less_one_class.zero_le_one)
      done
  qed

  (* APPLY DI_Vect: we get the invariant 1 \<le> u \<sqdot> y² at time t *)
  have ineq: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 2)^2\<close>
    using DI_Vect[where  h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2\<close>,
                  OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 0 = vec_nth (x t) 0\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 2)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 2)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 0 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed



text \<open>
  \textbf{WHAT WE HAVE ACCOMPLISHED}\\
  ACCOMPLISHED:
1. First formally verified property of the Gardner et al. toggle switch:
  strict positivity of protein u, conditional on v being non-negative.

\begin{enumerate}
\item Successful integration of Hill function derivatives with DG and DI\_Vect,
  demonstrating that our dDL tooling scales to realistic gene regulatory
  network models.
\item The proof pattern is reusable: the same structure applies to the
  symmetric argument for v (swapping the roles of u and v, and the
  coefficients alpha1/beta with alpha2/gamma).
\end{enumerate}
\<close>
text \<open>
  PART B: Non-negativity of v for the Gardner toggle switch (via DI\_boundary)
  We prove: if v(0) >= 0, alpha2 > 0, and gamma is a positive even Hill coefficient,
  then v(tau) >= 0 throughout the Gardner toggle switch trajectory.
  PROOF METHOD: Differential Induction with Boundary Condition (DI\_boundary).
  The candidate function is `invar(w) = vec\_nth w 1` (i.e., the v component).
\begin{itemize}
\item Differentiability assumption: invar is linear, so it's everywhere
  Frechet-differentiable with Dinvar = (lambdaw. vec\_nth w 1).
\item Boundary condition: at every point where v = 0 (i.e., vec\_nth (y tau) 1 = 0),
  we need 0 < Dinvar (f tau (y tau)) = vec\_nth (f tau (y tau)) 1.
\end{itemize}

    The Gardner ODE gives:
      vec\_nth (f tau (y tau)) 1 = alpha2/(1 + (vec\_nth (y tau) 0)\textasciicircum{}gamma) - vec\_nth (y tau) 1
                            = alpha2/(1 + (vec\_nth (y tau) 0)\textasciicircum{}gamma) - 0        (since v = 0)
                            = alpha2/(1 + u\textasciicircum{}gamma)

    Since alpha2 > 0 and 1 + u\textasciicircum{}gamma > 0 (because gamma is even, so u\textasciicircum{}gamma >= 0),
    the quotient is strictly positive.
\<close>

lemma gardner_toggle_switch_v_nonneg:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                      1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))
                                    )) {0..t} UNIV\<close>
  assumes v0_nn: \<open>0 \<le> vec_nth (x 0) 1\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>2_pos: \<open>0 < \<alpha>2\<close>
  assumes \<gamma>_even: \<open>even \<gamma>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>
  shows \<open>0 \<le> vec_nth (x t) 1\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Apply DI_boundary with  invar = \<lambda>w. vec_nth w 1
     
     DI_boundary establishes non-negativity of a funtion along the 
     trajectory, given that:
       1. (iv) The invariant is non-negative at the initial state.
       2. (ODE) The trajectory solves the ODE.
       3. (t) Time is non-negative.
       4. (invar_diff) The function is differentiable everywhere along 
          the trajectory.
       5. (boundary_step) Wherever the function equals zero, the Lie 
          derivative is STRICTLY positive (the trajectory points strictly 
          into the safe region).
     
     We discharge each obligation as a separate `have` statement, then 
     apply DI_boundary via forward reasoning at the bottom.
     
     BOUNDARY CONDITION: At v = 0, the Lie derivative is 
         dv/dt = \<alpha>2/(1 + u^\<gamma>) - v = \<alpha>2/(1 + u^\<gamma>) - 0 = \<alpha>2/(1 + u^\<gamma>) > 0
     since \<alpha>2 > 0 and 1 + u^\<gamma> > 0 (because \<gamma> is even, so u^\<gamma> \<ge> 0).
     This is precisely the strict positivity that DI_boundary needs.
     ========================================================================== *)

  (* PROOF OBLIGATION 1 (iv): initial condition 0 \<le> v(0) *)
  have iv: \<open>0 \<le> (\<lambda>w. vec_nth w 1) (x 0)\<close>
    using v0_nn by simp

  (* PROOF OBLIGATION 2 (ODE): directly from x_sol *)
  (* (no separate `have` needed; we pass x_sol directly) *)

  (* PROOF OBLIGATION 3 (t): directly from t *)
  (* (no separate `have` needed; we pass t directly) *)

  (* PROOF OBLIGATION 4 (invar_diff): invar is differentiable everywhere along x *)
  have invar_diff: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
                        \<exists> Dinvar. ((\<lambda>w. vec_nth w 1) has_derivative Dinvar) (at (x \<tau>))\<close>
  proof -
    fix \<tau> assume \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists> Dinvar. ((\<lambda>w. vec_nth w 1) has_derivative Dinvar) (at (x \<tau>))\<close>
      by (rule exI[where x = \<open>\<lambda>w. vec_nth w 1\<close>]) (rule has_derivative_vec_nth)
  qed

  (* PROOF OBLIGATION 5 (boundary_step): at v = 0, the Lie derivative is strictly positive.
     
     The Lie derivative is dv/dt = \<alpha>2/(1 + u^\<gamma>) - v. 
     When v = 0, this becomes \<alpha>2/(1 + u^\<gamma>), which is > 0 because 
     \<alpha>2 > 0 and the denominator is strictly positive (1 + u^\<gamma> > 0 
     when \<gamma> is even, so u^\<gamma> \<ge> 0). *)
  have boundary_step: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> (\<lambda>w. vec_nth w 1) (x \<tau>) = 0 \<Longrightarrow>
                           \<exists> Dinvar. ((\<lambda>w. vec_nth w 1) has_derivative Dinvar) (at (x \<tau>)) \<and>
                                     0 < Dinvar ((\<lambda>t v.
                                       vec_lambda ((\<lambda>k. 0)(
                                         0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                         1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> (x \<tau>))\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>
    assume v_eq_0: \<open>(\<lambda>w. vec_nth w 1) (x \<tau>) = 0\<close>
    hence v_zero: \<open>vec_nth (x \<tau>) 1 = 0\<close> by simp

    (* Use Dinvar = vec_nth \<sqdot> 1 *)
    have deriv: \<open>((\<lambda>w. vec_nth w 1) has_derivative (\<lambda>w. vec_nth w 1)) (at (x \<tau>))\<close>
      by (rule has_derivative_vec_nth)

    (* Compute Dinvar applied to the vector field *)
    let ?u = \<open>vec_nth (x \<tau>) 0\<close>
    have field_1: \<open>vec_nth ((\<lambda>t v.
        vec_lambda ((\<lambda>k. 0)(
          0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
          1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> (x \<tau>)) 1 = 
         \<alpha>2 / (1 + ?u^\<gamma>) - vec_nth (x \<tau>) 1\<close>
      by (simp add: fun_upd_def)
    also have \<open>... = \<alpha>2 / (1 + ?u^\<gamma>)\<close>
      using v_zero by simp
    finally have lie_val: 
              \<open>vec_nth ((\<lambda>t v.
                            vec_lambda ((\<lambda>k. 0)(
                              0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                              1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> (x \<tau>)) 1 =
                             \<alpha>2 / (1 + ?u^\<gamma>)\<close> .

    (* Show this is strictly positive *)
    have u_\<gamma>_nn: \<open>0 \<le> ?u^\<gamma>\<close>
      using \<gamma>_even by (simp add: zero_le_even_power)
    have denom_pos: \<open>0 < 1 + ?u^\<gamma>\<close>
      using u_\<gamma>_nn by linarith
    have lie_pos: \<open>0 < \<alpha>2 / (1 + ?u^\<gamma>)\<close>
      using \<alpha>2_pos denom_pos 
      by simp
    show \<open>\<exists> Dinvar. ((\<lambda>w. vec_nth w 1) has_derivative Dinvar) (at (x \<tau>)) \<and>
                    0 < Dinvar ((\<lambda>t v.
                      vec_lambda ((\<lambda>k. 0)(
                        0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                        1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> (x \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>w. vec_nth w 1\<close>])
      apply (rule conjI)
       apply (rule deriv)
      using lie_val lie_pos 
      apply simp
      done
  qed

  (* APPLY DI_boundary via forward reasoning *)
  have nn_at_t: \<open>0 \<le> (\<lambda>w. vec_nth w 1) (x t)\<close>
    using DI_boundary[where invar = \<open>\<lambda>w. vec_nth w 1\<close> and
                            f = \<open>\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                  1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))\<close> and
                            Q = UNIV,
                      OF iv x_sol t invar_diff boundary_step] .

  thus ?thesis 
    by simp
qed


text \<open>
  PART C: The unconditional Gardner toggle switch positivity theorem

  This upgrades gardner\_toggle\_switch\_u\_positive from conditional
  (assuming v(tau) >= 0 throughout) to UNCONDITIONAL (just assuming
  v(0) >= 0 and the parameter assumptions).

  \textbf{PROOF STRATEGY:}\\
\begin{enumerate}
\item Use gardner\_toggle\_switch\_v\_nonneg (from Part B) to establish
  v(tau) >= 0 for all tau in [0..t]. This requires:
  - alpha2 > 0
  - gamma even
  - gamma >= 1
  - v(0) >= 0
\item Feed this as the v\_nn assumption to gardner\_toggle\_switch\_u\_positive.
\item Conclude u(t) > 0 unconditionally.
\end{enumerate}

  The key observation: once we can prove v >= 0 via DI\_boundary, we have
  exactly what the conditional theorem needed. No DC required for this
  composition , we just apply the conditional theorem with the proven
  non-negativity.
\<close>
lemma gardner_toggle_switch_u_positive_unconditional:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)
                                                (0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                                 1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))
                                    )) {0..t} UNIV\<close>
  assumes u0_pos: \<open>vec_nth (x 0) 0 > (0::real)\<close>
  assumes v0_nn: \<open>0 \<le> vec_nth (x 0) 1\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn: \<open>0 \<le> \<alpha>1\<close>
  assumes \<alpha>2_pos: \<open>0 < \<alpha>2\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  assumes \<gamma>_even: \<open>even \<gamma>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
proof -
  (* Step 1: we prove 0 \<le> v(\<tau>) for all \<tau> \<in> [0..t] using gardner_toggle_switch_v_nonneg *)
  have v_nn_on_interval: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) 1\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have x_sol_\<tau>: \<open>(x solves_ode (\<lambda>t v.
                                     vec_lambda ((\<lambda>k. 0)
                                                 (0 := \<alpha>1 / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                                  1 := \<alpha>2 / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))
                                     )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF x_sol] \<tau>_in  .
    (* Apply gardner_toggle_switch_v_nonneg *)
    show \<open>0 \<le> vec_nth (x \<tau>) 1\<close>
      using \<tau>_in gardner_toggle_switch_v_nonneg[OF x_sol_\<tau> v0_nn _  \<alpha>2_pos \<gamma>_even \<gamma>_pos] 
      by simp
  qed
  (* Step 2: Apply the conditional theorem gardner_toggle_switch_u_positive *)
  show ?thesis
    using gardner_toggle_switch_u_positive[OF x_sol u0_pos t \<alpha>1_nn \<beta>_pos v_nn_on_interval] .
qed

text \<open>
  \textbf{SUMMARY OF THE UNCONDITIONAL RESULT}\\
  We have proved:
    THEOREM (Unconditional Strict Positivity for the Gardner Toggle Switch):

    For the Gardner et al. (Nature 2000) toggle switch ODE

        du/dt = alpha1 / (1 + v\textasciicircum{}beta) - u
        dv/dt = alpha2 / (1 + u\textasciicircum{}gamma) - v

    if:
\begin{itemize}
\item u(0) > 0  (protein u initially present)
\item v(0) >= 0  (protein v non-negative initially)
\item alpha1 >= 0  (non-negative production rate for u)
\item alpha2 > 0  (strictly positive production rate for v - required by the
  boundary argument)
\item beta >= 1, gamma >= 1  (positive Hill coefficients)
\item gamma is even  (standard for dimerizing repressors - matches Gardner
  et al.'s experimental parameters beta = gamma = 2)
\end{itemize}

    then u(t) > 0 for all t >= 0.
  \textbf{TECHNICAL CONTRIBUTIONS DEMONSTRATED:}\\
1. DI\_boundary (boundary-aware differential induction) enables the
  unconditional non-negativity proof. This is the first Isabelle/HOL
  formalization of a strengthened DI rule in the style of Platzer's
  barrier-certificate variants.

1. Hill function derivatives for EVEN Hill coefficients (without sign
  assumption on the regulator) provide the analytic machinery needed
  for gene regulatory network formalization.

1. The composition of DI\_boundary + the existing conditional theorem
  (via DG) shows that our dDL tooling supports MODULAR proof strategies:
  each rule handles a specific kind of argument, and they compose
  cleanly via shared trajectory objects.
\<close>

subsubsection \<open>Time-dependent Gardner toggle switch\<close>

text \<open>
  This section generalizes the Gardner toggle switch lemmas to allow
  TIME-DEPENDENT production rates alpha1(tau), alpha2(tau). This captures the
  experimental scenario where an inducer is added to the chemical bath,
  transiently changing the effective transcription rate of one of the
  genes and causing the switch to flip.

  \textbf{THE MODEL}\\
  The time-varying toggle switch ODE is:

      du/dt = alpha1(tau) / (1 + v\textasciicircum{}beta) - u
      dv/dt = alpha2(tau) / (1 + u\textasciicircum{}gamma) - v

  where alpha1, alpha2 :: real => real are continuous functions of time.

  \textbf{WHAT CHANGES FROM THE CONSTANT-RATE VERSION}\\
   LITTLE. The reasoning with DG  for u-positivity used the cancellation

      d(u*y\textasciicircum{}2)/dt = (alpha1/(1+v\textasciicircum{}beta) - u)*y\textasciicircum{}2 + u*2y*(y/2)
                 = alpha1/(1+v\textasciicircum{}beta)*y\textasciicircum{}2 - u*y\textasciicircum{}2 + u*y\textasciicircum{}2
                 = alpha1/(1+v\textasciicircum{}beta)*y\textasciicircum{}2

  which remains valid when alpha1 is replaced by alpha1(tau), giving
  alpha1(tau)/(1+v\textasciicircum{}beta)*y\textasciicircum{}2 , still non-negative provided alpha1(tau) >= 0 pointwise.

  Likewise, the reasoning with DI\_boundary for v >= 0 only needs alpha2(tau) > 0
  AT THE SPECIFIC TIMES tau where v(tau) = 0 (the boundary-crossing
  times). The cleanest sufficient condition is alpha2(tau) > 0 for all
  tau in [0..t].

  The continuity requirements on alpha1, alpha2 come from the ODE existence
  theory: the vector field (lambdat v. vec\_lambda ((lambdak. 0)(0 := alpha1(t)/... - v?,
  1 := alpha2(t)/... - v?))) must be continuous in t for the classical
  ODE theory we rely on. So we require alpha1, alpha2 to be continuous\_on \{0..t\}.

  \textbf{USING THE LEMMAS}\\
  To model an "induced switching experiment", instantiate alpha1 and alpha2
  with smooth time profiles. For example, a transient inducer pulse
  that drops alpha1 from a baseline alpha1\_high to a low value alpha1\_low and
  back could be modeled as a bump:

      alpha1(tau) = alpha1\_high - (alpha1\_high - alpha1\_low) * bump(tau, t\_start, t\_end, steepness)

  where `bump` is a continuous function that is 0 outside
  [t\_start, t\_end] and close to 1 inside. Piecewise-constant inducer
  signals (exact step functions) are not directly modeled here because
  they violate the continuity assumption , they naturally fit the
  compositional Hoare-logic approach instead.

  \textbf{WHAT THIS STILL DOES NOT PROVE}\\
  Positivity is a safety property , it says the system doesn't
  collapse regardless of how the rates are varied. It does NOT prove
  that changing alpha1(tau) actually causes the switch to flip to a
  different stable state; that would require basin-of-attraction
  analysis and Lyapunov stability reasoning (see the other proof leveraging
  the Lyapunov reachability rule). But the
  positivity guarantee is a necessary precondition for any meaningful
  switching behavior, and it holds under genuinely time-varying rates.
\<close>

lemma gardner_toggle_switch_u_positive_time_dependent:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: \<open>real \<Rightarrow> real\<close>
  fixes \<beta> \<gamma> :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>\<tau> v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                      1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Time-varying Gardner toggle switch:
           du/dt = alpha1(tau)/(1 + v\textasciicircum{}beta) - u;
           dv/dt = alpha2(tau)/(1 + u\textasciicircum{}gamma) - v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) 0 > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn_pointwise: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> \<alpha>1 \<tau>\<close>
      \<comment> \<open>The production rate for u is non-negative pointwise along the trajectory\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  \<comment> \<open>The conditional assumption: v stays non-negative\<close>
  assumes v_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) 1\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Same apply-DG-then-apply-DI pattern as the constant-rate version.
     
     STAGE 1 (DG): Ghost y at index 2 with dy/dt = (1/2)\<sqdot>y, y(0) = 1/\<surd>u(0).
     STAGE 2 (DI): Invariant 1 \<le> u\<sqdot>y². Lie derivative computation uses 
                   \<alpha>1(\<tau>)/(1+v^\<beta>)\<sqdot>y² \<ge> 0, which requires \<alpha>1(\<tau>) \<ge> 0 pointwise.
     STAGE 3 (algebra): From u\<sqdot>y² \<ge> 1 and y² \<ge> 0, conclude u > 0.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 0)\<close>

  (* ==========================================================================
     STAGE 1: We apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.1 (x_sol): passed directly from assumption *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 2 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>\<tau> v.
      vec_lambda ((\<lambda>k::4. 0)(
        0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
        1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v) 2 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index.
     Note: even though \<alpha>1, \<alpha>2 are functions of \<tau>, they depend only on \<tau> 
     (not on v), so the gi_fresh argument is unchanged: the vector field reads 
     vec_nth v 0 and vec_nth v 1 but not vec_nth v 2. *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 2 \<longrightarrow> vec_nth v i = vec_nth w i) 
                           \<Longrightarrow> (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                 1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v 
                              = (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
                                 1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 2 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    have v1: \<open>vec_nth v 1 = vec_nth w 1\<close> using eq by simp
    show \<open>(\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
            1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> v =
          (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha>1 \<tau> / (1 + (vec_nth v 1)^\<beta>) - vec_nth v 0,
            1 := \<alpha>2 \<tau> / (1 + (vec_nth v 0)^\<gamma>) - vec_nth v 1))) \<tau> w\<close>
      using v0 v1 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(2 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                   1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (2 := (1/2) * vec_nth v 2 + 0))))
         {0..t} UNIV)\<close>
    using DG[where 
            a = \<open>\<lambda>\<tau>. 1/2\<close> and 
            b = \<open>\<lambda>\<tau>. 0\<close> and 
            ?y0.0 = y0 and
            gi = 2,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(2 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                   1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                vec_lambda
                 ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(2 := y \<tau>))\<close>

  (* Helper: Fréchet derivative of u \<sqdot> y² *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative 
      (\<lambda>v. vec_nth v 0 * (vec_nth p 2)^2 + 
           vec_nth p 0 * (2 * vec_nth p 2 * vec_nth v 2))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 2)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 2 * vec_nth v 2)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> u \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> u(0) \<sqdot> y(0)² *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) 0 * (vec_nth (?z 0) 2)^2\<close>
    unfolding fun_upd_def
    using u0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect).
     
     Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives, after cancellation of \<plusminus>u\<sqdot>y² terms, \<alpha>1(\<tau>)/(1 + v^\<beta>) \<sqdot> y² \<ge> 0 
     (using \<alpha>1(\<tau>) \<ge> 0 from \<alpha>1_nn_pointwise, v \<ge> 0 from v_nn, and y² \<ge> 0). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                           1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                        vec_lambda
                         ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                           1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                        vec_lambda
                         ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    have \<alpha>1_\<tau>_nn: \<open>0 \<le> \<alpha>1 \<tau>\<close> using \<alpha>1_nn_pointwise[OF \<tau>_in_t] .
    have v_\<tau>_nn: \<open>0 \<le> vec_nth (x \<tau>) 1\<close> using v_nn[OF \<tau>_in_t] .
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                            1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                         vec_lambda
                          ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha>1 \<tau> / (1 + vec_nth v 1 ^ \<beta>) - vec_nth v 0,
                            1 := \<alpha>2 \<tau> / (1 + vec_nth v 0 ^ \<gamma>) - vec_nth v 1)) +
                         vec_lambda
                          ((\<lambda>i. 0)(2 := (1/2) * vec_nth v 2 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 0 * (vec_nth (?z \<tau>) 2)^2 + 
                                      vec_nth (?z \<tau>) 0 * (2 * vec_nth (?z \<tau>) 2 * vec_nth v 2)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      using \<alpha>1_\<tau>_nn v_\<tau>_nn
      apply (metis add_increasing2 diff_eq_eq distrib_right mult_nonneg_nonneg 
                   zero_le_divide_iff zero_le_power zero_le_square zero_less_one_class.zero_le_one)
      done
  qed

  (* We APPLY DI_Vect *)
  have ineq: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 2)^2\<close>
    using DI_Vect[where 
            h = \<open>\<lambda>v. 1\<close> and 
            g = \<open>\<lambda>v. vec_nth v 0 * (vec_nth v 2)^2\<close>,
            OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 0 = vec_nth (x t) 0\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 2)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 2)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 0 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

subsubsection \<open>Negative autoregulation\<close>

text \<open>
  CONTEXT
  Negative autoregulation is the simplest gene regulatory motif: a gene
  whose protein product represses its own expression. This is the
  foundational feedback loop in biology, appearing in \textasciitilde{}40\% of all known
  transcription networks.

  Reference: Uri Alon, "An Introduction to Systems Biology: Design
  Principles of Biological Circuits" (2006), Chapter 3.

  \textbf{THE ODE MODEL}\\
      du/dt = alpha / (1 + u\textasciicircum{}n) - beta*u

  where:
    alpha  is the maximal production rate (baseline promoter strength)
    beta  is the protein degradation rate
    n  is the Hill coefficient (cooperativity of the self-repression)
    u  is the protein concentration

  INTUITION
  When u is small, the Hill term alpha/(1+u\textasciicircum{}n) approx alpha is large -> rapid production.
  When u is large, the Hill term is small -> production slows while
  degradation beta*u continues. The system converges to a unique steady state.

  Negative autoregulation is used by cells to:
\begin{itemize}
\item Speed up response times (homeostasis)
\item Reduce cell-to-cell variability in protein levels
\item Provide robustness against fluctuations in alpha
\end{itemize}

  \textbf{PROPERTY TO VERIFY}\\
    If u(0) > 0, alpha >= 0, beta > 0, and n is a positive even integer,
    then u(t) > 0 for all t >= 0.

  In words: protein concentration remains strictly positive forever,
  provided the initial condition is positive.

  \textbf{PROOF METHOD , DIFFERENTIAL GHOST (DG)}\\
  This is the same proof pattern as our "production-decay" example
  (Example 12 in the CRN benchmark), just with the numerator alpha replaced
  by the Hill term alpha/(1+u\textasciicircum{}n). The Hill term is always >= 0 (since alpha >= 0
  and u\textasciicircum{}n >= 0 for even n), so the argument carries through unchanged.

  Ghost: g' = (beta/2)*g,  g(0) = 1/surdu(0)
  Invariant: u * g\textasciicircum{}2 >= 1
  Lie derivative:
    d(u*g\textasciicircum{}2)/dt = (du/dt)*g\textasciicircum{}2 + u*2g*(dg/dt)
               = (alpha/(1+u\textasciicircum{}n) - beta*u)*g\textasciicircum{}2 + u*2g*(beta/2*g)
               = alpha/(1+u\textasciicircum{}n)*g\textasciicircum{}2 - beta*u*g\textasciicircum{}2 + beta*u*g\textasciicircum{}2
               = alpha/(1+u\textasciicircum{}n)*g\textasciicircum{}2
               >= 0   (since alpha >= 0, 1+u\textasciicircum{}n > 0, g\textasciicircum{}2 >= 0)

  The beta*u*g\textasciicircum{}2 terms cancel (DG magic). The residual alpha/(1+u\textasciicircum{}n)*g\textasciicircum{}2 is
  non-negative. Hence u*g\textasciicircum{}2 >= 1 is invariant, which implies u > 0.

  NOTE ON DI\_boundary
  For negative autoregulation, DI\_boundary is NOT needed because the
  ODE has the clean -beta*u decay term that DG handles directly. DI\_boundary
  becomes necessary only when the decay structure is absent, non-uniform,
  or when we need non-negativity without strict positivity.

  This illustrates a design principle: our dDL proof rules offers multiple
  proof strategies, and the choice on how to apply them  depends on the ODE structure.
  DG is the shorter path for systems with uniform linear decay;
  DI\_boundary is the right tool for boundary-only invariants.
\<close>

lemma negative_autoregulation_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> \<beta> :: real
  fixes n :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: protein u. ODE: du/dt = alpha/(1 + u\textasciicircum{}n) - beta*u\<close>
  assumes u0_pos: \<open>vec_nth (x 0) 0 > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes \<beta>_pos: \<open>0 < \<beta>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the apply-DG-then-apply-DI pattern:
     
       STAGE 1 (DG): Introduce a ghost species y at position 1 satisfying 
                     dy/dt = (\<beta>/2)\<sqdot>y with initial value y(0) = 1/sqrt(u(0)). 
                     The combined trajectory ?z = x extended at index 1 
                     with y solves the extended ODE.
       
       STAGE 2 (DI): Prove the invariant 1 \<le> u \<sqdot> y\<^sup>2 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = u \<sqdot> y\<^sup>2.
                     
                     Lie derivative computation:
                       d(u\<sqdot>y\<^sup>2)/dt = (\<alpha>/(1+u\<^sup>n) - \<beta>\<sqdot>u)\<sqdot>y\<^sup>2 + u\<sqdot>2y\<sqdot>(\<beta>/2\<sqdot>y)
                                  = \<alpha>/(1+u\<^sup>n)\<sqdot>y\<^sup>2 - \<beta>\<sqdot>u\<sqdot>y\<^sup>2 + \<beta>\<sqdot>u\<sqdot>y\<^sup>2
                                  = \<alpha>/(1+u\<^sup>n)\<sqdot>y\<^sup>2
                                  \<ge> 0   (\<alpha> \<ge> 0, 1+u\<^sup>n > 0 for even n, y\<^sup>2 \<ge> 0)
       
       STAGE 3 (algebra): Since u \<sqdot> y\<^sup>2 \<ge> 1 and y\<^sup>2 \<ge> 0, we get u > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured as: each proof obligation is discharged as a 
     separate `have` statement, and the dDL axiom is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 0)\<close>

  (* ==========================================================================
     STAGE 1: we apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.1 (x_sol): the trajectory solves the ODE directly from x_sol *)
  (* (no separate `have` needed; we pass x_sol directly) *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. \<beta>/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. \<beta>/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 1 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::4. 0)(
        0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))) \<tau> v) 1 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 1 \<longrightarrow> vec_nth v i = vec_nth w i) 
                           \<Longrightarrow> (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))) \<tau> v 
                              = (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 1 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The field only reads index 0; not index 1 *)
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0))) \<tau> w\<close>
      using v0 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (\<beta>/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(1 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (1 := (\<beta>/2) * vec_nth v 1 + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. \<beta>/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = 1,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(1 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                vec_lambda
                 ((\<lambda>i. 0)(1 := (\<beta>/2) * vec_nth v 1 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (1:=y \<tau>))\<close>

  (* Helper: Frechet derivative of u \<sqdot> y\<^sup>2 (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative 
      (\<lambda>v. vec_nth v 0 * (vec_nth p 1)^2 + 
           vec_nth p 0 * (2 * vec_nth p 1 * vec_nth v 1))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 1)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 1 * vec_nth v 1)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> u \<sqdot> y\<^sup>2 along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> u(0) \<sqdot> y(0)\<^sup>2 *)
  (* Since y(0) = 1/sqrt(u(0)), we have y(0)\<^sup>2 = 1/u(0), so u(0) \<sqdot> y(0)\<^sup>2 = 1 *)
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using u0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + u\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even, with the 
     \<beta>\<sqdot>u\<sqdot>y\<^sup>2 terms canceling). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                        vec_lambda
                         ((\<lambda>i. 0)(1 := (\<beta>/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                        ((\<lambda>k. 0)
                         (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                       vec_lambda
                        ((\<lambda>i. 0)(1 := (\<beta>/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                         vec_lambda
                          ((\<lambda>i. 0)(1 := (\<beta>/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>))\<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 0)^n) - \<beta> * vec_nth v 0)) +
                        vec_lambda
                         ((\<lambda>i. 0)(1 := (\<beta>/2) * vec_nth v 1 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 0 * (vec_nth (?z \<tau>) 1)^2 + 
                                    vec_nth (?z \<tau>) 0 * (2 * vec_nth (?z \<tau>) 1 * vec_nth v 1)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) 0 ^ n) - \<beta> * vec_nth (x \<tau>) 0) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) 0 * (y \<tau> * (\<beta> * y \<tau>)) =
                          \<alpha> / (1 + vec_nth (x \<tau>) 0 ^ n) * (y \<tau> * y \<tau>)\<close>)
       prefer 2
       apply (simp add: algebra_simps)
      apply simp
      apply (rule divide_nonneg_nonneg)
       apply (simp add: \<alpha>_nn)
      using n_even 
      apply (simp add: zero_le_even_power)
      done
  qed

  (* WE APPLY DI_Vect: we get the invariant 1 \<le> u \<sqdot> y\<^sup>2 at time t *)
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 0 * (vec_nth v 1)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 0 = vec_nth (x t) 0\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 1)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 1)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 0 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed


subsubsection \<open>The repressilator (Elowitz \& Leibler 2000)\<close>

text \<open>
  CONTEXT
  The repressilator is the first synthetic biological clock , a
  three-gene ring oscillator where each gene represses the next,
  forming a negative feedback cycle that produces sustained oscillations.

  Elowitz \& Leibler built and characterized this in E. coli in 2000,
  alongside Gardner et al.'s toggle switch in the same year (Nature 403).
  Together these two constructs launched synthetic biology as a
  discipline: they demonstrated that simple mathematical models could
  predict and engineer non-trivial dynamical behavior in living cells.

  Reference: Elowitz, M.B. \& Leibler, S. "A synthetic oscillatory network
  of transcriptional regulators." Nature 403, 335-338 (2000).

  Referenced in Section 3.4.5 of our biological computing survey
  (Nag et al., 2026).

  \textbf{THE CIRCUIT}\\
      Gene u -> Protein u stileturn Gene v
      Gene v -> Protein v stileturn Gene w
      Gene w -> Protein w stileturn Gene u

  A ring of three repressive interactions. With the right parameters,
  no stable fixed point exists and the system oscillates , the three
  protein concentrations rise and fall in sequence, forming a
  phase-shifted trio.

  \textbf{THE ODE MODEL}\\
      du/dt = alpha / (1 + w\textasciicircum{}n) - u
      dv/dt = alpha / (1 + u\textasciicircum{}n) - v
      dw/dt = alpha / (1 + v\textasciicircum{}n) - w

  where:
    alpha  is the maximal protein production rate
    n  is the Hill coefficient (cooperativity)
    u, v, w  are the three protein concentrations

  For simplicity we use a symmetric model (same alpha and n for all three
  genes). The original Elowitz-Leibler paper uses this symmetric form
  for their theoretical analysis.

  \textbf{PROPERTY TO VERIFY}\\
  \textbf{STRICT POSITIVITY OF ALL THREE PROTEINS:}\\
    If u(0) > 0, v(0) > 0, w(0) > 0, alpha >= 0, and n is a positive even
    integer, then u(t) > 0, v(t) > 0, w(t) > 0 for all t >= 0.

  In words: once all three proteins are present, they all remain
  strictly positive forever. The repressilator never "turns off" any
  of its components in finite time.

  \textbf{PROOF METHOD , DIFFERENTIAL GHOST (DG), THREE INDEPENDENT COPIES}\\
  KEY OBSERVATION: With EVEN Hill coefficients, the positivity proof
  for each component is INDEPENDENT of the other components. The ring
  coupling disappears at the level of the positivity argument.

  For u-positivity:
    Ghost: g' = g/2,  g(0) = 1/surdu(0)
    Invariant: u*g\textasciicircum{}2 >= 1
    Lie derivative:
      d(u*g\textasciicircum{}2)/dt = (du/dt)*g\textasciicircum{}2 + u*2g*(dg/dt)
                 = (alpha/(1+w\textasciicircum{}n) - u)*g\textasciicircum{}2 + u*2g*(g/2)
                 = alpha/(1+w\textasciicircum{}n)*g\textasciicircum{}2 - u*g\textasciicircum{}2 + u*g\textasciicircum{}2
                 = alpha/(1+w\textasciicircum{}n)*g\textasciicircum{}2
                 >= 0   (since alpha >= 0, w\textasciicircum{}n >= 0 for even n, g\textasciicircum{}2 >= 0)

  CRUCIALLY: the Hill term alpha/(1+w\textasciicircum{}n) is always non-negative for even n,
  regardless of the sign of w. So we do NOT need to prove w >= 0 first.
  This is the same reason negative autoregulation works with DG alone.

  The proofs for v and w are symmetric.

  \textbf{FOR OSCILLATION, FUTURE WORK}\\
  Proving that the repressilator actually OSCILLATES (under certain
  parameters) requires machinery beyond our current tooling ,
  Poincar?-Bendixson theory, Hopf bifurcation analysis, or numerical
  phase portrait computations. We focus here on the simpler but
  still meaningful safety property of strict positivity, which
  certifies that the ODE model remains physically meaningful forever.
\<close>

text \<open>Lemma 1: positivity of u (ghost at position 3, witness u * g\textasciicircum{}2).\<close>
lemma repressilator_u_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                      1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                      2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: u, position 1: v, position 2: w.
         Ring: u is repressed by w, v by u, and w by v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) 0 > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) 0\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(u(0)). The combined 
                     trajectory ?z = x extended at index 3 with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant 1 \<le> u \<sqdot> y\<^sup>2 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = u \<sqdot> y\<^sup>2.
       
       STAGE 3 (algebra): Since u \<sqdot> y\<^sup>2 \<ge> 1 and y\<^sup>2 \<ge> 0, we get u > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, axiom on bottom" pattern: each obligation is discharged as a 
     separate `have` statement, and the dDL axiom is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 0)\<close>

  (* ==========================================================================
     STAGE 1: We apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (*PROOF OBLIGATION DG.1 (x_sol): the trajectory solves the ODE, directly from x_sol *)
  (* (no separate `have` needed; we pass x_sol directly) *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 3 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::4. 0)(
        0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
        1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
        2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v) 3 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                 1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                 2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v = 
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                 1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                 2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    have v1: \<open>vec_nth v 1 = vec_nth w 1\<close> using eq by simp
    have v2: \<open>vec_nth v 2 = vec_nth w 2\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
      using v0 v1 v2 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* WE APPLY DG: obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0) (3 := (1/2) * vec_nth v 3 + 0)))) {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and  ?y0.0 = y0 and gi = 3,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (3:=y \<tau>))\<close>

  (* Helper: Frechet derivative of u \<sqdot> y\<^sup>2 (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2) has_derivative 
      (\<lambda>v. vec_nth v 0 * (vec_nth p 3)^2 + 
           vec_nth p 0 * (2 * vec_nth p 3 * vec_nth v 3))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 0) has_derivative (\<lambda>v. vec_nth v 0)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 3)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 3 * vec_nth v 3)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> u \<sqdot> y\<^sup>2 along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> u(0) \<sqdot> y(0)\<^sup>2 *)
  (* Since y(0) = 1/sqrt(u(0)), we have y(0)\<^sup>2 = 1/u(0), so u(0) \<sqdot> y(0)\<^sup>2 = 1 *)
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using u0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + w\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                   Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 0 * (vec_nth (?z \<tau>) 3)^2 + 
                                   vec_nth (?z \<tau>) 0 * (2 * vec_nth (?z \<tau>) 3 * vec_nth v 3)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) 2 ^ n) - vec_nth (x \<tau>) 0) * (y \<tau> * y \<tau>) +
                           vec_nth (x \<tau>) 0 * (y \<tau> * y \<tau>) =
                          \<alpha> / (1 + vec_nth (x \<tau>) 2 ^ n) * (y \<tau> * y \<tau>)\<close>)
       prefer 2
       apply (simp add: algebra_simps)
      apply simp
      apply (rule divide_nonneg_nonneg)
       apply (simp add: \<alpha>_nn)
      using n_even 
      apply (simp add: zero_le_even_power)
      done
  qed

  (* WE APPLY DI_Vect: we get the invariant 1 \<le> u \<sqdot> y\<^sup>2 at time t *)
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 0 * (vec_nth v 3)^2\<close>,
                  OF    iv combined_sol induct_step t] .
  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 0 = vec_nth (x t) 0\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 3)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 0 * (vec_nth (?z t) 3)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 0 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Lemma 2: positivity of v (mirror argument, ghost at position 3).\<close>
lemma repressilator_v_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                      1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                      2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))
                                    )) {0..t} UNIV\<close>
  assumes v0_pos: \<open>vec_nth (x 0) 1 > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) 1\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove v(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(v(0)). The combined 
                     trajectory ?z = x extended at index 3 with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant 1 \<le> v \<sqdot> y\<^sup>2 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = v \<sqdot> y\<^sup>2.
       
       STAGE 3 (algebra): Since v \<sqdot> y\<^sup>2 \<ge> 1 and y\<^sup>2 \<ge> 0, we get v > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, axiom on bottom" pattern.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 1)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 3 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::4. 0)(
        0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
        1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
        2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v) 3 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                 1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                 2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v = 
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                 1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                 2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    have v1: \<open>vec_nth v 1 = vec_nth w 1\<close> using eq by simp
    have v2: \<open>vec_nth v 2 = vec_nth w 2\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
      using v0 v1 v2 
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (3 := (1/2) * vec_nth v 3 + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = 3,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (3:=y \<tau>))\<close>

  (* Helper: Frechet derivative of v \<sqdot> y\<^sup>2 (product rule) *)
  have vg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2) has_derivative 
      (\<lambda>v. vec_nth v 1 * (vec_nth p 3)^2 + 
           vec_nth p 1 * (2 * vec_nth p 3 * vec_nth v 3))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 1) has_derivative (\<lambda>v. vec_nth v 1)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 3)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 3 * vec_nth v 3)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> v \<sqdot> y\<^sup>2 along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> v(0) \<sqdot> y(0)\<^sup>2 *)
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using v0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + u\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 1 * (vec_nth (?z \<tau>) 3)^2 + 
                                    vec_nth (?z \<tau>) 1 * (2 * vec_nth (?z \<tau>) 3 * vec_nth v 3)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule vg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) 0 ^ n) - vec_nth (x \<tau>) 1) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) 1 * (y \<tau> * y \<tau>) =
                          \<alpha> / (1 + vec_nth (x \<tau>) 0 ^ n) * (y \<tau> * y \<tau>)\<close>)
       prefer 2
       apply (simp add: algebra_simps)
      apply simp
      apply (rule divide_nonneg_nonneg)
       apply (simp add: \<alpha>_nn)
      using n_even 
      apply (simp add: zero_le_even_power)
      done
  qed

  (* WE APPLY DI_Vect: we get the invariant 1 \<le> v \<sqdot> y\<^sup>2 at time t *)
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 1 * (vec_nth v 3)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From v(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude v(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) 1\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 1 = vec_nth (x t) 1\<close> by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) 3)^2\<close> by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) 1 * (vec_nth (?z t) 3)^2\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 1 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Lemma 3: positivity of w (mirror argument, ghost at position 3).\<close>
lemma repressilator_w_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>k. 0)(
                                     0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                     1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                     2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))
                                   )) {0..t} UNIV\<close>
  assumes w0_pos: \<open>vec_nth (x 0) 2 > (0::real)\<close>
  assumes t: \<open>t \<ge> 0\<close>
  assumes \<alpha>_nn: \<open>\<alpha> \<ge> 0\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows \<open>vec_nth (x t) 2 > (0::real)\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove W(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(W(0)). The combined 
                     trajectory ?z = x extended at index 3 with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant W \<sqdot> y² \<ge> 1 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = W \<sqdot> y².
       
       STAGE 3 (algebra): Since W \<sqdot> y² \<ge> 1 and y² \<ge> 0, we get W > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, axiom on bottom" pattern: each obligation is discharged as a 
     separate `have` statement, and the dDL axiom is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) 2)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.1 (x_sol): the trajectory solves the ODE \<emdash> directly from x_sol *)
  (* (no separate `have` needed; we pass x_sol directly) *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at index 3 is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::4. 0)(
        0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
        1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
        2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v) 3 = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 4) vec. (\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                  1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                  2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v =
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                  1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                  2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 4) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> 3 \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The field only reads indices 0, 1, 2; none of these is 3 *)
    have v0: \<open>vec_nth v 0 = vec_nth w 0\<close> using eq by simp
    have v1: \<open>vec_nth v 1 = vec_nth w 1\<close> using eq by simp
    have v2: \<open>vec_nth v 2 = vec_nth w 2\<close> using eq by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))) \<tau> w\<close>
      using v0 v1 v2 by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* WE APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (3 := (1/2) * vec_nth v 3 + 0))))
         {0..t} UNIV)\<close>
    using DG[where 
            a = \<open>\<lambda>\<tau>. 1/2\<close> and 
            b = \<open>\<lambda>\<tau>. 0\<close> and 
            ?y0.0 = y0 and
            gi = 3,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(3 := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                   1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                   2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                vec_lambda
                 ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (3:=y \<tau>))\<close>

  (* Helper: Frechet derivative of w \<sqdot> y\<^sup>2 (product rule) *)
  have wg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2) has_derivative 
      (\<lambda>v. vec_nth v 2 * (vec_nth p 3)^2 + 
           vec_nth p 2 * (2 * vec_nth p 3 * vec_nth v 3))) (at p)\<close>
    for p :: \<open>(real, 4) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v 2) has_derivative (\<lambda>v. vec_nth v 2)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v 3)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p 3 * vec_nth v 3)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: Apply DI_Vect to prove the invariant W \<sqdot> y\<^sup>2 \<ge> 1 along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> W(0) \<sqdot> y(0)\<^sup>2 *)
  (* Since y(0) = 1/sqrt(W(0)), we have y(0)\<^sup>2 = 1/W(0), so W(0) \<sqdot> y(0)\<^sup>2 = 1 *)
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using w0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + x\<^sub>1\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                           1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                           2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                        vec_lambda
                         ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                            1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                            2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2)) +
                         vec_lambda
                          ((\<lambda>i. 0)(3 := (1/2) * vec_nth v 3 + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 2 * (vec_nth (?z \<tau>) 3)^2 + 
                                    vec_nth (?z \<tau>) 2 * (2 * vec_nth (?z \<tau>) 3 * vec_nth v 3)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule wg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) 1 ^ n) - vec_nth (x \<tau>) 2) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) 2 * (y \<tau> * y \<tau>)
                        = \<alpha> / (1 + vec_nth (x \<tau>) 1 ^ n) * (y \<tau> * y \<tau>)\<close>)
       prefer 2
       apply (simp add: algebra_simps)
      apply simp
      apply (rule divide_nonneg_nonneg)
       apply (simp add: \<alpha>_nn)
      using n_even 
      apply (simp add: zero_le_even_power)
      done
  qed

  (* WE APPLY DI_Vect: we get the invariant W \<sqdot> y\<^sup>2 \<ge> 1 at time t *)
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v 2 * (vec_nth v 3)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From W(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude W(t) > 0
     ========================================================================== *)
  show \<open>vec_nth (x t) 2 > 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) 2 = vec_nth (x t) 2\<close> by simp
    have y_sq_nn: \<open>(vec_nth (?z t) 3)^2 \<ge> 0\<close> by simp
    have prod_ge_1: \<open>vec_nth (?z t) 2 * (vec_nth (?z t) 3)^2 \<ge> 1\<close>
      using ineq by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) 2 \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Main theorem: all three proteins stay strictly positive.\<close>
theorem repressilator_all_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<alpha> / (1 + (vec_nth v 2)^n) - vec_nth v 0,
                                      1 := \<alpha> / (1 + (vec_nth v 0)^n) - vec_nth v 1,
                                      2 := \<alpha> / (1 + (vec_nth v 1)^n) - vec_nth v 2))
                                    )) {0..t} UNIV\<close>
  assumes u0_pos: \<open>(0::real)< vec_nth (x 0) 0\<close>
  assumes v0_pos: \<open>(0::real) < vec_nth (x 0) 1\<close>
  assumes w0_pos: \<open>(0::real) < vec_nth (x 0) 2\<close>
  assumes t: \<open> 0 \<le> t \<close>
  assumes \<alpha>_nn: \<open> 0 \<le> \<alpha> \<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open> 1 \<le> n \<close>
  shows \<open>0 < vec_nth (x t) 0 \<and>  0 < vec_nth (x t) 1 \<and>  0 < vec_nth (x t) 2\<close>
proof (intro conjI)
  show \<open>0 < vec_nth (x t) 0\<close>
    using repressilator_u_positive[OF x_sol u0_pos t \<alpha>_nn n_even n_pos] .
  show \<open>0 < vec_nth (x t) 1\<close>
    using repressilator_v_positive[OF x_sol v0_pos t \<alpha>_nn n_even n_pos] .
  show \<open>0 < vec_nth (x t) 2\<close>
    using repressilator_w_positive[OF x_sol w0_pos t \<alpha>_nn n_even n_pos] .
qed


subsubsection \<open>Antithetic integral feedback (Briat et al.\ 2016)\<close>

text \<open>
  CONTEXT
  The antithetic integral feedback (AIF) motif is a biomolecular
  control scheme that implements integral feedback at the molecular
  level using a pair of species that annihilate each other. It was
  introduced by Briat, Gupta \& Khammash (Cell Systems, 2016) as the
  first rationally designed integral feedback control system for
  living cells.

  AIF is the molecular analog of integral feedback in control engineering:
  it provides ROBUST PERFECT ADAPTATION (RPA) , the ability of a
  biological system to return to a precise setpoint regardless of
  disturbances, and robustly to parameter variations.

  Reference: Briat, C., Gupta, A. \& Khammash, M. "Antithetic Integral
  Feedback Ensures Robust Perfect Adaptation in Noisy Biomolecular
  Networks." Cell Systems 2, 15-26 (2016).

  This motif is referenced in Section 3.4.6 of our biological
  computing survey (Nag et al., 2026).

  \textbf{THE CIRCUIT}\\
  Two "controller species" Z1, Z2 that stoichiometrically annihilate
  each other (\{\} <- Z1 + Z2), plus one "process species" X that is
  the controlled variable:

      \{\}        ->(mu)     Z1        (constant production of Z1 - setpoint)
      X        ->(theta)     Z2 + X    (Z2 produced at rate proportional to X)
      Z1 + Z2  ->(eta)     \{\}         (stoichiometric annihilation)

  Plus some dynamics for X (which we leave abstract as d*X terms).

  THE ODE MODEL (symmetric formulation)
      dZ1/dt = mu - eta * Z1 * Z2
      dZ2/dt = theta * X - eta * Z1 * Z2

  The X dynamics can be anything - biosensors, protein circuits, etc.
  The key observation is that the DIFFERENCE Z1 - Z2 encodes the
  \textbf{INTEGRAL OF THE TRACKING ERROR:}\\
      d(Z1 - Z2)/dt = (mu - eta*Z1*Z2) - (theta*X - eta*Z1*Z2)
                    = mu - theta*X
                    = theta * (mu/theta - X)
                    = theta * (X\_setpoint - X)

  The eta*Z1*Z2 annihilation terms CANCEL, leaving the tracking error.
  So Z1 - Z2 acts as the integrator of the error X\_setpoint - X.

  At steady state (when dZ1/dt = dZ2/dt = 0), the tracking error must
  be zero, forcing X = X\_setpoint = mu/theta. This is the ROBUST PERFECT
  ADAPTATION property.

  \textbf{WHAT WE PROVE}\\
  We verify the fundamental conservation-law property that makes AIF
  work: when the system IS at the setpoint (X(tau) = mu/theta for all tau in
  the interval), the difference Z1 - Z2 is CONSERVED.

  Formally:
    If X(tau) = mu/theta throughout [0..t], then Z1(t) - Z2(t) = Z1(0) - Z2(0).

  INTERPRETATION: at the setpoint, the controller's "integral state"
  (Z1 - Z2) is frozen - no further correction is needed because the
  tracking error is zero. This is precisely the behavior we'd expect
  from a perfect integral controller: it accumulates error when there
  is error, and stops accumulating when the error vanishes.

  \textbf{WHY THIS MATTERS FOR MANAGEMENT}\\
1. CONTROL-THEORETIC GRN PRIMITIVE: Unlike the toggle switch and
  repressilator (which use Hill-function gene regulation),
  antithetic integral feedback uses POLYNOMIAL dynamics with
  bimolecular annihilation. This demonstrates that our dDL tooling
  handles a QUALITATIVELY DIFFERENT class of GRN primitives.

1. BIOMOLECULAR IMPLEMENTATION OF CLASSICAL CONTROL: AIF is the
  first experimentally realized integral feedback control system
  in a living cell (by Aoki et al., Nature 2019, based on Briat
  et al.'s theoretical design). Our formal verification connects
  dDL reasoning to the control-theoretic analysis of synthetic
  biology.

1. SIMPLEST NON-TRIVIAL AIF INVARIANT: The conservation of Z1? - Z2?
  at setpoint is the foundational lemma for proving set-point
  tracking and robust perfect adaptation. More ambitious
  properties (convergence to the setpoint, disturbance rejection)
  would require Lyapunov or LaSalle machinery beyond our current
  tooling, but they BUILD ON this conservation-law foundation.

 \textbf{PROOF METHOD - DIFFERENTIAL INDUCTION (DI)}\\
  The proof is a textbook DI conservation argument, structurally
  identical to our CRN conservation laws. The Lie derivative of
  (Z1 - Z2) along the field is:

      d(Z1 - Z2)/dt = (mu - eta*Z1*Z2) - (theta*X - eta*Z1*Z2)
                    = mu - theta*X

  At the setpoint X = mu/theta, this becomes mu - theta*(mu/theta) = 0, so
  Z1 - Z2 is conserved.

  The setpoint hypothesis is a pointwise assumption `X(tau) = mu/theta`,
  which enters the proof via the DI\_Vect inductive step.
\<close>

lemma antithetic_integral_feedback_conservation:
  fixes x :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes \<mu>1 \<theta> \<eta> :: real
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                                      1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                                      2 := 0))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Position 0: Z1 (controller species, constant production);
         position 1: Z2 (controller species, X-proportional production);
         position 2: X (process species, held constant at the setpoint for simplicity)\<close>
  assumes iv: \<open>vec_nth (x 0) 0 - vec_nth (x 0) 1 = c\<close>
      \<comment> \<open>Initial integral state: c = Z1(0) - Z2(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<theta>_pos: \<open>0 < \<theta>\<close>
  assumes setpoint: \<open>vec_nth (x 0) 2 = \<mu>1 / \<theta>\<close>
      \<comment> \<open>X starts at the setpoint mu1/theta. Since dX/dt = 0 in this
         simplified model, X stays there; the proof establishes this first,
         as a separate conservation.\<close>
  shows \<open>vec_nth (x t) 0 - vec_nth (x t) 1 = c\<close>
      \<comment> \<open>Conclusion: the integral state Z1 - Z2 is conserved at the setpoint\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY
     
     This proof uses FIVE applications of DI_Vect, all structured with the 
     "obligations on top, axiom on bottom" pattern:
     
       PART A: Prove X(\<tau>) = \<mu>/\<theta> for all \<tau> \<in> [0..t]
         - Apply DI_Vect TWICE (one direction each) to sandwich X(\<tau>) at \<mu>/\<theta>
       
       PART B: Prove the main conservation Z\<^sub>1(t) - Z\<^sub>2(t) = c
         - Apply DI_Vect TWICE (one direction each) to sandwich 
           Z\<^sub>1(t) - Z\<^sub>2(t) at c
     
     Each DI_Vect application has its obligations (iv, induct_step) 
     discharged as separate `have` statements before the forward 
     application at the bottom.
     ========================================================================== *)

  (* ==========================================================================
     PART A: We establish X(\<tau>) = \<mu>/\<theta> for all \<tau> \<in> [0..t]
     ========================================================================== *)
  have X_constant: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (x \<tau>) 2 = \<mu>1 / \<theta>\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    
    (* Restrict the ODE to {0..\<tau>} *)
    have x_sol_\<tau>: \<open>(x solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>k. 0)(
                                     0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                                     1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                                     2 := 0))
                                   )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF x_sol] \<tau>_in .
    
    (* ------------------------------------------------------------------------
       SUB-PART A1: \<mu>/\<theta> \<le> X(\<tau>) via DI_Vect with h = \<mu>/\<theta>, g = X
       ------------------------------------------------------------------------ *)
    
    (* PROOF OBLIGATION A1.1 (iv): initial condition \<mu>/\<theta> \<le> X(0) *)
    have iv_up: \<open>(\<lambda>v. \<mu>1/\<theta>) (x 0) \<le> (\<lambda>v. vec_nth v 2) (x 0)\<close>
      using setpoint by simp

    (* PROOF OBLIGATION A1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
    have induct_step_up:
      \<open>\<And>\<tau>'. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dh) (at (x \<tau>')) \<and>
                   ((\<lambda>v. vec_nth v 2) has_derivative Dg) (at (x \<tau>')) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau>' (x \<tau>'))
                   \<le> Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau>' (x \<tau>'))\<close>
    proof -
      fix \<tau>' :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dh) (at (x \<tau>')) \<and>
                    ((\<lambda>v. vec_nth v 2) has_derivative Dg) (at (x \<tau>')) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau>' (x \<tau>')) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau>' (x \<tau>'))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 2\<close>])
        apply (rule conjI, rule has_derivative_const)
        apply (rule conjI, rule has_derivative_vec_nth)
        apply (auto simp: fun_upd_def)
        done
    qed

    (* WE APPLY DI_Vect for direction UP *)
    have up: \<open>\<mu>1/\<theta> \<le> vec_nth (x \<tau>) 2\<close>
      using DI_Vect[where  h = \<open>\<lambda>v. \<mu>1/\<theta>\<close> and g = \<open>\<lambda>v. vec_nth v 2\<close>,
                    OF iv_up x_sol_\<tau> induct_step_up] \<tau>_in by simp

    (* ------------------------------------------------------------------------
       SUB-PART A2: X(\<tau>) \<le> \<mu>/\<theta> via DI_Vect with h = X, g = \<mu>/\<theta>
       ------------------------------------------------------------------------ *)

    (* PROOF OBLIGATION A2.1 (iv): initial condition X(0) \<le> \<mu>/\<theta> *)
    have iv_down: \<open>(\<lambda>v. vec_nth v 2) (x 0) \<le> (\<lambda>v. \<mu>1/\<theta>) (x 0)\<close>
      using setpoint by simp

    (* PROOF OBLIGATION A2.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_down:
      \<open>\<And>\<tau>'. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. vec_nth v 2) has_derivative Dh) (at (x \<tau>')) \<and>
                   ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dg) (at (x \<tau>')) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau>' (x \<tau>')) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau>' (x \<tau>'))\<close>
    proof -
      fix \<tau>' :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 2) has_derivative Dh) (at (x \<tau>')) \<and>
                    ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dg) (at (x \<tau>')) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau>' (x \<tau>')) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau>' (x \<tau>'))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 2\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule conjI, rule has_derivative_vec_nth)
        apply (rule conjI, rule has_derivative_const)
        apply (auto simp: fun_upd_def)
        done
    qed

    (* WE APPLY DI_Vect for direction DOWN *)
    have down: \<open>vec_nth (x \<tau>) 2 \<le> \<mu>1/\<theta>\<close>
      using DI_Vect[where 
                    h = \<open>\<lambda>v. vec_nth v 2\<close> and 
                    g = \<open>\<lambda>v. \<mu>1/\<theta>\<close>,
                    OF iv_down x_sol_\<tau> induct_step_down] \<tau>_in by simp

    (* Sandwich: up and down give equality *)
    from up down show \<open>vec_nth (x \<tau>) 2 = \<mu>1/\<theta>\<close> by linarith
  qed

  (* ==========================================================================
     PART B: We prove the main conservation Z\<^sub>1(t) - Z\<^sub>2(t) = c
     
     Lie derivative of (Z\<^sub>1 - Z\<^sub>2):
       d(Z\<^sub>1 - Z\<^sub>2)/dt = (\<mu> - \<eta>\<sqdot>Z\<^sub>1\<sqdot>Z\<^sub>2) - (\<theta>\<sqdot>X - \<eta>\<sqdot>Z\<^sub>1\<sqdot>Z\<^sub>2)
                     = \<mu> - \<theta>\<sqdot>X
                     = \<mu> - \<theta>\<sqdot>(\<mu>/\<theta>)        (since X = \<mu>/\<theta>)
                     = 0
     
     The \<eta>\<sqdot>Z\<^sub>1\<sqdot>Z\<^sub>2 annihilation terms cancel, leaving the tracking error 
     \<mu> - \<theta>\<sqdot>X, which is zero at the setpoint.
     ========================================================================== *)
  show ?thesis
  proof -
    
    (* ------------------------------------------------------------------------
       SUB-PART B1: c \<le> Z\<^sub>1(t) - Z\<^sub>2(t) via DI_Vect with h = c, g = Z\<^sub>1 - Z\<^sub>2
       ------------------------------------------------------------------------ *)

    (* PROOF OBLIGATION B1.1 (iv): initial condition c \<le> Z\<^sub>1(0) - Z\<^sub>2(0) *)
    have iv_ge: \<open>(\<lambda>v. c) (x 0) \<le> (\<lambda>v. vec_nth v 0 - vec_nth v 1) (x 0)\<close>
      using iv by simp

    (* PROOF OBLIGATION B1.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_ge:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (x \<tau>)) \<and>
                   ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dg) (at (x \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau> (x \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau> (x \<tau>))\<close>
    proof -
      fix \<tau> :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (x \<tau>)) \<and>
                    ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dg) (at (x \<tau>)) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau> (x \<tau>)) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau> (x \<tau>))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>])
        apply (rule conjI, rule has_derivative_const)
        apply (rule conjI)
        apply (intro has_derivative_diff has_derivative_vec_nth)
        using X_constant[OF \<tau>_in] \<theta>_pos
        apply (auto simp: fun_upd_def field_simps)
        done
    qed

    (* ------------------------------------------------------------------------
       SUB-PART B2: Z\<^sub>1(t) - Z\<^sub>2(t) \<le> c via DI_Vect with h = Z\<^sub>1 - Z\<^sub>2, g = c
       ------------------------------------------------------------------------ *)

    (* PROOF OBLIGATION B2.1 (iv): initial condition Z\<^sub>1(0) - Z\<^sub>2(0) \<le> c *)
    have iv_le: \<open>(\<lambda>v. vec_nth v 0 - vec_nth v 1) (x 0) \<le> (\<lambda>v. c) (x 0)\<close>
      using iv by simp

    (* PROOF OBLIGATION B2.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_le:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dh) (at (x \<tau>)) \<and>
                   ((\<lambda>v. c) has_derivative Dg) (at (x \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau> (x \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                         2 := 0))) \<tau> (x \<tau>))\<close>
    proof -
      fix \<tau> :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v 0 - vec_nth v 1) has_derivative Dh) (at (x \<tau>)) \<and>
                    ((\<lambda>v. c) has_derivative Dg) (at (x \<tau>)) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau> (x \<tau>))
                    \<le> Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          0 := \<mu>1 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          1 := \<theta> * vec_nth v 2 - \<eta> * vec_nth v 0 * vec_nth v 1,
                          2 := 0))) \<tau> (x \<tau>))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule conjI)
        apply (intro has_derivative_diff has_derivative_vec_nth)
        apply (rule conjI, rule has_derivative_const)
        using X_constant[OF \<tau>_in] \<theta>_pos
        apply (auto simp: fun_upd_def field_simps)
        done
    qed
    (* WE APPLY DI_Vect for direction Z\<^sub>1(t) - Z\<^sub>2(t) \<le> c *)
    show ?thesis 
       by (auto intro!: antisym 
                        DI_Vect[where h = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close> and g = \<open>\<lambda>v. c\<close>,
                                OF iv_le x_sol induct_step_le t]
                        DI_Vect[where h = \<open>\<lambda>v. c\<close> and g = \<open>\<lambda>v. vec_nth v 0 - vec_nth v 1\<close>,
                                OF iv_ge x_sol induct_step_ge t]
          )
  qed
qed


subsubsection \<open>GRN benchmark summary\<close>

text \<open>
  |  \# | System                       | Property              | Method         |
  |----|------------------------------|-----------------------|----------------|
  |  1 | Gardner toggle switch (cond) | u(t) > 0              | DG + Hill      |
  |  2 | Gardner toggle switch (uncon)| u(t) > 0              | DG+DI\_bnd+Hill |
  |  3 | Negative autoregulation      | u(t) > 0              | DG + Hill-even |
  |  4 | Repressilator                | u,v,w > 0             | DG + Hill-even |
  |  5 | Antithetic integral feedback | Z? - Z? conserved    | DI (setpoint)  |

  \textbf{TAKING STOCK: WHAT WE HAVE}\\
  \textbf{CORE AXIOMS:}\\
\begin{itemize}
\item DI\_Generic, DI\_Vect       (standard differential induction)
\item DG, DG\_backward, DG\_elim  (differential ghost + derived rules)
\item DC                        (differential cut)
\item DI\_boundary              (boundary-aware DI , novel contribution)
\item linear\_ode\_solution       (FTC-based ghost trajectory construction)
\end{itemize}

  \textbf{HILL FUNCTION LIBRARY:}\\
\begin{itemize}
\item Scalar/Fr?chet/vector versions for x >= 0 (general Hill)
\item Scalar/Fr?chet/vector versions for even n (unconditional)
\end{itemize}

  \textbf{TECHNICAL HELPERS:}\\
\begin{itemize}
\item has\_real\_derivative\_pos\_inc\_right\_within
\item deriv\_pos\_right\_strict
\item solves\_ode\_subset\_ivl
\item assemble\_test, component\_sq\_has\_derivative, ...
\end{itemize}

  CRN BENCHMARK (12 examples):
    Conservation laws, strict positivity via DG

  GRN BENCHMARK (5 examples):
    Gene regulatory motifs from Gardner (toggle switch), Elowitz
    (repressilator), Alon (negative autoregulation), Briat et al.
    (antithetic integral feedback).
\<close>

subsection \<open>Benchmark on Programmable Biological Circuit\<close>
text \<open>
  Programmable Biological Circuit: Correctness of the min(x,y) CRN
  via DIRECT use of dDL axioms (DI, DC)

  CONTEXT
  This file demonstrates that dDL axioms can be used DIRECTLY to reason
  about the CORRECTNESS of computing chemical reaction networks. We take
  the min(x,y) CRN and prove three correctness properties, EACH OF WHICH
  uses a dDL axiom in the correctness layer (not just transitively through
  pre-proved invariants).

  \textbf{THE CRN}\\
      X + Y ->(k) Z
      d[X]/dt = -k * [X] * [Y]
      d[Y]/dt = -k * [X] * [Y]
      d[Z]/dt =  k * [X] * [Y]

  \textbf{PROPERTIES VERIFIED HERE}\\
  PROPERTY 1 , MONOTONIC PROGRESS  (uses DI\_Vect DIRECTLY)
    [Z](t) >= [Z](0) for all t >= 0.

    Interpretation: the output Z never decreases. This is the fundamental
    correctness property of any monotonic computation , once part of the
    answer has been computed, it is never lost.

    Proof method: a fresh DI\_Vect application with the invariant pair
    (h, g) = (constant Z(0), current Z value). The Lie derivative is
    d[Z]/dt = k*X*Y, which is >= 0 when k >= 0 and X, Y >= 0.

  PROPERTY 2 , BOUNDED OUTPUT  (uses conservation laws via DI\_Vect)
    [Z](t) <= min(x?, y?) for all t >= 0.

    Interpretation: the output never overshoots the correct answer.

    Proof method: algebraic consequence of crn\_min\_X\_conservation and
    crn\_min\_Y\_conservation (each proved with DI\_Vect).

  PROPERTY 3 , COMMITMENT  (uses DC DIRECTLY)
    If [Z](0) >= c, then we can strengthen the ODE's domain to enforce
    [Z] >= c throughout the trajectory.

    Interpretation: the output is COMMITTED , once Z has reached value c,
    it cannot fall back below c. This is the analog of write-once memory.

    Proof method: PROPERTY 1 gives monotonic progress, then DC strengthens
    the domain by adding the \{v. v\_2 >= c\} constraint. This is a direct
    application of the DC axiom in the correctness layer.

  PROPERTY 5 , EQUILIBRIUM CORRECTNESS  (algebraic on conservation laws)
    If at time t the system is at no-reaction equilibrium ([X]*[Y] = 0),
    then [Z](t) = min(x?, y?).

    Interpretation: IF the trajectory ever reaches a state where no more
    reactions can fire, THEN at that state the answer is exactly correct.
    Combined with the trajectory bounds (Properties 1-3), this gives:
    "the trajectory is consistent with computing min, and at any
    equilibrium it returns the correct value." Convergence (the system
    actually reaches equilibrium) is identified as future work.

    Proof method: case analysis on X = 0 or Y = 0, with each case
    discharged by linarith on the conservation laws and non-negativity.

  TOGETHER, these properties certify the min(x,y) CRN as a CORRECT-BY-
  DESIGN, MONOTONIC, COMMITTED computational primitive.

  \textbf{WHAT'S MISSING (FUTURE WORK)}\\
  CONVERGENCE: lim\_\{t->infinity\} [Z](t) = min(x?, y?).  Requires Lyapunov function
  analysis or LaSalle's invariance principle, beyond our current tooling.

  Even without convergence, the three properties give a meaningful
  trajectory-level correctness specification: the output is monotonic,
  bounded above by the correct answer, and committed once written.
\<close>


subsubsection \<open>Property 1: monotonic progress (direct use of DI\_Vect)\<close>

text \<open>
  We prove [Z](t) >= [Z](0) by a FRESH DI\_Vect application with:
    h(v) = vec\_nth (y 0) 2     (constant: the initial value of Z)
    g(v) = vec\_nth v 2          (current value of Z)

  Initial condition:  Z(0) <= Z(0)  trivially
  Lie derivative check:
    Dh(field) = 0
    Dg(field) = field[2] = k*X*Y
  Need: 0 <= k*X*Y, which holds when k >= 0 and X(tau), Y(tau) >= 0.

  Limitation: the non-negativity of X and Y along the trajectory
  (assumptions X\_nn\_along and Y\_nn\_along) is assumed here.
  Discharging it requires a non-strict variant of DI\_boundary,
  which is left for future work.
\<close>

lemma crn_min_Z_monotonic:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>i. 0)(
                                      0 := -k * vec_nth v 0 * vec_nth v 1,
                                      1 := -k * vec_nth v 0 * vec_nth v 1,
                                      2 :=  k * vec_nth v 0 * vec_nth v 1))
                                    )) {0..t} UNIV\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes k_nn: \<open>0 \<le> k\<close>
  \<comment> \<open>Non-negativity of X and Y along the trajectory is assumed; see the limitation stated above.\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) 1\<close>
  shows \<open>vec_nth (y 0) 2 \<le> vec_nth (y t) 2\<close>
proof -
  (* ==========================================================================
     PROOF STRATEGY: Apply DI_Vect with the invariant pair
       h = \<lambda>v. vec_nth (y 0) 2  (constant: initial value of Z)
       g = \<lambda>v. vec_nth v 2       (current value of Z)
     The conclusion h(y t) \<le> g(y t) unfolds to Z(0) \<le> Z(t), which is the 
     monotonicity claim.
     
     We discharge each proof obligation generated by  DI_Vect as a separate `have` statement, 
     then apply DI_Vect via forward reasoning at the bottom of the proof.
     ========================================================================== *)

  (* PROOF OBLIGATION 1 (iv): initial condition h(y 0) \<le> g(y 0), i.e., Z(0) \<le> Z(0) *)
  have iv: \<open>(\<lambda>v. vec_nth (y 0) 2) (y 0) \<le> (\<lambda>v. vec_nth v 2) (y 0)\<close>
    by simp

  (* PROOF OBLIGATION 2 (ODE): the trajectory solves the ODE , directly from y_sol *)
  (* (no separate `have` needed; we pass y_sol directly) *)

  (* PROOF OBLIGATION 3 (induct_step): at every \<tau> \<in> [0..t], there exist Fr\<eacute>chet 
     derivatives Dh, Dg of h and g such that Dh(field) \<le> Dg(field). 
     Here Dh = 0 (h is constant) and Dg = vec_nth \<sqdot> 2 (linear projection), 
     so Dg(field) = field[2] = k\<sqdot>X(\<tau>)\<sqdot>Y(\<tau>) \<ge> 0 by k_nn, X_nn_along, Y_nn_along. *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth (y 0) 2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       0 := -k * vec_nth v 0 * vec_nth v 1,
                       1 := -k * vec_nth v 0 * vec_nth v 1,
                       2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le> 
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       0 := -k * vec_nth v 0 * vec_nth v 1,
                       1 := -k * vec_nth v 0 * vec_nth v 1,
                       2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth (y 0) 2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v 2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        0 := -k * vec_nth v 0 * vec_nth v 1,
                        1 := -k * vec_nth v 0 * vec_nth v 1,
                        2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v 2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule has_derivative_vec_nth)
      using k_nn X_nn_along[OF \<tau>_in] Y_nn_along[OF \<tau>_in]
      apply (auto simp: fun_upd_def)
      done
  qed
  (* The conclusion of DI_Vect simplifies to the monotonicity claim *)
  show ?thesis 
   using DI_Vect[where h = \<open>\<lambda>v. vec_nth (y 0) 2\<close> and 
                       g = \<open>\<lambda>v. vec_nth v 2\<close>,
                 OF iv y_sol induct_step t] .
qed

text \<open>
  HELPER: Generalized monotonicity , Z(t1) <= Z(t2) for any t1 <= t2

  Generalizes crn\_min\_Z\_monotonic from "Z(t) >= Z(0)" to "Z(t1) <= Z(t2)
  for any 0 <= t1 <= t2 <= T".
\<close>

lemma crn_min_Z_monotonic_general:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
    and k :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..T} UNIV\<close>
    and t1_nn: \<open>0 \<le> t1\<close>
    and t1_le_t2: \<open>t1 \<le> t2\<close>
    and t2_le_T: \<open>t2 \<le> T\<close>
    and k_nn: \<open>k \<ge> 0\<close>
    and X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 0 \<ge> 0\<close>
    and Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 1 \<ge> 0\<close>
  shows \<open>vec_nth (y t1) 2 \<le> vec_nth (y t2) 2\<close>
proof -
  let ?y' = \<open>\<lambda>s. y (t1 + s)\<close>
  define t' where \<open>t' = t2 - t1\<close>
  
  have t'_nn: \<open>0 \<le> t'\<close> using t1_le_t2 by (simp add: t'_def)
  have t1_le_T: \<open>t1 \<le> T\<close> using t1_le_t2 t2_le_T by linarith

  (* The CRN ODE is time-invariant , the lambda body has no t *)
  have time_inv: 
    \<open>\<And>\<tau>1 \<tau>2 v. 
        (\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                            0 := -k * vec_nth v 0 * vec_nth v 1,
                            1 := -k * vec_nth v 0 * vec_nth v 1,
                            2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau>1 v = 
        (\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                            0 := -k * vec_nth v 0 * vec_nth v 1,
                            1 := -k * vec_nth v 0 * vec_nth v 1,
                            2 :=  k * vec_nth v 0 * vec_nth v 1))) \<tau>2 v\<close>
    by simp

  (* Apply solves_ode_shift to get the shifted trajectory *)
  have y'_sol: \<open>(?y' solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
                  0 := -k * vec_nth v 0 * vec_nth v 1,
                  1 := -k * vec_nth v 0 * vec_nth v 1,
                  2 :=  k * vec_nth v 0 * vec_nth v 1))
                  )) {0..(T - t1)} UNIV\<close>
    using solves_ode_shift[OF y_sol t1_nn t1_le_T time_inv] .

  (* Restrict the shifted trajectory to [0..t'] *)
  have t'_le: \<open>t' \<le> T - t1\<close> using t'_def t2_le_T by simp
  have y'_sol_t': \<open>(?y' solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
                   0 := -k * vec_nth v 0 * vec_nth v 1,
                   1 := -k * vec_nth v 0 * vec_nth v 1,
                   2 :=  k * vec_nth v 0 * vec_nth v 1))
                 )) {0..t'} UNIV\<close>
    using solves_ode_subset_ivl[OF y'_sol]  t'_nn t'_le by simp

  (* Non-negativity along the shifted trajectory follows from along [0..T] *)
  have X_nn_y': \<open>\<And>\<tau>. \<tau> \<in> {0..t'} \<Longrightarrow> vec_nth (?y' \<tau>) 0 \<ge> 0\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t'}\<close>
    hence \<open>t1 + \<tau> \<in> {0..T}\<close>
      using t1_nn t1_le_t2 t2_le_T t'_def by auto
    thus \<open>vec_nth (?y' \<tau>) 0 \<ge> 0\<close>
      using X_nn_along by simp
  qed
  have Y_nn_y': \<open>\<And>\<tau>. \<tau> \<in> {0..t'} \<Longrightarrow> vec_nth (?y' \<tau>) 1 \<ge> 0\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t'}\<close>
    hence \<open>t1 + \<tau> \<in> {0..T}\<close>
      using t1_nn t1_le_t2 t2_le_T t'_def by auto
    thus \<open>vec_nth (?y' \<tau>) 1 \<ge> 0\<close>
      using Y_nn_along by simp
  qed

  (* Apply the basic monotonicity lemma to the shifted trajectory *)
  have \<open>vec_nth (?y' t') 2 \<ge> vec_nth (?y' 0) 2\<close>
    using crn_min_Z_monotonic[OF y'_sol_t' t'_nn k_nn X_nn_y' Y_nn_y'] .

  (* Translate back: ?y' 0 = y t1 and ?y' t' = y (t1 + (t2 - t1)) = y t2 *)
  thus ?thesis by (simp add: t'_def)
qed
subsubsection \<open>Property 2: bounded output (conservation laws and algebra)\<close>

text \<open>
  The conservation laws (each proved with DI\_Vect) plus non-negativity
  give the upper bound algebraically.
\<close>

lemma crn_min_Z_upper_bound_via_DI:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
    and k x0 y0 :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..t} UNIV\<close>
    and iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
    and iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
    and t: \<open>t \<ge> 0\<close>
    and X_nn_t: \<open>vec_nth (y t) 0 \<ge> 0\<close>
    and Y_nn_t: \<open>vec_nth (y t) 1 \<ge> 0\<close>
  shows \<open>vec_nth (y t) 2 \<le> min x0 y0\<close>
proof -
  have X_cons: \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = x0\<close>
    using crn_min_X_conservation[OF y_sol iv_x t] .
  have Y_cons: \<open>vec_nth (y t) 1 + vec_nth (y t) 2 = y0\<close>
    using crn_min_Y_conservation[OF y_sol iv_y t] .
  
  have Z_le_x0: \<open>vec_nth (y t) 2 \<le> x0\<close>
    using X_nn_t X_cons by linarith
  have Z_le_y0: \<open>vec_nth (y t) 2 \<le> y0\<close>
    using Y_nn_t Y_cons by linarith
  
  show ?thesis
    using Z_le_x0 Z_le_y0 by simp
qed


subsubsection \<open>Property 3: commitment (direct use of DC)\<close>

text \<open>
  Once Z(0) >= c, we use DC to strengthen the ODE's domain so that the
  trajectory is constrained to \{v. vec\_nth v 2 >= c\}. This is the
  WRITE-ONCE / COMMITTED property: once the output crosses a threshold,
  it stays above that threshold , the computational analog of
  write-once memory.

  STANDALONE LEMMA: This is the only computing-CRN correctness property
  in the Programmable Biological Circuit section that uses DC directly.
  It is not bundled into crn\_min\_correctness\_full because its conclusion
  is a domain-restricted solves\_ode predicate (not a scalar inequality),
  which doesn't fit the conjunction shape of the bundled theorem. The
  scalar-trajectory consequence "for any c <= Z(0), every Z(tau) >= c on
  [0..T]" IS bundled into crn\_min\_correctness\_full as Property 3.

  \textbf{PROOF STRATEGY:}\\
\begin{enumerate}
\item Use PROPERTY 1 (monotonicity) at every tau in [0..t] to get
  Z(tau) >= Z(0) >= c.
\item Apply DC to lift this trajectory-pointwise invariant into
  a domain restriction on the ODE solution.
\end{enumerate}
\<close>

lemma crn_min_Z_committed_via_DC:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
    and k c :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..t} UNIV\<close>
    and t: \<open>t \<ge> 0\<close>
    and k_nn: \<open>k \<ge> 0\<close>
    and Z_init_at_c: \<open>vec_nth (y 0) 2 \<ge> c\<close>
    and X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) 0 \<ge> 0\<close>
    and Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) 1 \<ge> 0\<close>
  shows \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..t} (UNIV \<inter> {v. vec_nth v 2 \<ge> c})\<close>
proof -
  (* STEP 1: Use PROPERTY 1 (monotonicity) to establish Z(\<tau>) \<ge> c at every \<tau> *)
  have Z_at_c: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) 2 \<ge> c\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    (* WE restrict the ODE to {0..\<tau>} so we can apply monotonicity at \<tau> *)
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol \<tau>_in] .    
    (* We apply PROPERTY 1 (monotonicity) *)
    have \<open>vec_nth (y \<tau>) 2 \<ge> vec_nth (y 0) 2\<close>
      using crn_min_Z_monotonic[OF y_sol_\<tau>  ] k_nn \<tau>_in
      using assms(5) assms(6) atLeastAtMost_iff order_trans by auto
    thus \<open>vec_nth (y \<tau>) 2 \<ge> c\<close>
      using Z_init_at_c by linarith
  qed 
  (* STEP 2: DC strengthens the ODE's domain with the commitment invariant *)
  show ?thesis
    using Z_at_c DC[OF y_sol] 
    by simp
qed

subsubsection \<open>Property 4: equilibrium correctness\<close>

text \<open>
  This is the conditional steady-state result. It says: IF the trajectory
  ever reaches a state where no more reactions can fire (i.e., X*Y = 0),
  THEN at that state, the value of Z is exactly min(x0, y0).

  Note that this lemma does NOT prove the trajectory actually reaches
  equilibrium - that's the convergence question identified as future work.
  But it does close the "what is the answer at equilibrium?" question
  algebraically, completing the equilibrium-correctness side of the story.

  PROOF:
    The conservation laws give X + Z = x0 and Y + Z = y0.
    From X*Y = 0, either X = 0 or Y = 0:
      Case X = 0: Z = x0 from X+Z=x0; Y = y0-x0 from Y+Z=y0.
                  Y >= 0 forces x0 <= y0, so min(x0,y0) = x0 = Z.
      Case Y = 0: symmetric, gives min(x0,y0) = y0 = Z.

  \textbf{TOOLING USED:}\\
\begin{itemize}
\item crn\_min\_X\_conservation, crn\_min\_Y\_conservation (via DI\_Vect)
\item linarith and case analysis
\end{itemize}

  This is pure algebra on the conservation laws - dDL appears only
  transitively. The lemma's value is in providing the steady-state
  characterization that complements the trajectory-level properties
  (1, 2, 3) which use dDL directly.
\<close>

lemma crn_min_Z_equilibrium_correct:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
    and k x0 y0 :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..t} UNIV\<close>
    and iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
    and iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
    and t: \<open>t \<ge> 0\<close>
    and X_nn_t: \<open>vec_nth (y t) 0 \<ge> 0\<close>
    and Y_nn_t: \<open>vec_nth (y t) 1 \<ge> 0\<close>
    and equilibrium: \<open>vec_nth (y t) 0 * vec_nth (y t) 1 = 0\<close>
  shows \<open>vec_nth (y t) 2 = min x0 y0\<close>
proof -
  (* We apply the conservation laws (each proved via DI_Vect) *)
  have X_cons: \<open>vec_nth (y t) 0 + vec_nth (y t) 2 = x0\<close>
    using crn_min_X_conservation[OF y_sol iv_x t] .
  have Y_cons: \<open>vec_nth (y t) 1 + vec_nth (y t) 2 = y0\<close>
    using crn_min_Y_conservation[OF y_sol iv_y t] .
                      
  (* From X\<sqdot>Y = 0, either X = 0 or Y = 0 *)
  from equilibrium have \<open>vec_nth (y t) 0 = 0 \<or> vec_nth (y t) 1 = 0\<close>
    by simp

  thus ?thesis
  proof
    (* CASE: X = 0 *)
    assume X_zero: \<open>vec_nth (y t) 0 = 0\<close>
    from X_zero X_cons have Z_eq_x0: \<open>vec_nth (y t) 2 = x0\<close> by linarith
    from Z_eq_x0 Y_cons have Y_eq: \<open>vec_nth (y t) 1 = y0 - x0\<close> by linarith
    from Y_eq Y_nn_t have x0_le_y0: \<open>x0 \<le> y0\<close> by linarith
    from x0_le_y0 Z_eq_x0 show \<open>vec_nth (y t) 2 = min x0 y0\<close> by simp
  next
    (* CASE: Y = 0 (symmetric) *)
    assume Y_zero: \<open>vec_nth (y t) 1 = 0\<close>
    from Y_zero Y_cons have Z_eq_y0: \<open>vec_nth (y t) 2 = y0\<close> by linarith
    from Z_eq_y0 X_cons have X_eq: \<open>vec_nth (y t) 0 = x0 - y0\<close> by linarith
    from X_eq X_nn_t have y0_le_x0: \<open>y0 \<le> x0\<close> by linarith
    from y0_le_x0 Z_eq_y0 show \<open>vec_nth (y t) 2 = min x0 y0\<close> by simp
  qed
qed


text \<open>
  \textbf{WHAT THIS DEMONSTRATES - A PROOF MAP}\\
  Each correctness property is proved using dDL rules in the correctness
  layer (not just transitively through pre-proved invariants):

    PROPERTY 1 (monotonicity)     ->  fresh DI\_Vect application with new invariant
    PROPERTY 2 (upper bound)      ->  conservation laws + algebra (DI used)
    PROPERTY 3 (commitment)       ->  DC application (with PROPERTY 1 as a sub-lemma)
    PROPERTY 4 (combined spec)    ->  packages 1 and 2
    PROPERTY 5 (equilibrium correct) ->  algebra on conservation laws (DI used transitively)
  \textbf{THE COMPOSITIONAL PATTERN:}\\
  PROPERTY 3 (commitment) demonstrates the **DI-then-DC** compositional
  pattern: prove an invariant with DI, then use DC to lift it into a
  domain restriction. This is the same pattern as our
  toggle\_switch\_DC\_strengthened\_domain example, and it's the building
  block for modular reasoning about CRN compositions in future work.

  \textbf{WHAT'S MISSING (FUTURE WORK):}\\
1. CONVERGENCE: lim\_\{t->infinity\} Z(t) = min(x0, y0). Needs Lyapunov / LaSalle.

1. NON-NEGATIVITY ALONG THE TRAJECTORY: currently assumed. For the
  min(x,y) CRN, the boundary condition for DI\_boundary at X=0 is
  non-strict (Lie derivative = 0), so DI\_boundary doesn't apply.
  A non-strict variant of DI\_boundary would close this gap.
\<close>

subsubsection \<open>Property 5: asymptotic epsilon-convergence\<close>

text \<open>
  This example extends our correctness proof for the min(x,y) CRN with an
  epsilon-convergence theorem: for any epsilon > 0, the trajectory becomes epsilon-close
  to the correct answer min(x0, y0) within an explicit, computable time
  bound. This provides a finite-time convergence rate, strictly stronger
  than the conditional equilibrium correctness.

  CONTRIBUTION
  Together with the trajectory-level properties (monotonicity, upper bound,
  commitment) and the equilibrium characterization, this gives a NEAR-COMPLETE
  correctness story for the min(x,y) CRN:

     The output Z is monotonically non-decreasing       (PROPERTY 1, DI)
     The output Z is bounded above by min(x0, y0)       (PROPERTY 2, DI)
     Once Z reaches a value, it stays                   (PROPERTY 3, DC)
     At any equilibrium, Z = min(x0, y0)                (PROPERTY 4, algebra)
     For any epsilon > 0, Z reaches within epsilon of min in        (PROPERTY 5, FTC)
       finite time T(epsilon) = (min(x0,y0) - epsilon - Z(0)) / (k*epsilon2)

  PROPERTY 5 closes the gap left by PROPERTY 4: it doesn't just say
  "if you reach equilibrium, the answer is correct"; it says "you DO
  reach within epsilon of the answer within an explicit time bound, for any epsilon".

  \textbf{THE PROOF IDEA}\\
  By contradiction. Suppose Z(T) <= min(x0, y0) - epsilon.

  By monotonicity (PROPERTY 1), Z(tau) <= Z(T) <= min(x0, y0) - epsilon for all
  tau in \{0..T\}.

  By the conservation laws, X(tau) = x0 - Z(tau) >= x0 - (min(x0, y0) - epsilon) >= epsilon
  and Y(tau) >= epsilon.

  So the rate dZ/dtau = k*X*Y >= k*epsilon2 uniformly on \{0..T\}.

  By the fundamental theorem of calculus:
    Z(T) - Z(0) = integral0T (dZ/dtau) dtau >= k*epsilon2*T

  So Z(T) >= Z(0) + k*epsilon2*T.

  If T is large enough (specifically, T > (min(x0, y0) - epsilon - Z(0))/(k*epsilon2)),
  then Z(0) + k*epsilon2*T > min(x0, y0) - epsilon, contradicting Z(T) <= min(x0, y0) - epsilon.

  \textbf{TOOLING USED}\\
\begin{itemize}
\item PROPERTY 1 (monotonicity, via DI)
\item Conservation laws (via DI)
\item Fundamental theorem of calculus from HOL-Analysis
\item Integration bounds (integral\_le / integral\_mono)
\item linarith for the final arithmetic contradiction
\end{itemize}

  \textbf{WHAT THIS DOES NOT PROVE}\\
  The strict statement "lim\_\{t -> infinity\} Z(t) = min(x0, y0)" requires
  reformulating solves\_ode for the half-line [0, infinity), which is a separate
  piece of work. The epsilon-convergence proved here is mathematically equivalent
  for any practical purpose: it gives an explicit finite-time bound rather
  than an infinite-limit statement.
\<close>


lemma crn_min_Z_epsilon_convergence_via_axiom:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  assumes y_sol: 
         \<open>(y solves_ode (\<lambda>t v.
                           vec_lambda ((\<lambda>i. 0)(
                             0 := -k * vec_nth v 0 * vec_nth v 1,
                             1 := -k * vec_nth v 0 * vec_nth v 1,
                             2 :=  k * vec_nth v 0 * vec_nth v 1))
                           )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 0 \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 1 \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) 2) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) 2 > min x0 y0 - \<epsilon>\<close>
proof -
  have k_nn: \<open>k \<ge> 0\<close> using k_pos by simp
  have \<delta>_pos: \<open>0 < k * \<epsilon>^2\<close> using k_pos \<epsilon>_pos by simp

  (* Discharge `monotone` via the existing crn_min_Z_monotonic_general *)
  have below_final: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 2 \<le> vec_nth (y T) 2\<close>
    using crn_min_Z_monotonic_general[OF y_sol _ _ _ k_nn X_nn_along Y_nn_along]
    by auto

 \<comment> \<open>The vector field, bound once so it need not be repeated.
      Must match y\_sol's inline lambda EXACTLY.\<close>
  let ?F = \<open>\<lambda>(t::real) (v::(real,4) vec). vec_lambda ((\<lambda>i. 0)(
              0 := -k * vec_nth v 0 * vec_nth v 1,
              1 := -k * vec_nth v 0 * vec_nth v 1,
              2 :=  k * vec_nth v 0 * vec_nth v 1))\<close>

(* rate_below_target: when Z(\<tau>) \<le> min - \<epsilon>, conservation
     laws give X(\<tau>), Y(\<tau>) \<ge> \<epsilon>, so the rate k\<cdot>X\<cdot>Y \<ge> k\<cdot>\<epsilon>² *)
  have rate_below_target: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon> \<Longrightarrow>
         k * vec_nth (y \<tau>) 0 * vec_nth (y \<tau>) 1 \<ge> k * \<epsilon>^2\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close> and Z_low: \<open>vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon>\<close>
    then have \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_le: \<open>\<tau> \<le> T\<close> by auto
    
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
                                  vec_lambda ((\<lambda>i. 0)(
                                    0 := -k * vec_nth v 0 * vec_nth v 1,
                                    1 := -k * vec_nth v 0 * vec_nth v 1,
                                    2 :=  k * vec_nth v 0 * vec_nth v 1))
                                  )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol \<tau>_in] .

    have X_cons: \<open>vec_nth (y \<tau>) 0 + vec_nth (y \<tau>) 2 = x0\<close>
      using crn_min_X_conservation[OF y_sol_\<tau> iv_x \<tau>_nn] .
    have Y_cons: \<open>vec_nth (y \<tau>) 1 + vec_nth (y \<tau>) 2 = y0\<close>
      using crn_min_Y_conservation[OF y_sol_\<tau> iv_y \<tau>_nn] .

    have X_ge: \<open>vec_nth (y \<tau>) 0 \<ge> \<epsilon>\<close> using X_cons Z_low by linarith
    have Y_ge: \<open>vec_nth (y \<tau>) 1 \<ge> \<epsilon>\<close> using Y_cons Z_low by linarith

    show \<open>k * vec_nth (y \<tau>) 0 * vec_nth (y \<tau>) 1 \<ge> k * \<epsilon>^2\<close>
      using X_ge Y_ge k_pos \<epsilon>_pos
      by (simp add: mult_mono' power2_eq_square)
  qed
  \<comment> \<open>`induct\_step`:  The measure is the projection v |-> v\$2, whose
      Frechet derivative is itself (has\_derivative\_vec\_nth); the Lie
      derivative is then just the field's 2-component, namely k*X*Y.\<close>
  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
      \<exists> Dquant. ((\<lambda>v::(real,4) vec. vec_nth v 2) has_derivative Dquant) (at (y \<tau>)) \<and>
                (vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                 k * \<epsilon>^2 \<le> Dquant (?F \<tau> (y \<tau>)))\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>

    have deriv: \<open>((\<lambda>v::(real,4) vec. vec_nth v 2)
                   has_derivative (\<lambda>w. vec_nth w 2)) (at (y \<tau>))\<close>
      by (rule has_derivative_vec_nth)

    have rate: \<open>vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                k * \<epsilon>^2 \<le> vec_nth (?F \<tau> (y \<tau>)) 2\<close>
    proof
      assume below: \<open>vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon>\<close>
      have field_2: \<open>vec_nth (?F \<tau> (y \<tau>)) 2
                     = k * vec_nth (y \<tau>) 0 * vec_nth (y \<tau>) 1\<close>
        by (simp add: fun_upd_def)
      show \<open>k * \<epsilon>^2 \<le> vec_nth (?F \<tau> (y \<tau>)) 2\<close>
        using rate_below_target[OF h\<tau> below] field_2 
        by simp
    qed
    show \<open>\<exists> Dquant. ((\<lambda>v::(real,4) vec. vec_nth v 2) has_derivative Dquant) (at (y \<tau>)) \<and>
                (vec_nth (y \<tau>) 2 \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                 k * \<epsilon>^2 \<le> Dquant (?F \<tau> (y \<tau>)))\<close>
      using deriv rate 
      by blast
  qed

  show ?thesis
    using DI_convergence_rate[where
            quant  = \<open>\<lambda>v::(real,4) vec. vec_nth v 2\<close> and
            Ltarget = \<open>min x0 y0 - \<epsilon>\<close> and
            \<delta>      = \<open>k * \<epsilon>^2\<close> and
            T      = T,
            OF y_sol T_nn \<delta>_pos below_final induct_step T_large]
    by fastforce
qed

subsubsection \<open>Property 6: combined correctness specification\<close>

text \<open>
  The min(x,y) CRN is a CORRECT-BY-DESIGN computational primitive in the
  following formal sense:

     MONOTONIC PROGRESS:    Z(t) >= Z(0)              (PROPERTY 1, via DI)
     BOUNDED OUTPUT:        Z(t) <= min(x0, y0)        (PROPERTY 2, via DI conservation)
     COMMITTED OUTPUT:      Z(0) >= c ==> Z(t) >= c     (PROPERTY 3, via DI + DC; not bundled here)
     EQUILIBRIUM CORRECT:   X*Y = 0 ==> Z = min(x0,y0)  (PROPERTY 4, algebra)
     epsilon-CONVERGENCE:        T large ==> Z(T) > min - epsilon  (PROPERTY 5, FTC via DI\_convergence\_rate)

  Property 3 (commitment) is NOT bundled here because its conclusion is a
  domain-restricted solves\_ode predicate, not a scalar inequality, so it
  doesn't fit the same conjunction shape. It remains available as the
  separate lemma crn\_min\_Z\_committed\_via\_DC.

  This bundled specification gives a near-complete correctness story for
  the min(x,y) CRN: the trajectory is monotonic, bounded by the correct
  answer, equals the correct answer at any equilibrium, and provably
  converges to within epsilon of the correct answer in finite time.
\<close>

lemma crn_min_correctness_specification:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        0 := -k * vec_nth v 0 * vec_nth v 1,
        1 := -k * vec_nth v 0 * vec_nth v 1,
        2 :=  k * vec_nth v 0 * vec_nth v 1))
      )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 0 \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 1 \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) 2) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) 2 \<ge> vec_nth (y 0) 2 \<and>
         vec_nth (y T) 2 \<le> min x0 y0 \<and>
         (vec_nth (y T) 0 * vec_nth (y T) 1 = 0 \<longrightarrow> vec_nth (y T) 2 = min x0 y0) \<and>
         vec_nth (y T) 2 > min x0 y0 - \<epsilon>\<close>
proof (intro conjI impI)
  have k_nn: \<open>k \<ge> 0\<close> using k_pos by simp
  have X_nn_T: \<open>vec_nth (y T) 0 \<ge> 0\<close> using X_nn_along T_nn by auto
  have Y_nn_T: \<open>vec_nth (y T) 1 \<ge> 0\<close> using Y_nn_along T_nn by auto

  (* PROPERTY 1: monotonic progress *)
  show \<open>vec_nth (y T) 2 \<ge> vec_nth (y 0) 2\<close>
    using crn_min_Z_monotonic[OF y_sol T_nn k_nn X_nn_along Y_nn_along] .

  (* PROPERTY 2: bounded output *)
  show \<open>vec_nth (y T) 2 \<le> min x0 y0\<close>
    using crn_min_Z_upper_bound_via_DI[OF y_sol iv_x iv_y T_nn X_nn_T Y_nn_T] .

  (* PROPERTY 4: equilibrium correctness (conditional) *)
  assume equil: \<open>vec_nth (y T) 0 * vec_nth (y T) 1 = 0\<close>
  show \<open>vec_nth (y T) 2 = min x0 y0\<close>
    using crn_min_Z_equilibrium_correct[OF y_sol iv_x iv_y T_nn X_nn_T Y_nn_T equil] .

next
  (* PROPERTY 5: \<epsilon>-convergence *)
  show \<open>vec_nth (y T) 2 > min x0 y0 - \<epsilon>\<close>
    using crn_min_Z_epsilon_convergence_via_axiom[OF 
            y_sol iv_x iv_y T_nn k_pos \<epsilon>_pos X_nn_along Y_nn_along T_large] .
qed
text \<open>
   Combined correctness specification (5 properties)

  This theorem bundles ALL FIVE correctness properties of the min(x,y) CRN
  into a single statement. Unlike the scalar-only crn\_min\_correctness\_specification,
  this version also includes Property 3 (commitment) , a predicate-level fact
  about the ODE solution's domain restriction.

  Properties bundled:
     1: MONOTONIC PROGRESS    Z(T) >= Z(0)                  (DI)
     2: BOUNDED OUTPUT        Z(T) <= min(x0, y0)            (DI conservation)
     3: COMMITTED OUTPUT      ALLc. Z(0) >= c ==> ALLtauin[0..T]. Z(tau) >= c   (DI + DC)
     4: EQUILIBRIUM CORRECT   X(T)*Y(T) = 0 ==> Z(T) = min      (algebra)
     5: epsilon-CONVERGENCE         T large ==> Z(T) > min - epsilon      (DI\_convergence\_rate)

  Note that Property 3 here is stated in its scalar-trajectory form
  "the value Z(tau) stays >= c at every point in [0..T]". The full
  domain-restriction form (the strengthened solves\_ode predicate)
  remains available as the separate lemma crn\_min\_Z\_committed\_via\_DC.
\<close>

theorem crn_min_correctness_full:
  fixes y :: \<open>real \<Rightarrow> (real, 4) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda 
                                    ((\<lambda>i. 0)
                                     (0 := -k * vec_nth v 0 * vec_nth v 1,
                                      1 := -k * vec_nth v 0 * vec_nth v 1,
                                      2 :=  k * vec_nth v 0 * vec_nth v 1))
                                    )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) 0 + vec_nth (y 0) 2 = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) 1 + vec_nth (y 0) 2 = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 0 \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) 1 \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) 2) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) 2 \<ge> vec_nth (y 0) 2 \<and>
         vec_nth (y T) 2 \<le> min x0 y0 \<and>
         (\<forall>c. vec_nth (y 0) 2 \<ge> c \<longrightarrow> (\<forall>\<tau>\<in>{0..T}. vec_nth (y \<tau>) 2 \<ge> c)) \<and>
         (vec_nth (y T) 0 * vec_nth (y T) 1 = 0 \<longrightarrow> vec_nth (y T) 2 = min x0 y0) \<and>
         vec_nth (y T) 2 > min x0 y0 - \<epsilon>\<close>
proof (intro conjI impI ballI allI)
  have k_nn: \<open>k \<ge> 0\<close> using k_pos by simp
  have X_nn_T: \<open>vec_nth (y T) 0 \<ge> 0\<close> using X_nn_along T_nn by auto
  have Y_nn_T: \<open>vec_nth (y T) 1 \<ge> 0\<close> using Y_nn_along T_nn by auto

  (* PROPERTY 1: monotonic progress *)
  show \<open>vec_nth (y T) 2 \<ge> vec_nth (y 0) 2\<close>
    using crn_min_Z_monotonic[OF y_sol T_nn k_nn X_nn_along Y_nn_along] .

  (* PROPERTY 2: bounded output *)
  show \<open>vec_nth (y T) 2 \<le> min x0 y0\<close>
    using crn_min_Z_upper_bound_via_DI[OF y_sol iv_x iv_y T_nn X_nn_T Y_nn_T] .

  (* PROPERTY 3: commitment (scalar form) , for any c \<le> Z(0), every Z(\<tau>) \<ge> c.
     This is the trajectory-pointwise content of crn_min_Z_committed_via_DC. *)
  fix c :: real
  fix \<tau> :: real
  assume Z0_ge_c: \<open>vec_nth (y 0) 2 \<ge> c\<close>
  assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
  then have \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_le: \<open>\<tau> \<le> T\<close> 
         by auto
  have \<open>vec_nth (y \<tau>) 2 \<ge> vec_nth (y 0) 2\<close>
    using crn_min_Z_monotonic_general[OF y_sol order_refl \<tau>_nn \<tau>_le k_nn X_nn_along Y_nn_along] .
  thus \<open>vec_nth (y \<tau>) 2 \<ge> c\<close>
    using Z0_ge_c 
    by linarith

next
  (* PROPERTY 4: equilibrium correctness (conditional) *)
  have X_nn_T: \<open>vec_nth (y T) 0 \<ge> 0\<close> using X_nn_along T_nn 
    by auto
  have Y_nn_T: \<open>vec_nth (y T) 1 \<ge> 0\<close> using Y_nn_along T_nn 
    by auto
  assume equil: \<open>vec_nth (y T) 0 * vec_nth (y T) 1 = 0\<close>
  show \<open>vec_nth (y T) 2 = min x0 y0\<close>
    using crn_min_Z_equilibrium_correct[OF y_sol iv_x iv_y T_nn X_nn_T Y_nn_T equil] .

next
  (* PROPERTY 5: \<epsilon>-convergence *)
  show \<open>vec_nth (y T) 2 > min x0 y0 - \<epsilon>\<close>
    using crn_min_Z_epsilon_convergence_via_axiom[OF 
            y_sol iv_x iv_y T_nn k_pos \<epsilon>_pos X_nn_along Y_nn_along T_large] .
qed

end