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

\begin{verbatim}
    Reaction 1:  A + B  ->  2B    (rate k1)
    Reaction 2:  B + C  ->  2C    (rate k2)
    Reaction 3:  C + A  ->  2A    (rate k3)
\end{verbatim}

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

\begin{verbatim}
    d[A]/dt = -k1*[A]*[B] + k3*[C]*[A]
    d[B]/dt =  k1*[A]*[B] - k2*[B]*[C]
    d[C]/dt =  k2*[B]*[C] - k3*[C]*[A]
\end{verbatim}

  Each equation has two terms:
\begin{itemize}
\item A negative term: the species is consumed by one reaction
\item A positive term: the species is produced by another reaction
\end{itemize}

  This is a nonlinear system (products of concentrations appear on the
  right-hand side), which generally cannot be solved in closed form.

  \textbf{WHAT WE VERIFY}\\
  We formally prove the CONSERVATION LAW:

\begin{verbatim}
    [A](t) + [B](t) + [C](t) = [A](0) + [B](0) + [C](0)    for all t >= 0
\end{verbatim}

  This states that the TOTAL concentration of all species is preserved
  over time. Although individual concentrations oscillate, their sum
  remains constant. Physically, this means no matter is created or
  destroyed - every molecule of A consumed in a reaction produces exactly
  one molecule of B (or C), maintaining the total count.

  \textbf{WHY THIS MATTERS}\\
\begin{enumerate}
\item CORRECTNESS OF THE MODEL: Conservation of mass is a fundamental
  physical law. If the ODE model violates it, the model is wrong.
  Our proof certifies the model is physically consistent.
\item COMPILATION VERIFICATION: When compiling this CRN to DNA strand
  displacement circuits (as in the Nuskell compiler), the compiled
  implementation should also satisfy conservation. Our proof
  methodology can verify this.
\item SAFETY PROPERTY: The conservation law implies that concentrations
  stay bounded: no species can exceed the total initial concentration.
  This is a safety property - the system cannot "blow up."
\end{enumerate}

  \textbf{HOW WE VERIFY IT}\\
  We use DIFFERENTIAL INDUCTION (DI), a proof technique from Andre
  Platzer's Differential Dynamic Logic (dDL). The key idea:

  Instead of solving the ODE (which is impossible in closed form for
  this nonlinear system), we show that the DERIVATIVE of the invariant
  quantity [A]+[B]+[C] along the vector field is ZERO:

\begin{verbatim}
    d([A]+[B]+[C])/dt
      = d[A]/dt + d[B]/dt + d[C]/dt
      = (-k1*A*B + k3*C*A) + (k1*A*B - k2*B*C) + (k2*B*C - k3*C*A)
      = 0
\end{verbatim}

  Every term appears once with + and once with -, so they cancel perfectly.
  Since the derivative is zero and the quantity starts at total0, it
  remains at total0 forever. This is proved WITHOUT solving the ODE.

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [A](0) + [B](0) + [C](0) = total0
\item The time t >= 0
\item The rate constants k1, k2, k3 are arbitrary real numbers
  (the conservation law holds regardless of their values)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iA: concentration of A, i.e., [A]
\item Coordinate iB: concentration of B, i.e., [B]
\item Coordinate iC: concentration of C, i.e., [C]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iA := d[A]/dt, iB := d[B]/dt, iC := d[C]/dt))
\end{verbatim}

  The proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>


text \<open>Main theorem: conservation of the total concentration.\<close>
lemma crn_oscillator_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
      \<comment> \<open>y(t) = ([A](t), [B](t), [C](t))\<close>
  fixes k1 k2 k3 :: real
  fixes iA iB iC :: 'p
  assumes coords: \<open>iA \<noteq> iB\<close> \<open>iA \<noteq> iC\<close> \<open>iB \<noteq> iC\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v. 
                       vec_lambda ((\<lambda>k. 0)(
                         iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                         iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                         iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Oscillator ODE:
           d[A]/dt = -k1*[A]*[B] + k3*[C]*[A];
           d[B]/dt = k1*[A]*[B] - k2*[B]*[C];
           d[C]/dt = k2*[B]*[C] - k3*[C]*[A]\<close>
  assumes iv: \<open>vec_nth (y 0) iA + vec_nth (y 0) iB + vec_nth (y 0) iC = total0\<close>
      \<comment> \<open>Initially: [A](0) + [B](0) + [C](0) = total0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iA + vec_nth (y t) iB + vec_nth (y t) iC = total0\<close>
      \<comment> \<open>Conclusion: [A](t) + [B](t) + [C](t) = total0 for all t >= 0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC) has_derivative 
      (\<lambda>w. vec_nth w iA + vec_nth w iB + vec_nth w iC)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: total0 \<le> [A](t) + [B](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>total0 \<le> vec_nth (y 0) iA + vec_nth (y 0) iB + vec_nth (y 0) iC\<close>
    using iv
    by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                       iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                       iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                      \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                       iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                       iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                      \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                        iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                        iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                      \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                        iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                        iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                      \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + [B](t) + [C](t) \<le> total0
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iA + vec_nth (y 0) iB + vec_nth (y 0) iC \<le> total0\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                       iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                       iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                     \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                        iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                        iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                       \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                        iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                        iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                       \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + k3 * vec_nth v iC * vec_nth v iA,
                        iB :=  k1 * vec_nth v iA * vec_nth v iB - k2 * vec_nth v iB * vec_nth v iC,
                        iC :=  k2 * vec_nth v iB * vec_nth v iC - k3 * vec_nth v iC * vec_nth v iA))) 
                       \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC\<close> and 
                                   g = \<open>\<lambda>v. total0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. total0\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v iA + vec_nth v iB + vec_nth v iC\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

text \<open>
  We formally proved that the total concentration in an autocatalytic chemical oscillator
  is conserved, using differential induction, a technique that verifies properties of nonlinear
  ODE systems without solving them. This is the first step toward formally certified
  compilation of chemical reaction networks.

  \textbf{Chemical Reaction Network: Autocatalytic Oscillator}\\

  \textbf{Reactions:}\\
\begin{verbatim}
    A + B -> 2B    (rate k1)
    B + C -> 2C    (rate k2)
    C + A -> 2A    (rate k3)
\end{verbatim}
  \textbf{Mass-action ODEs:}\\
\begin{verbatim}
    d[A]/dt = -k1*[A]*[B] + k3*[C]*[A]
    d[B]/dt =  k1*[A]*[B] - k2*[B]*[C]
    d[C]/dt =  k2*[B]*[C] - k3*[C]*[A]
\end{verbatim}
  \textbf{Conservation law:}\\
\begin{verbatim}
    [A](t) + [B](t) + [C](t) = [A](0) + [B](0) + [C](0)
\end{verbatim}

  Proof method: DI\_Vect via antisymmetry (same structure as circular\_invariant).
  The Lie derivative of [A]+[B]+[C] along the vector field is:
\begin{verbatim}
    (-k1*A*B + k3*C*A) + (k1*A*B - k2*B*C) + (k2*B*C - k3*C*A) = 0
\end{verbatim}
\<close>

subsubsection \<open>Michaelis-Menten enzyme kinetics: conservation laws\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  Michaelis-Menten kinetics is the most fundamental model in enzymology,
  describing how enzymes catalyze biochemical reactions. Proposed by
  Leonor Michaelis and Maud Menten in 1913, it is the foundation for
  understanding drug metabolism, cellular signaling, and metabolic pathways.

  \textbf{THE CHEMICAL REACTIONS}\\
  An enzyme E binds reversibly to a substrate S to form an enzyme-substrate
  complex ES, which then irreversibly produces a product P and releases
  the enzyme:

\begin{verbatim}
           k1       k2
    E + S  <=>  ES  ->  E + P
           k-1
\end{verbatim}

  Where:
\begin{verbatim}
    k1  = binding rate (enzyme + substrate -> complex)
    km1 = unbinding rate (complex -> enzyme + substrate)
    k2  = catalytic rate (complex -> enzyme + product)
\end{verbatim}

  The enzyme acts as a catalyst: it facilitates the reaction but is
  regenerated at the end. The substrate is consumed and transformed
  into product.

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics, the concentrations evolve according to:

\begin{verbatim}
    d[E]/dt  = -k1*[E]*[S] + (km1 + k2)*[ES]
    d[S]/dt  = -k1*[E]*[S] + km1*[ES]
    d[ES]/dt =  k1*[E]*[S] - (km1 + k2)*[ES]
    d[P]/dt  =  k2*[ES]
\end{verbatim}

  This is a 4-species, nonlinear system (due to the k1*[E]*[S] terms).

  \textbf{WHAT WE VERIFY}\\
  We formally prove TWO conservation laws:
\begin{enumerate}
\item ENZYME CONSERVATION:
  [E](t) + [ES](t) = [E](0) + [ES](0)    for all t >= 0

  The total enzyme (free + bound) is constant. The enzyme is a
  catalyst: it participates in the reaction but is never consumed
  or created. This is the fundamental property that makes enzymes
  reusable.
\item SUBSTRATE CONSERVATION (mass balance):
  [S](t) + [ES](t) + [P](t) = [S](0) + [ES](0) + [P](0)    for all t >= 0

  The total amount of substrate-derived material is constant.
  Substrate is either free [S], bound in the complex [ES], or
  converted to product [P]. No matter is created or destroyed.
\end{enumerate}

  \textbf{WHY THIS MATTERS}\\
\begin{enumerate}
\item ENZYME CONSERVATION is the key assumption that enables deriving
  the Michaelis-Menten equation V = Vmax*[S]/(Km + [S]).
  Without it, the standard derivation is invalid.
\item SUBSTRATE CONSERVATION ensures the model respects physical law
  (conservation of mass). It also implies boundedness: no species
  concentration can exceed the total initial amount.
\item Both properties are assumed (often implicitly) in every textbook
  treatment of enzyme kinetics. Here we PROVE them from the ODEs.
\end{enumerate}

  \textbf{HOW WE VERIFY IT}\\
  Both conservation laws are proved using Differential Induction (DI),
  the same technique used for the CRN oscillator conservation law.

  \textbf{For enzyme conservation [E]+[ES]:}\\
\begin{verbatim}
    d([E]+[ES])/dt = d[E]/dt + d[ES]/dt
                   = (-k1*E*S + (km1+k2)*ES) + (k1*E*S - (km1+k2)*ES)
                   = 0
\end{verbatim}
  \textbf{For substrate conservation [S]+[ES]+[P]:}\\
\begin{verbatim}
    d([S]+[ES]+[P])/dt = d[S]/dt + d[ES]/dt + d[P]/dt
                       = (-k1*E*S + km1*ES) + (k1*E*S - (km1+k2)*ES) + k2*ES
                       = 0
\end{verbatim}

  \textbf{ASSUMPTIONS}\\
  Each proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [E](0) + [ES](0) = E\_total for enzyme
  conservation, and [S](0) + [ES](0) + [P](0) = S\_total for substrate
  conservation
\item The time t >= 0
\item The rate constants k1, km1, k2 are arbitrary real numbers
  (the conservation laws hold regardless of their values)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the four species as components of a state vector over an
  arbitrary finite index type 'p, at four pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iE: concentration of the free enzyme, i.e., [E]
\item Coordinate iS: concentration of the free substrate, i.e., [S]
\item Coordinate iES: concentration of the enzyme-substrate complex, i.e., [ES]
\item Coordinate iP: concentration of the product, i.e., [P]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iE := d[E]/dt, iS := d[S]/dt,
                              iES := d[ES]/dt, iP := d[P]/dt))
\end{verbatim}

  Each proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>



paragraph \<open>Conservation law 1: enzyme conservation, [E](t) + [ES](t) = E\_total\<close>

text \<open>
  The enzyme is a catalyst: it is neither created nor destroyed.
  The total enzyme concentration [E] + [ES] remains constant.

  \textbf{Lie derivative calculation:}\\
\begin{verbatim}
      d([E]+[ES])/dt
        = (-k1*[E]*[S] + (km1+k2)*[ES]) + (k1*[E]*[S] - (km1+k2)*[ES])
        = -k1*E*S + (km1+k2)*ES + k1*E*S - (km1+k2)*ES
        = 0
\end{verbatim}
\<close>

lemma michaelis_menten_enzyme_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
      \<comment> \<open>y(t) = ([E](t), [S](t), [ES](t), [P](t))\<close>
  fixes k1 km1 k2 :: real
      \<comment> \<open>k1: binding rate, km1: unbinding rate, k2: catalytic rate\<close>
  fixes iE iS iES iP :: 'p
  assumes coords: \<open>iE \<noteq> iS\<close> \<open>iE \<noteq> iES\<close> \<open>iE \<noteq> iP\<close>
                  \<open>iS \<noteq> iES\<close> \<open>iS \<noteq> iP\<close> \<open>iES \<noteq> iP\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                         iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                         iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                         iP :=  k2 * vec_nth v iES))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Michaelis-Menten ODE:
           d[E]/dt = -k1*[E]*[S] + (km1 + k2)*[ES];
           d[S]/dt = -k1*[E]*[S] + km1*[ES];
           d[ES]/dt = k1*[E]*[S] - (km1 + k2)*[ES];
           d[P]/dt = k2*[ES]\<close>
  assumes iv: \<open>vec_nth (y 0) iE + vec_nth (y 0) iES = E_total\<close>
      \<comment> \<open>Initially: [E](0) + [ES](0) = E\_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iE + vec_nth (y t) iES = E_total\<close>
      \<comment> \<open>Conclusion: [E](t) + [ES](t) = E\_total for all t >= 0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have enz_deriv:
    \<open>((\<lambda>v. vec_nth v iE + vec_nth v iES) has_derivative 
      (\<lambda>w. vec_nth w iE + vec_nth w iES)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: E_total \<le> [E](t) + [ES](t)
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition E_total \<le> [E](0) + [ES](0) *)
  have iv_ge: \<open>E_total \<le> vec_nth (y 0) iE + vec_nth (y 0) iES\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. E_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iE + vec_nth v iES) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. E_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iE + vec_nth v iES) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                      iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                      iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                      iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                      iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iE + vec_nth v iES\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule enz_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [E](t) + [ES](t) \<le> E_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iE + vec_nth (y 0) iES \<le> E_total\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iE + vec_nth v iES) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. E_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close> 
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iE + vec_nth v iES) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. E_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iE + vec_nth v iES\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule enz_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iE + vec_nth v iES\<close> and g = \<open>\<lambda>v. E_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. E_total\<close> and g = \<open>\<lambda>v. vec_nth v iE + vec_nth v iES\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

paragraph \<open>Conservation law 2: substrate conservation, [S](t) + [ES](t) + [P](t) = S\_total\<close>

text \<open>
  The substrate is transformed but not destroyed: it is either free [S],
  bound in the complex [ES], or converted to product [P].

  \textbf{Lie derivative calculation:}\\
\begin{verbatim}
    d([S]+[ES]+[P])/dt = d[S]/dt + d[ES]/dt + d[P]/dt
                       = (-k1*E*S + km1*ES) + (k1*E*S - (km1+k2)*ES) + k2*ES
                       = -k1*E*S + km1*ES + k1*E*S - km1*ES - k2*ES + k2*ES
                       = 0
\end{verbatim}
\<close>
lemma michaelis_menten_substrate_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k1 km1 k2 :: real
  fixes iE iS iES iP :: 'p
  assumes coords: \<open>iE \<noteq> iS\<close> \<open>iE \<noteq> iES\<close> \<open>iE \<noteq> iP\<close>
                  \<open>iS \<noteq> iES\<close> \<open>iS \<noteq> iP\<close> \<open>iES \<noteq> iP\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                         iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                         iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                         iP :=  k2 * vec_nth v iES))
                       )) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (y 0) iS + vec_nth (y 0) iES + vec_nth (y 0) iP = S_total\<close>
      \<comment> \<open>Initially: [S](0) + [ES](0) + [P](0) = S\_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iS + vec_nth (y t) iES + vec_nth (y t) iP = S_total\<close>
      \<comment> \<open>Conclusion: [S](t) + [ES](t) + [P](t) = S\_total for all t >= 0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have sub_deriv:
    \<open>((\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP) has_derivative 
      (\<lambda>w. vec_nth w iS + vec_nth w iES + vec_nth w iP)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: S_total \<le> [S](t) + [ES](t) + [P](t)
     ------------------------------------------------------------------------ *)

  (*PROOF OBLIGATION 1.1 (iv): initial condition S_total \<le> [S](0) + [ES](0) + [P](0) *)
  have iv_ge: \<open>S_total \<le> vec_nth (y 0) iS + vec_nth (y 0) iES + vec_nth (y 0) iP\<close>
    using iv
    by simp

  (*PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. S_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. S_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sub_deriv)
      apply (auto simp: fun_upd_def)
      apply argo
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [S](t) + [ES](t) + [P](t) \<le> S_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iS + vec_nth (y 0) iES + vec_nth (y 0) iP \<le> S_total\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. S_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                      iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                      iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                      iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                      iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. S_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                        iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                        iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                        iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iE := -k1 * vec_nth v iE * vec_nth v iS + (km1 + k2) * vec_nth v iES,
                       iS := -k1 * vec_nth v iE * vec_nth v iS + km1 * vec_nth v iES,
                       iES :=  k1 * vec_nth v iE * vec_nth v iS - (km1 + k2) * vec_nth v iES,
                       iP :=  k2 * vec_nth v iES))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sub_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      apply argo
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP\<close> and 
                                   g = \<open>\<lambda>v. S_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. S_total\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v iS + vec_nth v iES + vec_nth v iP\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed
subsubsection \<open>SIR epidemic model: population conservation\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The SIR model is one of the most fundamental models in epidemiology,
  proposed by Kermack and McKendrick in 1927. It divides a population
  into three compartments:
\begin{itemize}
\item S = Susceptible (healthy, can become infected)
\item I = Infected (can spread the disease)
\item R = Recovered (immune, no longer infectious)
\end{itemize}

  \textbf{THE CHEMICAL REACTIONS}\\
  Read as a chemical reaction network, the model has two reactions:

\begin{verbatim}
    S + I -> 2I    (infection: an S meets an I and becomes I)
    I -> R         (recovery: an I becomes R)
\end{verbatim}

  Where beta = infection rate, gamma = recovery rate.

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics:

\begin{verbatim}
    d[S]/dt = -beta*[S]*[I]
    d[I]/dt =  beta*[S]*[I] - gamma*[I]
    d[R]/dt =  gamma*[I]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
  Population conservation: [S](t) + [I](t) + [R](t) = N  for all t >= 0

  The total population is constant: species move between compartments
  but are neither created nor destroyed.

  \textbf{WHY THIS MATTERS}\\
  Conservation is the basic consistency check of the model: the two
  reactions only move mass between S, I and R, so an ODE model that
  changed the total would be wrong.  The law also bounds each of [S], [I]
  and [R] by N while all three are non-negative, and it allows eliminating
  [R] = N - [S] - [I], the usual first step in analyzing the epidemic.

  \textbf{HOW WE VERIFY IT}\\
  We use Differential Induction (DI), as for the CRN oscillator: the Lie
  derivative of [S]+[I]+[R] along the vector field is zero:

\begin{verbatim}
    d([S]+[I]+[R])/dt = (-beta*S*I) + (beta*S*I - gamma*I) + (gamma*I)
                      = -beta*S*I + beta*S*I - gamma*I + gamma*I
                      = 0
\end{verbatim}

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [S](0) + [I](0) + [R](0) = N
\item The time t >= 0
\item The rates beta, gamma are arbitrary real numbers
  (the conservation law holds regardless of their values)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iS: concentration of S, i.e., [S]
\item Coordinate iI: concentration of I, i.e., [I]
\item Coordinate iR: concentration of R, i.e., [R]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iS := d[S]/dt, iI := d[I]/dt, iR := d[R]/dt))
\end{verbatim}

  The proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>
lemma sir_population_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes beta gamma :: real
      \<comment> \<open>beta: infection rate, gamma: recovery rate\<close>
  fixes iS iI iR :: 'p
  assumes coords: \<open>iS \<noteq> iI\<close> \<open>iS \<noteq> iR\<close> \<open>iI \<noteq> iR\<close>
  assumes y_sol: 
    \<open>(y solves_ode (\<lambda>t v.
                       vec_lambda ((\<lambda>k. 0)(
                         iS := -beta * vec_nth v iS * vec_nth v iI,
                         iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                         iR :=  gamma * vec_nth v iI))
                       )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iS: [S], coordinate iI: [I], coordinate iR: [R]\<close>
  assumes iv: \<open>vec_nth (y 0) iS + vec_nth (y 0) iI + vec_nth (y 0) iR = N\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iS + vec_nth (y t) iI + vec_nth (y t) iR = N\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR) has_derivative 
      (\<lambda>w. vec_nth w iS + vec_nth w iI + vec_nth w iR)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: N \<le> [S](t) + [I](t) + [R](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>N \<le> vec_nth (y 0) iS + vec_nth (y 0) iI + vec_nth (y 0) iR\<close>
    using iv
    by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. N) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iS := -beta * vec_nth v iS * vec_nth v iI,
                       iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                       iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iS := -beta * vec_nth v iS * vec_nth v iI,
                       iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                       iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. N) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iS := -beta * vec_nth v iS * vec_nth v iI,
                        iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                        iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iS := -beta * vec_nth v iS * vec_nth v iI,
                        iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                        iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [S](t) + [I](t) + [R](t) \<le> N
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iS + vec_nth (y 0) iI + vec_nth (y 0) iR \<le> N\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. N) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iS := -beta * vec_nth v iS * vec_nth v iI,
                       iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                       iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iS := -beta * vec_nth v iS * vec_nth v iI,
                       iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                       iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. N) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iS := -beta * vec_nth v iS * vec_nth v iI,
                        iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                        iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iS := -beta * vec_nth v iS * vec_nth v iI,
                        iI :=  beta * vec_nth v iS * vec_nth v iI - gamma * vec_nth v iI,
                        iR :=  gamma * vec_nth v iI))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule sum_deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR\<close> and 
                                   g = \<open>\<lambda>v. N\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. N\<close> and 
                                   g = \<open>\<lambda>v. vec_nth v iS + vec_nth v iI + vec_nth v iR\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

subsubsection \<open>Reversible binding: two conservation laws\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  Reversible binding is the most basic reaction in chemistry and biology.
  A ligand A binds to a receptor B to form a complex C, and the complex
  can dissociate back.  This models:
\begin{itemize}
\item Drug-receptor binding in pharmacology
\item Antibody-antigen interactions in immunology
\item Transcription factor-DNA binding in gene regulation
\item Protein-protein interactions in cell signaling
\end{itemize}

  \textbf{THE CHEMICAL REACTIONS}\\
\begin{verbatim}
    A + B <=> C     (k1 forward, km1 reverse)
\end{verbatim}

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics:

\begin{verbatim}
    d[A]/dt = -k1*[A]*[B] + km1*[C]
    d[B]/dt = -k1*[A]*[B] + km1*[C]
    d[C]/dt =  k1*[A]*[B] - km1*[C]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
  Two conservation laws:
\begin{enumerate}
\item{} [A](t) + [C](t) = A\_total   (total A-containing material)
\item{} [B](t) + [C](t) = B\_total   (total B-containing material)
\end{enumerate}

  These express that A and B are conserved moieties: they change form
  (free vs bound) but are never created or destroyed.

  \textbf{WHY THIS MATTERS}\\
  Conserved moieties reduce the model: with [A] = A\_total - [C] and
  [B] = B\_total - [C], the single equation for the complex [C] determines
  the whole system, which is the standard route to binding curves and
  dissociation constants.  The laws also bound each concentration by its
  total while all concentrations are non-negative.

  \textbf{HOW WE VERIFY IT}\\
  Each law is proved with Differential Induction (DI): the Lie derivative
  of the conserved quantity along the vector field is zero:

\begin{verbatim}
    d([A]+[C])/dt = (-k1*A*B + km1*C) + (k1*A*B - km1*C) = 0
    d([B]+[C])/dt = (-k1*A*B + km1*C) + (k1*A*B - km1*C) = 0
\end{verbatim}

  \textbf{ASSUMPTIONS}\\
  Each proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [A](0) + [C](0) = A\_total for the first law,
  and [B](0) + [C](0) = B\_total for the second
\item The time t >= 0
\item The rate constants k1, km1 are arbitrary real numbers
  (the conservation laws hold regardless of their values)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iA: concentration of A, i.e., [A]
\item Coordinate iB: concentration of B, i.e., [B]
\item Coordinate iC: concentration of C, i.e., [C]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iA := d[A]/dt, iB := d[B]/dt, iC := d[C]/dt))
\end{verbatim}

  Each proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>

text \<open>Conservation law 1: [A] + [C] = A\_total.\<close>
lemma reversible_binding_A_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k1 km1 :: real
  fixes iA iB iC :: 'p
  assumes coords: \<open>iA \<noteq> iB\<close> \<open>iA \<noteq> iC\<close> \<open>iB \<noteq> iC\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                                      iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                                      iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iA: [A], coordinate iB: [B], coordinate iC: [C]\<close>
  assumes iv: \<open>vec_nth (y 0) iA + vec_nth (y 0) iC = A_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iA + vec_nth (y t) iC = A_total\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [A](t) + [C](t) at A_total via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([A]+[C])/dt = (-k\<sqdot>A\<sqdot>B + km1\<sqdot>C) + (k\<sqdot>A\<sqdot>B - km1\<sqdot>C) = 0
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v₀ + v₂ *)
  have deriv:
    \<open>((\<lambda>v. vec_nth v iA + vec_nth v iC) has_derivative 
      (\<lambda>w. vec_nth w iA + vec_nth w iC)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: A_total \<le> [A](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>A_total \<le> vec_nth (y 0) iA + vec_nth (y 0) iC\<close>
    using iv
    by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. A_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iA + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. A_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iA + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + vec_nth v iC\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + [C](t) \<le> A_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iA + vec_nth (y 0) iC \<le> A_total\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. A_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. A_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + vec_nth v iC\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iA + vec_nth v iC\<close> and g = \<open>\<lambda>v. A_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. A_total\<close> and g = \<open>\<lambda>v. vec_nth v iA + vec_nth v iC\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

text \<open>Conservation law 2: [B] + [C] = B\_total.\<close>
lemma reversible_binding_B_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k1 km1 :: real
  fixes iA iB iC :: 'p
  assumes coords: \<open>iA \<noteq> iB\<close> \<open>iA \<noteq> iC\<close> \<open>iB \<noteq> iC\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                                      iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                                      iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iA: [A], coordinate iB: [B], coordinate iC: [C]\<close>
  assumes iv: \<open>vec_nth (y 0) iB + vec_nth (y 0) iC = B_total\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iB + vec_nth (y t) iC = B_total\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [B](t) + [C](t) at B_total via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([B]+[C])/dt = (-k1\<sqdot>A\<sqdot>B + km1\<sqdot>C) + (k1\<sqdot>A\<sqdot>B - km1\<sqdot>C) = 0
     ========================================================================== *)

  (* Helper: Fr\<eacute>chet derivative of the sum \<lambda>v. v\<^sub>1 + v\<^sub>2*)
  have deriv:
    \<open>((\<lambda>v. vec_nth v iB + vec_nth v iC) has_derivative 
      (\<lambda>w. vec_nth w iB + vec_nth w iC)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: B_total \<le> [B](t) + [C](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>B_total \<le> vec_nth (y 0) iB + vec_nth (y 0) iC\<close>
    using iv
    by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. B_total) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iB + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. B_total) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iB + vec_nth v iC) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iB + vec_nth v iC\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [B](t) + [C](t) \<le> B_total
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iB + vec_nth (y 0) iC \<le> B_total\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iB + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. B_total) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                       iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iB + vec_nth v iC) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. B_total) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iB := -k1 * vec_nth v iA * vec_nth v iB + km1 * vec_nth v iC,
                        iC :=  k1 * vec_nth v iA * vec_nth v iB - km1 * vec_nth v iC))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iB + vec_nth v iC\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule deriv)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iB + vec_nth v iC\<close> and g = \<open>\<lambda>v. B_total\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. B_total\<close> and g = \<open>\<lambda>v. vec_nth v iB + vec_nth v iC\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


subsubsection \<open>Dimerization: weighted conservation law\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  Dimerization is when two identical molecules combine to form a dimer.
  This is fundamental in:
\begin{itemize}
\item Protein dimerization (many transcription factors function as dimers)
\item Receptor dimerization (e.g., EGFR signaling)
\item Hemoglobin assembly
\end{itemize}

  \textbf{THE CHEMICAL REACTIONS}\\
\begin{verbatim}
    2A  <=>  A2     (k1 forward, km1 reverse)
\end{verbatim}

  \textbf{THE MASS-ACTION ODE MODEL}\\
  Under mass-action kinetics:

\begin{verbatim}
    d[A]/dt  = -2*k1*[A]^2 + 2*km1*[A2]
    d[A2]/dt =    k1*[A]^2 -    km1*[A2]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
  Weighted conservation: [A](t) + 2*[A2](t) = total0  for all t >= 0

  Each dimer contains 2 monomers, so the total monomer count is
  [A] + 2*[A2]. The factor of 2 in the stoichiometry is crucial.

  \textbf{WHY THIS MATTERS}\\
  This is the first conservation law in the CRN benchmark with a non-unit
  stoichiometric weight: the factor 2 must appear in the conserved
  quantity, and the proof confirms that this weighting matches the
  reactions.
  The law bounds the free monomer by the total, [A](t) <= total0 while
  [A2](t) >= 0, and it reduces the model to a single equation for [A].

  \textbf{HOW WE VERIFY IT}\\
  We use Differential Induction (DI): the Lie derivative of [A] + 2*[A2]
  along the vector field is zero:

\begin{verbatim}
    d([A] + 2*[A2])/dt = (-2*k1*A^2 + 2*km1*A2) + 2*(k1*A^2 - km1*A2)
                       = -2*k1*A^2 + 2*km1*A2 + 2*k1*A^2 - 2*km1*A2
                       = 0
\end{verbatim}

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [A](0) + 2*[A2](0) = total0
\item The time t >= 0
\item The rate constants k1, km1 are arbitrary real numbers
  (the conservation law holds regardless of their values)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the two species as components of a state vector over an
  arbitrary finite index type 'p, at two distinct coordinates:
\begin{itemize}
\item Coordinate iA: concentration of the monomer A, i.e., [A]
\item Coordinate iA2: concentration of the dimer A2, i.e., [A2]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iA := d[A]/dt, iA2 := d[A2]/dt))
\end{verbatim}

  The proof uses DI\_Vect (Differential Induction for vector-valued ODEs)
  applied twice (via antisymmetry) to establish the equality.
\<close>

lemma dimerization_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k1 km1 :: real
  fixes iA iA2 :: 'p
  assumes coords: \<open>iA \<noteq> iA2\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                                      iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iA: [A] (monomer), coordinate iA2: [A2] (dimer)\<close>
  assumes iv: \<open>vec_nth (y 0) iA + 2 * vec_nth (y 0) iA2 = total0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iA + 2 * vec_nth (y t) iA2 = total0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [A](t) + 2\<sqdot>[A\<^sub>2](t) at total0 via two DI_Vect 
     applications.  The Lie derivative cancels:
     
         d([A] + 2\<sqdot>[A\<^sub>2])/dt = (-2\<sqdot>k1\<sqdot>A² + 2\<sqdot>km1\<sqdot>A\<^sub>2) + 2\<sqdot>(k1\<sqdot>A² - km1\<sqdot>A\<^sub>2)
                            = -2\<sqdot>k1\<sqdot>A² + 2\<sqdot>km1\<sqdot>A\<^sub>2+ 2\<sqdot>k1\<sqdot>A² - 2\<sqdot>km1\<sqdot>A\<^sub>2
                            = 0
     
     Each dimer contains 2 monomers, so the total monomer count is 
     [A] + 2\<sqdot>[A\<^sub>2].  The factor of 2 in the stoichiometry is crucial.
     ========================================================================== *)

  (* ------------------------------------------------------------------------
     SUB-PART 1: total0 \<le> [A](t) + 2\<sqdot>[A\<^sub>2](t)
     ------------------------------------------------------------------------ *)

  have iv_ge: \<open>total0 \<le> vec_nth (y 0) iA + 2 * vec_nth (y 0) iA2\<close>
    using iv
    by simp

  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                       iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>))\<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                       iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. total0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                        iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                        iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule weighted_sum_has_derivative)
      apply (auto simp: power2_eq_square algebra_simps fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [A](t) + 2\<sqdot>[A₂](t) \<le> total0
     ------------------------------------------------------------------------ *)

  have iv_le: \<open>vec_nth (y 0) iA + 2 * vec_nth (y 0) iA2 \<le> total0\<close>
    using iv
    by simp

  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                       iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                       iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. total0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                        iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iA := -2 * k1 * (vec_nth v iA)^2 + 2 * km1 * vec_nth v iA2,
                        iA2 :=      k1 * (vec_nth v iA)^2 -     km1 * vec_nth v iA2))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule conjI, rule weighted_sum_has_derivative)
      apply (rule conjI, rule has_derivative_const)
      apply (auto simp: power2_eq_square algebra_simps fun_upd_def)
      done
  qed

  show ?thesis
    by (auto intro!: antisym 
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2\<close> and g = \<open>\<lambda>v. total0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. total0\<close> and g = \<open>\<lambda>v. vec_nth v iA + 2 * vec_nth v iA2\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


subsubsection \<open>Simple decay: positivity via DG\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The simplest irreversible reaction: a species decays at a rate
  proportional to its concentration.  This models:
\begin{itemize}
\item Radioactive decay
\item mRNA degradation in cells
\item Drug clearance from the body
\item Protein turnover
\end{itemize}

  \textbf{THE CHEMICAL REACTIONS}\\
\begin{verbatim}
    A  ->  {}     (first-order degradation, rate k)
\end{verbatim}

  \textbf{THE MASS-ACTION ODE MODEL}\\
\begin{verbatim}
    d[A]/dt = -k*[A]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
  If [A](0) > 0, then [A](t) > 0 for all t >= 0.

  The species decays but never reaches zero in finite time.
  (The exact solution is [A](t) = [A](0)*e\textasciicircum{}\{-kt\} > 0.)

  \textbf{WHY THIS MATTERS}\\
  Positivity is the basic sanity property of a concentration model: a
  concentration that reached zero or became negative in finite time would
  signal a modeling error.  The example is also the simplest instance of
  the DG proof pattern used later for the gene regulatory networks
  (negative autoregulation, the repressilator, the Gardner toggle switch).

  This is exactly our exponential\_decay example with the ODE written in
  CRN notation. We state it here for completeness of the benchmark suite.

  \textbf{HOW WE VERIFY IT}\\
  DI alone fails: the Lie derivative of [A] along -k*[A] is -k*[A].
  For [A] >= 0, DI needs -k*[A] >= 0, which requires [A] <= 0, the
  opposite of what we want.

  Instead we use a Differential Ghost (DG):
\begin{verbatim}
    Ghost: g' = (k/2)*g,  g(0) = 1/sqrt([A](0))
    Invariant: [A]*g^2 = 1
    Lie derivative: (-k*A)*g^2 + A*2g*(k/2*g) = -kAg^2 + kAg^2 = 0
    Initial: A0*(1/sqrt(A0))^2 = 1
    Conclude: A*g^2 >= 1 and g^2 >= 0 ==> A > 0
\end{verbatim}

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: [A](0) > 0
\item The time t >= 0
\item The decay rate is positive: k > 0
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the species and the ghost as components of a state vector
  over an arbitrary finite index type 'p, at two distinct coordinates:
\begin{itemize}
\item Coordinate iA: concentration of A, i.e., [A]
\item Coordinate iG: a spare coordinate that holds the ghost g
\end{itemize}

  The ODE is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iA := d[A]/dt))
\end{verbatim}

  The proof (crn\_simple\_decay\_positivity, below) applies DG to extend
  the trajectory with the ghost at iG, then DI\_Vect to prove
  [A]*g\textasciicircum{}2 >= 1 along the extended trajectory.
\<close>

subsubsection \<open>CRN benchmark summary\<close>

text \<open>
\begin{verbatim}
  | #  | System              | Property       | Method | Species |
  |----|---------------------|----------------|--------|---------|
  | 1  | CRN Oscillator      | A+B+C = const  | DI     | 3       |
  | 2  | Michaelis-Menten    | E+ES = const   | DI     | 4       |
  | 3  | Michaelis-Menten    | S+ES+P = const | DI     | 4       |
  | 4  | Exponential decay   | x > 0          | DG+DI  | 1+ghost |
  | 5  | Harmonic oscillator | x^2+y^2 = r0^2 | DI     | 2       |
  | 6  | SIR Epidemic        | S+I+R = N      | DI     | 3       |
  | 7a | Reversible binding  | A+C = A_total  | DI     | 3       |
  | 7b | Reversible binding  | B+C = B_total  | DI     | 3       |
  | 8  | Dimerization        | A+2*A2 = total | DI     | 2       |
  | 9  | Simple decay A->{}  | [A] > 0        | DG+DI  | 1+ghost |
  |    | (CRN form of 4)     |                |        |         |
\end{verbatim}

  All properties verified WITHOUT solving the ODEs, purely from
  local derivative analysis using differential induction (DI) and
  differential ghosts (DG).
\<close>
subsubsection \<open>CRN properties requiring differential ghosts\<close>

text \<open>
  The example below demonstrates a property that CANNOT be proved by
  Differential Induction (DI) alone. The Lie derivative has the
  "wrong sign", so a ghost variable must be introduced to create
  an invariant that implies the desired property.

  \textbf{General pattern:}\\
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
  The DG proof of the simple decay example described above: the ghost
  g' = (k/2)*g with g(0) = 1/sqrt([A](0)) makes [A]*g\textasciicircum{}2 >= 1
  invariant, which forces [A] > 0.
\<close>
lemma crn_simple_decay_positivity:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k :: real
  fixes iA iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iA \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode 
                    (\<lambda>t v. 
                      vec_lambda ((\<lambda>k. 0)(iA := -k * (vec_nth v iA))))) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (x 0) iA > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes k_pos: \<open>0 < k\<close>
  shows \<open>0 < vec_nth (x t) iA\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove [A](t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): Introduce a ghost species y at coordinate iG satisfying 
                     dy/dt = (k/2)\<sqdot>y with initial value y(0) = 1/sqrt([A](0)). 
                     The combined trajectory ?z = x extended at the ghost coordinate iG 
                     with y solves the extended ODE.
       
       STAGE 2 (DI): Prove the invariant 1 \<le> [A] \<sqdot> y² along the combined 
                     trajectory, via DI_Vect with h = 1 and g = [A] \<sqdot> y².
                     
                     Lie derivative:
                       d([A]\<sqdot>y²)/dt = (-k\<sqdot>A)\<sqdot>y² + A\<sqdot>2y\<sqdot>(k/2\<sqdot>y)
                                    = -k\<sqdot>A\<sqdot>y² + k\<sqdot>A\<sqdot>y²
                                    = 0
       
       STAGE 3 (algebra): Since [A] \<sqdot> y² \<ge> 1 and y² \<ge> 0, we get [A] > 0.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iA)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. k/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. k/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(iA := -k * (vec_nth v iA)))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iA := -k * (vec_nth v iA)))) \<tau> v = 
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iA := -k * (vec_nth v iA)))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v iA = vec_nth w iA\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iA := -k * (vec_nth v iA)))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(iA := -k * (vec_nth v iA)))) \<tau> w\<close>
      using v0 
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: obtain a ghost trajectory y satisfying dy/dt = (k/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. k/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = iG,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))\<close>

  (* Helper: Fréchet derivative of [A] \<sqdot> y² (product rule) *)
  have xg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iA * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iA * (vec_nth p iG)^2 + 
           vec_nth p iA * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iA) has_derivative (\<lambda>v. vec_nth v iA)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: Apply DI_Vect to prove the invariant 1 \<le> [A] \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> [A](0) \<sqdot> y(0)² *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) iA * (vec_nth (?z 0) iG)^2\<close>
    using iv
    by (simp add: y0_def y_init field_simps power2_eq_square fun_upd_def)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iA * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                            vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                            vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iA * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                             vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda ((\<lambda>i. 0)(iA := -k * (vec_nth v iA))) +
                             vec_lambda ((\<lambda>i. 0)(iG := (k/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iA * (vec_nth (?z \<tau>) iG)^2 + 
                                     vec_nth (?z \<tau>) iA * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule xg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      done
  qed

  (* APPLY DI_Vect: we get the invariant 1 \<le> [A] \<sqdot> y² at time t *)
  have ineq: \<open>1 \<le> vec_nth (?z t) iA * (vec_nth (?z t) iG)^2\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iA * (vec_nth v iG)^2\<close>,
                  OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From [A](t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude [A](t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iA\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iA = vec_nth (x t) iA\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iA * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iA \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

subsubsection \<open>Computing CRN min(x, y): conservation laws\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  This is the first example where we verify a property of a CRN that
  performs COMPUTATION - not just a natural biochemical process, but a
  deliberately designed chemical program.
  The CRN computes the minimum of two non-negative integers x and y
  (Bridger 2019, "Computing with chemical reaction networks: a tutorial").
  This is referenced in Section 2.1.1 of "A Survey of Existing Paradigms
  in Biological Computing" (Nag et al., 2026).

  \textbf{THE CHEMICAL REACTIONS}\\
\begin{verbatim}
    X + Y -> Z     (rate k)
\end{verbatim}

  Starting from initial concentrations [X](0) = x0 and [Y](0) = y0
  (with [Z](0) = 0), the reaction consumes equal amounts of X and Y
  to produce Z. When the minority species is exhausted, the reaction
  stops, and [Z] = min(x0, y0).

  \textbf{THE MASS-ACTION ODE MODEL}\\
\begin{verbatim}
    d[X]/dt = -k*[X]*[Y]
    d[Y]/dt = -k*[X]*[Y]
    d[Z]/dt =  k*[X]*[Y]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
  Two conservation laws that together ensure computational correctness:
\begin{enumerate}
\item INPUT-OUTPUT BALANCE FOR X:
  [X](t) + [Z](t) = x0     for all t >= 0
  Every molecule of X consumed produces exactly one molecule of Z.
  At completion (when X or Y is exhausted):
  if x0 <= y0, then [X] -> 0, so [Z] -> x0;
  if x0 > y0, then [X] -> x0 - y0, and [Z] -> y0.
\item INPUT-OUTPUT BALANCE FOR Y:
  [Y](t) + [Z](t) = y0     for all t >= 0
  Every molecule of Y consumed produces exactly one molecule of Z.
\end{enumerate}
  Together these imply:
\begin{itemize}
\item{} [X](t) - [Y](t) = x0 - y0 (the difference is preserved)
\item{} [Z](t) = x0 - [X](t) = y0 - [Y](t)
\item At steady state: [Z] = min(x0, y0)
\end{itemize}

  \textbf{WHY THIS MATTERS}\\
  This CRN is a PROGRAM - it takes inputs (initial concentrations of X, Y)
  and produces an output (final concentration of Z = min(x0, y0)).
  Our conservation laws prove that the program is CORRECT in the sense
  that it maintains the right "balance" throughout its execution:
  no molecules are lost or created spuriously.
  This is analogous to proving loop invariants in software verification:
  the conservation laws are invariants of the chemical "loop" that hold
  at every time step.

  \textbf{HOW WE VERIFY IT}\\
  Differential Induction (DI). Both Lie derivatives cancel to zero:

\begin{verbatim}
    d([X]+[Z])/dt = (-k*X*Y) + (k*X*Y) = 0
    d([Y]+[Z])/dt = (-k*X*Y) + (k*X*Y) = 0
\end{verbatim}

  The preserved difference [X](t) - [Y](t) = x0 - y0 follows by
  subtracting the two laws.

  \textbf{ASSUMPTIONS}\\
  The proofs assume:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial conditions: [X](0) + [Z](0) = x0 and [Y](0) + [Z](0) = y0
\item The time t >= 0
\item The rate constant k is an arbitrary real number
  (the conservation laws hold regardless of its value)
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iX: concentration of X, i.e., [X]
\item Coordinate iY: concentration of Y, i.e., [Y]
\item Coordinate iZ: concentration of Z, i.e., [Z]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda i. 0)(iX := d[X]/dt, iY := d[Y]/dt, iZ := d[Z]/dt))
\end{verbatim}

  Each conservation law uses DI\_Vect (Differential Induction for
  vector-valued ODEs) applied twice (via antisymmetry);
  crn\_min\_difference\_preserved combines the two laws.
\<close>


lemma crn_min_X_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)
                                               (iX := -k * vec_nth v iX * vec_nth v iY,
                                                iY := -k * vec_nth v iX * vec_nth v iY,
                                                iZ :=  k * vec_nth v iX * vec_nth v iY))
                                   )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iX: [X], coordinate iY: [Y], coordinate iZ: [Z].
         d[X]/dt = -k*[X]*[Y];
         d[Y]/dt = -k*[X]*[Y];
         d[Z]/dt = k*[X]*[Y]\<close>
  assumes iv: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
      \<comment> \<open>Initially: [X](0) + [Z](0) = x0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iX + vec_nth (y t) iZ = x0\<close>
      \<comment> \<open>Conclusion: [X](t) + [Z](t) = x0 for all t >= 0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [X](t) + [Z](t) at x0 via TWO DI_Vect applications.
     
     To prove A = B, we prove A \<le> B and B \<le> A (antisymmetry).  Each direction 
     uses DI_Vect with a constant lower/upper bound.  The Lie derivative of 
     [X] + [Z] cancels:
     
         d([X]+[Z])/dt = -k\<sqdot>X\<sqdot>Y + k\<sqdot>X\<sqdot>Y = 0
     
     so both directions hold with the same derivative check.
     
     We discharge each DI_Vect obligation as a separate `have` statement,
     then apply both instances of the provably verified lemma DI_Vect via
     forward reasoning combined with antisym in the final show.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v\<^sub>1+ v\<^sub>2*)
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v iX + vec_nth v iZ) has_derivative 
      (\<lambda>w. vec_nth w iX + vec_nth w iZ)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: x0 \<le> [X](t) + [Z](t) via DI_Vect with h = x0, g = [X] + [Z]
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition x0 \<le> [X](0) + [Z](0) *)
  have iv_ge: \<open>x0 \<le> vec_nth (y 0) iX + vec_nth (y 0) iZ\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. x0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iX + vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. 
                         vec_lambda ((\<lambda>i. 0)
                                     (iX := -k * vec_nth v iX * vec_nth v iY,
                                      iY := -k * vec_nth v iX * vec_nth v iY,
                                      iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (iX := -k * vec_nth v iX * vec_nth v iY,
                                         iY := -k * vec_nth v iX * vec_nth v iY,
                                         iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. x0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iX + vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iX + vec_nth v iZ\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [X](t) + [Z](t) \<le> x0 via DI_Vect with h = [X] + [Z], g = x0
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition [X](0) + [Z](0) \<le> x0 *)
  have iv_le: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ \<le> x0\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iX + vec_nth v iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. x0) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (iX := -k * vec_nth v iX * vec_nth v iY,
                                         iY := -k * vec_nth v iX * vec_nth v iY,
                                         iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)
                                        (iX := -k * vec_nth v iX * vec_nth v iY,
                                         iY := -k * vec_nth v iX * vec_nth v iY,
                                         iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iX + vec_nth v iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. x0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iX + vec_nth v iZ\<close>])
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
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iX + vec_nth v iZ\<close> and g = \<open>\<lambda>v. x0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. x0\<close> and g = \<open>\<lambda>v. vec_nth v iX + vec_nth v iZ\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


text \<open>Conservation law 2: [Y](t) + [Z](t) = y0.\<close>
lemma crn_min_Y_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)(
                                     iX := -k * vec_nth v iX * vec_nth v iY,
                                     iY := -k * vec_nth v iX * vec_nth v iY,
                                     iZ :=  k * vec_nth v iX * vec_nth v iY))
                                   )) {0..t} UNIV\<close>
  assumes iv: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
      \<comment> \<open>Initially: [Y](0) + [Z](0) = y0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iY + vec_nth (y t) iZ = y0\<close>
      \<comment> \<open>Conclusion: [Y](t) + [Z](t) = y0 for all t >= 0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich [Y](t) + [Z](t) at y0 via two DI_Vect applications.
     
     The Lie derivative of [Y] + [Z] cancels:
     
         d([Y]+[Z])/dt = -k\<sqdot>X\<sqdot>Y + k\<sqdot>X\<sqdot>Y = 0
     
     so both directions hold with the same derivative check.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the sum \<lambda>v. v\<^sub>1+ v\<^sub>2*)
  have sum_deriv:
    \<open>((\<lambda>v. vec_nth v iY + vec_nth v iZ) has_derivative 
      (\<lambda>w. vec_nth w iY + vec_nth w iZ)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_add has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: y0 \<le> [Y](t) + [Z](t) via DI_Vect with h = y₀, g = [Y] + [Z]
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition y0 \<le> [Y](0) + [Z](0) *)
  have iv_ge: \<open>y0 \<le> vec_nth (y 0) iY + vec_nth (y 0) iZ\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. y0) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iY + vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -k * vec_nth v iX * vec_nth v iY,
                       iY := -k * vec_nth v iX * vec_nth v iY,
                       iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -k * vec_nth v iX * vec_nth v iY,
                       iY := -k * vec_nth v iX * vec_nth v iY,
                       iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. y0) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iY + vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iY + vec_nth v iZ\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule sum_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: [Y](t) + [Z](t) \<le> y0 via DI_Vect with h = [Y] + [Z], g = y0
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition [Y](0) + [Z](0) \<le> y0 *)
  have iv_le: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ \<le> y0\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iY + vec_nth v iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. y0) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iY + vec_nth v iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. y0) has_derivative Dg) (at (y \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                         iX := -k * vec_nth v iX * vec_nth v iY,
                         iY := -k * vec_nth v iX * vec_nth v iY,
                         iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                         iX := -k * vec_nth v iX * vec_nth v iY,
                         iY := -k * vec_nth v iX * vec_nth v iY,
                         iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iY + vec_nth v iZ\<close>])
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
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iY + vec_nth v iZ\<close> and g = \<open>\<lambda>v. y0\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. y0\<close> and g = \<open>\<lambda>v. vec_nth v iY + vec_nth v iZ\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed

lemma crn_min_difference_preserved:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>i. 0)(
                                     iX := -k * vec_nth v iX * vec_nth v iY,
                                     iY := -k * vec_nth v iX * vec_nth v iY,
                                     iZ :=  k * vec_nth v iX * vec_nth v iY))
                                   )) {0..t} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iX - vec_nth (y t) iY = x0 - y0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Compose the two conservation lemmas.
     
     From crn_min_X_conservation:  [X](t) + [Z](t) = x0
     From crn_min_Y_conservation:  [Y](t) + [Z](t) = y0
     Subtracting:                  [X](t) - [Y](t) = x0 - y0
     
     This lemma needs no DI_Vect application of its own; it's a pure 
     forward composition of the two established conservation laws, 
     finished by linarith.
     ========================================================================== *)

  have x_conservation: \<open>vec_nth (y t) iX + vec_nth (y t) iZ = x0\<close>
    using crn_min_X_conservation[OF coords y_sol iv_x t] .
  have y_conservation: \<open>vec_nth (y t) iY + vec_nth (y t) iZ = y0\<close>
    using crn_min_Y_conservation[OF coords y_sol iv_y t] .
  show ?thesis
    using x_conservation y_conservation 
    by linarith
qed

subsection \<open>GRN benchmark\<close>

subsubsection \<open>Simplified genetic toggle switch, mass-action form\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The genetic toggle switch was constructed by Gardner, Cantor, and
  Collins in E. coli (Nature, 2000), the first synthetic, bistable
  gene-regulatory network. It is referenced in Section 3.4.5 of the
  biological computing survey (Nag et al., 2026).

  \textbf{THE CIRCUIT}\\
  Two repressors that mutually inhibit each other:

\begin{verbatim}
    Gene 1 -> Protein 1 -| Gene 2
    Gene 2 -> Protein 2 -| Gene 1
\end{verbatim}

  Each protein represses the other through a bimolecular destruction
  reaction (beta*u*v term). This is the "annihilation" form of repression,
  often used in synthetic biology and specifically in antithetic feedback
  controllers (Briat et al. 2016).

  \textbf{THE MASS-ACTION ODE MODEL}\\
  The full Hill-function model used by Gardner et al.,

\begin{verbatim}
    du/dt = alpha1/(1 + v^beta) - u
    dv/dt = alpha2/(1 + u^gamma) - v
\end{verbatim}

  involves rational functions and needs has\_derivative for Hill
  functions; it is treated in the next example. Here we formalize the
  SIMPLIFIED LINEAR REPRESSION version:

\begin{verbatim}
    du/dt = alpha1 - beta*u*v - delta*u
    dv/dt = alpha2 - beta*u*v - delta*v
\end{verbatim}

  Where:
\begin{verbatim}
    alpha1, alpha2 = constitutive production rates of proteins 1 and 2
    beta           = mutual repression rate
                     (each protein degrades the other)
    delta          = degradation rate (basal turnover)
\end{verbatim}

  The lemmas below use its symmetric, degradation-free case
  (alpha1 = alpha2 = alpha, delta = 0):

\begin{verbatim}
    du/dt = alpha - beta*u*v
    dv/dt = alpha - beta*u*v
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
\begin{enumerate}
\item DIFFERENCE CONSERVATION (toggle\_switch\_difference\_conservation):
  u(t) - v(t) = u(0) - v(0) for all t >= 0.
\item DOMAIN STRENGTHENING BY DC (toggle\_switch\_DC\_strengthened\_domain):
  if u(0) = v(0), the trajectory also solves the ODE on the evolution
  domain strengthened to \{u = v\}.
\end{enumerate}

  \textbf{WHY THIS MATTERS}\\
  This is our first example of the Differential Cut (DC): an invariant
  proved with DI is added to the evolution domain, so that later
  reasoning can use it. On the strengthened domain the ODE reduces to the
  1-D system du/dt = alpha - beta*u\textasciicircum{}2, on which further
  invariants can be proved.

  \textbf{HOW WE VERIFY IT}\\
  DIFFERENCE CONSERVATION is proved with Differential Induction (DI). In
  the symmetric case the Lie derivative of u - v cancels:

\begin{verbatim}
    d(u - v)/dt = (alpha - beta*u*v) - (alpha - beta*u*v) = 0
\end{verbatim}

  For different production rates no such combination is conserved in
  general: d(alpha2*u - alpha1*v)/dt = (alpha1 - alpha2)*beta*u*v, which
  vanishes only when alpha1 = alpha2.

  DOMAIN STRENGTHENING is a Differential Cut (DC): when u(0) = v(0) the
  conserved difference is 0, so u = v holds all along the trajectory, and
  DC adds this cut formula to the domain of solves\_ode.

  \textbf{ASSUMPTIONS}\\
  The proofs assume:
\begin{enumerate}
\item The solution y exists and satisfies the symmetric, degradation-free
  ODE on [0,t] (from solves\_ode)
\item The initial condition: u(0) - v(0) = c for difference conservation,
  and u(0) = v(0) for the domain strengthening
\item The time t >= 0
\item The rates alpha, beta are arbitrary real numbers
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the two proteins as components of a state vector over an
  arbitrary finite index type 'p, at two distinct coordinates:
\begin{itemize}
\item Coordinate iU: concentration of protein 1, i.e., u
\item Coordinate iV: concentration of protein 2, i.e., v
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iU := du/dt, iV := dv/dt))
\end{verbatim}

  Difference conservation uses DI\_Vect (Differential Induction for
  vector-valued ODEs) applied twice (via antisymmetry); the domain
  strengthening uses DC with the cut formula u = v.

  \textbf{LIMITATIONS}\\
  REGIONAL INVARIANCE is not proved for this model: if u(0) >= 0 and
  v(0) >= 0 and the parameters are positive, then u(t) >= 0 and v(t) >= 0
  for all t >= 0, i.e., protein concentrations stay non-negative.

  A direct DI proof of u >= 0 fails. The Lie derivative of u along the
  field is alpha1 - beta*u*v - delta*u. Only the BOUNDARY u = 0 matters
  for u >= 0, and there du/dt = alpha1 >= 0 (since alpha1 > 0), so the
  boundary is repelling and u stays >= 0. But DI as we have formalized it
  (DI\_Vect) checks the derivative EVERYWHERE along the trajectory, not
  just at the boundary: it needs 0 <= alpha1 - beta*u*v - delta*u for ALL
  reachable u, v, which fails when u is large. DC can build up the
  invariant region step by step:
\begin{enumerate}
\item Prove u >= 0 is invariant (using DI on a strong assumption: we need
  v >= 0 to be in the picture, but at u = 0 the argument works regardless
  of v as long as alpha1 > 0)
\item Cut: the domain becomes UNIV Int \{u >= 0\}
\item Prove v >= 0 is invariant (symmetric)
\item Cut again: the domain becomes \{u >= 0 and v >= 0\}
\end{enumerate}
  DI\_boundary, which only needs a strictly positive derivative on the
  boundary, would discharge steps 1 and 3 when alpha1 > 0 and alpha2 > 0
  (at u = 0, du/dt = alpha1; at v = 0, dv/dt = alpha2); this is not done
  here. For the Hill model, the next example proves positivity with DG
  and DI\_boundary.
\<close>


paragraph \<open>Toggle switch: conservation in degradation-free form\<close>
text \<open>
  \textbf{ODE:}\\
\begin{verbatim}
    du/dt = alpha1 - beta*u*v
    dv/dt = alpha2 - beta*u*v
\end{verbatim}

  \textbf{CONSERVATION LAW (Lie derivative argument):}\\
\begin{verbatim}
    d(alpha2*u - alpha1*v)/dt
      = alpha2*(alpha1 - beta*u*v) - alpha1*(alpha2 - beta*u*v)
      = alpha2*alpha1 - alpha2*beta*u*v - alpha1*alpha2 + alpha1*beta*u*v
      = (alpha1 - alpha2)*beta*u*v
\end{verbatim}

  In the symmetric case alpha1 = alpha2 = alpha, the conservation is:
\begin{verbatim}
    d(u - v)/dt = (alpha - beta*u*v) - (alpha - beta*u*v) = 0
\end{verbatim}

  So u(t) - v(t) = u(0) - v(0)  (the difference is preserved)
\<close>

lemma toggle_switch_difference_conservation:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> \<beta> :: real
  fixes iU iV :: 'p
  assumes coords: \<open>iU \<noteq> iV\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                                      iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Symmetric toggle switch without degradation, u at coordinate iU and v at coordinate iV:
         du/dt = alpha - beta*u*v;
         dv/dt = alpha - beta*u*v\<close>
  assumes iv: \<open>vec_nth (y 0) iU - vec_nth (y 0) iV = c\<close>
      \<comment> \<open>Initial difference: c = u(0) - v(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>vec_nth (y t) iU - vec_nth (y t) iV = c\<close>
      \<comment> \<open>Conclusion: the difference u(t) - v(t) is preserved\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Sandwich u(t) - v(t) at c via two DI_Vect applications.
     
     The Lie derivative of u - v cancels:
     
         d(u - v)/dt = (\<alpha> - \<beta>\<sqdot>u\<sqdot>v) - (\<alpha> - \<beta>\<sqdot>u\<sqdot>v) = 0
     
     so both directions hold with the same derivative check.
     ========================================================================== *)

  (* Helper: Fréchet derivative of the difference \<lambda>v. v₀ - v₁ *)
  have diff_deriv:
    \<open>((\<lambda>v. vec_nth v iU - vec_nth v iV) has_derivative 
      (\<lambda>w. vec_nth w iU - vec_nth w iV)) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
    by (intro has_derivative_diff has_derivative_vec_nth)

  (* ------------------------------------------------------------------------
     SUB-PART 1: c \<le> u(t) - v(t)
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 1.1 (iv): initial condition c \<le> u(0) - v(0) *)
  have iv_ge: \<open>c \<le> vec_nth (y 0) iU - vec_nth (y 0) iV\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_ge:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iU - vec_nth v iV) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                       iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                       iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iU - vec_nth v iV) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                        iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                        iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iU - vec_nth v iV\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule diff_deriv)
      apply (auto simp: fun_upd_def)
      done
  qed

  (* ------------------------------------------------------------------------
     SUB-PART 2: u(t) - v(t) \<le> c
     ------------------------------------------------------------------------ *)

  (* PROOF OBLIGATION 2.1 (iv): initial condition u(0) - v(0) \<le> c *)
  have iv_le: \<open>vec_nth (y 0) iU - vec_nth (y 0) iV \<le> c\<close>
    using iv
    by simp

  (* PROOF OBLIGATION 2.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
  have induct_step_le:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth v iU - vec_nth v iV) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. c) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                       iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>)) \<le>
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                       iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                       iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iU - vec_nth v iV) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. c) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                        iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                        iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                        iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iU - vec_nth v iV\<close>])
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
                     DI_Vect[where h = \<open>\<lambda>v. vec_nth v iU - vec_nth v iV\<close> and g = \<open>\<lambda>v. c\<close>,
                             OF iv_le y_sol induct_step_le t]
                     DI_Vect[where h = \<open>\<lambda>v. c\<close> and g = \<open>\<lambda>v. vec_nth v iU - vec_nth v iV\<close>,
                             OF iv_ge y_sol induct_step_ge t])
qed


text \<open>
  \textbf{Using DC to derive a stronger invariant}\\

  Now we demonstrate the DC pattern: USE the conservation law as a
  CUT to strengthen the domain, then derive further consequences.

  Suppose we additionally have the standing assumption u(0) = v(0) = u0.
  Then by the conservation law, u(t) = v(t) for all t (the difference
  c = 0 stays 0).

  Using DC, we strengthen the domain to \{(u,v). u = v\}, and within
  this domain the ODE simplifies to a 1-D system:
\begin{verbatim}
    du/dt = alpha - beta*u^2
\end{verbatim}

  Now we can prove further invariants on this restricted system.
\<close>

text \<open>DC application: strengthen the domain to include the conservation invariant.\<close>
lemma toggle_switch_DC_strengthened_domain:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> \<beta> :: real
  fixes iU iV :: 'p
  assumes coords: \<open>iU \<noteq> iV\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
                                      iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))
                                    )) {0..t} UNIV\<close>
  assumes iv_eq: \<open>vec_nth (y 0) iU = vec_nth (y 0) iV\<close>
      \<comment> \<open>Symmetric initial condition: u(0) = v(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  shows \<open>(y solves_ode (\<lambda>t v.
            vec_lambda ((\<lambda>k. 0)(
              iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
              iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))
          )) {0..t} (UNIV \<inter> {v. vec_nth v iU = vec_nth v iV})\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Apply DC with cut-formula C v \<equiv> (v₀ = v₁).
     
     DC requires two obligations:
       1. (y_sol) The trajectory solves the ODE on the original domain.
          This is passed directly from our assumption.
       2. (C_inv) For every \<tau> \<in> [0..t], the cut-formula holds at y(\<tau>), 
          i.e., vec_nth (y \<tau>) iU = vec_nth (y \<tau>) iV.
     
     The C_inv obligation is discharged using 
     toggle_switch_difference_conservation: since u(0) = v(0) gives 
     initial difference c = 0, the preserved difference u(\<tau>) - v(\<tau>) 
     is also 0 for all \<tau>, i.e., u(\<tau>) = v(\<tau>).
     ========================================================================== *)

  (* PROOF OBLIGATION DC.1 (y_sol): passed directly from assumption *)

  (* PROOF OBLIGATION DC.2 (C_inv): u(\<tau>) = v(\<tau>) for all \<tau> \<in> [0..t].
     Proved by restricting y to {0..\<tau>} and invoking the difference 
     conservation lemma with initial difference c = 0. *)
  have C_inv: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) iU = vec_nth (y \<tau>) iV\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>

    (* Restrict the ODE to {0..\<tau>} *)
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
        vec_lambda ((\<lambda>k. 0)(
          iU := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV,
          iV := \<alpha> - \<beta> * vec_nth v iU * vec_nth v iV))
        )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol h\<tau>] .

    (* Initial difference is 0 (from the symmetric initial condition) *)
    have iv0: \<open>vec_nth (y 0) iU - vec_nth (y 0) iV = 0\<close>
      using iv_eq
      by simp

    (* Apply the difference conservation lemma at time \<tau> *)
    have \<open>vec_nth (y \<tau>) iU - vec_nth (y \<tau>) iV = 0\<close>
      using h\<tau> toggle_switch_difference_conservation[OF coords y_sol_\<tau> iv0 ]
      by simp
    thus \<open>vec_nth (y \<tau>) iU = vec_nth (y \<tau>) iV\<close> 
      by simp
  qed

  (* APPLY DC via forward reasoning *)
  show ?thesis
    using DC[OF y_sol _] C_inv 
    by auto
qed

                    

text \<open>
  \textbf{SUMMARY: What we have achieved with DC}\\

  We have:
\begin{enumerate}
\item Formalized the Differential Cut (DC) rule of dDL in Isabelle/HOL as a
  provably verified lemma
\item Demonstrated DC application on the symmetric toggle switch:
\begin{itemize}
\item Used DI to prove the conservation law u(t) - v(t) = c
\item Used DC to strengthen the domain with this invariant
\end{itemize}
\item The strengthened solves\_ode predicate now carries the conservation
  law as part of the domain constraint, enabling further reasoning.
\end{enumerate}
\<close>


subsubsection \<open>Gardner genetic toggle switch\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The genetic toggle switch (Gardner, Cantor \& Collins, Nature 2000) is a
  landmark device in synthetic biology: the first synthetic, bistable,
  gene-regulatory network constructed in a living organism (E. coli). It
  is referenced in Section 3.4.5 of our biological computing survey and
  is considered a foundational primitive for cellular memory.

  \textbf{THE CIRCUIT}\\
  The toggle switch consists of two genes encoding proteins that
  mutually repress each other's expression:

\begin{verbatim}
      Gene 1 -> Protein u -| Gene 2
      Gene 2 -> Protein v -| Gene 1
\end{verbatim}

  \textbf{THE ODE MODEL}\\
  Gardner et al. modeled the dynamics using Hill functions, which capture
  the cooperative nature of transcription-factor binding:

\begin{verbatim}
      du/dt = alpha1 / (1 + v^beta) - u
      dv/dt = alpha2 / (1 + u^gamma) - v
\end{verbatim}

  where:
\begin{verbatim}
    alpha1, alpha2 are the maximal production rates of each protein
    beta, gamma    are the Hill coefficients (cooperativity exponents)
    u, v           are protein concentrations
\end{verbatim}

  Each Hill term is a DECREASING function of the repressor concentration,
  capturing the fact that as repressor levels rise, target gene expression
  falls. The -u and -v terms represent linear degradation.

  \textbf{WHAT WE VERIFY}\\
  Three results, from the conditional one to the unconditional one:
\begin{enumerate}
\item CONDITIONAL POSITIVITY OF u (gardner\_toggle\_switch\_u\_positive):
  if u(0) > 0, and the concentration v(tau) stays non-negative throughout
  the time interval [0, t], then u(t) > 0.
\item NON-NEGATIVITY OF v (gardner\_toggle\_switch\_v\_nonneg): if
  v(0) >= 0, alpha2 > 0 and gamma is a positive even Hill coefficient,
  then v(t) >= 0.
\item UNCONDITIONAL POSITIVITY OF u
  (gardner\_toggle\_switch\_u\_positive\_unconditional): if u(0) > 0 and
  v(0) >= 0, then u(t) > 0. The non-negativity of v along the trajectory
  is proved by the second result instead of assumed.
\end{enumerate}

  In words: under mild assumptions, the concentration of protein u remains
  strictly positive: it never vanishes. This is a fundamental SAFETY
  PROPERTY of any chemical model: concentrations of existing species
  cannot become negative or zero in finite time.

  \textbf{WHY THIS MATTERS}\\
\begin{enumerate}
\item MODEL VALIDITY: For the Hill function alpha1/(1+v\textasciicircum{}beta) to be well-defined
  and well-behaved, we need v >= 0 (so that v\textasciicircum{}beta is non-negative and
  the denominator stays strictly positive). Proving that u stays
  positive given that v is non-negative is a building block for
  proving that BOTH concentrations stay positive, which certifies
  that the entire ODE model remains physically meaningful over time.
\item CORRECTNESS OF THE CIRCUIT: In the toggle switch, the two proteins
  represent two distinct stable states ("on" for u, "off" for v, or
  vice versa). If either protein concentration could reach zero,
  the circuit would lose information. Strict positivity means the
  system retains its state indefinitely.
\item FIRST FORMAL PROOF OF A HILL-FUNCTION PROPERTY: To the best of our
  knowledge, this is the first formally verified property of the
  Gardner et al. toggle switch using interactive theorem proving. It
  demonstrates that our dDL tooling scales from simple mass-action CRN
  examples to realistic gene regulatory network models involving
  rational functions.
\end{enumerate}

  \textbf{HOW WE VERIFY IT}\\
  \textbf{POSITIVITY OF u: DIFFERENTIAL GHOST (DG).}\\
  We cannot prove u(t) > 0 by Differential Induction (DI) alone: the Lie
  derivative of u along the vector field includes the -u term, which
  is negative when u is positive. DI requires this derivative to be
  non-negative along the trajectory, which fails.

  Instead, we use the DIFFERENTIAL GHOST technique. We introduce a ghost
  variable g satisfying the linear ODE:

\begin{verbatim}
      g' = g / 2,    g(0) = 1 / sqrt(u(0))
\end{verbatim}

  (This is the same ghost trick we use for exponential decay and for
  CRN simple decay.) The key insight: consider the combined quantity

\begin{verbatim}
      I(u, g) = u * g^2
\end{verbatim}

  Its Lie derivative along the EXTENDED vector field (u-dynamics plus
  g-dynamics) is:

\begin{verbatim}
      dI/dt = (du/dt) * g^2 + u * 2g * (dg/dt)
            = (alpha1/(1+v^beta) - u) * g^2 + u * 2g * (g/2)
            = alpha1/(1+v^beta) * g^2 - u*g^2 + u*g^2
            = alpha1/(1+v^beta) * g^2
\end{verbatim}

  The -u*g\textasciicircum{}2 from the ODE and the +u*g\textasciicircum{}2 from the ghost CANCEL
  perfectly (this is DG magic!). The residual
  alpha1/(1+v\textasciicircum{}beta) * g\textasciicircum{}2 is >= 0 provided:
\begin{enumerate}
\item alpha1 >= 0 (the production rate is non-negative - physically natural)
\item 1 + v\textasciicircum{}beta > 0 (the Hill denominator is positive)
\item g\textasciicircum{}2 >= 0 (always true for real g)
\end{enumerate}
  Condition 2 holds whenever v >= 0 and beta is a positive integer, which
  is exactly the assumption of the conditional result.

  Given that dI/dt >= 0 and I(0) = u(0) * g(0)\textasciicircum{}2 = u(0) * (1/sqrt(u(0)))\textasciicircum{}2 = 1,
  we conclude I(tau) >= 1 for all tau in [0, t]. Since g\textasciicircum{}2 >= 0, this means u*g\textasciicircum{}2 >= 1
  forces u > 0 (because if u <= 0, the product u*g\textasciicircum{}2 could not be >= 1).

  \textbf{NON-NEGATIVITY OF v: DIFFERENTIAL INDUCTION WITH A BOUNDARY CONDITION
  (DI\_boundary).}\\
  Our DI\_Generic (and its vector counterpart DI\_Vect)
  faithfully formalizes, as a provably verified lemma, the STANDARD
  differential induction rule of dDL, which requires the Lie derivative
  of the candidate invariant to be >= 0 EVERYWHERE ALONG THE TRAJECTORY,
  not just at the boundary. For the invariant v >= 0, the Lie derivative
  is:

\begin{verbatim}
      d(v - 0)/dt = alpha2/(1+u^gamma) - v
\end{verbatim}

  This expression is NOT globally non-negative: when v is large, it
  becomes negative. Hence, standard DI cannot discharge the inductive
  step. The property v >= 0 is only at risk on the BOUNDARY v = 0,
  where the Lie derivative reduces to alpha2/(1+u\textasciicircum{}gamma), which
  is strictly positive when alpha2 > 0 and gamma is even. This is a
  well-known limitation in the original formulation of DI, not a defect
  of our formalization; DI\_boundary only requires a strictly positive
  derivative on the boundary.

  \textbf{UNCONDITIONAL POSITIVITY OF u}\\
  The non-negativity of v discharges the
  assumption of the conditional result. No DC is needed for this
  composition.

  \textbf{ASSUMPTIONS}\\
  The unconditional theorem assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial conditions: u(0) > 0 and v(0) >= 0
\item The time t >= 0
\item The production rates: alpha1 >= 0 and alpha2 > 0
\item The Hill coefficients beta and gamma are natural numbers with
  beta >= 1 and gamma >= 1, and gamma is even
\end{enumerate}
  The conditional result needs only alpha1 >= 0 and beta >= 1 among the
  parameter conditions, and assumes v(tau) >= 0 for all tau in [0, t]
  instead of v(0) >= 0.

  \textbf{FORMALIZATION}\\
  We represent the two proteins and the ghost as components of a state
  vector over an arbitrary finite index type 'p, at three pairwise
  distinct coordinates:
\begin{itemize}
\item Coordinate iU: concentration of protein u
\item Coordinate iV: concentration of protein v
\item Coordinate iG: a spare coordinate that holds the ghost g
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iU := du/dt, iV := dv/dt))
\end{verbatim}

  The positivity proofs apply DG to extend the trajectory with the ghost
  at iG, then DI\_Vect to prove u*g\textasciicircum{}2 >= 1 along the extended
  trajectory; the non-negativity of v uses DI\_boundary.
\<close>
lemma gardner_toggle_switch_u_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  fixes iU iV iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iG\<close> \<open>iV \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                      iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iU: u (protein 1), coordinate iV: v (protein 2).
         Gardner toggle switch:
           du/dt = alpha1/(1 + v\textasciicircum{}beta) - u;
           dv/dt = alpha2/(1 + u\textasciicircum{}gamma) - v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) iU > (0::real)\<close>
      \<comment> \<open>Initial condition: u(0) > 0 (protein 1 is initially present)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn: \<open>0 \<le> \<alpha>1\<close>
      \<comment> \<open>The production rate is non-negative, as is physically natural\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
      \<comment> \<open>The Hill coefficient is a positive integer\<close>
  \<comment> \<open>The conditional assumption, explained in the text above the lemma:\<close>
  assumes v_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) iV\<close>
      \<comment> \<open>Protein v stays non-negative along the trajectory.
         This assumption is discharged in
         gardner\_toggle\_switch\_u\_positive\_unconditional by applying
         gardner\_toggle\_switch\_v\_nonneg, which uses DI\_boundary.\<close>
  shows \<open>0 < vec_nth (x t) iU\<close>
    \<comment> \<open>Conclusion: protein u remains strictly positive at time t\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the apply-DG-then-apply-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y at coordinate iG satisfying 
                     dy/dt = (1/2)\<sqdot>y with initial value y(0) = 1/sqrt(u(0)). 
                     The combined trajectory ?z = x extended at the ghost coordinate iG 
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

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iU)\<close>

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

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: 
   \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
          vec_lambda ((\<lambda>k::'p. 0)(
                       iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                       iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                  iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v =
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                  iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The vector field reads indices 0 and 1; neither is 2 *)
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    have v1: \<open>vec_nth v iV = vec_nth w iV\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
            iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
            iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> w\<close>
      using v0 v1
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                   iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = iG,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                   iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (iG := y \<tau>))\<close>

  (* Helper: Fréchet derivative of u \<sqdot> y² (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iU * (vec_nth p iG)^2 + 
           vec_nth p iU * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iU) has_derivative (\<lambda>v. vec_nth v iU)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
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
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) iU * (vec_nth (?z 0) iG)^2\<close>
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
                 ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                           iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                           iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have v_nn_\<tau>: \<open>0 \<le> vec_nth (x \<tau>) iV\<close>
      using v_nn[OF \<tau>_in] .
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                            iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha>1 / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                            iV := \<alpha>2 / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iU * (vec_nth (?z \<tau>) iG)^2 + 
                                      vec_nth (?z \<tau>) iU * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
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
  have ineq: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
    using DI_Vect[where  h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iU * (vec_nth v iG)^2\<close>,
                  OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iU\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iU = vec_nth (x t) iU\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iU \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed



text \<open>
  \textbf{WHAT WE HAVE ACCOMPLISHED}\\
\begin{enumerate}
\item First formally verified property of the Gardner et al. toggle switch:
  strict positivity of protein u, conditional on v being non-negative.
\item Successful integration of Hill function derivatives with DG and DI\_Vect,
  demonstrating that our dDL tooling scales to realistic gene regulatory
  network models.
\item The proof pattern is reusable: the same structure applies to the
  symmetric argument for v (swapping the roles of u and v, and the
  coefficients alpha1/beta with alpha2/gamma).
\end{enumerate}
\<close>
text \<open>
  \textbf{PART B: Non-negativity of v for the Gardner toggle switch (via DI\_boundary)}\\
  We prove: if v(0) >= 0, alpha2 > 0, and gamma is a positive even Hill coefficient,
  then v(tau) >= 0 throughout the Gardner toggle switch trajectory.

  \textbf{PROOF METHOD: Differential Induction with Boundary Condition (DI\_boundary).}\\
  The candidate function is \texttt{invar(w) = vec\_nth w iV} (i.e., the v component).
\begin{itemize}
\item Differentiability assumption: invar is linear, so it's everywhere
  Frechet-differentiable with Dinvar = (lambda w. vec\_nth w iV).
\item Boundary condition: at every point where v = 0 (i.e., vec\_nth (y tau) iV = 0),
  we need 0 < Dinvar (f tau (y tau)) = vec\_nth (f tau (y tau)) iV.
\end{itemize}

    The Gardner ODE gives:
\begin{verbatim}
      vec_nth (f tau (y tau)) iV
        = alpha2/(1 + (vec_nth (y tau) iU)^gamma) - vec_nth (y tau) iV
        = alpha2/(1 + (vec_nth (y tau) iU)^gamma) - 0      (since v = 0)
        = alpha2/(1 + u^gamma)
\end{verbatim}

    Since alpha2 > 0 and 1 + u\textasciicircum{}gamma > 0 (because gamma is even, so u\textasciicircum{}gamma >= 0),
    the quotient is strictly positive.
\<close>

lemma gardner_toggle_switch_v_nonneg:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  fixes iU iV :: 'p
  assumes coords: \<open>iU \<noteq> iV\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                      iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))
                                    )) {0..t} UNIV\<close>
  assumes v0_nn: \<open>0 \<le> vec_nth (x 0) iV\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>2_pos: \<open>0 < \<alpha>2\<close>
  assumes \<gamma>_even: \<open>even \<gamma>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>
  shows \<open>0 \<le> vec_nth (x t) iV\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Apply DI_boundary with  invar = \<lambda>w. vec_nth w iV
     
     DI_boundary establishes non-negativity of a function along the 
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
  have iv: \<open>0 \<le> (\<lambda>w. vec_nth w iV) (x 0)\<close>
    using v0_nn
    by simp

  (* PROOF OBLIGATION 2 (ODE): directly from x_sol *)
  (* (no separate `have` needed; we pass x_sol directly) *)

  (* PROOF OBLIGATION 3 (t): directly from t *)
  (* (no separate `have` needed; we pass t directly) *)

  (* PROOF OBLIGATION 4 (invar_diff): invar is differentiable everywhere along x *)
  have invar_diff: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 
                        \<exists> Dinvar. ((\<lambda>w. vec_nth w iV) has_derivative Dinvar) (at (x \<tau>))\<close>
  proof -
    fix \<tau> assume \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists> Dinvar. ((\<lambda>w. vec_nth w iV) has_derivative Dinvar) (at (x \<tau>))\<close>
      by (rule exI[where x = \<open>\<lambda>w. vec_nth w iV\<close>]) (rule has_derivative_vec_nth)
  qed

  (* PROOF OBLIGATION 5 (boundary_step): at v = 0, the Lie derivative is strictly positive.
     
     The Lie derivative is dv/dt = \<alpha>2/(1 + u^\<gamma>) - v. 
     When v = 0, this becomes \<alpha>2/(1 + u^\<gamma>), which is > 0 because 
     \<alpha>2 > 0 and the denominator is strictly positive (1 + u^\<gamma> > 0 
     when \<gamma> is even, so u^\<gamma> \<ge> 0). *)
  have boundary_step: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> (\<lambda>w. vec_nth w iV) (x \<tau>) = 0 \<Longrightarrow>
                           \<exists> Dinvar. ((\<lambda>w. vec_nth w iV) has_derivative Dinvar) (at (x \<tau>)) \<and>
                                     0 < Dinvar ((\<lambda>t v.
                                       vec_lambda ((\<lambda>k. 0)(
                                         iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                         iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> (x \<tau>))\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t}\<close>
    assume v_eq_0: \<open>(\<lambda>w. vec_nth w iV) (x \<tau>) = 0\<close>
    hence v_zero: \<open>vec_nth (x \<tau>) iV = 0\<close>
      by simp

    (* Use Dinvar = vec_nth \<sqdot> iV *)
    have deriv: \<open>((\<lambda>w. vec_nth w iV) has_derivative (\<lambda>w. vec_nth w iV)) (at (x \<tau>))\<close>
      by (rule has_derivative_vec_nth)

    (* Compute Dinvar applied to the vector field *)
    let ?u = \<open>vec_nth (x \<tau>) iU\<close>
    have field_1: \<open>vec_nth ((\<lambda>t v.
        vec_lambda ((\<lambda>k. 0)(
          iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
          iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> (x \<tau>)) iV = 
         \<alpha>2 / (1 + ?u^\<gamma>) - vec_nth (x \<tau>) iV\<close>
      by (simp add: fun_upd_def)
    also have \<open>... = \<alpha>2 / (1 + ?u^\<gamma>)\<close>
      using v_zero
      by simp
    finally have lie_val: 
              \<open>vec_nth ((\<lambda>t v.
                            vec_lambda ((\<lambda>k. 0)(
                              iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                              iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> (x \<tau>)) iV =
                             \<alpha>2 / (1 + ?u^\<gamma>)\<close> .

    (* Show this is strictly positive *)
    have u_\<gamma>_nn: \<open>0 \<le> ?u^\<gamma>\<close>
      using \<gamma>_even
      by (simp add: zero_le_even_power)
    have denom_pos: \<open>0 < 1 + ?u^\<gamma>\<close>
      using u_\<gamma>_nn
      by linarith
    have lie_pos: \<open>0 < \<alpha>2 / (1 + ?u^\<gamma>)\<close>
      using \<alpha>2_pos denom_pos 
      by simp
    show \<open>\<exists> Dinvar. ((\<lambda>w. vec_nth w iV) has_derivative Dinvar) (at (x \<tau>)) \<and>
                    0 < Dinvar ((\<lambda>t v.
                      vec_lambda ((\<lambda>k. 0)(
                        iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                        iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> (x \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>w. vec_nth w iV\<close>])
      apply (rule conjI)
       apply (rule deriv)
      using lie_val lie_pos 
      apply simp
      done
  qed

  (* APPLY DI_boundary via forward reasoning *)
  have nn_at_t: \<open>0 \<le> (\<lambda>w. vec_nth w iV) (x t)\<close>
    using DI_boundary[where invar = \<open>\<lambda>w. vec_nth w iV\<close> and
                            f = \<open>\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                  iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))\<close> and
                            Q = UNIV,
                      OF iv x_sol t invar_diff boundary_step] .

  thus ?thesis 
    by simp
qed


text \<open>
  \textbf{PART C: The unconditional Gardner toggle switch positivity theorem}\\

  This upgrades gardner\_toggle\_switch\_u\_positive from conditional
  (assuming v(tau) >= 0 throughout) to UNCONDITIONAL (just assuming
  v(0) >= 0 and the parameter assumptions).

  \textbf{PROOF STRATEGY:}\\
\begin{enumerate}
\item Use gardner\_toggle\_switch\_v\_nonneg (from Part B) to establish
  v(tau) >= 0 for all tau in [0..t]. This requires:
\begin{itemize}
\item alpha2 > 0
\item gamma even
\item gamma >= 1
\item v(0) >= 0
\end{itemize}
\item Feed this as the v\_nn assumption to gardner\_toggle\_switch\_u\_positive.
\item Conclude u(t) > 0 unconditionally.
\end{enumerate}

  The key observation: once we can prove v >= 0 via DI\_boundary, we have
  exactly what the conditional theorem needed. No DC required for this
  composition: we just apply the conditional theorem with the proven
  non-negativity.
\<close>
lemma gardner_toggle_switch_u_positive_unconditional:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: real
  fixes \<beta> \<gamma> :: nat
  fixes iU iV iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iG\<close> \<open>iV \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)
                                                (iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                                 iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))
                                    )) {0..t} UNIV\<close>
  assumes u0_pos: \<open>vec_nth (x 0) iU > (0::real)\<close>
  assumes v0_nn: \<open>0 \<le> vec_nth (x 0) iV\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn: \<open>0 \<le> \<alpha>1\<close>
  assumes \<alpha>2_pos: \<open>0 < \<alpha>2\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  assumes \<gamma>_even: \<open>even \<gamma>\<close>
  assumes \<gamma>_pos: \<open>1 \<le> \<gamma>\<close>
  shows \<open>0 < vec_nth (x t) iU\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* Step 1: we prove 0 \<le> v(\<tau>) for all \<tau> \<in> [0..t] using gardner_toggle_switch_v_nonneg *)
  have v_nn_on_interval: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) iV\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    have x_sol_\<tau>: \<open>(x solves_ode (\<lambda>t v.
                                     vec_lambda ((\<lambda>k. 0)
                                                 (iU := \<alpha>1 / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                                  iV := \<alpha>2 / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))
                                     )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF x_sol] \<tau>_in  .
    (* Apply gardner_toggle_switch_v_nonneg *)
    show \<open>0 \<le> vec_nth (x \<tau>) iV\<close>
      using \<tau>_in gardner_toggle_switch_v_nonneg[OF coords(1) x_sol_\<tau> v0_nn _  \<alpha>2_pos \<gamma>_even \<gamma>_pos] 
      by simp
  qed
  (* Step 2: Apply the conditional theorem gardner_toggle_switch_u_positive *)
  show ?thesis
    using gardner_toggle_switch_u_positive[OF coords x_sol u0_pos t \<alpha>1_nn \<beta>_pos v_nn_on_interval] .
qed

text \<open>
  \textbf{SUMMARY OF THE UNCONDITIONAL RESULT}\\
  We have proved:

    \textbf{THEOREM (Unconditional Strict Positivity for the Gardner Toggle Switch):}\\

    For the Gardner et al. (Nature 2000) toggle switch ODE

\begin{verbatim}
        du/dt = alpha1 / (1 + v^beta) - u
        dv/dt = alpha2 / (1 + u^gamma) - v
\end{verbatim}

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
\begin{enumerate}
\item DI\_boundary (boundary-aware differential induction) enables the
  unconditional non-negativity proof. This is the first Isabelle/HOL
  formalization of a strengthened DI rule in the style of Platzer's
  barrier-certificate variants.
\item Hill function derivatives for EVEN Hill coefficients (without sign
  assumption on the regulator) provide the analytic machinery needed
  for gene regulatory network formalization.
\item The composition of DI\_boundary + the existing conditional theorem
  (via DG) shows that our dDL tooling supports MODULAR proof strategies:
  each rule handles a specific kind of argument, and they compose
  cleanly via shared trajectory objects.
\end{enumerate}
\<close>

subsubsection \<open>Time-dependent Gardner toggle switch\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  This example generalizes the Gardner toggle switch lemmas to allow
  TIME-DEPENDENT production rates alpha1(tau), alpha2(tau). This captures the
  experimental scenario where an inducer is added to the chemical bath,
  transiently changing the effective transcription rate of one of the
  genes and causing the switch to flip.

  \textbf{THE CIRCUIT}\\
  The circuit is the Gardner toggle switch of the previous example,

\begin{verbatim}
      Gene 1 -> Protein u -| Gene 2
      Gene 2 -> Protein v -| Gene 1
\end{verbatim}

  with production rates that vary in time.

  \textbf{THE ODE MODEL}\\
  The time-varying toggle switch ODE is:

\begin{verbatim}
      du/dt = alpha1(tau) / (1 + v^beta) - u
      dv/dt = alpha2(tau) / (1 + u^gamma) - v
\end{verbatim}

  where alpha1, alpha2 :: real => real are functions of time.

  \textbf{WHAT WE VERIFY}\\
  Conditional positivity of u under time-varying rates: if u(0) > 0,
  alpha1(tau) >= 0 for all tau in [0, t], and v(tau) stays non-negative
  throughout [0, t], then u(t) > 0.

  \textbf{WHY THIS MATTERS}\\
  Positivity is a safety property: it says the system doesn't
  collapse regardless of how the rates are varied. It is a necessary
  precondition for any meaningful switching behavior, and it holds under
  genuinely time-varying rates.

  To model an "induced switching experiment", instantiate alpha1 and alpha2
  with smooth time profiles. For example, a transient inducer pulse
  that drops alpha1 from a baseline alpha1\_high to a low value alpha1\_low and
  back could be modeled as a bump:

\begin{verbatim}
      alpha1(tau) = alpha1_high - (alpha1_high - alpha1_low) *
                                  bump(tau, t_start, t_end, steepness)
\end{verbatim}

  where bump is a continuous function that is 0 outside
  [t\_start, t\_end] and close to 1 inside. Piecewise-constant inducer
  signals (exact step functions) are not directly modeled here: a single
  solution x cannot cross a jump of alpha1, because u' would have to jump
  there and a derivative cannot have a jump discontinuity. They naturally
  fit the compositional Hoare-logic approach instead.

  \textbf{HOW WE VERIFY IT}\\
  Little changes from the constant-rate version. The DG reasoning for
  u-positivity used the cancellation

\begin{verbatim}
      d(u*y^2)/dt = (alpha1/(1+v^beta) - u)*y^2 + u*2y*(y/2)
                  = alpha1/(1+v^beta)*y^2 - u*y^2 + u*y^2
                  = alpha1/(1+v^beta)*y^2
\end{verbatim}

  which remains valid when alpha1 is replaced by alpha1(tau), giving
  alpha1(tau)/(1+v\textasciicircum{}beta)*y\textasciicircum{}2, still non-negative provided alpha1(tau) >= 0 pointwise.

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: u(0) > 0
\item The time t >= 0
\item The production rate for u is non-negative pointwise:
  alpha1(tau) >= 0 for all tau in [0, t]
\item The Hill coefficient beta is a natural number with beta >= 1
\item Protein v stays non-negative: v(tau) >= 0 for all tau in [0, t]
\end{enumerate}
  Continuity of alpha1 and alpha2 is not among the assumptions, because
  the theorem assumes the solution x. Continuity is what the classical
  ODE existence theory needs to provide such a solution: the vector field
  (lambda t v. vec\_lambda ((lambda k. 0)(iU := alpha1(t)/... - vec\_nth v iU,
  iV := alpha2(t)/... - vec\_nth v iV))) must be continuous in t, so in
  applications alpha1 and alpha2 should be continuous\_on \{0..t\}.

  \textbf{FORMALIZATION}\\
  We represent the two proteins and the ghost as components of a state
  vector over an arbitrary finite index type 'p, at three pairwise
  distinct coordinates:
\begin{itemize}
\item Coordinate iU: concentration of protein u
\item Coordinate iV: concentration of protein v
\item Coordinate iG: a spare coordinate that holds the ghost y
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iU := du/dt, iV := dv/dt))
\end{verbatim}

  As in the constant-rate version, the proof applies DG to extend the
  trajectory with the ghost at iG, then DI\_Vect to prove
  u*y\textasciicircum{}2 >= 1 along the extended trajectory.

  \textbf{LIMITATIONS}\\
  Non-negativity of v is assumed here. The DI\_boundary argument of the
  constant-rate version would only need alpha2(tau) > 0 AT THE SPECIFIC
  TIMES tau where v(tau) = 0 (the boundary-crossing times); the cleanest
  sufficient condition is alpha2(tau) > 0 for all tau in [0..t].

  Positivity does NOT prove that changing alpha1(tau) actually causes the
  switch to flip to a different stable state; that would require
  basin-of-attraction analysis and Lyapunov stability reasoning (see the
  other proof leveraging the Lyapunov reachability rule).
\<close>

lemma gardner_toggle_switch_u_positive_time_dependent:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha>1 \<alpha>2 :: \<open>real \<Rightarrow> real\<close>
  fixes \<beta> \<gamma> :: nat
  fixes iU iV iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iG\<close> \<open>iV \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>\<tau> v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                      iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Time-varying Gardner toggle switch:
           du/dt = alpha1(tau)/(1 + v\textasciicircum{}beta) - u;
           dv/dt = alpha2(tau)/(1 + u\textasciicircum{}gamma) - v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) iU > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>1_nn_pointwise: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> \<alpha>1 \<tau>\<close>
      \<comment> \<open>The production rate for u is non-negative pointwise along the trajectory\<close>
  assumes \<beta>_pos: \<open>1 \<le> \<beta>\<close>
  \<comment> \<open>The conditional assumption: v stays non-negative\<close>
  assumes v_nn: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (x \<tau>) iV\<close>
  shows \<open>0 < vec_nth (x t) iU\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Same apply-DG-then-apply-DI pattern as the constant-rate version.
     
     STAGE 1 (DG): Ghost y at coordinate iG with dy/dt = (1/2)\<sqdot>y, y(0) = 1/\<surd>u(0).
     STAGE 2 (DI): Invariant 1 \<le> u\<sqdot>y². Lie derivative computation uses 
                   \<alpha>1(\<tau>)/(1+v^\<beta>)\<sqdot>y² \<ge> 0, which requires \<alpha>1(\<tau>) \<ge> 0 pointwise.
     STAGE 3 (algebra): From u\<sqdot>y² \<ge> 1 and y² \<ge> 0, conclude u > 0.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iU)\<close>

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

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>\<tau> v.
      vec_lambda ((\<lambda>k::'p. 0)(
        iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
        iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index.
     Note: even though \<alpha>1, \<alpha>2 are functions of \<tau>, they depend only on \<tau> 
     (not on v), so the gi_fresh argument is unchanged: the vector field reads 
     vec_nth v iU and vec_nth v iV but not vec_nth v iG. *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                           (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                 iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v =
                              (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
                                 iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    have v1: \<open>vec_nth v iV = vec_nth w iV\<close>
      using eq
      by simp
    show \<open>(\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
            iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> v =
          (\<lambda>\<tau> v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha>1 \<tau> / (1 + (vec_nth v iV)^\<beta>) - vec_nth v iU,
            iV := \<alpha>2 \<tau> / (1 + (vec_nth v iU)^\<gamma>) - vec_nth v iV))) \<tau> w\<close>
      using v0 v1
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                   iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where 
            a = \<open>\<lambda>\<tau>. 1/2\<close> and 
            b = \<open>\<lambda>\<tau>. 0\<close> and 
            ?y0.0 = y0 and
            gi = iG,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                   iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i)(iG := y \<tau>))\<close>

  (* Helper: Fréchet derivative of u \<sqdot> y² *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iU * (vec_nth p iG)^2 + 
           vec_nth p iU * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iU) has_derivative (\<lambda>v. vec_nth v iU)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> u \<sqdot> y² along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> u(0) \<sqdot> y(0)² *)
  have iv_ineq: \<open>1 \<le> vec_nth (?z 0) iU * (vec_nth (?z 0) iG)^2\<close>
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
                 ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                           iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                           iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in_t: \<open>\<tau> \<in> {0..t}\<close>
    have \<alpha>1_\<tau>_nn: \<open>0 \<le> \<alpha>1 \<tau>\<close>
      using \<alpha>1_nn_pointwise[OF \<tau>_in_t] .
    have v_\<tau>_nn: \<open>0 \<le> vec_nth (x \<tau>) iV\<close>
      using v_nn[OF \<tau>_in_t] .
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                            iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha>1 \<tau> / (1 + vec_nth v iV ^ \<beta>) - vec_nth v iU,
                            iV := \<alpha>2 \<tau> / (1 + vec_nth v iU ^ \<gamma>) - vec_nth v iV)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iU * (vec_nth (?z \<tau>) iG)^2 + 
                                      vec_nth (?z \<tau>) iU * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      using \<alpha>1_\<tau>_nn v_\<tau>_nn
      apply (metis add_increasing2 diff_eq_eq distrib_right mult_nonneg_nonneg 
                   zero_le_divide_iff zero_le_power zero_le_square zero_less_one_class.zero_le_one)
      done
  qed

  (* We APPLY DI_Vect *)
  have ineq: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
    using DI_Vect[where 
            h = \<open>\<lambda>v. 1\<close> and 
            g = \<open>\<lambda>v. vec_nth v iU * (vec_nth v iG)^2\<close>,
            OF iv_ineq combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)² \<ge> 1 and y(t)² \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iU\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iU = vec_nth (x t) iU\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iU \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

subsubsection \<open>Negative autoregulation\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  Negative autoregulation is the simplest gene regulatory motif: a gene
  whose protein product represses its own expression. This is the
  foundational feedback loop in biology, appearing in \textasciitilde{}40\% of all known
  transcription networks.

  Reference: Uri Alon, "An Introduction to Systems Biology: Design
  Principles of Biological Circuits" (2006), Chapter 3.

  Negative autoregulation is used by cells to:
\begin{itemize}
\item Speed up response times (homeostasis)
\item Reduce cell-to-cell variability in protein levels
\item Provide robustness against fluctuations in alpha
\end{itemize}

  \textbf{THE CIRCUIT}\\
  A single gene whose protein represses its own expression:

\begin{verbatim}
      Gene u -> Protein u -| Gene u
\end{verbatim}

  \textbf{THE ODE MODEL}\\
\begin{verbatim}
      du/dt = alpha / (1 + u^n) - beta*u
\end{verbatim}

  where:
\begin{verbatim}
    alpha  is the maximal production rate (baseline promoter strength)
    beta   is the protein degradation rate
    n      is the Hill coefficient (cooperativity of the self-repression)
    u      is the protein concentration
\end{verbatim}

  When u is small, the Hill term alpha/(1+u\textasciicircum{}n) approx alpha is large -> rapid production.
  When u is large, the Hill term is small -> production slows while
  degradation beta*u continues. The system converges to a unique steady state.

  \textbf{WHAT WE VERIFY}\\
    If u(0) > 0, alpha >= 0, beta > 0, and n is a positive even integer,
    then u(t) > 0 for all t >= 0.

  In words: protein concentration remains strictly positive forever,
  provided the initial condition is positive.

  \textbf{WHY THIS MATTERS}\\
  Positivity certifies that the model stays physically meaningful: a
  protein concentration that vanished or became negative in finite time
  would signal a modeling error. Negative autoregulation is also the
  smallest feedback loop in the benchmark, and its positivity proof is the
  pattern for the larger circuits: the repressilator uses three copies of
  the same argument.

  \textbf{HOW WE VERIFY IT}\\
  DIFFERENTIAL GHOST (DG). This is the same proof pattern as the simple
  decay example in the CRN benchmark (crn\_simple\_decay\_positivity), with
  the non-negative production term alpha/(1+u\textasciicircum{}n) added. That term
  is always >= 0 (since alpha >= 0 and u\textasciicircum{}n >= 0 for even n), so
  the argument carries through unchanged.

\begin{verbatim}
  Ghost: g' = (beta/2)*g,  g(0) = 1/sqrt(u(0))
  Invariant: u * g^2 >= 1
  Lie derivative:
    d(u*g^2)/dt = (du/dt)*g^2 + u*2g*(dg/dt)
                = (alpha/(1+u^n) - beta*u)*g^2 + u*2g*(beta/2*g)
                = alpha/(1+u^n)*g^2 - beta*u*g^2 + beta*u*g^2
                = alpha/(1+u^n)*g^2
                >= 0   (since alpha >= 0, 1+u^n > 0, g^2 >= 0)
\end{verbatim}

  The beta*u*g\textasciicircum{}2 terms cancel (DG magic). The residual alpha/(1+u\textasciicircum{}n)*g\textasciicircum{}2 is
  non-negative. Hence u*g\textasciicircum{}2 >= 1 is invariant, which implies u > 0.

  DI\_boundary is NOT needed here, because the ODE has the clean -beta*u
  decay term that DG handles directly. DI\_boundary becomes necessary only
  when the decay structure is absent, non-uniform, or when we need
  non-negativity without strict positivity. This illustrates a design
  principle: our dDL proof rules offer multiple proof strategies, and the
  choice of how to apply them depends on the ODE structure. DG is the
  shorter path for systems with uniform linear decay; DI\_boundary is the
  right tool for boundary-only invariants.

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial condition: u(0) > 0
\item The time t >= 0
\item The production rate is non-negative: alpha >= 0
\item The degradation rate is positive: beta > 0
\item The Hill coefficient n is a natural number with n >= 1, and n is even
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the protein and the ghost as components of a state vector
  over an arbitrary finite index type 'p, at two distinct coordinates:
\begin{itemize}
\item Coordinate iU: concentration of the protein, i.e., u
\item Coordinate iG: a spare coordinate that holds the ghost g
\end{itemize}

  The ODE is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iU := du/dt))
\end{verbatim}

  The proof applies DG to extend the trajectory with the ghost at iG,
  then DI\_Vect to prove u*g\textasciicircum{}2 >= 1 along the extended
  trajectory.
\<close>

lemma negative_autoregulation_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> \<beta> :: real
  fixes n :: nat
  fixes iU iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iU: protein u. ODE: du/dt = alpha/(1 + u\textasciicircum{}n) - beta*u\<close>
  assumes u0_pos: \<open>vec_nth (x 0) iU > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes \<beta>_pos: \<open>0 < \<beta>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) iU\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the apply-DG-then-apply-DI pattern:
     
       STAGE 1 (DG): Introduce a ghost species y at coordinate iG satisfying 
                     dy/dt = (\<beta>/2)\<sqdot>y with initial value y(0) = 1/sqrt(u(0)). 
                     The combined trajectory ?z = x extended at the ghost coordinate iG 
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
     separate `have` statement, and the provably verified dDL lemma is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iU)\<close>

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

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(
        iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                           (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))) \<tau> v =
                              (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The field only reads coordinate iU; not coordinate iG *)
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU))) \<tau> w\<close>
      using v0
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (\<beta>/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (iG := (\<beta>/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. \<beta>/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = iG,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (\<beta>/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (iG:=y \<tau>))\<close>

  (* Helper: Frechet derivative of u \<sqdot> y\<^sup>2 (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iU * (vec_nth p iG)^2 + 
           vec_nth p iU * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iU) has_derivative (\<lambda>v. vec_nth v iU)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
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
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) (?z 0)\<close>
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
                 ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (\<beta>/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                        ((\<lambda>k. 0)
                         (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                       vec_lambda
                        ((\<lambda>i. 0)(iG := (\<beta>/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (\<beta>/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iU)^n) - \<beta> * vec_nth v iU)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (\<beta>/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iU * (vec_nth (?z \<tau>) iG)^2 + 
                                    vec_nth (?z \<tau>) iU * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) iU ^ n) - \<beta> * vec_nth (x \<tau>) iU) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) iU * (y \<tau> * (\<beta> * y \<tau>)) =
                          \<alpha> / (1 + vec_nth (x \<tau>) iU ^ n) * (y \<tau> * y \<tau>)\<close>)
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
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iU * (vec_nth v iG)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iU\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iU = vec_nth (x t) iU\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iU \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed


subsubsection \<open>The repressilator (Elowitz \& Leibler 2000)\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The repressilator is the first synthetic biological clock: a
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
\begin{verbatim}
      Gene u -> Protein u -| Gene v
      Gene v -> Protein v -| Gene w
      Gene w -> Protein w -| Gene u
\end{verbatim}

  A ring of three repressive interactions. With the right parameters,
  no stable fixed point exists and the system oscillates: the three
  protein concentrations rise and fall in sequence, forming a
  phase-shifted trio.

  \textbf{THE ODE MODEL}\\
\begin{verbatim}
      du/dt = alpha / (1 + w^n) - u
      dv/dt = alpha / (1 + u^n) - v
      dw/dt = alpha / (1 + v^n) - w
\end{verbatim}

  where:
\begin{verbatim}
    alpha    is the maximal protein production rate
    n        is the Hill coefficient (cooperativity)
    u, v, w  are the three protein concentrations
\end{verbatim}

  For simplicity we use a symmetric model (same alpha and n for all three
  genes). The original Elowitz-Leibler paper uses this symmetric form
  for their theoretical analysis.

  \textbf{WHAT WE VERIFY}\\
  \textbf{STRICT POSITIVITY OF ALL THREE PROTEINS:}\\
    If u(0) > 0, v(0) > 0, w(0) > 0, alpha >= 0, and n is a positive even
    integer, then u(t) > 0, v(t) > 0, w(t) > 0 for all t >= 0.

  In words: once all three proteins are present, they all remain
  strictly positive forever. The repressilator never "turns off" any
  of its components in finite time.

  \textbf{WHY THIS MATTERS}\\
  Strict positivity is a simpler but still meaningful safety property:
  it certifies that the ODE model remains physically meaningful forever.
  It is also a precondition for the oscillation analysis, which needs
  machinery beyond our current tooling (see LIMITATIONS).

  \textbf{HOW WE VERIFY IT}\\
  \textbf{DIFFERENTIAL GHOST (DG), THREE INDEPENDENT COPIES.}\\
  \textbf{KEY OBSERVATION}\\
  With EVEN Hill coefficients, the positivity proof
  for each component is INDEPENDENT of the other components. The ring
  coupling disappears at the level of the positivity argument.

  \textbf{For u-positivity:}\\
\begin{verbatim}
    Ghost: g' = g/2,  g(0) = 1/sqrt(u(0))
    Invariant: u*g^2 >= 1
    Lie derivative:
      d(u*g^2)/dt = (du/dt)*g^2 + u*2g*(dg/dt)
                  = (alpha/(1+w^n) - u)*g^2 + u*2g*(g/2)
                  = alpha/(1+w^n)*g^2 - u*g^2 + u*g^2
                  = alpha/(1+w^n)*g^2
                  >= 0   (since alpha >= 0, w^n >= 0 for even n, g^2 >= 0)
\end{verbatim}

  CRUCIALLY: the Hill term alpha/(1+w\textasciicircum{}n) is always non-negative for even n,
  regardless of the sign of w. So we do NOT need to prove w >= 0 first.
  This is the same reason negative autoregulation works with DG alone.

  The proofs for v and w are symmetric.

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from solves\_ode)
\item The initial conditions: u(0) > 0, v(0) > 0 and w(0) > 0
\item The time t >= 0
\item The production rate is non-negative: alpha >= 0
\item The Hill coefficient n is a natural number with n >= 1, and n is even
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three proteins and the ghost as components of a state
  vector over an arbitrary finite index type 'p, at four pairwise
  distinct coordinates:
\begin{itemize}
\item Coordinate iU: concentration of protein u
\item Coordinate iV: concentration of protein v
\item Coordinate iW: concentration of protein w
\item Coordinate iG: a spare coordinate that holds the ghost g
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iU := du/dt, iV := dv/dt, iW := dw/dt))
\end{verbatim}

  Each of repressilator\_u\_positive, repressilator\_v\_positive and
  repressilator\_w\_positive applies DG to extend the trajectory with the
  ghost at iG, then DI\_Vect along the extended trajectory;
  repressilator\_all\_positive combines the three.

  \textbf{LIMITATIONS}\\
  Proving that the repressilator actually OSCILLATES (under certain
  parameters) requires machinery beyond our current tooling:
  Poincar\'{e}-Bendixson theory, Hopf bifurcation analysis, or numerical
  phase portrait computations.
\<close>

text \<open>Lemma 1: positivity of u (ghost at coordinate iG, witness u * g\textasciicircum{}2).\<close>
lemma repressilator_u_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  fixes iU iV iW iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iW\<close> \<open>iU \<noteq> iG\<close>
                  \<open>iV \<noteq> iW\<close> \<open>iV \<noteq> iG\<close> \<open>iW \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                      iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                      iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iU: u, coordinate iV: v, coordinate iW: w.
         Ring: u is repressed by w, v by u, and w by v\<close>
  assumes u0_pos: \<open>vec_nth (x 0) iU > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) iU\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove u(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(u(0)). The combined 
                     trajectory ?z = x extended at the ghost coordinate iG with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant 1 \<le> u \<sqdot> y\<^sup>2 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = u \<sqdot> y\<^sup>2.
       
       STAGE 3 (algebra): Since u \<sqdot> y\<^sup>2 \<ge> 1 and y\<^sup>2 \<ge> 0, we get u > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, lemma on bottom" pattern: each obligation is discharged as a 
     separate `have` statement, and the provably verified dDL lemma is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iU)\<close>

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

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(
        iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
        iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
        iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                 iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                 iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v = 
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                 iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                 iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    have v1: \<open>vec_nth v iV = vec_nth w iV\<close>
      using eq
      by simp
    have v2: \<open>vec_nth v iW = vec_nth w iW\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
      using v0 v1 v2
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* WE APPLY DG: obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0) (iG := (1/2) * vec_nth v iG + 0)))) {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and  ?y0.0 = y0 and gi = iG,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (iG:=y \<tau>))\<close>

  (* Helper: Frechet derivative of u \<sqdot> y\<^sup>2 (product rule) *)
  have ug2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iU * (vec_nth p iG)^2 + 
           vec_nth p iU * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iU) has_derivative (\<lambda>v. vec_nth v iU)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
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
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using u0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + w\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                   Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iU * (vec_nth (?z \<tau>) iG)^2 + 
                                   vec_nth (?z \<tau>) iU * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule ug2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) iW ^ n) - vec_nth (x \<tau>) iU) * (y \<tau> * y \<tau>) +
                           vec_nth (x \<tau>) iU * (y \<tau> * y \<tau>) =
                          \<alpha> / (1 + vec_nth (x \<tau>) iW ^ n) * (y \<tau> * y \<tau>)\<close>)
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
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v iU * (vec_nth v iG)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iU * (vec_nth v iG)^2\<close>,
                  OF    iv combined_sol induct_step t] .
  (* ==========================================================================
     STAGE 3: From u(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude u(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iU\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iU = vec_nth (x t) iU\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iU * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iU \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Lemma 2: positivity of v (mirror argument, ghost at coordinate iG).\<close>
lemma repressilator_v_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  fixes iU iV iW iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iW\<close> \<open>iU \<noteq> iG\<close>
                  \<open>iV \<noteq> iW\<close> \<open>iV \<noteq> iG\<close> \<open>iW \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                      iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                      iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))
                                    )) {0..t} UNIV\<close>
  assumes v0_pos: \<open>vec_nth (x 0) iV > (0::real)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<alpha>_nn: \<open>0 \<le> \<alpha>\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>1 \<le> n\<close>
  shows \<open>0 < vec_nth (x t) iV\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove v(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(v(0)). The combined 
                     trajectory ?z = x extended at the ghost coordinate iG with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant 1 \<le> v \<sqdot> y\<^sup>2 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = v \<sqdot> y\<^sup>2.
       
       STAGE 3 (algebra): Since v \<sqdot> y\<^sup>2 \<ge> 1 and y\<^sup>2 \<ge> 0, we get v > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, lemma on bottom" pattern.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iV)\<close>

  (* ==========================================================================
     STAGE 1: Apply DG to obtain the ghost-extended trajectory
     ========================================================================== *)

  (* PROOF OBLIGATION DG.2 (a_cont): a = \<lambda>\<tau>. 1/2 is continuous on {0..t} *)
  have a_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 1/2)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.3 (b_cont): b = \<lambda>\<tau>. 0 is continuous on {0..t} *)
  have b_cont: \<open>continuous_on {0..t} (\<lambda>\<tau>::real. 0)\<close>
    by (rule continuous_on_const)

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(
        iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
        iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
        iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                 iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                 iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v = 
                            (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                 iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                 iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                 iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    have v1: \<open>vec_nth v iV = vec_nth w iV\<close>
      using eq
      by simp
    have v2: \<open>vec_nth v iW = vec_nth w iW\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
      using v0 v1 v2 
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where a = \<open>\<lambda>\<tau>. 1/2\<close> and b = \<open>\<lambda>\<tau>. 0\<close> and ?y0.0 = y0 and gi = iG,
             OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (iG:=y \<tau>))\<close>

  (* Helper: Frechet derivative of v \<sqdot> y\<^sup>2 (product rule) *)
  have vg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iV * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iV * (vec_nth p iG)^2 + 
           vec_nth p iV * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iV) has_derivative (\<lambda>v. vec_nth v iV)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
      by (rule component_sq_has_derivative)
    show ?thesis
      using has_derivative_mult[OF f g] 
      by (simp add: algebra_simps)
  qed

  (* ==========================================================================
     STAGE 2: We apply DI_Vect to prove the invariant 1 \<le> v \<sqdot> y\<^sup>2 along ?z
     ========================================================================== *)

  (* PROOF OBLIGATION DI.1 (iv): initial condition 1 \<le> v(0) \<sqdot> y(0)\<^sup>2 *)
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v iV * (vec_nth v iG)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using v0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + u\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iV * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iV * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iV * (vec_nth (?z \<tau>) iG)^2 + 
                                    vec_nth (?z \<tau>) iV * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule vg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) iU ^ n) - vec_nth (x \<tau>) iV) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) iV * (y \<tau> * y \<tau>) =
                          \<alpha> / (1 + vec_nth (x \<tau>) iU ^ n) * (y \<tau> * y \<tau>)\<close>)
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
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v iV * (vec_nth v iG)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iV * (vec_nth v iG)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From v(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude v(t) > 0
     ========================================================================== *)
  show \<open>0 < vec_nth (x t) iV\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iV = vec_nth (x t) iV\<close>
      by simp
    have y_sq_nn: \<open>0 \<le> (vec_nth (?z t) iG)^2\<close>
      by simp
    have prod_ge_1: \<open>1 \<le> vec_nth (?z t) iV * (vec_nth (?z t) iG)^2\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iV \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Lemma 3: positivity of w (mirror argument, ghost at coordinate iG).\<close>
lemma repressilator_w_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  fixes iU iV iW iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iW\<close> \<open>iU \<noteq> iG\<close>
                  \<open>iV \<noteq> iW\<close> \<open>iV \<noteq> iG\<close> \<open>iW \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>k. 0)(
                                     iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                     iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                     iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))
                                   )) {0..t} UNIV\<close>
  assumes w0_pos: \<open>vec_nth (x 0) iW > (0::real)\<close>
  assumes t: \<open>t \<ge> 0\<close>
  assumes \<alpha>_nn: \<open>\<alpha> \<ge> 0\<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open>n \<ge> 1\<close>
  shows \<open>vec_nth (x t) iW > (0::real)\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     To prove W(t) > 0, we use the DG-then-DI pattern:
     
       STAGE 1 (DG): We introduce a ghost species y satisfying dy/dt = (1/2)\<sqdot>y
                     with initial value y(0) = 1/sqrt(W(0)). The combined 
                     trajectory ?z = x extended at the ghost coordinate iG with y solves 
                     the extended ODE.
       
       STAGE 2 (DI): We prove the invariant W \<sqdot> y² \<ge> 1 along the combined 
                     trajectory, via DI_Vect with h = 1 and g = W \<sqdot> y².
       
       STAGE 3 (algebra): Since W \<sqdot> y² \<ge> 1 and y² \<ge> 0, we get W > 0.
     
     Both STAGE 1 (DG) and STAGE 2 (DI) are structured in the "obligations 
     on top, lemma on bottom" pattern: each obligation is discharged as a 
     separate `have` statement, and the provably verified dDL lemma is applied via forward 
     reasoning at the bottom of each stage.
     ========================================================================== *)

  define y0 where \<open>y0 = 1 / sqrt (vec_nth (x 0) iW)\<close>

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

  (* PROOF OBLIGATION DG.4 (gi_zero): the vector field's component at the ghost coordinate iG is zero *)
  have gi_zero: \<open>\<And>\<tau> v. vec_nth ((\<lambda>t v.
      vec_lambda ((\<lambda>k::'p. 0)(
        iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
        iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
        iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v) iG = 0\<close>
    by (auto simp add: fun_upd_def)

  (* PROOF OBLIGATION DG.5 (gi_fresh): the vector field doesn't depend on the ghost index *)
  have gi_fresh: 
    \<open>\<And>\<tau> v w::(real, 'p) vec. (\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i) \<Longrightarrow>
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                  iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                  iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v =
                             (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                                  iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                  iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                  iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
  proof -
    fix \<tau> :: real and v w :: \<open>(real, 'p) vec\<close>
    assume eq: \<open>\<forall>i. i \<noteq> iG \<longrightarrow> vec_nth v i = vec_nth w i\<close>
    (* The field only reads indices 0, 1, 2; none of these is 3 *)
    have v0: \<open>vec_nth v iU = vec_nth w iU\<close>
      using eq
      by simp
    have v1: \<open>vec_nth v iV = vec_nth w iV\<close>
      using eq
      by simp
    have v2: \<open>vec_nth v iW = vec_nth w iW\<close>
      using eq
      by simp
    show \<open>(\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> v =
          (\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
            iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))) \<tau> w\<close>
      using v0 v1 v2
      by (simp add: vec_eq_iff fun_upd_def)
  qed

  (* WE APPLY DG: we obtain a ghost trajectory y satisfying dy/dt = (1/2)\<sqdot>y + 0 *)
  have dg_result: \<open>\<exists> y. y 0 = y0 \<and>
      (((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0)
                  (iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV)\<close>
    using DG[where 
            a = \<open>\<lambda>\<tau>. 1/2\<close> and 
            b = \<open>\<lambda>\<tau>. 0\<close> and 
            ?y0.0 = y0 and
            gi = iG,
            OF x_sol a_cont b_cont gi_zero gi_fresh] .

  (* We extract the ghost trajectory y and the combined solves_ode fact *)
  then obtain y where 
    y_init: \<open>y 0 = y0\<close> and
    combined_sol: 
      \<open>((\<lambda>\<tau>. vec_lambda ((vec_nth (x \<tau>))(iG := y \<tau>))) solves_ode
         (\<lambda>\<tau> v. vec_lambda
                 ((\<lambda>k. 0)
                  (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                   iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                   iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                vec_lambda
                 ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))))
         {0..t} UNIV\<close>
    by auto

  let ?z = \<open>\<lambda>\<tau>. vec_lambda ((\<lambda>i. vec_nth (x \<tau>) i) (iG:=y \<tau>))\<close>

  (* Helper: Frechet derivative of w \<sqdot> y\<^sup>2 (product rule) *)
  have wg2_has_derivative:
    \<open>((\<lambda>v. vec_nth v iW * (vec_nth v iG)^2) has_derivative 
      (\<lambda>v. vec_nth v iW * (vec_nth p iG)^2 + 
           vec_nth p iW * (2 * vec_nth p iG * vec_nth v iG))) (at p)\<close>
    for p :: \<open>(real, 'p) vec\<close>
  proof -
    have f: \<open>((\<lambda>v. vec_nth v iW) has_derivative (\<lambda>v. vec_nth v iW)) (at p)\<close>
      by (rule has_derivative_vec_nth)
    have g: \<open>((\<lambda>v. (vec_nth v iG)^2) has_derivative 
        (\<lambda>v. 2 * vec_nth p iG * vec_nth v iG)) (at p)\<close>
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
  have iv: \<open>(\<lambda>v. (1::real)) (?z 0) \<le> (\<lambda>v. vec_nth v iW * (vec_nth v iG)^2) (?z 0)\<close>
    unfolding fun_upd_def
    using w0_pos 
    by (simp add: y0_def y_init field_simps power2_eq_square)

  (* PROOF OBLIGATION DI.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
  (* Here Dh = 0 and Dg (via product rule) evaluated at the extended field 
     gives \<alpha>/(1 + x\<^sub>1\<^sup>n) \<sqdot> y\<^sup>2 \<ge> 0 (using \<alpha> \<ge> 0 and n even). *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iW * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                 Dh ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                 Dg ((\<lambda>\<tau> v. vec_lambda
                         ((\<lambda>k. 0)
                          (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                           iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                           iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                        vec_lambda
                         ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. (1::real)) has_derivative Dh) (at (?z \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iW * (vec_nth v iG)^2) has_derivative Dg) (at (?z \<tau>)) \<and>
                  Dh ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>)) \<le>
                  Dg ((\<lambda>\<tau> v. vec_lambda
                          ((\<lambda>k. 0)
                           (iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                            iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                            iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW)) +
                         vec_lambda
                          ((\<lambda>i. 0)(iG := (1/2) * vec_nth v iG + 0))) \<tau> (?z \<tau>))\<close>
      apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iW * (vec_nth (?z \<tau>) iG)^2 + 
                                    vec_nth (?z \<tau>) iW * (2 * vec_nth (?z \<tau>) iG * vec_nth v iG)\<close>])
      apply (rule conjI)
       apply (rule has_derivative_const)
      apply (rule conjI)
       apply (rule wg2_has_derivative)
      apply (auto simp add: power2_eq_square fun_upd_def)
      apply (subgoal_tac \<open>(\<alpha> / (1 + vec_nth (x \<tau>) iV ^ n) - vec_nth (x \<tau>) iW) * (y \<tau> * y \<tau>) +
                          vec_nth (x \<tau>) iW * (y \<tau> * y \<tau>) =
                        \<alpha> / (1 + vec_nth (x \<tau>) iV ^ n) * (y \<tau> * y \<tau>)\<close>)
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
  have ineq: \<open>(\<lambda>v. (1::real)) (?z t) \<le> (\<lambda>v. vec_nth v iW * (vec_nth v iG)^2) (?z t)\<close>
    using DI_Vect[where h = \<open>\<lambda>v. 1\<close> and g = \<open>\<lambda>v. vec_nth v iW * (vec_nth v iG)^2\<close>,
                  OF iv combined_sol induct_step t] .

  (* ==========================================================================
     STAGE 3: From W(t) \<sqdot> y(t)\<^sup>2 \<ge> 1 and y(t)\<^sup>2 \<ge> 0, conclude W(t) > 0
     ========================================================================== *)
  show \<open>vec_nth (x t) iW > 0\<close>
  proof -
    have z_eq_x: \<open>vec_nth (?z t) iW = vec_nth (x t) iW\<close>
      by simp
    have y_sq_nn: \<open>(vec_nth (?z t) iG)^2 \<ge> 0\<close>
      by simp
    have prod_ge_1: \<open>vec_nth (?z t) iW * (vec_nth (?z t) iG)^2 \<ge> 1\<close>
      using ineq
      by simp
    show ?thesis
      using z_eq_x y_sq_nn prod_ge_1
      apply (cases \<open>vec_nth (x t) iW \<le> 0\<close>) 
       apply (auto simp: mult_le_0_iff)
      apply (metis approximation_preproc_push_neg(1) le_less_trans 
                   power2_less_0 zero_compare_simps(6) zero_less_one)
      done
  qed
qed

text \<open>Main theorem: all three proteins stay strictly positive.\<close>
theorem repressilator_all_positive:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<alpha> :: real
  fixes n :: nat
  fixes iU iV iW iG :: 'p
      \<comment> \<open>iG is a spare coordinate for the ghost\<close>
  assumes coords: \<open>iU \<noteq> iV\<close> \<open>iU \<noteq> iW\<close> \<open>iU \<noteq> iG\<close>
                  \<open>iV \<noteq> iW\<close> \<open>iV \<noteq> iG\<close> \<open>iW \<noteq> iG\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iU := \<alpha> / (1 + (vec_nth v iW)^n) - vec_nth v iU,
                                      iV := \<alpha> / (1 + (vec_nth v iU)^n) - vec_nth v iV,
                                      iW := \<alpha> / (1 + (vec_nth v iV)^n) - vec_nth v iW))
                                    )) {0..t} UNIV\<close>
  assumes u0_pos: \<open>(0::real)< vec_nth (x 0) iU\<close>
  assumes v0_pos: \<open>(0::real) < vec_nth (x 0) iV\<close>
  assumes w0_pos: \<open>(0::real) < vec_nth (x 0) iW\<close>
  assumes t: \<open> 0 \<le> t \<close>
  assumes \<alpha>_nn: \<open> 0 \<le> \<alpha> \<close>
  assumes n_even: \<open>even n\<close>
  assumes n_pos: \<open> 1 \<le> n \<close>
  shows \<open>0 < vec_nth (x t) iU \<and>  0 < vec_nth (x t) iV \<and>  0 < vec_nth (x t) iW\<close>
proof (intro conjI)
  note coords_neq [simp] = coords coords[THEN not_sym]
  show \<open>0 < vec_nth (x t) iU\<close>
    using repressilator_u_positive[OF coords x_sol u0_pos t \<alpha>_nn n_even n_pos] .
  show \<open>0 < vec_nth (x t) iV\<close>
    using repressilator_v_positive[OF coords x_sol v0_pos t \<alpha>_nn n_even n_pos] .
  show \<open>0 < vec_nth (x t) iW\<close>
    using repressilator_w_positive[OF coords x_sol w0_pos t \<alpha>_nn n_even n_pos] .
qed


subsubsection \<open>Antithetic integral feedback (Briat et al.\ 2016)\<close>

text \<open>
  \textbf{BIOLOGICAL CONTEXT}\\
  The antithetic integral feedback (AIF) motif is a biomolecular
  control scheme that implements integral feedback at the molecular
  level using a pair of species that annihilate each other. It was
  introduced by Briat, Gupta \& Khammash (Cell Systems, 2016) as the
  first rationally designed integral feedback control system for
  living cells.

  AIF is the molecular analog of integral feedback in control engineering:
  it provides ROBUST PERFECT ADAPTATION (RPA), the ability of a
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

\begin{verbatim}
      {}       ->(mu)     Z1        (constant production of Z1 - setpoint)
      X        ->(theta)  Z2 + X    (Z2 produced at rate proportional to X)
      Z1 + Z2  ->(eta)    {}        (stoichiometric annihilation)
\end{verbatim}

  Plus some dynamics for X (which we leave abstract as d*X terms).

  \textbf{THE MASS-ACTION ODE MODEL}\\
  In the symmetric formulation:

\begin{verbatim}
      dZ1/dt = mu - eta * Z1 * Z2
      dZ2/dt = theta * X - eta * Z1 * Z2
\end{verbatim}

  The X dynamics can be anything - biosensors, protein circuits, etc.
  The key observation is that the DIFFERENCE Z1 - Z2 encodes the
  integral of the tracking error:

\begin{verbatim}
      d(Z1 - Z2)/dt = (mu - eta*Z1*Z2) - (theta*X - eta*Z1*Z2)
                    = mu - theta*X
                    = theta * (mu/theta - X)
                    = theta * (X_setpoint - X)
\end{verbatim}

  The eta*Z1*Z2 annihilation terms CANCEL, leaving the tracking error.
  So Z1 - Z2 acts as the integrator of the error X\_setpoint - X.

  At steady state (when dZ1/dt = dZ2/dt = 0), the tracking error must
  be zero, forcing X = X\_setpoint = mu/theta. This is the ROBUST PERFECT
  ADAPTATION property.

  \textbf{WHAT WE VERIFY}\\
  We verify the fundamental conservation-law property that makes AIF
  work: when the system IS at the setpoint X = mu/theta, the difference
  Z1 - Z2 is CONSERVED:

\begin{verbatim}
    Z1(t) - Z2(t) = Z1(0) - Z2(0)   for all t >= 0.
\end{verbatim}

  \textbf{INTERPRETATION}\\
  At the setpoint, the controller's "integral state"
  (Z1 - Z2) is frozen - no further correction is needed because the
  tracking error is zero. This is precisely the behavior we'd expect
  from a perfect integral controller: it accumulates error when there
  is error, and stops accumulating when the error vanishes.

  \textbf{WHY THIS MATTERS}\\
\begin{enumerate}
\item CONTROL-THEORETIC GRN PRIMITIVE: Unlike the toggle switch and
  repressilator (which use Hill-function gene regulation),
  antithetic integral feedback uses POLYNOMIAL dynamics with
  bimolecular annihilation. This demonstrates that our dDL tooling
  handles a QUALITATIVELY DIFFERENT class of GRN primitives.
\item BIOMOLECULAR IMPLEMENTATION OF CLASSICAL CONTROL: AIF is the
  first experimentally realized integral feedback control system
  in a living cell (by Aoki et al., Nature 2019, based on Briat
  et al.'s theoretical design). Our formal verification connects
  dDL reasoning to the control-theoretic analysis of synthetic
  biology.
\item SIMPLEST NON-TRIVIAL AIF INVARIANT: The conservation of Z1 - Z2
  at setpoint is the foundational lemma for proving set-point
  tracking and robust perfect adaptation.
\end{enumerate}

  \textbf{HOW WE VERIFY IT}\\
  DIFFERENTIAL INDUCTION (DI). The proof is a textbook DI conservation
  argument, structurally identical to our CRN conservation laws. The Lie
  derivative of (Z1 - Z2) along the field is:

\begin{verbatim}
      d(Z1 - Z2)/dt = (mu - eta*Z1*Z2) - (theta*X - eta*Z1*Z2)
                    = mu - theta*X
\end{verbatim}

  At the setpoint X = mu/theta, this becomes mu - theta*(mu/theta) = 0, so
  Z1 - Z2 is conserved.

  In the formal model X does not change (dX/dt = 0) and starts at the
  setpoint, so the proof first shows, again with DI, that X stays at
  mu/theta; this fact then enters the DI\_Vect inductive step for Z1 - Z2.

  \textbf{ASSUMPTIONS}\\
  The proof assumes:
\begin{enumerate}
\item The solution x exists and satisfies the ODE on [0,t] (from
  solves\_ode), in which X is held constant (dX/dt = 0)
\item The initial conditions: Z1(0) - Z2(0) = c, and X(0) = mu/theta
  (X starts at the setpoint)
\item The time t >= 0
\item The rate theta is positive: theta > 0
\end{enumerate}

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iZ1: controller species Z1 (constant production)
\item Coordinate iZ2: controller species Z2 (X-proportional production)
\item Coordinate iX: process species X (held at the setpoint)
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda k. 0)(iZ1 := dZ1/dt, iZ2 := dZ2/dt, iX := 0))
\end{verbatim}

  The production rate mu is called mu1 in the formalization. The proof
  applies DI\_Vect twice (via antisymmetry) to show that X stays at
  mu1/theta, and twice more for the conservation of Z1 - Z2.

  \textbf{LIMITATIONS}\\
  The process species X is held at the setpoint in the formal model.
  More ambitious properties (convergence to the setpoint, disturbance
  rejection) would require Lyapunov or LaSalle machinery beyond our
  current tooling, but they BUILD ON this conservation-law foundation.
\<close>

lemma antithetic_integral_feedback_conservation:
  fixes x :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes \<mu>1 \<theta> \<eta> :: real
  fixes iZ1 iZ2 iX :: 'p
  assumes coords: \<open>iZ1 \<noteq> iZ2\<close> \<open>iZ1 \<noteq> iX\<close> \<open>iZ2 \<noteq> iX\<close>
  assumes x_sol: \<open>(x solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>k. 0)(
                                      iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                                      iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                                      iX := 0))
                                    )) {0..t} UNIV\<close>
      \<comment> \<open>Coordinate iZ1: Z1 (controller species, constant production);
         coordinate iZ2: Z2 (controller species, X-proportional production);
         coordinate iX: X (process species, held constant at the setpoint for simplicity)\<close>
  assumes iv: \<open>vec_nth (x 0) iZ1 - vec_nth (x 0) iZ2 = c\<close>
      \<comment> \<open>Initial integral state: c = Z1(0) - Z2(0)\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes \<theta>_pos: \<open>0 < \<theta>\<close>
  assumes setpoint: \<open>vec_nth (x 0) iX = \<mu>1 / \<theta>\<close>
      \<comment> \<open>X starts at the setpoint mu1/theta. Since dX/dt = 0 in this
         simplified model, X stays there; the proof establishes this first,
         as a separate conservation.\<close>
  shows \<open>vec_nth (x t) iZ1 - vec_nth (x t) iZ2 = c\<close>
      \<comment> \<open>Conclusion: the integral state Z1 - Z2 is conserved at the setpoint\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY
     
     This proof uses four applications of DI_Vect, all structured with the 
     "obligations on top, lemma on bottom" pattern:
     
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
  have X_constant: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (x \<tau>) iX = \<mu>1 / \<theta>\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    
    (* Restrict the ODE to {0..\<tau>} *)
    have x_sol_\<tau>: \<open>(x solves_ode (\<lambda>t v.
                                   vec_lambda ((\<lambda>k. 0)(
                                     iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                                     iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                                     iX := 0))
                                   )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF x_sol] \<tau>_in .
    
    (* ------------------------------------------------------------------------
       SUB-PART A1: \<mu>/\<theta> \<le> X(\<tau>) via DI_Vect with h = \<mu>/\<theta>, g = X
       ------------------------------------------------------------------------ *)
    
    (* PROOF OBLIGATION A1.1 (iv): initial condition \<mu>/\<theta> \<le> X(0) *)
    have iv_up: \<open>(\<lambda>v. \<mu>1/\<theta>) (x 0) \<le> (\<lambda>v. vec_nth v iX) (x 0)\<close>
      using setpoint
      by simp

    (* PROOF OBLIGATION A1.2 (induct_step): derivative check Dh(VelVect) \<le> Dg(VelVect) *)
    have induct_step_up:
      \<open>\<And>\<tau>'. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dh) (at (x \<tau>')) \<and>
                   ((\<lambda>v. vec_nth v iX) has_derivative Dg) (at (x \<tau>')) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau>' (x \<tau>')) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau>' (x \<tau>'))\<close>
    proof -
      fix \<tau>' :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dh) (at (x \<tau>')) \<and>
                    ((\<lambda>v. vec_nth v iX) has_derivative Dg) (at (x \<tau>')) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau>' (x \<tau>')) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau>' (x \<tau>'))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iX\<close>])
        apply (rule conjI, rule has_derivative_const)
        apply (rule conjI, rule has_derivative_vec_nth)
        apply (auto simp: fun_upd_def)
        done
    qed

    (* WE APPLY DI_Vect for direction UP *)
    have up: \<open>\<mu>1/\<theta> \<le> vec_nth (x \<tau>) iX\<close>
      using DI_Vect[where  h = \<open>\<lambda>v. \<mu>1/\<theta>\<close> and g = \<open>\<lambda>v. vec_nth v iX\<close>,
                    OF iv_up x_sol_\<tau> induct_step_up] \<tau>_in
      by simp

    (* ------------------------------------------------------------------------
       SUB-PART A2: X(\<tau>) \<le> \<mu>/\<theta> via DI_Vect with h = X, g = \<mu>/\<theta>
       ------------------------------------------------------------------------ *)

    (* PROOF OBLIGATION A2.1 (iv): initial condition X(0) \<le> \<mu>/\<theta> *)
    have iv_down: \<open>(\<lambda>v. vec_nth v iX) (x 0) \<le> (\<lambda>v. \<mu>1/\<theta>) (x 0)\<close>
      using setpoint
      by simp

    (* PROOF OBLIGATION A2.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_down:
      \<open>\<And>\<tau>'. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. vec_nth v iX) has_derivative Dh) (at (x \<tau>')) \<and>
                   ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dg) (at (x \<tau>')) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau>' (x \<tau>')) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau>' (x \<tau>'))\<close>
    proof -
      fix \<tau>' :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iX) has_derivative Dh) (at (x \<tau>')) \<and>
                    ((\<lambda>v. \<mu>1/\<theta>) has_derivative Dg) (at (x \<tau>')) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau>' (x \<tau>')) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau>' (x \<tau>'))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iX\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule conjI, rule has_derivative_vec_nth)
        apply (rule conjI, rule has_derivative_const)
        apply (auto simp: fun_upd_def)
        done
    qed

    (* WE APPLY DI_Vect for direction DOWN *)
    have down: \<open>vec_nth (x \<tau>) iX \<le> \<mu>1/\<theta>\<close>
      using DI_Vect[where 
                    h = \<open>\<lambda>v. vec_nth v iX\<close> and 
                    g = \<open>\<lambda>v. \<mu>1/\<theta>\<close>,
                    OF iv_down x_sol_\<tau> induct_step_down] \<tau>_in
      by simp

    (* Sandwich: up and down give equality *)
    from up down show \<open>vec_nth (x \<tau>) iX = \<mu>1/\<theta>\<close>
      by linarith
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
    have iv_ge: \<open>(\<lambda>v. c) (x 0) \<le> (\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) (x 0)\<close>
      using iv
      by simp

    (* PROOF OBLIGATION B1.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_ge:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (x \<tau>)) \<and>
                   ((\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) has_derivative Dg) (at (x \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau> (x \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau> (x \<tau>))\<close>
    proof -
      fix \<tau> :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. c) has_derivative Dh) (at (x \<tau>)) \<and>
                    ((\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) has_derivative Dg) (at (x \<tau>)) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau> (x \<tau>)) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau> (x \<tau>))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. 0\<close>])
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2\<close>])
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
    have iv_le: \<open>(\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) (x 0) \<le> (\<lambda>v. c) (x 0)\<close>
      using iv
      by simp

    (* PROOF OBLIGATION B2.2 (induct_step): derivative check Dh(field) \<le> Dg(field) *)
    have induct_step_le:
      \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
           \<exists>Dh Dg. ((\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) has_derivative Dh) (at (x \<tau>)) \<and>
                   ((\<lambda>v. c) has_derivative Dg) (at (x \<tau>)) \<and>
                   Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau> (x \<tau>)) \<le>
                   Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                         iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                         iX := 0))) \<tau> (x \<tau>))\<close>
    proof -
      fix \<tau> :: real
      assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
      show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2) has_derivative Dh) (at (x \<tau>)) \<and>
                    ((\<lambda>v. c) has_derivative Dg) (at (x \<tau>)) \<and>
                    Dh ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau> (x \<tau>)) \<le>
                    Dg ((\<lambda>t v. vec_lambda ((\<lambda>k. 0)(
                          iZ1 := \<mu>1 - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iZ2 := \<theta> * vec_nth v iX - \<eta> * vec_nth v iZ1 * vec_nth v iZ2,
                          iX := 0))) \<tau> (x \<tau>))\<close>
        apply (rule exI[where x=\<open>\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2\<close>])
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
                       DI_Vect[where h = \<open>\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2\<close> and g = \<open>\<lambda>v. c\<close>,
                               OF iv_le x_sol induct_step_le t]
                       DI_Vect[where h = \<open>\<lambda>v. c\<close> and g = \<open>\<lambda>v. vec_nth v iZ1 - vec_nth v iZ2\<close>,
                               OF iv_ge x_sol induct_step_ge t]
         )
  qed
qed


subsubsection \<open>GRN benchmark summary\<close>

text \<open>
\begin{verbatim}
  | # | System                        | Property          | Method         |
  |---|-------------------------------|-------------------|----------------|
  | 1 | Gardner toggle switch (cond)  | u(t) > 0          | DG + Hill      |
  | 2 | Gardner toggle switch (uncon) | u(t) > 0          | DG+DI_bnd+Hill |
  | 3 | Negative autoregulation       | u(t) > 0          | DG + Hill-even |
  | 4 | Repressilator                 | u,v,w > 0         | DG + Hill-even |
  | 5 | Antithetic integral feedback  | Z1 - Z2 conserved | DI (setpoint)  |
\end{verbatim}

  \textbf{TAKING STOCK: WHAT WE HAVE}\\
  \textbf{CORE dDL RULES (PROVABLY VERIFIED LEMMAS):}\\
\begin{itemize}
\item DI\_Generic, DI\_Vect       (standard differential induction)
\item DG, DG\_backward, DG\_elim  (differential ghost + derived rules)
\item DC                        (differential cut)
\item DI\_boundary              (boundary-aware DI; novel contribution)
\item linear\_ode\_solution       (FTC-based ghost trajectory construction)
\end{itemize}

  \textbf{HILL FUNCTION LIBRARY:}\\
\begin{itemize}
\item Scalar/Fr\'{e}chet/vector versions for x >= 0 (general Hill)
\item Scalar/Fr\'{e}chet/vector versions for even n (unconditional)
\end{itemize}

  \textbf{TECHNICAL HELPERS:}\\
\begin{itemize}
\item has\_real\_derivative\_pos\_inc\_right\_within
\item deriv\_pos\_right\_strict
\item solves\_ode\_subset\_ivl
\item assemble\_test, component\_sq\_has\_derivative, ...
\end{itemize}

  \textbf{CRN BENCHMARK (12 examples):}\\
    Conservation laws, strict positivity via DG

  \textbf{GRN BENCHMARK (5 examples):}\\
    Gene regulatory motifs from Gardner (toggle switch), Elowitz
    (repressilator), Alon (negative autoregulation), Briat et al.
    (antithetic integral feedback).
\<close>

subsection \<open>Benchmark on Programmable Biological Circuit\<close>
text \<open>
  \textbf{Programmable Biological Circuit: Correctness of the min(x,y) CRN
  via DIRECT use of the provably verified dDL lemmas DI\_Vect, DC and
  DI\_convergence\_rate}\\

  \textbf{BIOLOGICAL CONTEXT}\\
  This part demonstrates that the provably verified dDL lemmas can be used
  DIRECTLY to reason about the CORRECTNESS of computing chemical reaction
  networks. We take the min(x,y) CRN of the CRN benchmark, a chemical
  program whose output [Z] computes the minimum of its two inputs, and
  prove six correctness properties.

  \textbf{THE CHEMICAL REACTIONS}\\
\begin{verbatim}
      X + Y ->(k) Z
\end{verbatim}

  \textbf{THE MASS-ACTION ODE MODEL}\\
\begin{verbatim}
      d[X]/dt = -k * [X] * [Y]
      d[Y]/dt = -k * [X] * [Y]
      d[Z]/dt =  k * [X] * [Y]
\end{verbatim}

  \textbf{WHAT WE VERIFY}\\
\begin{enumerate}
\item MONOTONIC PROGRESS: [Z](t) >= [Z](0) for all t >= 0.
  Interpretation: the output Z never decreases. This is the fundamental
  correctness property of any monotonic computation: once part of the
  answer has been computed, it is never lost.
\item BOUNDED OUTPUT: [Z](t) <= min(x0, y0) for all t >= 0.
  Interpretation: the output never overshoots the correct answer.
\item COMMITMENT: if [Z](0) >= c, then we can strengthen the ODE's domain
  to enforce [Z] >= c throughout the trajectory.
  Interpretation: the output is COMMITTED: once Z has reached value c,
  it cannot fall back below c. This is the analog of write-once memory.
\item EQUILIBRIUM CORRECTNESS: if at time t the system is at no-reaction
  equilibrium ([X]*[Y] = 0), then [Z](t) = min(x0, y0).
  Interpretation: IF the trajectory ever reaches a state where no more
  reactions can fire, THEN at that state the answer is exactly correct.
  Combined with the trajectory bounds (Properties 1-3), this gives:
  "the trajectory is consistent with computing min, and at any
  equilibrium it returns the correct value."
\item EPSILON-CONVERGENCE: for any epsilon > 0, [Z](T) > min(x0, y0) - epsilon
  as soon as T > (min(x0, y0) - epsilon - [Z](0)) / (k*epsilon\textasciicircum{}2).
  Interpretation: the output comes within epsilon of the correct answer
  within an explicit, computable time.
\item COMBINED SPECIFICATION: crn\_min\_correctness\_specification bundles
  Properties 1, 2, 4 and 5 in one statement; crn\_min\_correctness\_full
  also includes Property 3 in scalar form.
\end{enumerate}

  \textbf{WHY THIS MATTERS}\\
  TOGETHER, these properties certify the min(x,y) CRN as a CORRECT-BY-
  DESIGN, MONOTONIC, COMMITTED computational primitive. Even without the
  limit statement (see LIMITATIONS), Properties 1-3 already give a
  meaningful trajectory-level correctness specification: the output is
  monotonic, bounded above by the correct answer, and committed once
  written.

  \textbf{HOW WE VERIFY IT}\\
  Properties 1, 3 and 5 apply a provably verified dDL lemma directly in
  the correctness layer (not just transitively through pre-proved
  invariants); Properties 2 and 4 are algebra on the conservation laws,
  and Property 6 bundles the others:
\begin{enumerate}
\item MONOTONIC PROGRESS (uses DI\_Vect DIRECTLY): a fresh DI\_Vect
  application with the invariant pair (h, g) = (constant Z(0), current
  Z value). The Lie derivative is d[Z]/dt = k*X*Y, which is >= 0 when
  k >= 0 and X, Y >= 0.
\item BOUNDED OUTPUT (uses conservation laws via DI\_Vect): algebraic
  consequence of crn\_min\_X\_conservation and crn\_min\_Y\_conservation
  (each proved with DI\_Vect).
\item COMMITMENT (uses DC DIRECTLY): PROPERTY 1 gives monotonic progress,
  then DC strengthens the domain by adding the \{v. vec\_nth v iZ >= c\}
  constraint. This is a direct application of the provably verified DC
  lemma in the correctness layer.
\item EQUILIBRIUM CORRECTNESS (algebraic on conservation laws): case
  analysis on X = 0 or Y = 0, with each case discharged by linarith on the
  conservation laws and non-negativity.
\item EPSILON-CONVERGENCE (uses DI\_convergence\_rate DIRECTLY):
  DI\_convergence\_rate, with the rate k*epsilon\textasciicircum{}2 as a lower
  bound on d[Z]/dt while [Z] is still below min(x0, y0) - epsilon.
\item COMBINED SPECIFICATION: the conjunction of the lemmas above.
\end{enumerate}

  \textbf{ASSUMPTIONS}\\
  The lemmas share these assumptions:
\begin{enumerate}
\item The solution y exists and satisfies the ODE on [0,t] (from
  solves\_ode); Properties 5 and 6 use the time T instead of t
\item The initial conditions [X](0) + [Z](0) = x0 and [Y](0) + [Z](0) = y0,
  in the properties that mention x0 and y0
\item The time t >= 0 (T >= 0 for Properties 5 and 6)
\item The rate constant is non-negative, k >= 0 (Properties 1 and 3), or
  positive, k > 0 (Properties 5 and 6)
\item{} [X] and [Y] stay non-negative along the trajectory (Properties 1, 3,
  5 and 6), or at the final time (Properties 2 and 4)
\end{enumerate}
  In addition, Property 3 assumes [Z](0) >= c, Property 4 assumes the
  equilibrium [X](t)*[Y](t) = 0, and Properties 5 and 6 assume epsilon > 0
  and the lower bound on T.

  \textbf{FORMALIZATION}\\
  We represent the three species as components of a state vector over an
  arbitrary finite index type 'p, at three pairwise distinct coordinates:
\begin{itemize}
\item Coordinate iX: concentration of X, i.e., [X]
\item Coordinate iY: concentration of Y, i.e., [Y]
\item Coordinate iZ: concentration of Z, i.e., [Z]
\end{itemize}

  The ODE system is encoded using Isabelle's vec\_lambda and fun\_upd:
\begin{verbatim}
    vec_lambda ((lambda i. 0)(iX := d[X]/dt, iY := d[Y]/dt, iZ := d[Z]/dt))
\end{verbatim}

  crn\_min\_correctness\_full\_R3 instantiates the full specification in
  R\textasciicircum{}3, at the coordinates 0, 1 and 2.

  \textbf{LIMITATIONS}\\
\begin{enumerate}
\item CONVERGENCE AS A LIMIT: lim\_\{t->infinity\} [Z](t) = min(x0, y0).
  Property 5 gives the epsilon-version with an explicit time bound; the
  limit itself needs solves\_ode on the half-line [0, infinity).
\item NON-NEGATIVITY ALONG THE TRAJECTORY is assumed. For the min(x,y)
  CRN, the boundary condition for DI\_boundary at X = 0 is non-strict
  (Lie derivative = 0), so DI\_boundary doesn't apply. A non-strict
  variant of DI\_boundary would close this gap.
\end{enumerate}
\<close>


subsubsection \<open>Property 1: monotonic progress (direct use of DI\_Vect)\<close>

text \<open>
  We prove [Z](t) >= [Z](0) by a FRESH DI\_Vect application with:
\begin{verbatim}
    h(v) = vec_nth (y 0) iZ    (constant: the initial value of Z)
    g(v) = vec_nth v iZ        (current value of Z)
\end{verbatim}

\begin{verbatim}
  Initial condition:  Z(0) <= Z(0)  trivially
  Lie derivative check:
    Dh(field) = 0
    Dg(field) = field[iZ] = k*X*Y
\end{verbatim}
  Need: 0 <= k*X*Y, which holds when k >= 0 and X(tau), Y(tau) >= 0.

  Limitation: the non-negativity of X and Y along the trajectory
  (assumptions X\_nn\_along and Y\_nn\_along) is assumed here.
  Discharging it requires a non-strict variant of DI\_boundary,
  which is left for future work.
\<close>

lemma crn_min_Z_monotonic:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda ((\<lambda>i. 0)(
                                      iX := -k * vec_nth v iX * vec_nth v iY,
                                      iY := -k * vec_nth v iX * vec_nth v iY,
                                      iZ :=  k * vec_nth v iX * vec_nth v iY))
                                    )) {0..t} UNIV\<close>
  assumes t: \<open>0 \<le> t\<close>
  assumes k_nn: \<open>0 \<le> k\<close>
  \<comment> \<open>Non-negativity of X and Y along the trajectory is assumed; see the limitation stated above.\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iX\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> 0 \<le> vec_nth (y \<tau>) iY\<close>
  shows \<open>vec_nth (y 0) iZ \<le> vec_nth (y t) iZ\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* ==========================================================================
     PROOF STRATEGY: Apply DI_Vect with the invariant pair
       h = \<lambda>v. vec_nth (y 0) iZ  (constant: initial value of Z)
       g = \<lambda>v. vec_nth v iZ       (current value of Z)
     The conclusion h(y t) \<le> g(y t) unfolds to Z(0) \<le> Z(t), which is the 
     monotonicity claim.
     
     We discharge each proof obligation generated by  DI_Vect as a separate `have` statement, 
     then apply DI_Vect via forward reasoning at the bottom of the proof.
     ========================================================================== *)

  (* PROOF OBLIGATION 1 (iv): initial condition h(y 0) \<le> g(y 0), i.e., Z(0) \<le> Z(0) *)
  have iv: \<open>(\<lambda>v. vec_nth (y 0) iZ) (y 0) \<le> (\<lambda>v. vec_nth v iZ) (y 0)\<close>
    by simp

  (* PROOF OBLIGATION 2 (ODE): the trajectory solves the ODE, directly from y_sol *)
  (* (no separate `have` needed; we pass y_sol directly) *)

  (* PROOF OBLIGATION 3 (induct_step): at every \<tau> \<in> [0..t], there exist Fr\<eacute>chet 
     derivatives Dh, Dg of h and g such that Dh(field) \<le> Dg(field). 
     Here Dh = 0 (h is constant) and Dg = vec_nth \<sqdot> iZ (linear projection), 
     so Dg(field) = field[iZ] = k\<sqdot>X(\<tau>)\<sqdot>Y(\<tau>) \<ge> 0 by k_nn, X_nn_along, Y_nn_along. *)
  have induct_step:
    \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow>
         \<exists>Dh Dg. ((\<lambda>v. vec_nth (y 0) iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                 ((\<lambda>v. vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                 Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -k * vec_nth v iX * vec_nth v iY,
                       iY := -k * vec_nth v iX * vec_nth v iY,
                       iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le> 
                 Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                       iX := -k * vec_nth v iX * vec_nth v iY,
                       iY := -k * vec_nth v iX * vec_nth v iY,
                       iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
  proof -
    fix \<tau> :: real
    assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    show \<open>\<exists>Dh Dg. ((\<lambda>v. vec_nth (y 0) iZ) has_derivative Dh) (at (y \<tau>)) \<and>
                  ((\<lambda>v. vec_nth v iZ) has_derivative Dg) (at (y \<tau>)) \<and>
                  Dh ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>)) \<le>
                  Dg ((\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                        iX := -k * vec_nth v iX * vec_nth v iY,
                        iY := -k * vec_nth v iX * vec_nth v iY,
                        iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau> (y \<tau>))\<close>
      apply (rule exI[where x = \<open>\<lambda>v. 0\<close>])
      apply (rule exI[where x = \<open>\<lambda>v. vec_nth v iZ\<close>])
      apply (rule conjI, rule has_derivative_const)
      apply (rule conjI, rule has_derivative_vec_nth)
      using k_nn X_nn_along[OF \<tau>_in] Y_nn_along[OF \<tau>_in]
      apply (auto simp: fun_upd_def)
      done
  qed
  (* The conclusion of DI_Vect simplifies to the monotonicity claim *)
  show ?thesis 
    using DI_Vect[where h = \<open>\<lambda>v. vec_nth (y 0) iZ\<close> and
                        g = \<open>\<lambda>v. vec_nth v iZ\<close>,
                  OF iv y_sol induct_step t] .
qed

text \<open>
  \textbf{HELPER: Generalized monotonicity -- Z(t1) <= Z(t2) for any t1 <= t2}\\

  Generalizes crn\_min\_Z\_monotonic from "Z(t) >= Z(0)" to "Z(t1) <= Z(t2)
  for any 0 <= t1 <= t2 <= T".
\<close>

lemma crn_min_Z_monotonic_general:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
    and k :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..T} UNIV\<close>
    and t1_nn: \<open>0 \<le> t1\<close>
    and t1_le_t2: \<open>t1 \<le> t2\<close>
    and t2_le_T: \<open>t2 \<le> T\<close>
    and k_nn: \<open>k \<ge> 0\<close>
    and X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iX \<ge> 0\<close>
    and Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iY \<ge> 0\<close>
  shows \<open>vec_nth (y t1) iZ \<le> vec_nth (y t2) iZ\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  let ?y' = \<open>\<lambda>s. y (t1 + s)\<close>
  define t' where \<open>t' = t2 - t1\<close>
  
  have t'_nn: \<open>0 \<le> t'\<close>
    using t1_le_t2
    by (simp add: t'_def)
  have t1_le_T: \<open>t1 \<le> T\<close>
    using t1_le_t2 t2_le_T
    by linarith

  (* The CRN ODE is time-invariant: the lambda body has no t *)
  have time_inv: 
    \<open>\<And>\<tau>1 \<tau>2 v. 
        (\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                            iX := -k * vec_nth v iX * vec_nth v iY,
                            iY := -k * vec_nth v iX * vec_nth v iY,
                            iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau>1 v = 
        (\<lambda>t v. vec_lambda ((\<lambda>i. 0)(
                            iX := -k * vec_nth v iX * vec_nth v iY,
                            iY := -k * vec_nth v iX * vec_nth v iY,
                            iZ :=  k * vec_nth v iX * vec_nth v iY))) \<tau>2 v\<close>
    by simp

  (* Apply solves_ode_shift to get the shifted trajectory *)
  have y'_sol: \<open>(?y' solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
                  iX := -k * vec_nth v iX * vec_nth v iY,
                  iY := -k * vec_nth v iX * vec_nth v iY,
                  iZ :=  k * vec_nth v iX * vec_nth v iY))
                  )) {0..(T - t1)} UNIV\<close>
    using solves_ode_shift[OF y_sol t1_nn t1_le_T time_inv] .

  (* Restrict the shifted trajectory to [0..t'] *)
  have t'_le: \<open>t' \<le> T - t1\<close>
    using t'_def t2_le_T
    by simp
  have y'_sol_t': \<open>(?y' solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
                   iX := -k * vec_nth v iX * vec_nth v iY,
                   iY := -k * vec_nth v iX * vec_nth v iY,
                   iZ :=  k * vec_nth v iX * vec_nth v iY))
                 )) {0..t'} UNIV\<close>
    using solves_ode_subset_ivl[OF y'_sol]  t'_nn t'_le
    by simp

  (* Non-negativity along the shifted trajectory follows from along [0..T] *)
  have X_nn_y': \<open>\<And>\<tau>. \<tau> \<in> {0..t'} \<Longrightarrow> vec_nth (?y' \<tau>) iX \<ge> 0\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t'}\<close>
    hence \<open>t1 + \<tau> \<in> {0..T}\<close>
      using t1_nn t1_le_t2 t2_le_T t'_def
      by auto
    thus \<open>vec_nth (?y' \<tau>) iX \<ge> 0\<close>
      using X_nn_along
      by simp
  qed
  have Y_nn_y': \<open>\<And>\<tau>. \<tau> \<in> {0..t'} \<Longrightarrow> vec_nth (?y' \<tau>) iY \<ge> 0\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..t'}\<close>
    hence \<open>t1 + \<tau> \<in> {0..T}\<close>
      using t1_nn t1_le_t2 t2_le_T t'_def
      by auto
    thus \<open>vec_nth (?y' \<tau>) iY \<ge> 0\<close>
      using Y_nn_along
      by simp
  qed

  (* Apply the basic monotonicity lemma to the shifted trajectory *)
  have \<open>vec_nth (?y' t') iZ \<ge> vec_nth (?y' 0) iZ\<close>
    using crn_min_Z_monotonic[OF coords y'_sol_t' t'_nn k_nn X_nn_y' Y_nn_y'] .

  (* Translate back: ?y' 0 = y t1 and ?y' t' = y (t1 + (t2 - t1)) = y t2 *)
  thus ?thesis
    by (simp add: t'_def)
qed
subsubsection \<open>Property 2: bounded output (conservation laws and algebra)\<close>

text \<open>
  The conservation laws (each proved with DI\_Vect) plus non-negativity
  give the upper bound algebraically.
\<close>

lemma crn_min_Z_upper_bound_via_DI:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
    and k x0 y0 :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..t} UNIV\<close>
    and iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
    and iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
    and t: \<open>t \<ge> 0\<close>
    and X_nn_t: \<open>vec_nth (y t) iX \<ge> 0\<close>
    and Y_nn_t: \<open>vec_nth (y t) iY \<ge> 0\<close>
  shows \<open>vec_nth (y t) iZ \<le> min x0 y0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have X_cons: \<open>vec_nth (y t) iX + vec_nth (y t) iZ = x0\<close>
    using crn_min_X_conservation[OF coords y_sol iv_x t] .
  have Y_cons: \<open>vec_nth (y t) iY + vec_nth (y t) iZ = y0\<close>
    using crn_min_Y_conservation[OF coords y_sol iv_y t] .
  
  have Z_le_x0: \<open>vec_nth (y t) iZ \<le> x0\<close>
    using X_nn_t X_cons
    by linarith
  have Z_le_y0: \<open>vec_nth (y t) iZ \<le> y0\<close>
    using Y_nn_t Y_cons
    by linarith
  
  show ?thesis
    using Z_le_x0 Z_le_y0
    by simp
qed


subsubsection \<open>Property 3: commitment (direct use of DC)\<close>

text \<open>
  Once Z(0) >= c, we use DC to strengthen the ODE's domain so that the
  trajectory is constrained to \{v. vec\_nth v iZ >= c\}. This is the
  WRITE-ONCE / COMMITTED property: once the output crosses a threshold,
  it stays above that threshold, the computational analog of
  write-once memory.

  \textbf{STANDALONE LEMMA}\\
  This is the only computing-CRN correctness property
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
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
    and k c :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..t} UNIV\<close>
    and t: \<open>t \<ge> 0\<close>
    and k_nn: \<open>k \<ge> 0\<close>
    and Z_init_at_c: \<open>vec_nth (y 0) iZ \<ge> c\<close>
    and X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) iX \<ge> 0\<close>
    and Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) iY \<ge> 0\<close>
  shows \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..t} (UNIV \<inter> {v. vec_nth v iZ \<ge> c})\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* STEP 1: Use PROPERTY 1 (monotonicity) to establish Z(\<tau>) \<ge> c at every \<tau> *)
  have Z_at_c: \<open>\<And>\<tau>. \<tau> \<in> {0..t} \<Longrightarrow> vec_nth (y \<tau>) iZ \<ge> c\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..t}\<close>
    (* WE restrict the ODE to {0..\<tau>} so we can apply monotonicity at \<tau> *)
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol \<tau>_in] .    
    (* We apply PROPERTY 1 (monotonicity) *)
    have \<open>vec_nth (y \<tau>) iZ \<ge> vec_nth (y 0) iZ\<close>
      using crn_min_Z_monotonic[OF coords y_sol_\<tau>  ] k_nn \<tau>_in
      using X_nn_along Y_nn_along atLeastAtMost_iff order_trans
      by auto
    thus \<open>vec_nth (y \<tau>) iZ \<ge> c\<close>
      using Z_init_at_c
      by linarith
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
  equilibrium - that's the convergence question, which Property 5 below
  answers in its epsilon form.
  But it does close the "what is the answer at equilibrium?" question
  algebraically, completing the equilibrium-correctness side of the story.

  \textbf{PROOF:}\\
\begin{verbatim}
    The conservation laws give X + Z = x0 and Y + Z = y0.
    From X*Y = 0, either X = 0 or Y = 0:
      Case X = 0: Z = x0 from X+Z=x0; Y = y0-x0 from Y+Z=y0.
                  Y >= 0 forces x0 <= y0, so min(x0,y0) = x0 = Z.
      Case Y = 0: symmetric, gives min(x0,y0) = y0 = Z.
\end{verbatim}

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
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
    and k x0 y0 :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..t} UNIV\<close>
    and iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
    and iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
    and t: \<open>t \<ge> 0\<close>
    and X_nn_t: \<open>vec_nth (y t) iX \<ge> 0\<close>
    and Y_nn_t: \<open>vec_nth (y t) iY \<ge> 0\<close>
    and equilibrium: \<open>vec_nth (y t) iX * vec_nth (y t) iY = 0\<close>
  shows \<open>vec_nth (y t) iZ = min x0 y0\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  (* We apply the conservation laws (each proved via DI_Vect) *)
  have X_cons: \<open>vec_nth (y t) iX + vec_nth (y t) iZ = x0\<close>
    using crn_min_X_conservation[OF coords y_sol iv_x t] .
  have Y_cons: \<open>vec_nth (y t) iY + vec_nth (y t) iZ = y0\<close>
    using crn_min_Y_conservation[OF coords y_sol iv_y t] .
                      
  (* From X\<sqdot>Y = 0, either X = 0 or Y = 0 *)
  from equilibrium have \<open>vec_nth (y t) iX = 0 \<or> vec_nth (y t) iY = 0\<close>
    by simp

  thus ?thesis
  proof
    (* CASE: X = 0 *)
    assume X_zero: \<open>vec_nth (y t) iX = 0\<close>
    from X_zero X_cons have Z_eq_x0: \<open>vec_nth (y t) iZ = x0\<close>
      by linarith
    from Z_eq_x0 Y_cons have Y_eq: \<open>vec_nth (y t) iY = y0 - x0\<close>
      by linarith
    from Y_eq Y_nn_t have x0_le_y0: \<open>x0 \<le> y0\<close>
      by linarith
    from x0_le_y0 Z_eq_x0 show \<open>vec_nth (y t) iZ = min x0 y0\<close>
      by simp
  next
    (* CASE: Y = 0 (symmetric) *)
    assume Y_zero: \<open>vec_nth (y t) iY = 0\<close>
    from Y_zero Y_cons have Z_eq_y0: \<open>vec_nth (y t) iZ = y0\<close>
      by linarith
    from Z_eq_y0 X_cons have X_eq: \<open>vec_nth (y t) iX = x0 - y0\<close>
      by linarith
    from X_eq X_nn_t have y0_le_x0: \<open>y0 \<le> x0\<close>
      by linarith
    from y0_le_x0 Z_eq_y0 show \<open>vec_nth (y t) iZ = min x0 y0\<close>
      by simp
  qed
qed


text \<open>
  \textbf{WHAT THIS DEMONSTRATES - A PROOF MAP}\\
  Each correctness property is proved using dDL rules, either directly in
  the correctness layer or through the conservation laws:

\begin{verbatim}
    PROPERTY 1 (monotonicity)        ->  fresh DI_Vect application with
                                         new invariant
    PROPERTY 2 (upper bound)         ->  conservation laws + algebra
                                         (DI used)
    PROPERTY 3 (commitment)          ->  DC application (with PROPERTY 1
                                         as a sub-lemma)
    PROPERTY 4 (equilibrium correct) ->  algebra on conservation laws
                                         (DI used transitively)
    PROPERTY 5 (epsilon-convergence) ->  DI_convergence_rate application
                                         (below)
    PROPERTY 6 (combined spec)       ->  packages 1, 2, 4 and 5 (below)
\end{verbatim}
  \textbf{THE COMPOSITIONAL PATTERN:}\\
  PROPERTY 3 (commitment) demonstrates the \textbf{DI-then-DC} compositional
  pattern: prove an invariant with DI, then use DC to lift it into a
  domain restriction. This is the same pattern as our
  toggle\_switch\_DC\_strengthened\_domain example, and it's the building
  block for modular reasoning about CRN compositions in future work.

  \textbf{WHAT'S MISSING (FUTURE WORK):}\\
\begin{enumerate}
\item CONVERGENCE AS A LIMIT: lim\_\{t->infinity\} Z(t) = min(x0, y0).
  Property 5 below gives the epsilon-version with an explicit time bound;
  the limit itself needs solves\_ode on the half-line [0, infinity).
\item NON-NEGATIVITY ALONG THE TRAJECTORY: currently assumed. For the
  min(x,y) CRN, the boundary condition for DI\_boundary at X=0 is
  non-strict (Lie derivative = 0), so DI\_boundary doesn't apply.
  A non-strict variant of DI\_boundary would close this gap.
\end{enumerate}
\<close>

subsubsection \<open>Property 5: asymptotic epsilon-convergence\<close>

text \<open>
  This example extends our correctness proof for the min(x,y) CRN with an
  epsilon-convergence theorem: for any epsilon > 0, the trajectory becomes epsilon-close
  to the correct answer min(x0, y0) within an explicit, computable time
  bound. This provides a finite-time convergence rate, strictly stronger
  than the conditional equilibrium correctness.

  \textbf{CONTRIBUTION}\\
  Together with the trajectory-level properties (monotonicity, upper bound,
  commitment) and the equilibrium characterization, this gives a NEAR-COMPLETE
  correctness story for the min(x,y) CRN:

\begin{verbatim}
     The output Z is monotonically non-decreasing   (PROPERTY 1, DI)
     The output Z is bounded above by min(x0, y0)   (PROPERTY 2, DI)
     Once Z reaches a value, it stays               (PROPERTY 3, DC)
     At any equilibrium, Z = min(x0, y0)            (PROPERTY 4, algebra)
     For any epsilon > 0, Z reaches within epsilon  (PROPERTY 5,
       of min in finite time                         DI_convergence_rate)
       T(epsilon) = (min(x0,y0) - epsilon - Z(0)) / (k*epsilon^2)
\end{verbatim}

  PROPERTY 5 closes the gap left by PROPERTY 4: it doesn't just say
  "if you reach equilibrium, the answer is correct"; it says "you DO
  reach within epsilon of the answer within an explicit time bound, for any epsilon".

  \textbf{THE PROOF IDEA}\\
  The argument below is the one packaged in DI\_convergence\_rate (see
  TOOLING USED).  By contradiction. Suppose Z(T) <= min(x0, y0) - epsilon.

  By monotonicity (PROPERTY 1), Z(tau) <= Z(T) <= min(x0, y0) - epsilon for all
  tau in \{0..T\}.

  By the conservation laws, X(tau) = x0 - Z(tau) >= x0 - (min(x0, y0) - epsilon) >= epsilon
  and Y(tau) >= epsilon.

  So the rate dZ/dtau = k*X*Y >= k*epsilon\textasciicircum{}2 uniformly on \{0..T\}.

  By the fundamental theorem of calculus:
\begin{verbatim}
    Z(T) - Z(0) = (integral over [0..T] of dZ/dtau) >= k*epsilon^2*T
\end{verbatim}

  So Z(T) >= Z(0) + k*epsilon\textasciicircum{}2*T.

  If T is large enough (specifically, T > (min(x0, y0) - epsilon - Z(0))/(k*epsilon\textasciicircum{}2)),
  then Z(0) + k*epsilon\textasciicircum{}2*T > min(x0, y0) - epsilon, contradicting Z(T) <= min(x0, y0) - epsilon.

  \textbf{TOOLING USED}\\
\begin{itemize}
\item DI\_convergence\_rate, the provably verified dDL lemma for finite-time
  convergence. It carries out the integration argument above (the
  fundamental theorem of calculus) once and for all; the proof of
  Property 5 only discharges its premises.
\item PROPERTY 1 in its general form (crn\_min\_Z\_monotonic\_general, via
  DI) for the premise below\_final: Z(tau) <= Z(T) for all tau in \{0..T\}.
\item The conservation laws (crn\_min\_X\_conservation and
  crn\_min\_Y\_conservation, via DI), restricted to \{0..tau\} with
  solves\_ode\_subset\_ivl, for the rate bound k*X*Y >= k*epsilon\textasciicircum{}2
  while Z <= min(x0, y0) - epsilon.
\item has\_derivative\_vec\_nth for the derivative of the measure
  v |-> vec\_nth v iZ.
\end{itemize}

  \textbf{WHAT THIS DOES NOT PROVE}\\
  The strict statement "lim\_\{t -> infinity\} Z(t) = min(x0, y0)" requires
  reformulating solves\_ode for the half-line [0, infinity), which is a separate
  piece of work. The epsilon-convergence proved here is mathematically equivalent
  for any practical purpose: it gives an explicit finite-time bound rather
  than an infinite-limit statement.
\<close>


lemma crn_min_Z_epsilon_convergence_via_DI_convergence_rate:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: 
         \<open>(y solves_ode (\<lambda>t v.
                           vec_lambda ((\<lambda>i. 0)(
                             iX := -k * vec_nth v iX * vec_nth v iY,
                             iY := -k * vec_nth v iX * vec_nth v iY,
                             iZ :=  k * vec_nth v iX * vec_nth v iY))
                           )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iX \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iY \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) iZ) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) iZ > min x0 y0 - \<epsilon>\<close>
proof -
  note coords_neq [simp] = coords coords[THEN not_sym]
  have k_nn: \<open>k \<ge> 0\<close>
    using k_pos
    by simp
  have \<delta>_pos: \<open>0 < k * \<epsilon>^2\<close>
    using k_pos \<epsilon>_pos
    by simp

  (* Discharge `below_final` via the existing crn_min_Z_monotonic_general *)
  have below_final: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iZ \<le> vec_nth (y T) iZ\<close>
    using crn_min_Z_monotonic_general[OF coords y_sol _ _ _ k_nn X_nn_along Y_nn_along]
    by auto

 \<comment> \<open>The vector field, bound once so it need not be repeated.
      Must match y\_sol's inline lambda EXACTLY.\<close>
  let ?F = \<open>\<lambda>(t::real) (v::(real,'p) vec). vec_lambda ((\<lambda>i. 0)(
              iX := -k * vec_nth v iX * vec_nth v iY,
              iY := -k * vec_nth v iX * vec_nth v iY,
              iZ :=  k * vec_nth v iX * vec_nth v iY))\<close>

(* rate_below_target: when Z(\<tau>) \<le> min - \<epsilon>, conservation
     laws give X(\<tau>), Y(\<tau>) \<ge> \<epsilon>, so the rate k\<cdot>X\<cdot>Y \<ge> k\<cdot>\<epsilon>² *)
  have rate_below_target: 
    \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon> \<Longrightarrow>
         k * vec_nth (y \<tau>) iX * vec_nth (y \<tau>) iY \<ge> k * \<epsilon>^2\<close>
  proof -
    fix \<tau> assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close> and Z_low: \<open>vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon>\<close>
    then have \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_le: \<open>\<tau> \<le> T\<close>
      by auto
    
    have y_sol_\<tau>: \<open>(y solves_ode (\<lambda>t v.
                                  vec_lambda ((\<lambda>i. 0)(
                                    iX := -k * vec_nth v iX * vec_nth v iY,
                                    iY := -k * vec_nth v iX * vec_nth v iY,
                                    iZ :=  k * vec_nth v iX * vec_nth v iY))
                                  )) {0..\<tau>} UNIV\<close>
      using solves_ode_subset_ivl[OF y_sol \<tau>_in] .

    have X_cons: \<open>vec_nth (y \<tau>) iX + vec_nth (y \<tau>) iZ = x0\<close>
      using crn_min_X_conservation[OF coords y_sol_\<tau> iv_x \<tau>_nn] .
    have Y_cons: \<open>vec_nth (y \<tau>) iY + vec_nth (y \<tau>) iZ = y0\<close>
      using crn_min_Y_conservation[OF coords y_sol_\<tau> iv_y \<tau>_nn] .

    have X_ge: \<open>vec_nth (y \<tau>) iX \<ge> \<epsilon>\<close>
      using X_cons Z_low
      by linarith
    have Y_ge: \<open>vec_nth (y \<tau>) iY \<ge> \<epsilon>\<close>
      using Y_cons Z_low
      by linarith

    show \<open>k * vec_nth (y \<tau>) iX * vec_nth (y \<tau>) iY \<ge> k * \<epsilon>^2\<close>
      using X_ge Y_ge k_pos \<epsilon>_pos
      by (simp add: mult_mono' power2_eq_square)
  qed
  \<comment> \<open>\texttt{induct\_step}:  The measure is the projection v |-> vec\_nth v iZ, whose
      Frechet derivative is itself (has\_derivative\_vec\_nth); the Lie
      derivative is then just the field's iZ-component, namely k*X*Y.\<close>
  have induct_step: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow>
      \<exists> Dquant. ((\<lambda>v::(real,'p) vec. vec_nth v iZ) has_derivative Dquant) (at (y \<tau>)) \<and>
                (vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                 k * \<epsilon>^2 \<le> Dquant (?F \<tau> (y \<tau>)))\<close>
  proof -
    fix \<tau> assume h\<tau>: \<open>\<tau> \<in> {0..T}\<close>

    have deriv: \<open>((\<lambda>v::(real,'p) vec. vec_nth v iZ) has_derivative
                   (\<lambda>w. vec_nth w iZ)) (at (y \<tau>))\<close>
      by (rule has_derivative_vec_nth)

    have rate: \<open>vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                k * \<epsilon>^2 \<le> vec_nth (?F \<tau> (y \<tau>)) iZ\<close>
    proof
      assume below: \<open>vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon>\<close>
      have field_2: \<open>vec_nth (?F \<tau> (y \<tau>)) iZ =
                     k * vec_nth (y \<tau>) iX * vec_nth (y \<tau>) iY\<close>
        by (simp add: fun_upd_def)
      show \<open>k * \<epsilon>^2 \<le> vec_nth (?F \<tau> (y \<tau>)) iZ\<close>
        using rate_below_target[OF h\<tau> below] field_2 
        by simp
    qed
    show \<open>\<exists> Dquant. ((\<lambda>v::(real,'p) vec. vec_nth v iZ) has_derivative Dquant) (at (y \<tau>)) \<and>
                (vec_nth (y \<tau>) iZ \<le> min x0 y0 - \<epsilon> \<longrightarrow>
                 k * \<epsilon>^2 \<le> Dquant (?F \<tau> (y \<tau>)))\<close>
      using deriv rate 
      by blast
  qed

  show ?thesis
    using DI_convergence_rate[where
            quant  = \<open>\<lambda>v::(real,'p) vec. vec_nth v iZ\<close> and
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

\begin{verbatim}
     MONOTONIC PROGRESS:   Z(t) >= Z(0)
                           (PROPERTY 1, via DI)
     BOUNDED OUTPUT:       Z(t) <= min(x0, y0)
                           (PROPERTY 2, via DI conservation)
     COMMITTED OUTPUT:     Z(0) >= c ==> Z(t) >= c
                           (PROPERTY 3, via DI + DC; not bundled here)
     EQUILIBRIUM CORRECT:  X*Y = 0 ==> Z = min(x0,y0)
                           (PROPERTY 4, algebra)
     epsilon-CONVERGENCE:  T large ==> Z(T) > min - epsilon
                           (PROPERTY 5, FTC via DI_convergence_rate)
\end{verbatim}

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
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
      vec_lambda ((\<lambda>i. 0)(
        iX := -k * vec_nth v iX * vec_nth v iY,
        iY := -k * vec_nth v iX * vec_nth v iY,
        iZ :=  k * vec_nth v iX * vec_nth v iY))
      )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iX \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iY \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) iZ) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) iZ \<ge> vec_nth (y 0) iZ \<and>
         vec_nth (y T) iZ \<le> min x0 y0 \<and>
         (vec_nth (y T) iX * vec_nth (y T) iY = 0 \<longrightarrow> vec_nth (y T) iZ = min x0 y0) \<and>
         vec_nth (y T) iZ > min x0 y0 - \<epsilon>\<close>
proof (intro conjI impI)
  note coords_neq [simp] = coords coords[THEN not_sym]
  have k_nn: \<open>k \<ge> 0\<close>
    using k_pos
    by simp
  have X_nn_T: \<open>vec_nth (y T) iX \<ge> 0\<close>
    using X_nn_along T_nn
    by auto
  have Y_nn_T: \<open>vec_nth (y T) iY \<ge> 0\<close>
    using Y_nn_along T_nn
    by auto

  (* PROPERTY 1: monotonic progress *)
  show \<open>vec_nth (y T) iZ \<ge> vec_nth (y 0) iZ\<close>
    using crn_min_Z_monotonic[OF coords y_sol T_nn k_nn X_nn_along Y_nn_along] .

  (* PROPERTY 2: bounded output *)
  show \<open>vec_nth (y T) iZ \<le> min x0 y0\<close>
    using crn_min_Z_upper_bound_via_DI[OF coords y_sol iv_x iv_y T_nn X_nn_T Y_nn_T] .

  (* PROPERTY 4: equilibrium correctness (conditional) *)
  assume equil: \<open>vec_nth (y T) iX * vec_nth (y T) iY = 0\<close>
  show \<open>vec_nth (y T) iZ = min x0 y0\<close>
    using crn_min_Z_equilibrium_correct[OF coords y_sol iv_x iv_y T_nn X_nn_T Y_nn_T equil] .

next
  (* PROPERTY 5: \<epsilon>-convergence *)
  show \<open>vec_nth (y T) iZ > min x0 y0 - \<epsilon>\<close>
    using crn_min_Z_epsilon_convergence_via_DI_convergence_rate[OF coords 
            y_sol iv_x iv_y T_nn k_pos \<epsilon>_pos X_nn_along Y_nn_along T_large] .
qed
text \<open>
  \textbf{Combined correctness specification (5 properties)}\\

  This theorem bundles ALL FIVE correctness properties of the min(x,y) CRN
  into a single statement. Unlike the scalar-only crn\_min\_correctness\_specification,
  this version also includes Property 3 (commitment), a predicate-level fact
  about the ODE solution's domain restriction.

  \textbf{Properties bundled:}\\
\begin{verbatim}
     1: MONOTONIC PROGRESS    Z(T) >= Z(0)
                              (DI)
     2: BOUNDED OUTPUT        Z(T) <= min(x0, y0)
                              (DI conservation)
     3: COMMITTED OUTPUT      ALL c. Z(0) >= c ==>
                                (ALL tau in [0..T]. Z(tau) >= c)
                              (DI + DC)
     4: EQUILIBRIUM CORRECT   X(T)*Y(T) = 0 ==> Z(T) = min
                              (algebra)
     5: epsilon-CONVERGENCE   T large ==> Z(T) > min - epsilon
                              (DI_convergence_rate)
\end{verbatim}

  Note that Property 3 here is stated in its scalar-trajectory form
  "the value Z(tau) stays >= c at every point in [0..T]". The full
  domain-restriction form (the strengthened solves\_ode predicate)
  remains available as the separate lemma crn\_min\_Z\_committed\_via\_DC.
\<close>

theorem crn_min_correctness_full:
  fixes y :: \<open>real \<Rightarrow> (real, 'p::finite) vec\<close>
  fixes k x0 y0 \<epsilon> T :: real
  fixes iX iY iZ :: 'p
  assumes coords: \<open>iX \<noteq> iY\<close> \<open>iX \<noteq> iZ\<close> \<open>iY \<noteq> iZ\<close>
  assumes y_sol: \<open>(y solves_ode (\<lambda>t v.
                                    vec_lambda 
                                    ((\<lambda>i. 0)
                                     (iX := -k * vec_nth v iX * vec_nth v iY,
                                      iY := -k * vec_nth v iX * vec_nth v iY,
                                      iZ :=  k * vec_nth v iX * vec_nth v iY))
                                    )) {0..T} UNIV\<close>
  assumes iv_x: \<open>vec_nth (y 0) iX + vec_nth (y 0) iZ = x0\<close>
  assumes iv_y: \<open>vec_nth (y 0) iY + vec_nth (y 0) iZ = y0\<close>
  assumes T_nn: \<open>T \<ge> 0\<close>
  assumes k_pos: \<open>k > 0\<close>
  assumes \<epsilon>_pos: \<open>\<epsilon> > 0\<close>
  assumes X_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iX \<ge> 0\<close>
  assumes Y_nn_along: \<open>\<And>\<tau>. \<tau> \<in> {0..T} \<Longrightarrow> vec_nth (y \<tau>) iY \<ge> 0\<close>
  assumes T_large: \<open>T > (min x0 y0 - \<epsilon> - vec_nth (y 0) iZ) / (k * \<epsilon>^2)\<close>
  shows \<open>vec_nth (y T) iZ \<ge> vec_nth (y 0) iZ \<and>
         vec_nth (y T) iZ \<le> min x0 y0 \<and>
         (\<forall>c. vec_nth (y 0) iZ \<ge> c \<longrightarrow> (\<forall>\<tau>\<in>{0..T}. vec_nth (y \<tau>) iZ \<ge> c)) \<and>
         (vec_nth (y T) iX * vec_nth (y T) iY = 0 \<longrightarrow> vec_nth (y T) iZ = min x0 y0) \<and>
         vec_nth (y T) iZ > min x0 y0 - \<epsilon>\<close>
proof (intro conjI impI ballI allI)
  note coords_neq [simp] = coords coords[THEN not_sym]
  have k_nn: \<open>k \<ge> 0\<close>
    using k_pos
    by simp
  have X_nn_T: \<open>vec_nth (y T) iX \<ge> 0\<close>
    using X_nn_along T_nn
    by auto
  have Y_nn_T: \<open>vec_nth (y T) iY \<ge> 0\<close>
    using Y_nn_along T_nn
    by auto

  (* PROPERTY 1: monotonic progress *)
  show \<open>vec_nth (y T) iZ \<ge> vec_nth (y 0) iZ\<close>
    using crn_min_Z_monotonic[OF coords y_sol T_nn k_nn X_nn_along Y_nn_along] .

  (* PROPERTY 2: bounded output *)
  show \<open>vec_nth (y T) iZ \<le> min x0 y0\<close>
    using crn_min_Z_upper_bound_via_DI[OF coords y_sol iv_x iv_y T_nn X_nn_T Y_nn_T] .

  (* PROPERTY 3: commitment (scalar form): for any c \<le> Z(0), every Z(\<tau>) \<ge> c.
     This is the trajectory-pointwise content of crn_min_Z_committed_via_DC. *)
  fix c :: real
  fix \<tau> :: real
  assume Z0_ge_c: \<open>vec_nth (y 0) iZ \<ge> c\<close>
  assume \<tau>_in: \<open>\<tau> \<in> {0..T}\<close>
  then have \<tau>_nn: \<open>0 \<le> \<tau>\<close> and \<tau>_le: \<open>\<tau> \<le> T\<close> 
    by auto
  have \<open>vec_nth (y \<tau>) iZ \<ge> vec_nth (y 0) iZ\<close>
    using crn_min_Z_monotonic_general[OF coords y_sol order_refl \<tau>_nn \<tau>_le k_nn X_nn_along Y_nn_along] .
  thus \<open>vec_nth (y \<tau>) iZ \<ge> c\<close>
    using Z0_ge_c 
    by linarith

next
  (* PROPERTY 4: equilibrium correctness (conditional) *)
  have X_nn_T: \<open>vec_nth (y T) iX \<ge> 0\<close>
    using X_nn_along T_nn
    by auto
  have Y_nn_T: \<open>vec_nth (y T) iY \<ge> 0\<close>
    using Y_nn_along T_nn
    by auto
  assume equil: \<open>vec_nth (y T) iX * vec_nth (y T) iY = 0\<close>
  show \<open>vec_nth (y T) iZ = min x0 y0\<close>
    using crn_min_Z_equilibrium_correct[OF coords y_sol iv_x iv_y T_nn X_nn_T Y_nn_T equil] .

next
  (* PROPERTY 5: \<epsilon>-convergence *)
  show \<open>vec_nth (y T) iZ > min x0 y0 - \<epsilon>\<close>
    using crn_min_Z_epsilon_convergence_via_DI_convergence_rate[OF coords 
            y_sol iv_x iv_y T_nn k_pos \<epsilon>_pos X_nn_along Y_nn_along T_large] .
qed


text \<open>
  Two entries at concrete state spaces: the min(x, y) network in R\textasciicircum{}3,
  with X, Y and Z at the coordinates 0, 1 and 2, and the repressilator in
  R\textasciicircum{}4, with u, v and w at the coordinates 0, 1 and 2 and its ghost at 3.
  The distinctness assumptions are discharged once for each space.
\<close>

lemma coordinates_R3: \<open>(0::3) \<noteq> 1\<close> \<open>(0::3) \<noteq> 2\<close> \<open>(1::3) \<noteq> 2\<close>
  by simp_all

lemma coordinates_R4:
  \<open>(0::4) \<noteq> 1\<close> \<open>(0::4) \<noteq> 2\<close> \<open>(0::4) \<noteq> 3\<close>
  \<open>(1::4) \<noteq> 2\<close> \<open>(1::4) \<noteq> 3\<close> \<open>(2::4) \<noteq> 3\<close>
  by simp_all

lemmas crn_min_correctness_full_R3 = crn_min_correctness_full[OF coordinates_R3]
lemmas repressilator_all_positive_R4 = repressilator_all_positive[OF coordinates_R4]

end