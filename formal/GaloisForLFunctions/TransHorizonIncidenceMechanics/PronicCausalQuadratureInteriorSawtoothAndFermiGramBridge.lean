import GaloisForLFunctions.BezoutValuationIncidence.ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing
import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation
import GaloisForLFunctions.BezoutValuationIncidence.UniformRenormalizedInteriorEnergyRemainder
import GaloisForLFunctions.BezoutValuationIncidence.BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge
import GaloisForLFunctions.BezoutValuationIncidence.EndpointHaarCellDecompositionAndWitnessPronicTransfer
import GaloisForLFunctions.BezoutValuationIncidence.RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification

/-!
# Pronic Causal Quadrature, Interior Sawtooth Smoothing, and Vasyunin–Fermi Gram Bridge

This module synthesizes foundational results across `BiScaleUncertainty`,
`BezoutValuationIncidence`, and `TransHorizonIncidenceMechanics` to address Obstacles 1, 3, and 4
across Pillars 1, 2, 3, and 5 of the THIM programme:

1. **BiScale Chebyshev-Gauge Nyquist Cell Quadrature ↔ BVI Pronic Abel Summation (§1):**
   - Establishes the closed-form antiderivative `nyquistCellPrimitive c t` of the Chebyshev-gauge
     causal response integrand $e^{-t}(c + 1 - t - e^t)^2$ on each Nyquist log-cell
     $[\log n, \log(n + 1)]$ and simplifies its polynomial core via
     $(c + 1 - t)^2 - 2(c + 1 - t) + 2 = (c - t)^2 + 1$.
   - Proves the **Exact Pronic-Quadratic Decomposition of the Nyquist Cell Energy**
     (`nyquistCellPrimitive_nyquist_increment_eq_pronicSeq_quad`,
     `integral_nyquistCell_window_sq_eq_pronicSeq_quad`): for every $c \in \mathbb{R}$ and every
     integer $n \ge 1$, the cell integral $\int_{\log n}^{\log(n+1)} e^{-t}(c + 1 - t - e^t)^2\,dt$
     decomposes with **exact quadratic coefficient $1 / \operatorname{pronicSeq}(n) = 1 / (n(n + 1))$**:
     $$\int_{\log n}^{\log(n+1)} e^{-t}(c + 1 - t - e^t)^2\,dt =
       \frac{c^2}{\operatorname{pronicSeq}(n)} -
       2c\left(\left(1 - \frac{1}{n+1}\right)\log(n+1) - \left(1 - \frac{1}{n}\right)\log n\right) +
       \bigl(\operatorname{nyquistCellPrimitive}\,0\,(\log(n+1)) - \operatorname{nyquistCellPrimitive}\,0\,(\log n)\bigr).$$
   - Applies BVI's pronic Abel summation (`sum_sq_div_pronicSeq_add_terminal_eq_abel`) to telescope
     the cumulative pronic Chebyshev sum $\sum_{n=1}^T \psi(n)^2 / \operatorname{pronicSeq}(n) + \psi(T)^2 / (T + 1)$
     into the harmonic jump sum $\sum_{n=1}^{T-1} (\psi(n+1)^2 - \psi(n)^2)/(n+1)$.

2. **Universal Bézout Interior Sawtooth Smoothing, Non-Circular $O(1)$ Compensated Remainder, &
   Cofinal Strict Interior Contraction Criterion for `RiemannHypothesis` (§2):**
   - Combines `weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior` and
     `two_mul_sieveSeq_sub_mul_bezoutInterior_eq_addDiff_sq_sub` to prove the universal step
     identity for the interior-corrected sawtooth energy $W_{N,c}(n)^2 - (I^{\mathrm{int}}_{N,c}(n))^2$
     across all steps $n \in \mathbb{N}$ without any sub-horizon restriction $n \le N$.
   - Combines the non-circular interior conservation law
     `pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak` with
     `exists_pmActiveDeletedCovarianceDiagonal_compensated_bound` and
     `exists_pmPredecessorPeak_compensated_bound` to prove that for every $\varepsilon > 0$,
     `pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T` tracks its canonical
     compensated logarithmic drift $2\,\operatorname{pmInteriorLogCounterterm}\,\varepsilon \cdot H_T^{\mathrm{comp}}$
     within a horizon-independent $O(1)$ bound for all $T \ge 1$.
   - Combines `pmInterior_strict_contraction_iff_bounded_energy` with
     `riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget` to establish the **Cofinal Strict
     Interior Contraction Criterion for `RiemannHypothesis`**.

3. **Vasyunin Reciprocal-Cell Pronic Gram Matrix, Route PM Cofactor Iso-State Dissipation, &
   Barban–Vehov Initial-Window Annihilation (§3):**
   - Connects `pmCofactorDivisorWeight ε Q` (`RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence`)
     to THIM's `horizonObservationState (Q + 1)` and `shortWindowRenormalizedDefect`, proving exact
     iso-state non-positivity alongside the BVI-to-Route-PM pronic Gram identity.
   - Proves that on the initial window $[1, X]$ ($1 \le X < M$), the tapered Barban–Vehov source
     `DeletionAveragedDivisor.divisorSource X M` has unit $L^2$ energy and zero unit-shift
     correlation, isolating 100% of its $L^2$ excess to the trans-horizon von Mangoldt exposure band
     $X < k \le M$.
   - Packages the dilated Vasyunin reciprocal-cell pronic Gram decomposition and first-tail-cell
     Möbius energy $\mu(2M+1)^2 / \operatorname{pronicSeq}(2M+1)$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. BiScale Chebyshev-Gauge Nyquist Cell Quadrature ↔ BVI Pronic Abel Summation -/

/-- The Chebyshev-gauge Nyquist cell antiderivative
`F_c(t) = -e^{-t}((c + 1 - t)² - 2(c + 1 - t) + 2) - 2(c + 1)t + t² + e^t`
whose derivative is `e^{-t}(c + 1 - t - e^t)²`. -/
def nyquistCellPrimitive (c t : ℝ) : ℝ :=
  -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) - 2 * (c + 1) * t + t ^ 2 + Real.exp t

/-- Exact derivative of `nyquistCellPrimitive c` at any `t : ℝ`. -/
theorem hasDerivAt_nyquistCellPrimitive (c t : ℝ) :
    HasDerivAt (nyquistCellPrimitive c) (Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-t)) t := by
    have h0 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
      ((hasDerivAt_neg t).exp).neg
    exact h0.congr_deriv (by ring)
  have ha : HasDerivAt (fun t : ℝ => c + 1 - t) (-1) t := (hasDerivAt_id t).const_sub (c + 1)
  have h2 : HasDerivAt (fun t : ℝ => (c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2)
      (-2 * (c + 1 - t) + 2) t := by
    have := ((ha.pow 2).sub (ha.const_mul 2)).add_const 2
    refine this.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun t : ℝ => -2 * (c + 1) * t + t ^ 2 + Real.exp t)
      (-2 * (c + 1) + 2 * t + Real.exp t) t := by
    have := (((hasDerivAt_id t).const_mul (-2 * (c + 1))).add (hasDerivAt_pow 2 t)).add
      (Real.hasDerivAt_exp t)
    refine this.congr_deriv ?_
    norm_num
  have h : HasDerivAt (fun t : ℝ => -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
      (-2 * (c + 1) * t + t ^ 2 + Real.exp t))
      (Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
        -Real.exp (-t) * (-2 * (c + 1 - t) + 2) + (-2 * (c + 1) + 2 * t + Real.exp t)) t :=
    (h1.mul h2).add h3
  have hfun : nyquistCellPrimitive c = fun t : ℝ =>
      -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
        (-2 * (c + 1) * t + t ^ 2 + Real.exp t) := by
    funext u; unfold nyquistCellPrimitive; ring
  rw [hfun]
  refine h.congr_deriv ?_
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (2 * (c + 1 - t) - Real.exp t) * hexp

/-- **Closed-Form Nyquist Cell Integral (`integral_nyquistCell_window_sq`):**
`∫_{log n}^{log(n+1)} e^{-t}(c + 1 - t - e^t)² dt = nyquistCellPrimitive c (log (n + 1)) - nyquistCellPrimitive c (log n)`. -/
theorem integral_nyquistCell_window_sq (c : ℝ) (n : ℕ) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2) =
      nyquistCellPrimitive c (Real.log ((n : ℝ) + 1)) - nyquistCellPrimitive c (Real.log (n : ℝ)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_nyquistCellPrimitive c t)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2).intervalIntegrable
      _ _)

/-- **Square-Completed Form of `nyquistCellPrimitive` (`nyquistCellPrimitive_eq_sq_sub`):**
For every `c, t : ℝ`, the polynomial factor `(c + 1 - t)² - 2(c + 1 - t) + 2` inside
`nyquistCellPrimitive c t` simplifies to `(c - t)² + 1`. -/
theorem nyquistCellPrimitive_eq_sq_sub (c t : ℝ) :
    nyquistCellPrimitive c t =
      -Real.exp (-t) * ((c - t) ^ 2 + 1) - 2 * (c + 1) * t + t ^ 2 + Real.exp t := by
  unfold nyquistCellPrimitive
  ring

/-- **Square-Completed Logarithmic Evaluation of `nyquistCellPrimitive`
(`nyquistCellPrimitive_log_eq_sq_sub`):**
For every `c : ℝ` and `m > 0`:
`nyquistCellPrimitive c (log m) = -((c - log m)² + 1) / m - 2(c + 1) log m + (log m)² + m`. -/
theorem nyquistCellPrimitive_log_eq_sq_sub (c : ℝ) {m : ℝ} (hm : 0 < m) :
    nyquistCellPrimitive c (Real.log m) =
      -((c - Real.log m) ^ 2 + 1) / m -
        2 * (c + 1) * Real.log m + Real.log m ^ 2 + m := by
  rw [nyquistCellPrimitive_eq_sq_sub, Real.exp_neg, Real.exp_log hm]
  ring

/-- **Exact Quadratic-Plus-Linear Shift of `nyquistCellPrimitive` Relative to `c = 0`
(`nyquistCellPrimitive_sub_zero_log`):**
For every `c : ℝ` and `m > 0`:
`nyquistCellPrimitive c (log m) - nyquistCellPrimitive 0 (log m) = -c² / m - 2c (1 - 1 / m) log m`. -/
theorem nyquistCellPrimitive_sub_zero_log (c : ℝ) {m : ℝ} (hm : 0 < m) :
    nyquistCellPrimitive c (Real.log m) - nyquistCellPrimitive 0 (Real.log m) =
      -c ^ 2 / m - 2 * c * ((1 - 1 / m) * Real.log m) := by
  rw [nyquistCellPrimitive_log_eq_sq_sub c hm, nyquistCellPrimitive_log_eq_sq_sub 0 hm]
  ring

/-- **Exact Pronic-Quadratic Decomposition of the Nyquist Cell Increment
(`nyquistCellPrimitive_nyquist_increment_eq_pronicSeq_quad`):**
For every `c : ℝ` and every integer `n ≥ 1`, the Nyquist cell difference
`nyquistCellPrimitive c (log (n + 1)) - nyquistCellPrimitive c (log n)` decomposes into the **exact
pronic quadratic term** `c² / pronicSeq n` (`= c² / (n(n + 1))`), minus twice the linear log-cell
drift, plus the `c = 0` baseline cell increment. -/
theorem nyquistCellPrimitive_nyquist_increment_eq_pronicSeq_quad
    (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    nyquistCellPrimitive c (Real.log ((n : ℝ) + 1)) -
        nyquistCellPrimitive c (Real.log (n : ℝ)) =
      c ^ 2 / (pronicSeq n : ℝ) -
        2 * c *
          ((1 - 1 / ((n : ℝ) + 1)) * Real.log ((n : ℝ) + 1) -
            (1 - 1 / (n : ℝ)) * Real.log (n : ℝ)) +
        (nyquistCellPrimitive 0 (Real.log ((n : ℝ) + 1)) -
          nyquistCellPrimitive 0 (Real.log (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := nyquistCellPrimitive_sub_zero_log c hn1_pos
  have h0 := nyquistCellPrimitive_sub_zero_log c hn_pos
  have hpr : -c ^ 2 / ((n : ℝ) + 1) - (-c ^ 2 / (n : ℝ)) = c ^ 2 / (pronicSeq n : ℝ) := by
    rw [cast_pronicSeq_eq_mul_succ]
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    have hn1_ne : (n : ℝ) + 1 ≠ 0 := hn1_pos.ne'
    field_simp
    ring
  linarith

/-- **Exact Pronic-Quadratic Formula for the Chebyshev-Gauge Nyquist Cell Integral
(`integral_nyquistCell_window_sq_eq_pronicSeq_quad`):**
For every `c : ℝ` and cell index `1 ≤ n`, the Nyquist cell integral
`∫_{log n}^{log(n+1)} e^{-t}(c + 1 - t - e^t)² dt` equals `c² / pronicSeq n` minus the linear
log-cell drift plus the `c = 0` baseline cell increment. -/
theorem integral_nyquistCell_window_sq_eq_pronicSeq_quad
    (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2) =
      c ^ 2 / (pronicSeq n : ℝ) -
        2 * c *
          ((1 - 1 / ((n : ℝ) + 1)) * Real.log ((n : ℝ) + 1) -
            (1 - 1 / (n : ℝ)) * Real.log (n : ℝ)) +
        (nyquistCellPrimitive 0 (Real.log ((n : ℝ) + 1)) -
          nyquistCellPrimitive 0 (Real.log (n : ℝ))) := by
  rw [integral_nyquistCell_window_sq c n,
    nyquistCellPrimitive_nyquist_increment_eq_pronicSeq_quad c hn]

/-- **Pronic Abel Summation of the Nyquist Chebyshev Quadratic Energy
(`sum_chebyshev_psi_sq_div_pronicSeq_add_terminal_eq_abel`):**
For every horizon `T ≥ 1`, because `ψ(1) = 0`, the pronic quadratic Chebyshev sum
`∑_{n=1}^T ψ(n)² / pronicSeq n + ψ(T)² / (T + 1)` telescopes identically into the harmonic prime-jump
series `∑_{n=1}^{T-1} (ψ(n + 1)² - ψ(n)²) / (n + 1)`. -/
theorem sum_chebyshev_psi_sq_div_pronicSeq_add_terminal_eq_abel
    {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, Chebyshev.psi (n : ℝ) ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      Chebyshev.psi (T : ℝ) ^ (2 : ℕ) / ((T : ℝ) + 1) =
      ∑ n ∈ Finset.Icc 1 (T - 1),
        (Chebyshev.psi (((n + 1 : ℕ) : ℝ)) ^ (2 : ℕ) -
          Chebyshev.psi (n : ℝ) ^ (2 : ℕ)) / ((n : ℝ) + 1) := by
  have habel :=
    sum_sq_div_pronicSeq_add_terminal_eq_abel (fun n : ℕ => Chebyshev.psi (n : ℝ)) hT
  have hpsi1 : Chebyshev.psi ((1 : ℕ) : ℝ) = 0 := by
    rw [Nat.cast_one]
    exact Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)
  rw [hpsi1] at habel
  linarith

/-! ## §2. Universal Bézout Interior Sawtooth Smoothing, Non-Circular $O(1)$ Remainder & Strict Contraction -/

/-- **Universal Interior-Corrected Sawtooth Energy Step Identity
(`addDiff_weighted_sq_sub_bezoutInterior_sq_eq`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and step `n : ℕ` (with no sub-horizon restriction
`n ≤ N`), subtracting the square of `bezoutInteriorSawtoothSum N c` from the square of
`weightedCenteredSawtoothSum N c` eliminates the linear interior martingale product in favor of the
non-positive interior gradient square `-(addDiff (bezoutInteriorSawtoothSum N c) n)²`:
`addDiff (W_{N,c}² - (I^int_{N,c})²) n = (s_{N,c}(n) - Y(1))(s_{N,c}(n + 1) - Y(1)) - (addDiff I^int_{N,c} n)² + (s_{N,c}(n + 1) - Y(1)) addDiff (s_{N,c/d}) n - I^int_{N,c}(n) addDiff²(s_{N,c} - s_{N,c/d}) n`. -/
theorem addDiff_weighted_sq_sub_bezoutInterior_sq_eq
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    addDiff (fun k =>
      weightedCenteredSawtoothSum N c k ^ (2 : ℕ) -
        bezoutInteriorSawtoothSum N c k ^ (2 : ℕ)) n =
      (sieveSeq N c n - selbergMultiplesCoord N c 1) *
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) -
      addDiff (bezoutInteriorSawtoothSum N c) n ^ (2 : ℕ) +
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n -
      bezoutInteriorSawtoothSum N c n *
        addDiff (addDiff (fun k =>
          sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k)) n := by
  have h1 := weightedCenteredSawtoothSum_succ_sq_sub_sq_eq_bezout_interior N c n
  have h2 := two_mul_sieveSeq_sub_mul_bezoutInterior_eq_addDiff_sq_sub N c n
  have hdiff :
      addDiff (fun k =>
        weightedCenteredSawtoothSum N c k ^ (2 : ℕ) -
          bezoutInteriorSawtoothSum N c k ^ (2 : ℕ)) n =
      (weightedCenteredSawtoothSum N c (n + 1) ^ (2 : ℕ) -
        weightedCenteredSawtoothSum N c n ^ (2 : ℕ)) -
      addDiff (fun k => bezoutInteriorSawtoothSum N c k ^ (2 : ℕ)) n := by
    unfold addDiff
    ring
  linarith [h1, h2, hdiff]

/-- **Universal Upper Bound on the Interior-Corrected Sawtooth Energy Increment
(`addDiff_weighted_sq_sub_bezoutInterior_sq_le`):**
Because `(addDiff (bezoutInteriorSawtoothSum N c) n)² ≥ 0`, the step increment of
`W_{N,c}² - (I^int_{N,c})²` is bounded above by the Bézout successor covariance plus the
harmonic-divided difference terms alone. -/
theorem addDiff_weighted_sq_sub_bezoutInterior_sq_le
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    addDiff (fun k =>
      weightedCenteredSawtoothSum N c k ^ (2 : ℕ) -
        bezoutInteriorSawtoothSum N c k ^ (2 : ℕ)) n ≤
      (sieveSeq N c n - selbergMultiplesCoord N c 1) *
        (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) +
      (sieveSeq N c (n + 1) - selbergMultiplesCoord N c 1) *
        addDiff (sieveSeq N (fun d => c d / (d : ℝ))) n -
      bezoutInteriorSawtoothSum N c n *
        addDiff (addDiff (fun k =>
          sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k)) n := by
  rw [addDiff_weighted_sq_sub_bezoutInterior_sq_eq]
  linarith [sq_nonneg (addDiff (bezoutInteriorSawtoothSum N c) n)]

/-- **Unconditional $O(1)$ Compensated Remainder Bound on the Non-Circular Interior Gradient + Local-Impulse Sum
(`exists_pmBezoutInteriorGradient_add_two_mul_localImpulse_compensated_bound`):**
For every `ε > 0`, there exists a horizon-independent constant `C ≥ 0` such that for all `T ≥ 1`:
`|(pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) - 2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ C`. -/
theorem exists_pmBezoutInteriorGradient_add_two_mul_localImpulse_compensated_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 1 ≤ T →
      |(pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) -
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T| ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pmActiveDeletedCovarianceDiagonal_compensated_bound hε
  obtain ⟨C₂, hC₂, h₂⟩ := exists_pmPredecessorPeak_compensated_bound hε
  refine ⟨C₁ + 2 * C₂ + 1 / 4 + |pmInteriorActivePotential ε 1|, by positivity, fun T hT => ?_⟩
  have hcons :=
    pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak ε hT
  have hdrift := pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak ε
  have hrew :
      (pmBezoutInteriorGradientSum ε T + 2 * pmBezoutLocalImpulseCrossSum ε T) -
        2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T =
      (pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) +
      2 * (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) -
      pmActivePairPronicEnergy ε T -
      pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1)) := by
    rw [hcons, ← hdrift]
    ring
  rw [hrew]
  have hpr := pmActivePairPronicEnergy_bounds hε.le T
  have h1T0 : 0 ≤ 1 - 1 / ((T : ℝ) + 1) := by
    have : (1 : ℝ) / ((T : ℝ) + 1) ≤ 1 :=
      div_le_self zero_le_one (by linarith [Nat.cast_nonneg (α := ℝ) T])
    linarith
  have h1T1 : 1 - 1 / ((T : ℝ) + 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  have hA := h₁ T
  have hB := h₂ T
  obtain ⟨hA_low, hA_high⟩ := abs_le.mp hA
  obtain ⟨hB_low, hB_high⟩ := abs_le.mp hB
  have hpot_abs :
      |pmInteriorActivePotential ε 1 * (1 - 1 / ((T : ℝ) + 1))| ≤
        |pmInteriorActivePotential ε 1| := by
    rw [abs_mul, abs_of_nonneg h1T0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1T1
  obtain ⟨hpot_low, hpot_high⟩ := abs_le.mp hpot_abs
  exact abs_le.mpr ⟨by linarith [hpr.1, hpr.2], by linarith [hpr.1, hpr.2]⟩

/-- **Cofinal Strict Interior Contraction Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_cofinal_pmInterior_strict_contraction`):**
If for every `δ₀ > 0` there exist `ε ∈ (0, δ₀)`, a contraction margin `δ > 0`, and a constant `C : ℝ`
such that for all `T : ℕ`:
`2 * pmBezoutInteriorMartingaleSum ε T + 2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤ (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofinal_pmInterior_strict_contraction
    (h : ∀ δ₀ : ℝ, 0 < δ₀ → ∃ ε : ℝ, 0 < ε ∧ ε < δ₀ ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ T : ℕ,
        2 * pmBezoutInteriorMartingaleSum ε T +
          2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T ≤
          (1 - δ) * pmPowerDampedDivisorDiscreteEnergy ε T + C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ₀ hδ₀
  obtain ⟨ε, hε, hεδ₀, hcontr⟩ := h δ₀ hδ₀
  obtain ⟨K, hK⟩ := (pmInterior_strict_contraction_iff_bounded_energy hε).mp hcontr
  exact ⟨ε, hε, hεδ₀, K, hK⟩

/-! ## §3. Vasyunin Reciprocal-Cell Pronic Gram Matrix, Route PM Cofactor Iso-State Dissipation & Barban–Vehov Bridge -/

/-- **Route PM Cofactor Iso-State Dissipation & Spectral Gram Equivalence
(`pmCofactorDivisorWeight_isoState_defect_and_pronicGram_bridge`):**
For every `ε > 0` and `Q : ℕ`, the Route PM cofactor divisor weight `pmCofactorDivisorWeight ε Q`
at cutoff `Q + 1` simultaneously satisfies:
1. **Short-Window Iso-State Pure-Dirichlet Identity & Dissipation:** On any window `[M₀ + 1, M₀ + M]`
   whose endpoints share the same multiplicative observation fiber
   `horizonObservationState (Q + 1) (M₀ + M + 1) = horizonObservationState (Q + 1) (M₀ + 1)`,
   `2 * shortWindowRenormalizedDefect (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q) = -shortWindowDirichletEnergy (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q)`
   and `shortWindowRenormalizedDefect (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q) ≤ 0`.
2. **Exact Energy-Centered Pronic Gram Equivalence:**
   `sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) = pmPowerDampedRamanujanEnergyVariance ε Q`. -/
theorem pmCofactorDivisorWeight_isoState_defect_and_pronicGram_bridge
    {ε : ℝ} (hε : 0 < ε) (Q M₀ M : ℕ)
    (hstate :
      horizonObservationState (Q + 1) (M₀ + M + 1) =
        horizonObservationState (Q + 1) (M₀ + 1)) :
    2 * shortWindowRenormalizedDefect (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q) =
        -shortWindowDirichletEnergy (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q) ∧
      shortWindowRenormalizedDefect (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q) ≤ 0 ∧
      sieveEnergyCenteredPronicGramForm (Q + 1) (pmCofactorDivisorWeight ε Q) =
        pmPowerDampedRamanujanEnergyVariance ε Q := by
  have hsieve :=
    (horizonObservationState_eq_iff_all_sieveSeq (Q + 1) (M₀ + M + 1) (M₀ + 1)).mp hstate
      (pmCofactorDivisorWeight ε Q)
  have hpol :=
    two_mul_shortWindowRenormalizedDefect_eq (Q + 1) M₀ M (pmCofactorDivisorWeight ε Q)
  rw [hsieve] at hpol
  refine ⟨by linarith, ?_, sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq hε Q⟩
  exact (forall_weight_shortWindowRenormalizedDefect_nonpos_iff_state_eq (Q + 1) M₀ M).mpr
    hstate (pmCofactorDivisorWeight ε Q)

/-- **Initial-Window $L^2$ Normalization and Unit-Shift Correlation Annihilation of `DeletionAveragedDivisor.divisorSource`
(`deletionAveragedDivisor_initial_window_l2_and_shift_annihilation`):**
For any `1 ≤ X < M`, the tapered Barban–Vehov divisor source `DeletionAveragedDivisor.divisorSource X M`
has exact unit `L²` energy `∑_{k=1}^X (divisorSource X M k)² = 1` on `[1, X]` and vanishing
consecutive correlation `∑_{k=1}^{X-1} divisorSource X M k * divisorSource X M (k + 1) = 0`,
isolating 100% of its non-trivial correlation and `L²` excess to the trans-horizon von Mangoldt
exposure band `X < k ≤ M`. -/
theorem deletionAveragedDivisor_initial_window_l2_and_shift_annihilation
    {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) :
    (∑ k ∈ Finset.Icc 1 X, DeletionAveragedDivisor.divisorSource X M k ^ (2 : ℕ)) = 1 ∧
      (∑ k ∈ Finset.Icc 1 (X - 1),
        DeletionAveragedDivisor.divisorSource X M k *
          DeletionAveragedDivisor.divisorSource X M (k + 1)) = 0 := by
  obtain ⟨h1, hzero, _⟩ := deletionAveragedDivisor_window_annihilation_and_vonMangoldt_exposure hX hXM
  refine ⟨?_, ?_⟩
  · have hsplit : Finset.Icc 1 X = insert 1 (Finset.Icc 2 X) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (1 : ℕ) ∉ Finset.Icc 2 X := by simp
    rw [hsplit, Finset.sum_insert hnot, h1, one_pow]
    have hrest :
        (∑ k ∈ Finset.Icc 2 X, DeletionAveragedDivisor.divisorSource X M k ^ (2 : ℕ)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨hk2, hkX⟩ := Finset.mem_Icc.mp hk
      rw [hzero k (by omega) hkX, zero_pow (by decide)]
    linarith
  · refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hk1, hkX1⟩ := Finset.mem_Icc.mp hk
    rw [hzero (k + 1) (by omega) (by omega), mul_zero]

/-- **Unified Vasyunin Reciprocal-Cell Pronic Gram, Dilated Cell Scaling & First-Tail-Cell Möbius Bridge
(`vasyunin_pronic_gram_and_first_tail_cell_mobius_bridge`):**
Packages the exact pronic-cell decomposition of the Fermi–Nyman head/tail Gram matrices, the
multiplicative dilation scaling `fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k)`, the
head/tail pronic split of `singleCellFermiCombinator`, and the first-tail-cell Möbius energy
`μ(2M + 1)² / pronicSeq (2M + 1)`. -/
theorem vasyunin_pronic_gram_and_first_tail_cell_mobius_bridge
    (N d₁ d₂ k d n : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (fermiHeadGram N d₁ d₂ =
        ((∑ m ∈ Finset.Icc 1 N,
          (fermiCellMatrix (d₁ + 1) m * fermiCellMatrix (d₂ + 1) m) /
            (pronicSeq m : ℝ) : ℝ) : ℂ) ∧
      fermiTailGram N d₁ d₂ =
        fermiGlobalGram d₁ d₂ -
          ((∑ m ∈ Finset.Icc 1 N,
            (fermiCellMatrix (d₁ + 1) m * fermiCellMatrix (d₂ + 1) m) /
              (pronicSeq m : ℝ) : ℝ) : ℂ)) ∧
      fermiCellMatrix (k * d) n = fermiCellMatrix d (n / k) ∧
      ((∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
          (if k + 1 ≤ N then 1 / (pronicSeq (k + 1) : ℝ) else 0) ∧
        (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
          ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
          (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) -
            (if k + 1 ≤ N then 1 / (pronicSeq (k + 1) : ℝ) else 0)) ∧
      (∫ t in Ioc (1 / (((2 * M + 1 : ℕ) : ℝ) + 1)) (1 / ((2 * M + 1 : ℕ) : ℝ)),
        ‖singleCellFermiCombinator 1 (2 * M) t‖ ^ (2 : ℕ)) =
        moebiusReal (2 * M + 1) ^ (2 : ℕ) / (pronicSeq (2 * M + 1) : ℝ) :=
  ⟨fermiHead_and_tailGram_eq_pronicSeq_sum N d₁ d₂,
    fermiCellMatrix_mul_left k d n,
    singleCellFermiCombinator_pronicSeq_head_and_tail_energy k N,
    setIntegral_first_tail_cell_normSq_singleCellFermiCombinator_one_even hM⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
