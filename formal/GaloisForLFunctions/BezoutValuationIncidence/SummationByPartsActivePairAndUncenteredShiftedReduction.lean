import GaloisForLFunctions.BezoutValuationIncidence.ActivePairMartingaleDissipationAndShiftedTotientReduction

/-!
# Pillar XXVIII: Compensated Summation by Parts, the Sharp `1 / 8` Active-Sawtooth Envelope & Complete Centering Elimination

In Pillar XXVII (`ActivePairMartingaleDissipationAndShiftedTotientReduction`), we proved that the
sawtooth self-interaction inside the Bézout active-pair martingale sum
$$\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
  \operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T$$
is purely dissipative.

In this twenty-eighth pillar of **Bézout–Valuation Incidence Mechanics**, we establish three new
foundational mechanisms that completely eliminate the centering constant
$\alpha_\varepsilon = (\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}$ from the
oscillatory active-pair martingale sum:

1. **General Compensated Abel Summation by Parts & Uncentered Shifted-Totient Reduction
   (`succ_mul_addDiff_eq_addDiff_mul_sub`,
   `sum_succ_mul_addDiff_compensated_eq_pronic_sub`,
   `sum_addDiff_pmActiveSawtoothComponent_compensated_eq`,
   `pmActive_add_pmPredecessorPeak_le_uncentered_shiftedTotient`)**:
   - For every pair of sequences $X, Y : \mathbb{N} \to \mathbb{R}$ and $T \ge 1$:
     $$\sum_{n=1}^{T-1} X(n + 1)\,\operatorname{addDiff}\,Y\,n \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
       = \sum_{n=1}^T \frac{X(n)\,Y(n)}{\operatorname{pronicSeq}\,n}
         - X(1)\,Y(1)\left(1 - \frac{1}{T + 1}\right)
         - \sum_{n=1}^{T-1} Y(n)\,\operatorname{addDiff}\,X\,n \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$
   - Because $S_\varepsilon(1) = 0$ and $S_\varepsilon(n) \ge 0$ for $\varepsilon \ge 0$, the
     centering drift $-\alpha_\varepsilon \sum_{n=1}^{T-1} \operatorname{addDiff}\,(S_\varepsilon)\,n \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right) = -\alpha_\varepsilon \sum_{n=1}^T \frac{S_\varepsilon(n)}{\operatorname{pronicSeq}\,n} \le 0$
     is universally non-positive, strengthening Pillar XXVII's bound to the **uncentered**
     shifted-totient bound:
     $$\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
       \operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T
       \le \sum_{n=1}^{T-1} \tau_{1+\varepsilon}(n + 1)\,\operatorname{addDiff}\,(S_\varepsilon)\,n \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$

2. **Sharp `1 / 8` Quadratic Envelope on $\tau_\varepsilon(n)\,S_\varepsilon(n)$ & Pronic Cross-Series Bound
   (`pmPowerDampedDivisorCoeff_mul_pmActiveSawtoothComponent_bounds`,
   `pmPowerDampedCenteredDivisorCoeff_mul_pmActiveSawtoothComponent_le_eighth`,
   `sum_centered_mul_pmActiveSawtoothComponent_div_pronicSeq_le_eighth`)**:
   - Because $0 \le \tau_\varepsilon(n) \le \tau_{1+\varepsilon}(n) \le 1$ for all $\varepsilon \ge 0$,
     $$0 \le \tau_\varepsilon(n)\,S_\varepsilon(n)
       = \frac{1}{2}\,\tau_\varepsilon(n)\bigl(\tau_{1+\varepsilon}(n) - \tau_\varepsilon(n)\bigr)
       \le \frac{1}{2}\,\tau_\varepsilon(n)\bigl(1 - \tau_\varepsilon(n)\bigr)
       = \frac{1}{8} - \frac{1}{2}\left(\tau_\varepsilon(n) - \frac{1}{2}\right)^2
       \le \frac{1}{8},$$
     and $\widetilde{\tau}_\varepsilon(n)\,S_\varepsilon(n) \le \tau_\varepsilon(n)\,S_\varepsilon(n) \le 1/8$,
     so $\sum_{n=1}^T \frac{\widetilde{\tau}_\varepsilon(n)\,S_\varepsilon(n)}{\operatorname{pronicSeq}\,n} \le \frac{1}{8}$
     uniformly for all $T \in \mathbb{N}$ and $\varepsilon \ge 0$.

3. **Complete Centering-Free Summation-by-Parts Decomposition of the Active-Pair Martingale Sum
   (`pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq_sbp`,
   `pmActive_add_pmPredecessorPeak_eq_sbp_uncentered`,
   `pmActive_add_pmPredecessorPeak_le_eighth_add_half_shifted_diff`)**:
   - Applying summation by parts to $\widetilde{\tau}_\varepsilon(n + 1)\,\operatorname{addDiff}\,(S_\varepsilon)\,n$
     absorbs **100% of the $\alpha_\varepsilon$ dependence** into the bounded pronic series
     $\sum_{n=1}^T \frac{\widetilde{\tau}_\varepsilon(n)\,S_\varepsilon(n)}{\operatorname{pronicSeq}\,n} \le \frac{1}{8}$:
     $$\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
       \operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T
       = \sum_{n=1}^T \frac{\widetilde{\tau}_\varepsilon(n)\,S_\varepsilon(n)}{\operatorname{pronicSeq}\,n}
         + \frac{1}{4}\sum_{n=1}^T \frac{\tau_\varepsilon(n)^2 - 1}{\operatorname{pronicSeq}\,n}
         - \frac{1}{4}\sum_{n=1}^{T-1} \bigl(\operatorname{addDiff}\,(\tau_\varepsilon)\,n\bigr)^2\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
         + \frac{1}{2}\sum_{n=1}^{T-1} \bigl(\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n) - \tau_{1+\varepsilon}(n)\,\tau_\varepsilon(n + 1)\bigr)\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
       \le \frac{1}{8} + \frac{1}{2}\sum_{n=1}^{T-1} \bigl(\tau_\varepsilon(n)\,\tau_{1+\varepsilon}(n) - \tau_{1+\varepsilon}(n)\,\tau_\varepsilon(n + 1)\bigr)\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. General Compensated Abel Summation by Parts & Uncentered Shifted-Totient Reduction -/

/-- **Discrete Leibniz Summation-by-Parts Identity (`succ_mul_addDiff_eq_addDiff_mul_sub`):**
For every pair of sequences `X, Y : ℕ → ℝ` and `n : ℕ`:
`X(n + 1) * addDiff Y n = addDiff (fun k => X k * Y k) n - Y(n) * addDiff X n`. -/
theorem succ_mul_addDiff_eq_addDiff_mul_sub (X Y : ℕ → ℝ) (n : ℕ) :
    X (n + 1) * addDiff Y n =
      addDiff (fun k => X k * Y k) n - Y n * addDiff X n := by
  unfold addDiff
  ring

/-- **General Compensated Abel Summation-by-Parts Identity
(`sum_succ_mul_addDiff_compensated_eq_pronic_sub`):**
For every pair of sequences `X, Y : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^{T-1} X(n + 1) * addDiff Y n * (1 / (n + 1) - 1 / (T + 1))` equals
`∑_{n=1}^T X(n) * Y(n) / pronicSeq n - X(1) * Y(1) * (1 - 1 / (T + 1)) - ∑_{n=1}^{T-1} Y(n) * addDiff X n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem sum_succ_mul_addDiff_compensated_eq_pronic_sub (X Y : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      X (n + 1) * addDiff Y n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 T, (X n * Y n) / (pronicSeq n : ℝ)) -
        X 1 * Y 1 * (1 - 1 / ((T : ℝ) + 1)) -
        ∑ n ∈ Finset.Icc 1 (T - 1),
          Y n * addDiff X n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have habel := sum_div_pronicSeq_eq_compensated_abel (fun k => X k * Y k) hT
  have hsplit :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        X (n + 1) * addDiff Y n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (fun k => X k * Y k) n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        ∑ n ∈ Finset.Icc 1 (T - 1),
          Y n * addDiff X n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [succ_mul_addDiff_eq_addDiff_mul_sub X Y n]
    ring
  linarith

/-- **Exact Pronic Evaluation of the Compensated Active Sawtooth Increment Sum
(`sum_addDiff_pmActiveSawtoothComponent_compensated_eq`):**
For every `ε : ℝ` and `T ≥ 1`:
`∑_{n=1}^{T-1} addDiff (pmActiveSawtoothComponent ε) n * (1 / (n + 1) - 1 / (T + 1)) = ∑_{n=1}^T pmActiveSawtoothComponent ε n / pronicSeq n`. -/
theorem sum_addDiff_pmActiveSawtoothComponent_compensated_eq (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      addDiff (pmActiveSawtoothComponent ε) n *
        (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      ∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n / (pronicSeq n : ℝ) := by
  have habel := sum_div_pronicSeq_eq_compensated_abel (pmActiveSawtoothComponent ε) hT
  rw [pmActiveSawtoothComponent_one, zero_mul, zero_add] at habel
  exact habel.symm

/-- **Unconditional Uncentered Shifted-Totient Upper Bound on the Active-Pair Martingale Sum
(`pmActive_add_pmPredecessorPeak_le_uncentered_shiftedTotient`):**
For every `ε ≥ 0` and `T ≥ 1`, because `0 ≤ (pmPowerDampedDivisorDensity ε).re` and
`0 ≤ pmActiveSawtoothComponent ε n`, the centering drift term in
`pmActive_add_pmPredecessorPeak_le_shiftedTotient` is non-positive, yielding the completely
uncentered bound:
`pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ≤ ∑_{n=1}^{T-1} τ_{1+ε}(n + 1) * addDiff (pmActiveSawtoothComponent ε) n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem pmActive_add_pmPredecessorPeak_le_uncentered_shiftedTotient
    {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ≤
      ∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedDivisorCoeff (1 + ε) (n + 1) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have hle := pmActive_add_pmPredecessorPeak_le_shiftedTotient ε hT
  have hsplit :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedDivisorCoeff (1 + ε) (n + 1) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        (pmPowerDampedDivisorDensity ε).re *
          ∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n / (pronicSeq n : ℝ) := by
    rw [← sum_addDiff_pmActiveSawtoothComponent_compensated_eq ε hT,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hprod : 0 ≤ (pmPowerDampedDivisorDensity ε).re *
      ∑ n ∈ Finset.Icc 1 T, pmActiveSawtoothComponent ε n / (pronicSeq n : ℝ) :=
    mul_nonneg (pmPowerDampedDivisorDensity_re_pos hε).le
      (Finset.sum_nonneg fun n _ =>
        div_nonneg (pmActiveSawtoothComponent_nonneg hε.le n) (Nat.cast_nonneg _))
  linarith

/-! ## §2. Sharp `1 / 8` Quadratic Envelope on `τ_ε(n) * S_ε(n)` & Pronic Cross-Series Bound -/

/-- **Sharp `[0, 1 / 8]` Bounds on `pmPowerDampedDivisorCoeff ε n * pmActiveSawtoothComponent ε n`
(`pmPowerDampedDivisorCoeff_mul_pmActiveSawtoothComponent_bounds`):**
For every `ε ≥ 0` and `n : ℕ`:
`0 ≤ τ_ε(n) * pmActiveSawtoothComponent ε n ≤ 1 / 8`. -/
theorem pmPowerDampedDivisorCoeff_mul_pmActiveSawtoothComponent_bounds
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ pmPowerDampedDivisorCoeff ε n * pmActiveSawtoothComponent ε n ∧
      pmPowerDampedDivisorCoeff ε n * pmActiveSawtoothComponent ε n ≤ 1 / 8 := by
  have h0 : 0 ≤ pmPowerDampedDivisorCoeff ε n := pmPowerDampedDivisorCoeff_nonneg hε n
  have hS0 : 0 ≤ pmActiveSawtoothComponent ε n := pmActiveSawtoothComponent_nonneg hε n
  refine ⟨mul_nonneg h0 hS0, ?_⟩
  unfold pmActiveSawtoothComponent
  have h1 : pmPowerDampedDivisorCoeff (1 + ε) n ≤ 1 :=
    pmPowerDampedDivisorCoeff_le_one (by linarith) n
  have hle_quad :
      pmPowerDampedDivisorCoeff ε n *
        (-(1 / 2 : ℝ) * (pmPowerDampedDivisorCoeff ε n - pmPowerDampedDivisorCoeff (1 + ε) n)) ≤
      (1 / 2 : ℝ) * pmPowerDampedDivisorCoeff ε n * (1 - pmPowerDampedDivisorCoeff ε n) := by
    nlinarith
  have hsq : 0 ≤ (pmPowerDampedDivisorCoeff ε n - 1 / 2) ^ (2 : ℕ) := sq_nonneg _
  linarith

/-- **Universal `1 / 8` Upper Bound on `widetilde_τ_ε(n) * pmActiveSawtoothComponent ε n`
(`pmPowerDampedCenteredDivisorCoeff_mul_pmActiveSawtoothComponent_le_eighth`):**
For every `ε > 0` and `n : ℕ`:
`pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n ≤ 1 / 8`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_pmActiveSawtoothComponent_le_eighth
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n ≤ 1 / 8 := by
  unfold pmPowerDampedCenteredDivisorCoeff
  have hprod : 0 ≤ (pmPowerDampedDivisorDensity ε).re * pmActiveSawtoothComponent ε n :=
    mul_nonneg (pmPowerDampedDivisorDensity_re_pos hε).le
      (pmActiveSawtoothComponent_nonneg hε.le n)
  linarith [(pmPowerDampedDivisorCoeff_mul_pmActiveSawtoothComponent_bounds hε.le n).2]

/-- **Uniform `1 / 8` Pronic Series Bound on `widetilde_τ_ε(n) * pmActiveSawtoothComponent ε n`
(`sum_centered_mul_pmActiveSawtoothComponent_div_pronicSeq_le_eighth`):**
For every `ε > 0` and `T : ℕ`:
`∑_{n=1}^T (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) / pronicSeq n ≤ 1 / 8`. -/
theorem sum_centered_mul_pmActiveSawtoothComponent_div_pronicSeq_le_eighth
    {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T,
      (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) /
        (pronicSeq n : ℝ)) ≤ 1 / 8 := by
  have hle :
      (∑ n ∈ Finset.Icc 1 T,
        (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) /
          (pronicSeq n : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 T, (1 / 8 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := by
    apply Finset.sum_le_sum
    intro n _
    have hpt := pmPowerDampedCenteredDivisorCoeff_mul_pmActiveSawtoothComponent_le_eighth hε n
    have hpr : (0 : ℝ) ≤ 1 / (pronicSeq n : ℝ) := by positivity
    calc
      (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) / (pronicSeq n : ℝ)
        = (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) *
            ((1 : ℝ) / (pronicSeq n : ℝ)) := by ring
      _ ≤ (1 / 8 : ℝ) * ((1 : ℝ) / (pronicSeq n : ℝ)) := mul_le_mul_of_nonneg_right hpt hpr
  rw [← Finset.mul_sum] at hle
  linarith [sum_one_div_pronicSeq_le_one T]

/-! ## §3. Complete Centering-Free Summation-by-Parts Decomposition of the Active-Pair Martingale Sum -/

/-- **Pointwise Summation-by-Parts Identity for the Active-Pair Martingale Product
(`pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq_sbp`):**
For every `ε : ℝ` and `n : ℕ`:
`widetilde_τ_ε(n + 1) * addDiff (S_ε) n = addDiff (widetilde_τ_ε * S_ε) n + (1 / 4) * addDiff (τ_ε²) n - (1 / 4) * (addDiff (τ_ε) n)² + (1 / 2) * (τ_ε(n) * τ_{1+ε}(n) - τ_{1+ε}(n) * τ_ε(n + 1))`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq_sbp (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      addDiff (pmActiveSawtoothComponent ε) n =
      addDiff (fun k => pmPowerDampedCenteredDivisorCoeff ε k * pmActiveSawtoothComponent ε k) n +
        (1 / 4 : ℝ) * addDiff (fun k => pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ)) n -
        (1 / 4 : ℝ) * addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
            pmPowerDampedDivisorCoeff (1 + ε) n * pmPowerDampedDivisorCoeff ε (n + 1)) := by
  unfold addDiff pmPowerDampedCenteredDivisorCoeff pmActiveSawtoothComponent
  ring

/-- **Exact Pronic Evaluation of the Compensated Square-Increment Sum of `pmPowerDampedDivisorCoeff`
(`sum_addDiff_pmPowerDampedDivisorCoeff_sq_compensated_eq`):**
For every `ε : ℝ` and `T ≥ 1`:
`∑_{n=1}^{T-1} addDiff (τ_ε²) n * (1 / (n + 1) - 1 / (T + 1)) = ∑_{n=1}^T (τ_ε(n)² - 1) / pronicSeq n`. -/
theorem sum_addDiff_pmPowerDampedDivisorCoeff_sq_compensated_eq
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      addDiff (fun k => pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ)) n *
        (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      ∑ n ∈ Finset.Icc 1 T,
        (pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) - 1) / (pronicSeq n : ℝ) := by
  have habel := sum_div_pronicSeq_eq_compensated_abel
    (fun k => pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ)) hT
  rw [pmPowerDampedDivisorCoeff_one, one_pow, one_mul, ← sum_one_div_pronicSeq_eq hT] at habel
  have hsub :
      (∑ n ∈ Finset.Icc 1 T,
        (pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) - 1) / (pronicSeq n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 T,
        pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) -
        ∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  linarith

/-- **Complete Centering-Free Summation-by-Parts Decomposition of the Active-Pair Martingale Sum
(`pmActive_add_pmPredecessorPeak_eq_sbp_uncentered`):**
For every `ε : ℝ` and `T ≥ 1`:
`pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T` decomposes into:
1. The bounded pronic series `∑_{n=1}^T (widetilde_τ_ε(n) * S_ε(n)) / pronicSeq n`,
2. The non-positive pronic deficit `(1 / 4) * ∑_{n=1}^T (τ_ε(n)² - 1) / pronicSeq n ≤ 0`,
3. The non-positive gradient dissipation `-(1 / 4) * ∑_{n=1}^{T-1} (addDiff (τ_ε) n)² * (1 / (n + 1) - 1 / (T + 1)) ≤ 0`,
4. The completely uncentered shifted-exponent difference sum
   `(1 / 2) * ∑_{n=1}^{T-1} (τ_ε(n) * τ_{1+ε}(n) - τ_{1+ε}(n) * τ_ε(n + 1)) * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem pmActive_add_pmPredecessorPeak_eq_sbp_uncentered
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T =
      (∑ n ∈ Finset.Icc 1 T,
        (pmPowerDampedCenteredDivisorCoeff ε n * pmActiveSawtoothComponent ε n) /
          (pronicSeq n : ℝ)) +
        (1 / 4 : ℝ) * (∑ n ∈ Finset.Icc 1 T,
          (pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) - 1) / (pronicSeq n : ℝ)) -
        (1 / 4 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
            pmPowerDampedDivisorCoeff (1 + ε) n * pmPowerDampedDivisorCoeff ε (n + 1)) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  rw [(pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq ε T).2]
  have habel1 := sum_div_pronicSeq_eq_compensated_abel
    (fun k => pmPowerDampedCenteredDivisorCoeff ε k * pmActiveSawtoothComponent ε k) hT
  rw [pmActiveSawtoothComponent_one, mul_zero, zero_mul, zero_add] at habel1
  have habel2 := sum_addDiff_pmPowerDampedDivisorCoeff_sq_compensated_eq ε hT
  have hrew :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (fun k => pmPowerDampedCenteredDivisorCoeff ε k * pmActiveSawtoothComponent ε k) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 4 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (fun k => pmPowerDampedDivisorCoeff ε k ^ (2 : ℕ)) n *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        (1 / 4 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
            pmPowerDampedDivisorCoeff (1 + ε) n * pmPowerDampedDivisorCoeff ε (n + 1)) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq_sbp ε n]
    ring
  linarith

/-- **Unconditional `1 / 8` + Uncentered Shifted-Difference Upper Bound on the Active-Pair Martingale Sum
(`pmActive_add_pmPredecessorPeak_le_eighth_add_half_shifted_diff`):**
For every `ε ≥ 0` and `T ≥ 1`:
`pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ≤ 1 / 8 + (1 / 2) * ∑_{n=1}^{T-1} (τ_ε(n) * τ_{1+ε}(n) - τ_{1+ε}(n) * τ_ε(n + 1)) * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem pmActive_add_pmPredecessorPeak_le_eighth_add_half_shifted_diff
    {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ≤
      1 / 8 +
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
            pmPowerDampedDivisorCoeff (1 + ε) n * pmPowerDampedDivisorCoeff ε (n + 1)) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  rw [pmActive_add_pmPredecessorPeak_eq_sbp_uncentered ε hT]
  have h1 := sum_centered_mul_pmActiveSawtoothComponent_div_pronicSeq_le_eighth hε T
  have h2 :
      (∑ n ∈ Finset.Icc 1 T,
        (pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) - 1) / (pronicSeq n : ℝ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro n _
    have h0 := pmPowerDampedDivisorCoeff_nonneg hε.le n
    have hle1 := pmPowerDampedDivisorCoeff_le_one hε.le n
    have hsq : pmPowerDampedDivisorCoeff ε n ^ (2 : ℕ) - 1 ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg hsq (Nat.cast_nonneg _)
  have h3 :
      0 ≤ ∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
    have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
    have hkern : 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)
    exact mul_nonneg (sq_nonneg _) hkern
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
