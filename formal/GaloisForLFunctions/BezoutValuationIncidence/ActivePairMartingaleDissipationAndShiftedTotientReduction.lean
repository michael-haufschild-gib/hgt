import GaloisForLFunctions.BezoutValuationIncidence.PostStepInactiveEnergyAndPronicGradientConservation

/-!
# Pillar XXVII: Active-Pair Martingale Dissipation, Shifted-Totient Reduction & Compensated Pronic–Gradient Diagonal Identity

In Pillar XXVI (`PostStepInactiveEnergyAndPronicGradientConservation`), we established the general
linear Pronic Abel summation identity `sum_div_pronicSeq_eq_compensated_abel` and the exact
pointwise pronic–diagonal–gradient conservation law.

In this twenty-seventh pillar of **Bézout–Valuation Incidence Mechanics**, we apply these tools to
the combined Bézout active-pair martingale sum
$$\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
  \operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T
  = \operatorname{pmPredictableMartingaleSum}\,\varepsilon\,T -
    \operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T$$
and to `pmPowerDampedDivisorCovarianceDiagonal`, establishing three new foundational mechanisms:

1. **General Compensated Abel Dissipation Identity for Backward-Weighted Increments
   (`neg_succ_mul_addDiff_eq`,
   `sum_neg_succ_mul_addDiff_compensated_eq`,
   `sum_neg_succ_mul_addDiff_compensated_le`)**:
   - For every sequence $X : \mathbb{N} \to \mathbb{R}$ and $n \in \mathbb{N}$:
     $$-X(n + 1)\,\operatorname{addDiff}\,X\,n
       = -\frac{1}{2}\,\operatorname{addDiff}\,(X^2)\,n - \frac{1}{2}\bigl(\operatorname{addDiff}\,X\,n\bigr)^2.$$
   - Weighting by $\frac{1}{n + 1} - \frac{1}{T + 1}$ and applying `sum_div_pronicSeq_eq_compensated_abel`
     to $B(n) = X(n)^2$ gives for every $T \ge 1$:
     $$\sum_{n=1}^{T-1} \bigl(-X(n + 1)\,\operatorname{addDiff}\,X\,n\bigr)\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
       = \frac{1}{2}\,X(1)^2\left(1 - \frac{1}{T + 1}\right)
         - \frac{1}{2}\sum_{n=1}^T \frac{X(n)^2}{\operatorname{pronicSeq}\,n}
         - \frac{1}{2}\sum_{n=1}^{T-1} \bigl(\operatorname{addDiff}\,X\,n\bigr)^2\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
       \le \frac{1}{2}\,X(1)^2\left(1 - \frac{1}{T + 1}\right).$$

2. **Purely Dissipative Sawtooth Self-Interaction & Shifted-Totient Reduction of the Active-Pair Martingale
   (`pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq`,
   `pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq`,
   `pmActive_add_pmPredecessorPeak_eq_dissipation_add_shiftedTotient`,
   `pmActive_add_pmPredecessorPeak_le_shiftedTotient`)**:
   - Writing $\widetilde{\tau}_\varepsilon(n + 1) = -2\,S_\varepsilon(n + 1) + \bigl(\tau_{1+\varepsilon}(n + 1) - \alpha_\varepsilon\bigr)$
     where $S_\varepsilon = \operatorname{pmActiveSawtoothComponent}\,\varepsilon$ ($S_\varepsilon(1) = 0$),
     the self-interaction $-2\,S_\varepsilon(n + 1)\,\operatorname{addDiff}\,(S_\varepsilon)\,n$ is
     **purely dissipative** (with zero boundary term at $n = 1$!):
     $$\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
       \operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T
       = -\sum_{n=1}^T \frac{S_\varepsilon(n)^2}{\operatorname{pronicSeq}\,n}
         - \sum_{n=1}^{T-1} \bigl(\operatorname{addDiff}\,(S_\varepsilon)\,n\bigr)^2\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
         + \sum_{n=1}^{T-1} \bigl(\tau_{1+\varepsilon}(n + 1) - \alpha_\varepsilon\bigr)\,\operatorname{addDiff}\,(S_\varepsilon)\,n\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)
       \le \sum_{n=1}^{T-1} \bigl(\tau_{1+\varepsilon}(n + 1) - \alpha_\varepsilon\bigr)\,\operatorname{addDiff}\,(S_\varepsilon)\,n\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$

3. **Exact Compensated Pronic–Gradient Decomposition of `pmPowerDampedDivisorCovarianceDiagonal`
   (`sum_Icc_pred_compensated_add_sum_pronicSeq_eq`,
   `pmPowerDampedDivisorCovarianceDiagonal_eq_pronic_add_gradient`)**:
   - For every sequence $f : \mathbb{N} \to \mathbb{R}$ and $T \ge 1$:
     $$\sum_{n=1}^{T-1} f(n)\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right) +
       \sum_{n=1}^T \frac{f(n)}{\operatorname{pronicSeq}\,n}
       = \sum_{m=1}^T f(m)\left(\frac{1}{m} - \frac{1}{T + 1}\right).$$
   - Combining this with `pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal` and
     `addDiff_pmPowerDampedDivisorCoeff_sq_add_two_mul_centered_pronic` decomposes
     `pmPowerDampedDivisorCovarianceDiagonal ε T` into the compensated centered pronic sum, half the
     compensated squared BVI gradient, and the bounded $O(1)$ boundary/pronic terms.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. General Compensated Abel Dissipation Identity for Backward-Weighted Increments -/

/-- **Pointwise Backward-Weighted Increment Dissipation Identity (`neg_succ_mul_addDiff_eq`):**
For every sequence `X : ℕ → ℝ` and `n : ℕ`:
`-X(n + 1) * addDiff X n = -(1 / 2) * addDiff (fun k => X k ^ 2) n - (1 / 2) * (addDiff X n) ^ 2`. -/
theorem neg_succ_mul_addDiff_eq (X : ℕ → ℝ) (n : ℕ) :
    -X (n + 1) * addDiff X n =
      -(1 / 2 : ℝ) * addDiff (fun k => X k ^ (2 : ℕ)) n -
        (1 / 2 : ℝ) * addDiff X n ^ (2 : ℕ) := by
  unfold addDiff
  ring

/-- **General Compensated Abel Dissipation Identity (`sum_neg_succ_mul_addDiff_compensated_eq`):**
For every sequence `X : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^{T-1} (-X(n + 1) * addDiff X n) * (1 / (n + 1) - 1 / (T + 1))` equals
`(1 / 2) * X(1)² * (1 - 1 / (T + 1)) - (1 / 2) * ∑_{n=1}^T X(n)² / pronicSeq n - (1 / 2) * ∑_{n=1}^{T-1} (addDiff X n)² * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem sum_neg_succ_mul_addDiff_compensated_eq (X : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      (-X (n + 1) * addDiff X n) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (1 / 2 : ℝ) * X 1 ^ (2 : ℕ) * (1 - 1 / ((T : ℝ) + 1)) -
        (1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 T, X n ^ (2 : ℕ) / (pronicSeq n : ℝ)) -
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff X n ^ (2 : ℕ) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have habel := sum_div_pronicSeq_eq_compensated_abel (fun k => X k ^ (2 : ℕ)) hT
  have hsplit :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (-X (n + 1) * addDiff X n) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      -(1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (fun k => X k ^ (2 : ℕ)) n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) -
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff X n ^ (2 : ℕ) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [neg_succ_mul_addDiff_eq X n]
    ring
  linarith

/-- **Universal Upper Bound on Backward-Weighted Increment Sums
(`sum_neg_succ_mul_addDiff_compensated_le`):**
For every sequence `X : ℕ → ℝ` and every `T ≥ 1`, because both the pronic square sum and the
compensated gradient square sum are non-negative, the backward-weighted increment sum is bounded
above by `(1 / 2) * X(1)² * (1 - 1 / (T + 1)) ≤ (1 / 2) * X(1)²`. -/
theorem sum_neg_succ_mul_addDiff_compensated_le (X : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      (-X (n + 1) * addDiff X n) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) ≤
      (1 / 2 : ℝ) * X 1 ^ (2 : ℕ) * (1 - 1 / ((T : ℝ) + 1)) := by
  rw [sum_neg_succ_mul_addDiff_compensated_eq X hT]
  have hpr : 0 ≤ ∑ n ∈ Finset.Icc 1 T, X n ^ (2 : ℕ) / (pronicSeq n : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hgr :
      0 ≤ ∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff X n ^ (2 : ℕ) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
    have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
    have hkern : 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)
    exact mul_nonneg (sq_nonneg _) hkern
  linarith

/-! ## §2. Purely Dissipative Sawtooth Self-Interaction & Shifted-Totient Reduction -/

/-- **Exact Active-Pair Martingale Difference Identity
(`pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPredictableMartingaleSum ε T - pmBezoutInteriorMartingaleSum ε T = pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T`,
which equals the compensated sum of `widetilde_τ_ε(n + 1) * addDiff (pmActiveSawtoothComponent ε) n`. -/
theorem pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq (ε : ℝ) (T : ℕ) :
    pmPredictableMartingaleSum ε T - pmBezoutInteriorMartingaleSum ε T =
      pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ∧
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T =
      ∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [pmPredictableMartingaleSum_eq_active_add_inactive,
      pmInactivePredictableMartingaleSum_eq_predecessorPeak_add_bezoutInterior]
    ring
  · unfold pmActivePredictableMartingaleSum pmPredecessorPeakMartingaleSum addDiff
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring

/-- **Pointwise Sawtooth Dissipation + Shifted-Totient Decomposition of the Active-Pair Product
(`pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq`):**
For every `ε : ℝ` and `n : ℕ`, writing
`widetilde_τ_ε(n + 1) = -2 * S_ε(n + 1) + (τ_{1+ε}(n + 1) - α_ε)` decomposes the active-pair product
`widetilde_τ_ε(n + 1) * addDiff (S_ε) n` into the purely dissipative sawtooth self-interaction
`-addDiff (S_ε²) n - (addDiff S_ε n)²` plus the shifted-exponent totient coupling
`(τ_{1+ε}(n + 1) - α_ε) * addDiff (S_ε) n`. -/
theorem pmPowerDampedCenteredDivisorCoeff_mul_addDiff_active_eq (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      addDiff (pmActiveSawtoothComponent ε) n =
      -addDiff (fun k => pmActiveSawtoothComponent ε k ^ (2 : ℕ)) n -
        addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) +
        (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
          addDiff (pmActiveSawtoothComponent ε) n := by
  have hsplit :
      pmPowerDampedCenteredDivisorCoeff ε (n + 1) =
        -2 * pmActiveSawtoothComponent ε (n + 1) +
          (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) := by
    unfold pmPowerDampedCenteredDivisorCoeff pmActiveSawtoothComponent
    ring
  have hdiss := neg_succ_mul_addDiff_eq (pmActiveSawtoothComponent ε) n
  rw [hsplit]
  linarith

/-- **Exact Dissipation + Shifted-Totient Decomposition of the Active-Pair Martingale Sum
(`pmActive_add_pmPredecessorPeak_eq_dissipation_add_shiftedTotient`):**
For every `ε : ℝ` and `T ≥ 1`, because `pmActiveSawtoothComponent ε 1 = 0`, the active-pair
martingale sum `pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T` equals
`-∑_{n=1}^T S_ε(n)² / pronicSeq n - ∑_{n=1}^{T-1} (addDiff S_ε n)² * (1 / (n + 1) - 1 / (T + 1))`
plus the shifted-exponent totient martingale sum
`∑_{n=1}^{T-1} (τ_{1+ε}(n + 1) - α_ε) * addDiff (S_ε) n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem pmActive_add_pmPredecessorPeak_eq_dissipation_add_shiftedTotient
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T =
      -(∑ n ∈ Finset.Icc 1 T,
          pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
            addDiff (pmActiveSawtoothComponent ε) n *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  rw [(pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq ε T).2]
  have hdiss := sum_neg_succ_mul_addDiff_compensated_eq (pmActiveSawtoothComponent ε) hT
  rw [pmActiveSawtoothComponent_one] at hdiss
  have hsum :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      2 * (∑ n ∈ Finset.Icc 1 (T - 1),
        (-pmActiveSawtoothComponent ε (n + 1) * addDiff (pmActiveSawtoothComponent ε) n) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
            addDiff (pmActiveSawtoothComponent ε) n *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsplit :
        pmPowerDampedCenteredDivisorCoeff ε (n + 1) =
          -2 * pmActiveSawtoothComponent ε (n + 1) +
            (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) := by
      unfold pmPowerDampedCenteredDivisorCoeff pmActiveSawtoothComponent
      ring
    rw [hsplit]
    ring
  linarith

/-- **Unconditional Shifted-Totient Upper Bound on the Active-Pair Martingale Sum
(`pmActive_add_pmPredecessorPeak_le_shiftedTotient`):**
For every `ε : ℝ` and `T ≥ 1`, dropping the two non-positive sawtooth dissipation sums bounds
`pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T` above by the
shifted-exponent totient coupling with **zero boundary error**. -/
theorem pmActive_add_pmPredecessorPeak_le_shiftedTotient (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmActivePredictableMartingaleSum ε T + pmPredecessorPeakMartingaleSum ε T ≤
      ∑ n ∈ Finset.Icc 1 (T - 1),
        (pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - (pmPowerDampedDivisorDensity ε).re) *
          addDiff (pmActiveSawtoothComponent ε) n *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  rw [pmActive_add_pmPredecessorPeak_eq_dissipation_add_shiftedTotient ε hT]
  have hpr :
      0 ≤ ∑ n ∈ Finset.Icc 1 T,
        pmActiveSawtoothComponent ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hgr :
      0 ≤ ∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff (pmActiveSawtoothComponent ε) n ^ (2 : ℕ) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    obtain ⟨_, hnT⟩ := Finset.mem_Icc.mp hn
    have hle : (n : ℝ) + 1 ≤ (T : ℝ) + 1 := by exact_mod_cast (by omega : n + 1 ≤ T + 1)
    have hkern : 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hle)
    exact mul_nonneg (sq_nonneg _) hkern
  linarith

/-! ## §3. Exact Compensated Pronic–Gradient Decomposition of `pmPowerDampedDivisorCovarianceDiagonal` -/

/-- **Exact Pronic Shift Identity for Compensated Harmonic Sums
(`sum_Icc_pred_compensated_add_sum_pronicSeq_eq`):**
For every sequence `f : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^{T-1} f(n) * (1 / (n + 1) - 1 / (T + 1)) + ∑_{n=1}^T f(n) / pronicSeq n = ∑_{m=1}^T f(m) * (1 / m - 1 / (T + 1))`. -/
theorem sum_Icc_pred_compensated_add_sum_pronicSeq_eq (f : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1),
      f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
      (∑ n ∈ Finset.Icc 1 T, f n / (pronicSeq n : ℝ)) =
      ∑ m ∈ Finset.Icc 1 T, f m * (1 / (m : ℝ) - 1 / ((T : ℝ) + 1)) := by
  have hsplit : Finset.Icc 1 T = insert T (Finset.Icc 1 (T - 1)) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : T ∉ Finset.Icc 1 (T - 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot]
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT1_pos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have htermT :
      f T / (pronicSeq T : ℝ) = f T * (1 / (T : ℝ) - 1 / ((T : ℝ) + 1)) := by
    unfold pronicSeq
    push_cast
    field_simp
    ring
  have hsum_eq :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (∑ n ∈ Finset.Icc 1 (T - 1), f n / (pronicSeq n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 (T - 1),
        f n * (1 / (n : ℝ) - 1 / ((T : ℝ) + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    unfold pronicSeq
    push_cast
    field_simp
    ring
  linarith

/-- **Exact Compensated Pronic–Gradient Decomposition of `pmPowerDampedDivisorCovarianceDiagonal`
(`pmPowerDampedDivisorCovarianceDiagonal_eq_pronic_add_gradient`):**
For every `ε : ℝ` and `T ≥ 1`, `pmPowerDampedDivisorCovarianceDiagonal ε T` decomposes into the
compensated centered pronic sum, half the compensated squared BVI gradient, plus the bounded `O(1)`
initial and pronic square sums:
`pmPowerDampedDivisorCovarianceDiagonal ε T = ∑_{n=1}^{T-1} widetilde_τ_ε(n) * widetilde_τ_ε(n + 1) * (1 / (n + 1) - 1 / (T + 1)) + (1 / 2) * ∑_{n=1}^{T-1} (addDiff (τ_ε) n)² * (1 / (n + 1) - 1 / (T + 1)) + (1 / 2) * widetilde_τ_ε(1)² * (1 - 1 / (T + 1)) + (1 / 2) * ∑_{n=1}^T widetilde_τ_ε(n)² / pronicSeq n`. -/
theorem pmPowerDampedDivisorCovarianceDiagonal_eq_pronic_add_gradient
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPowerDampedDivisorCovarianceDiagonal ε T =
      (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε n *
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) *
          (1 - 1 / ((T : ℝ) + 1)) +
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 T,
          pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
  have h1 := pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal ε hT
  have h2 :
      pmPowerDampedDivisorCovarianceDiagonal ε T =
        (∑ n ∈ Finset.Icc 1 (T - 1),
          pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
          ∑ n ∈ Finset.Icc 1 T,
            pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) / (pronicSeq n : ℝ) := by
    unfold pmPowerDampedDivisorCovarianceDiagonal
    exact (sum_Icc_pred_compensated_add_sum_pronicSeq_eq
      (fun n => pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ)) hT).symm
  have hcomb :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε n *
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff (pmPowerDampedDivisorCoeff ε) n ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (1 / 2 : ℝ) * (∑ n ∈ Finset.Icc 1 (T - 1),
        pmPowerDampedCenteredDivisorCoeff ε n ^ (2 : ℕ) *
          (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        (1 / 2 : ℝ) * ∑ n ∈ Finset.Icc 1 (T - 1),
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold addDiff pmPowerDampedCenteredDivisorCoeff
    ring
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence
