import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSmallDampingVariance

/-!
# Pillar XIII: Predictable Martingale Decomposition & Covariance Cancellation Bridge for Route PM

In Pillar X (`PowerDampedPronicMultiplicativityAndRoutePMBridge`), we established the Pronic Abel
Summation identity for `pmPowerDampedDivisorDiscreteEnergy ε T`:
$$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T +
  \frac{A_\varepsilon(T)^2}{T + 1} =
  A_\varepsilon(1)^2 + \sum_{n=1}^{T-1} \frac{A_\varepsilon(n + 1)^2 - A_\varepsilon(n)^2}{n + 1},$$
where $A_\varepsilon(n) = \operatorname{pmPowerDampedCenteredDivisorPrefix}\,\varepsilon\,n$ and
$\widetilde{\tau}_\varepsilon(k) = \operatorname{pmPowerDampedCenteredDivisorCoeff}\,\varepsilon\,k$.

In this thirteenth pillar of **Bézout–Valuation Incidence Mechanics**, we resolve the square-difference
numerators $A(n + 1)^2 - A(n)^2$ into their **diagonal square increment** plus **twice the predictable
martingale increment**:
$$A(n + 1)^2 - A(n)^2 = (\Delta^+ A)(n)^2 + 2\,(\Delta^+ A)(n)\,A(n),$$
where $(\Delta^+ A)(n) = \operatorname{addDiff}\,A\,n = A(n + 1) - A(n)$.

## Core Main Theorems (100% Unconditional)

1. **Pointwise & Telescoping Square-Increment Martingale Identities
   (`sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff`,
   `sq_eq_sq_one_add_sum_addDiff_sq_add_two_mul_martingale`)**:
   For any sequence $A : \mathbb{N} \to \mathbb{R}$,
   $$A(n + 1)^2 - A(n)^2 = (\operatorname{addDiff}\,A\,n)^2 + 2\,(\operatorname{addDiff}\,A\,n)\,A(n),$$
   and for every $T \ge 1$,
   $$A(T)^2 = A(1)^2 + \sum_{n=1}^{T-1} (\operatorname{addDiff}\,A\,n)^2 +
     2 \sum_{n=1}^{T-1} (\operatorname{addDiff}\,A\,n)\,A(n).$$

2. **General Pronic-to-Martingale & Terminal-Compensated Decomposition
   (`sum_sq_div_pronicSeq_add_terminal_eq_martingale`,
   `sum_sq_div_pronicSeq_eq_compensated_martingale`)**:
   For every sequence $A : \mathbb{N} \to \mathbb{R}$ and every $T \ge 1$:
   $$\sum_{n=1}^T \frac{A(n)^2}{\operatorname{pronicSeq}\,n} =
     \left(A(1)^2\!\left(1 - \frac{1}{T + 1}\right) +
       \sum_{n=1}^{T-1} (\operatorname{addDiff}\,A\,n)^2\!\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)\right)
     + 2 \sum_{n=1}^{T-1} (\operatorname{addDiff}\,A\,n)\,A(n)\!\left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$

3. **Exact Predictable Martingale Identification of Route PM Covariance (`pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal`,
   `pmPowerDampedDivisorCovarianceOffDiagonal_eq_two_mul_pmPredictableMartingaleSum`)**:
   For $A_\varepsilon(n) = \operatorname{pmPowerDampedCenteredDivisorPrefix}\,\varepsilon\,n$, the BVI
   forward difference is $(\operatorname{addDiff}\,A_\varepsilon)(n) = \widetilde{\tau}_\varepsilon(n + 1)$,
   the diagonal sum equals `pmPowerDampedDivisorCovarianceDiagonal ε T`, and the off-diagonal sum
   `pmPowerDampedDivisorCovarianceOffDiagonal ε T` equals twice the one-dimensional predictable
   martingale sum `pmPredictableMartingaleSum ε T`:
   $$\operatorname{pmPowerDampedDivisorCovarianceOffDiagonal}\,\varepsilon\,T =
     2 \sum_{n=1}^{T-1} \widetilde{\tau}_\varepsilon(n + 1)\,A_\varepsilon(n)
       \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right).$$

4. **Asymptotic Martingale Drift Law & Route PM Cancellation Criteria for RH
   (`tendsto_pmPredictableMartingaleSum_div_log`,
   `tendsto_pmPredictableMartingaleSum_div_log_of_half_le`,
   `riemannHypothesis_of_pmPredictableMartingale_cancellation`,
   `riemannHypothesis_of_pmHarmonicMartingale_cancellation`)**:
   Whenever `pmPowerDampedFermiSource ε ∈ L²((0, ∞))` (in particular unconditionally for all
   $\varepsilon \ge 1/2$),
   $$\lim_{N \to \infty} \frac{\operatorname{pmPredictableMartingaleSum}\,\varepsilon\,N}{\log N} =
     -\frac{1}{2}\,\operatorname{pmPowerDampedDivisorVariance}\,\varepsilon,$$
   where $\lim_{\varepsilon \to 0^+} \operatorname{pmPowerDampedDivisorVariance}\,\varepsilon / \varepsilon = 1/2$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. General Predictable Forward-Increment & Pronic Martingale Decomposition -/

/-- **Pointwise Square-Increment Martingale Identity
(`sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff`):**
For every sequence `A : ℕ → ℝ` and every `n : ℕ`, the forward difference of squares decomposes into
the squared forward difference `(addDiff A n)²` plus twice the predictable martingale product
`2 * addDiff A n * A n`:
`A (n + 1)² - A n² = (addDiff A n)² + 2 * addDiff A n * A n`. -/
theorem sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff (A : ℕ → ℝ) (n : ℕ) :
    A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ) =
      addDiff A n ^ (2 : ℕ) + 2 * addDiff A n * A n := by
  unfold addDiff
  ring

/-- **Telescoping Sum of Square Increments (`sum_Icc_sq_succ_sub_sq`)**:
For every sequence `A : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^{T-1} (A(n + 1)² - A(n)²) = A(T)² - A(1)²`. -/
theorem sum_Icc_sq_succ_sub_sq (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 (T - 1), (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ))) =
      A T ^ (2 : ℕ) - A 1 ^ (2 : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, T = m + 1 := ⟨T - 1, by omega⟩
  clear hT
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [hsplit, Finset.sum_insert hnot, ih]
    ring

/-- **Telescoping Square-Increment Martingale Identity
(`sq_eq_sq_one_add_sum_addDiff_sq_add_two_mul_martingale`):**
For every sequence `A : ℕ → ℝ` and every `T ≥ 1`:
`A(T)² = A(1)² + ∑_{n=1}^{T-1} (addDiff A n)² + 2 * ∑_{n=1}^{T-1} addDiff A n * A n`. -/
theorem sq_eq_sq_one_add_sum_addDiff_sq_add_two_mul_martingale (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    A T ^ (2 : ℕ) =
      A 1 ^ (2 : ℕ) +
        (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ)) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n := by
  have htel := sum_Icc_sq_succ_sub_sq A hT
  have hrew :
      (∑ n ∈ Finset.Icc 1 (T - 1), (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ))) =
        (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ)) +
          2 * ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n := by
    simp_rw [sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
  linarith

/-- **General Pronic-to-Martingale Energy Decomposition
(`sum_sq_div_pronicSeq_add_terminal_eq_martingale`):**
For every sequence `A : ℕ → ℝ` and every `T ≥ 1`:
`∑_{n=1}^T A(n)² / pronicSeq n + A(T)² / (T + 1)` equals the harmonic square-increment sum
`A(1)² + ∑_{n=1}^{T-1} (addDiff A n)² / (n + 1)` plus twice the harmonic martingale sum
`2 * ∑_{n=1}^{T-1} addDiff A n * A n / (n + 1)`. -/
theorem sum_sq_div_pronicSeq_add_terminal_eq_martingale (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, A n ^ (2 : ℕ) / (pronicSeq n : ℝ)) +
      A T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      (A 1 ^ (2 : ℕ) +
        ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ) / ((n : ℝ) + 1)) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n / ((n : ℝ) + 1) := by
  rw [sum_sq_div_pronicSeq_add_terminal_eq_abel A hT]
  have hrew :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        (A (n + 1) ^ (2 : ℕ) - A n ^ (2 : ℕ)) / ((n : ℝ) + 1)) =
      (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ) / ((n : ℝ) + 1)) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff]
    ring
  linarith

/-- **Terminal-Compensated Pronic Martingale Identity
(`sum_sq_div_pronicSeq_eq_compensated_martingale`):**
For every sequence `A : ℕ → ℝ` and every `T ≥ 1`, eliminating the boundary term
`A(T)² / (T + 1)` via `sq_eq_sq_one_add_sum_addDiff_sq_add_two_mul_martingale` decomposes the
pronic energy `∑_{n=1}^T A(n)² / pronicSeq n` into the compensated diagonal square-increment sum
plus twice the compensated predictable martingale sum:
`∑_{n=1}^T A(n)² / pronicSeq n = (A(1)² * (1 - 1 / (T + 1)) + ∑_{n=1}^{T-1} (addDiff A n)² * (1 / (n + 1) - 1 / (T + 1))) + 2 * ∑_{n=1}^{T-1} addDiff A n * A n * (1 / (n + 1) - 1 / (T + 1))`. -/
theorem sum_sq_div_pronicSeq_eq_compensated_martingale (A : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ n ∈ Finset.Icc 1 T, A n ^ (2 : ℕ) / (pronicSeq n : ℝ)) =
      (A 1 ^ (2 : ℕ) * (1 - 1 / ((T : ℝ) + 1)) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff A n ^ (2 : ℕ) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) +
        2 * ∑ n ∈ Finset.Icc 1 (T - 1),
          addDiff A n * A n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  have hmart := sum_sq_div_pronicSeq_add_terminal_eq_martingale A hT
  have hAT := sq_eq_sq_one_add_sum_addDiff_sq_add_two_mul_martingale A hT
  have hAT_div :
      A T ^ (2 : ℕ) / ((T : ℝ) + 1) =
        A 1 ^ (2 : ℕ) / ((T : ℝ) + 1) +
          (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ) / ((T : ℝ) + 1)) +
          2 * ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n / ((T : ℝ) + 1) := by
    rw [hAT]
    simp only [add_div, mul_div_assoc, Finset.sum_div]
  have hdiag_sub :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff A n ^ (2 : ℕ) * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ) / ((n : ℝ) + 1)) -
        ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n ^ (2 : ℕ) / ((T : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hoff_sub :
      (∑ n ∈ Finset.Icc 1 (T - 1),
        addDiff A n * A n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
      (∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n / ((n : ℝ) + 1)) -
        ∑ n ∈ Finset.Icc 1 (T - 1), addDiff A n * A n / ((T : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hhead :
      A 1 ^ (2 : ℕ) * (1 - 1 / ((T : ℝ) + 1)) =
        A 1 ^ (2 : ℕ) - A 1 ^ (2 : ℕ) / ((T : ℝ) + 1) := by
    ring
  linarith

/-! ## §2. Predictable Increment Identification for `pmPowerDampedCenteredDivisorPrefix` -/

/-- For every `ε : ℝ`, `pmPowerDampedCenteredDivisorPrefix ε 0 = 0`. -/
@[simp]
theorem pmPowerDampedCenteredDivisorPrefix_zero (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 0 = 0 := by
  unfold pmPowerDampedCenteredDivisorPrefix
  simp

/-- For every `ε : ℝ`, `pmPowerDampedCenteredDivisorPrefix ε 1 = pmPowerDampedCenteredDivisorCoeff ε 1`. -/
@[simp]
theorem pmPowerDampedCenteredDivisorPrefix_one (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 1 = pmPowerDampedCenteredDivisorCoeff ε 1 := by
  unfold pmPowerDampedCenteredDivisorPrefix
  simp

/-- **Successor Step of `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_succ`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorPrefix ε (n + 1) = pmPowerDampedCenteredDivisorPrefix ε n + pmPowerDampedCenteredDivisorCoeff ε (n + 1)`. -/
theorem pmPowerDampedCenteredDivisorPrefix_succ (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (n + 1) =
      pmPowerDampedCenteredDivisorPrefix ε n + pmPowerDampedCenteredDivisorCoeff ε (n + 1) := by
  unfold pmPowerDampedCenteredDivisorPrefix
  have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert hnot, add_comm]

/-- **BVI Forward Difference of `pmPowerDampedCenteredDivisorPrefix`
(`addDiff_pmPowerDampedCenteredDivisorPrefix`):**
For every `ε : ℝ` and `n : ℕ`, the BVI forward difference `addDiff (pmPowerDampedCenteredDivisorPrefix ε) n`
is the next centered divisor coefficient `pmPowerDampedCenteredDivisorCoeff ε (n + 1)`. -/
@[simp]
theorem addDiff_pmPowerDampedCenteredDivisorPrefix (ε : ℝ) (n : ℕ) :
    addDiff (pmPowerDampedCenteredDivisorPrefix ε) n =
      pmPowerDampedCenteredDivisorCoeff ε (n + 1) := by
  unfold addDiff
  rw [pmPowerDampedCenteredDivisorPrefix_succ]
  ring

/-- **Pointwise Square-Increment Identity for `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq`):**
For every `ε : ℝ` and `n : ℕ`:
`(pmPowerDampedCenteredDivisorPrefix ε (n + 1))² - (pmPowerDampedCenteredDivisorPrefix ε n)² = (pmPowerDampedCenteredDivisorCoeff ε (n + 1))² + 2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmPowerDampedCenteredDivisorPrefix ε n`. -/
theorem pmPowerDampedCenteredDivisorPrefix_sq_succ_sub_sq (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
      pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ) =
      pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ) +
        2 * pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
          pmPowerDampedCenteredDivisorPrefix ε n := by
  rw [sq_succ_sub_sq_eq_addDiff_sq_add_two_mul_addDiff,
    addDiff_pmPowerDampedCenteredDivisorPrefix]

/-- **Shifted-Index Reindexing Lemma on `Finset.Icc 1 T` (`sum_Icc_one_split_head_and_shift`)**:
For every sequence `f : ℕ → ℝ` and every `T ≥ 1`:
`∑ m ∈ Finset.Icc 1 T, f m = f 1 + ∑ n ∈ Finset.Icc 1 (T - 1), f (n + 1)`. -/
theorem sum_Icc_one_split_head_and_shift (f : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ m ∈ Finset.Icc 1 T, f m) = f 1 + ∑ n ∈ Finset.Icc 1 (T - 1), f (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, T = k + 1 := ⟨T - 1, by omega⟩
  clear hT
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hsplit_lhs : Finset.Icc 1 (k + 1 + 1) = insert (k + 1 + 1) (Finset.Icc 1 (k + 1)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_lhs : k + 1 + 1 ∉ Finset.Icc 1 (k + 1) := by
      simp only [Finset.mem_Icc]; omega
    have hsplit_rhs : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot_rhs : k + 1 ∉ Finset.Icc 1 k := by
      simp only [Finset.mem_Icc]; omega
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [hsplit_lhs, Finset.sum_insert hnot_lhs, ih, hsplit_rhs, Finset.sum_insert hnot_rhs]
    ring

/-- **Exact Predictable Diagonal Identification
(`pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal`):**
For every `ε : ℝ` and `T ≥ 1`, `pmPowerDampedDivisorCovarianceDiagonal ε T` equals the diagonal
part of the terminal-compensated Pronic Martingale decomposition of
`pmPowerDampedCenteredDivisorPrefix ε`. -/
theorem pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPowerDampedDivisorCovarianceDiagonal ε T =
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) * (1 - 1 / ((T : ℝ) + 1)) +
        ∑ n ∈ Finset.Icc 1 (T - 1),
          pmPowerDampedCenteredDivisorCoeff ε (n + 1) ^ (2 : ℕ) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
  unfold pmPowerDampedDivisorCovarianceDiagonal
  rw [sum_Icc_one_split_head_and_shift
    (fun m : ℕ => pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) *
      (1 / (m : ℝ) - 1 / ((T : ℝ) + 1))) hT]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    rfl

/-! ## §3. Predictable Martingale Sum & Exact Off-Diagonal Identification for Route PM -/

/-- **Predictable Martingale Sum for Route PM (`pmPredictableMartingaleSum`):**
The one-dimensional predictable martingale sum weighting each new centered divisor impulse
`pmPowerDampedCenteredDivisorCoeff ε (n + 1)` against the strictly prior prefix sum
`pmPowerDampedCenteredDivisorPrefix ε n` with the compensated harmonic kernel
`1 / (n + 1) - 1 / (T + 1)`. -/
def pmPredictableMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      pmPowerDampedCenteredDivisorPrefix ε n *
      (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))

/-- **Uncompensated Harmonic Martingale Sum for Route PM (`pmHarmonicMartingaleSum`):**
The one-dimensional harmonic martingale sum
`∑_{n=1}^{T-1} pmPowerDampedCenteredDivisorCoeff ε (n + 1) * pmPowerDampedCenteredDivisorPrefix ε n / (n + 1)`. -/
def pmHarmonicMartingaleSum (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (T - 1),
    pmPowerDampedCenteredDivisorCoeff ε (n + 1) *
      pmPowerDampedCenteredDivisorPrefix ε n / ((n : ℝ) + 1)

/-- **Exact Harmonic-Diagonal + Martingale Decomposition of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_harmonic_diagonal_add_martingale`):**
For every `ε : ℝ` and `T ≥ 1`:
`pmPowerDampedDivisorDiscreteEnergy ε T + (pmPowerDampedCenteredDivisorPrefix ε T)² / (T + 1) = (∑_{m=1}^T (pmPowerDampedCenteredDivisorCoeff ε m)² / m) + 2 * pmHarmonicMartingaleSum ε T`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_harmonic_diagonal_add_martingale
    (ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pmPowerDampedDivisorDiscreteEnergy ε T +
      pmPowerDampedCenteredDivisorPrefix ε T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      (∑ m ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) / (m : ℝ)) +
        2 * pmHarmonicMartingaleSum ε T := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
    sum_sq_div_pronicSeq_add_terminal_eq_martingale (pmPowerDampedCenteredDivisorPrefix ε) hT]
  simp only [pmPowerDampedCenteredDivisorPrefix_one, addDiff_pmPowerDampedCenteredDivisorPrefix]
  congr 1
  rw [sum_Icc_one_split_head_and_shift
    (fun m : ℕ => pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) / (m : ℝ)) hT]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    rfl

/-- **Exact Predictable Martingale Decomposition of `pmPowerDampedDivisorDiscreteEnergy`
(`pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T = pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmPredictableMartingaleSum ε T`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum
    (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmPredictableMartingaleSum ε T := by
  by_cases hT : 1 ≤ T
  · rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
      sum_sq_div_pronicSeq_eq_compensated_martingale (pmPowerDampedCenteredDivisorPrefix ε) hT,
      pmPowerDampedDivisorCovarianceDiagonal_eq_abel_diagonal ε hT]
    simp only [pmPowerDampedCenteredDivisorPrefix_one,
      addDiff_pmPowerDampedCenteredDivisorPrefix, pmPredictableMartingaleSum]
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmPowerDampedDivisorDiscreteEnergy pmPowerDampedDivisorCovarianceDiagonal
      pmPredictableMartingaleSum
    simp

/-- **Exact Predictable Martingale Identification of `pmPowerDampedDivisorCovarianceOffDiagonal`
(`pmPowerDampedDivisorCovarianceOffDiagonal_eq_two_mul_pmPredictableMartingaleSum`):**
For every `ε : ℝ` and `T : ℕ`, the two-dimensional off-diagonal covariance sum
`pmPowerDampedDivisorCovarianceOffDiagonal ε T` equals twice the one-dimensional predictable
martingale sum `pmPredictableMartingaleSum ε T`:
`pmPowerDampedDivisorCovarianceOffDiagonal ε T = 2 * pmPredictableMartingaleSum ε T`. -/
theorem pmPowerDampedDivisorCovarianceOffDiagonal_eq_two_mul_pmPredictableMartingaleSum
    (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorCovarianceOffDiagonal ε T = 2 * pmPredictableMartingaleSum ε T := by
  have h1 := pmPowerDampedDivisorDiscreteEnergy_split ε T
  have h2 := pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum ε T
  linarith

/-! ## §4. Asymptotic Martingale Drift Law & Route PM Cancellation Criteria for RH -/

/-- **Logarithmic Asymptotic Drift of `pmPredictableMartingaleSum`
(`tendsto_pmPredictableMartingaleSum_div_log`):**
For every `ε > 0` such that `pmPowerDampedFermiSource ε ∈ L²((0, ∞))`, the predictable martingale
sum `pmPredictableMartingaleSum ε N` divided by `log N` converges as `N → ∞` to
`-pmPowerDampedDivisorVariance ε / 2 < 0`. -/
theorem tendsto_pmPredictableMartingaleSum_div_log {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun N : ℕ => pmPredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (-pmPowerDampedDivisorVariance ε / 2)) := by
  have hoff := tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log hε hf
  have hhalf := hoff.div_const (2 : ℝ)
  refine hhalf.congr fun N => ?_
  rw [pmPowerDampedDivisorCovarianceOffDiagonal_eq_two_mul_pmPredictableMartingaleSum]
  ring

/-- **Unconditional Logarithmic Asymptotic Drift of `pmPredictableMartingaleSum` for `ε ≥ 1/2`
(`tendsto_pmPredictableMartingaleSum_div_log_of_half_le`):**
For every `ε ≥ 1/2`, unconditionally:
`Tendsto (fun N => pmPredictableMartingaleSum ε N / Real.log N) atTop (𝓝 (-pmPowerDampedDivisorVariance ε / 2))`. -/
theorem tendsto_pmPredictableMartingaleSum_div_log_of_half_le {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Tendsto (fun N : ℕ => pmPredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (-pmPowerDampedDivisorVariance ε / 2)) :=
  tendsto_pmPredictableMartingaleSum_div_log (by linarith)
    (memLp_pmPowerDampedFermiSource_of_half_le hε)

/-- **Small-Damping Asymptotic Limit of the Predictable Martingale Drift Rate
(`tendsto_neg_half_pmPowerDampedDivisorVariance_div_parameter`):**
As `ε → 0⁺`, the normalized asymptotic drift rate
`(-pmPowerDampedDivisorVariance ε / 2) / ε` of `pmPredictableMartingaleSum ε N / log N`
converges to `-1 / 4`. -/
theorem tendsto_neg_half_pmPowerDampedDivisorVariance_div_parameter :
    Tendsto (fun ε : ℝ => (-pmPowerDampedDivisorVariance ε / 2) / ε)
      (𝓝[>] 0) (𝓝 (-1 / 4 : ℝ)) := by
  have h := (tendsto_pmPowerDampedDivisorVariance_div_parameter.neg).div_const (2 : ℝ)
  convert! h using 1
  · ext ε; ring
  · norm_num

/-- **Route PM Predictable Martingale Cancellation Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmPredictableMartingale_cancellation`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that for all `T ≥ 1`,
`pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmPredictableMartingaleSum ε T ≤ B`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmPredictableMartingale_cancellation
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T →
        pmPowerDampedDivisorCovarianceDiagonal ε T + 2 * pmPredictableMartingaleSum ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, max B 0, fun T => ?_⟩
  by_cases hT : 1 ≤ T
  · rw [pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum]
    exact (hB T hT).trans (le_max_left B 0)
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmPowerDampedDivisorDiscreteEnergy
    simp [le_max_right B 0]

/-- **Route PM Harmonic Martingale Cancellation Criterion for the Riemann Hypothesis
(`riemannHypothesis_of_pmHarmonicMartingale_cancellation`):**
If for every `δ > 0` there exist `ε ∈ (0, δ)` and a uniform bound `B : ℝ` such that for all `T ≥ 1`,
`(∑_{m=1}^T (pmPowerDampedCenteredDivisorCoeff ε m)² / m) + 2 * pmHarmonicMartingaleSum ε T ≤ B`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pmHarmonicMartingale_cancellation
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, 1 ≤ T →
        (∑ m ∈ Finset.Icc 1 T,
          pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) / (m : ℝ)) +
          2 * pmHarmonicMartingaleSum ε T ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_pronic_abel_budget
  intro δ hδ
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε, hεδ, B, fun T hT => ?_⟩
  have heq :
      pmPowerDampedCenteredDivisorCoeff ε 1 ^ (2 : ℕ) +
        (∑ n ∈ Finset.Icc 1 (T - 1),
          (pmPowerDampedCenteredDivisorPrefix ε (n + 1) ^ (2 : ℕ) -
            pmPowerDampedCenteredDivisorPrefix ε n ^ (2 : ℕ)) / ((n : ℝ) + 1)) =
      (∑ m ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorCoeff ε m ^ (2 : ℕ) / (m : ℝ)) +
        2 * pmHarmonicMartingaleSum ε T := by
    rw [← pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_abel ε hT,
      pmPowerDampedDivisorDiscreteEnergy_add_terminal_eq_harmonic_diagonal_add_martingale ε hT]
  rw [heq]
  exact hB T hT

end
end GaloisForLFunctions.BezoutValuationIncidence
