import GaloisForLFunctions.RHTower.MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP
import GaloisForLFunctions.RHTower.MarkovOddSectorFarkasAndOneSidedPBAP

/-!
# Multi-Stage Secular Counterterm Potential `secantStagePotential` and All-Ratio Sinh-Square Crossover PBAP Closure

This module closes the coupled `HF` target by unifying the finite-stage secular counterterm
telescoping and degree-16 first-cell secant bounds of
`MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP` with the odd-shift window and plastic
`+ 2 * sinhHalfMoment f ^ 2` crossover theory of `MarkovOddShiftWindowAndPlasticCrossoverPBAP` and
`MarkovOddSectorFarkasAndOneSidedPBAP`:

1. **General `M`-Stage Secular Counterterm Potential `secantStagePotential (M n : ℕ)` (`M ≥ 1`)**:
   - Defines `secantStagePotential M n` isolating every cell `k ∈ Finset.Icc n M` with its exact
     denominator `Real.sqrt k` and bounding the tail `k ≥ max n (M + 1)` with denominator
     `Real.sqrt (M + 1)`:
     $$\operatorname{secantStagePotential}(M, n)
       := \left(\sum_{k \in \operatorname{Finset.Icc}\,n\,M}
            \frac{\operatorname{secantQuadTerm}(k) - \operatorname{secantQuadTerm}(k + 1)}{\sqrt{k}}\right)
         + \frac{\operatorname{secantQuadTerm}(\max n (M + 1))}{\sqrt{M + 1}}
         - \frac{2}{3}\,\operatorname{secantCubeTerm}(n).$$
   - **Exact Zero-Loss Telescoping on `2 ≤ n ≤ M`** (`secantStagePotential_sub_succ_eq_of_le`):
     `secantStagePotential M n - secantStagePotential M (n + 1) = secantCombinedSecularWeight n * (2 / Real.sqrt n)`.
   - **Tail Step Inequality and Nonnegativity** (`secantCombinedSecularWeight_mul_two_div_sqrt_le_secantStagePotential_sub_succ`,
     `secantStagePotential_nonneg`):
     for all `M : ℕ` and `2 ≤ n`,
     `secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ secantStagePotential M n - secantStagePotential M (n + 1)`
     and `0 ≤ secantStagePotential M n`.
   - **Stage Monotonicity in `M`** (`secantStagePotential_sub_succ_stage_eq`, `secantStagePotential_succ_stage_le`):
     for `n ≤ M + 1`,
     `secantStagePotential M n - secantStagePotential (M + 1) n = secantQuadTerm (M + 2) * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (M + 2)) ≥ 0`,
     so `secantStagePotential (M + 1) 2 ≤ secantStagePotential M 2` and the origin surplus
     `(16 * Real.sqrt 2 - 20) / 3 - secantStagePotential M 2` is monotonically nondecreasing in `M`.
   - **Adaptive Support-Matched Zero-Loss Sum Identity (`1 ≤ N ≤ M`)**
     (`sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_eq_of_le_stage`):
     when `M ≥ N`, the secular counterterm sum on `Finset.Icc 2 N` telescopes **with zero
     square-root relaxation loss**:
     `∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n) = secantStagePotential M 2 - secantStagePotential M (N + 1)`.

2. **All-Ratio (`S / L` Unrestricted) Sinh-Square Crossover Conservation and `markovEnergy ≥ 0` Laws**:
   - Retaining `+ 2 * sinhHalfMoment f ^ 2` in the zero-sum conservation law on `coshHalfMoment f = 0`
     (`all_ratio_conservation_bound_of_cosh_zero`,
     `all_ratio_conservation_bound_of_cosh_zero_of_logValue_nonneg`,
     `all_ratio_conservation_bound_of_cosh_zero_of_logVector_eq_zero`) yields an **all-ratio**
     inequality valid for arbitrary `S = spectralSecondMoment F` and `L = ∫ ‖F‖²`:
     `(247 / 300) * L + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 + primeBlindCounterterm unitStepCountertermWeight F ≤ (7 / 480) * S + (71 / 3600) * √(S(S + 2L))`
     (and with `(1261 / 1440) * L` on the nonnegative log-value or prime-blind cone).
   - Retaining `+ 2 * θ * sinhHalfMoment f ^ 2` in the slope-gauge lower bound for `markovEnergy`
     (`all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess`,
     `all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess_of_logValue_nonneg`)
     proves that for **any** ratio `S / L`, whenever `2 * sinhHalfMoment f ^ 2` covers the
     high-frequency secant excess `(7 / 480) * S + (71 / 3600) * √(S(S + 2L)) - (41 / 50) * L`
     (or `- (7 / 8) * L` on the nonnegative log-value cone), we have unconditionally
     `(1 / 100) * L ≤ markovEnergy F` and `0 ≤ markovEnergy F`.

3. **All-Ratio Odd-Shift Window (`oddShift g h`) Exponential Sinh-Square Closure**:
   - Specializing to `oddShift g h` for any even `g ∈ C²_c(ℝ)` (`∀ x, g (-x) = g x`), where
     `coshHalfMoment (oddShift g h) = 0` and
     `2 * sinhHalfMoment (oddShift g h) ^ 2 = 2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2`,
     establishes the all-ratio conservation and `markovEnergy ≥ 0` laws for shifted odd windows.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The General `M`-Stage Secular Counterterm Potential `secantStagePotential M n` -/

/-- The **`M`-Stage Secular Counterterm Potential** `secantStagePotential M n`:
isolates each cell `k ∈ Finset.Icc n M` with its exact denominator `Real.sqrt k` and bounds the tail
at `max n (M + 1)` with denominator `Real.sqrt (M + 1)`.
For `M = 3`, this is `secantThreeStagePotential`; for `M = 4`, this is `secantFourStagePotential`;
for `M = N`, it telescopes `Finset.Icc 2 N` with zero square-root relaxation loss. -/
def secantStagePotential (M n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc n M, (secantQuadTerm k - secantQuadTerm (k + 1)) / Real.sqrt k) +
    secantQuadTerm (max n (M + 1)) / Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 * secantCubeTerm n / 3

/-- Exact difference decomposition of `secantCombinedSecularWeight n * (2 / Real.sqrt n)` for `2 ≤ n`. -/
theorem secantCombinedSecularWeight_mul_two_div_sqrt_eq {n : ℕ} (hn : 2 ≤ n) :
    secantCombinedSecularWeight n * (2 / Real.sqrt n) =
      (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n -
        2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
  have hn_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hne : Real.sqrt n ≠ 0 := hn_pos.ne'
  have hterm2 :
      ((secantCubeTerm n - secantCubeTerm (n + 1)) * Real.sqrt n / 3) * (2 / Real.sqrt n) =
        2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
    rw [div_eq_mul_inv (_ * Real.sqrt n) 3, div_eq_mul_inv 2 (Real.sqrt n)]
    calc (secantCubeTerm n - secantCubeTerm (n + 1)) * Real.sqrt n * 3⁻¹ *
          (2 * (Real.sqrt n)⁻¹)
      _ = (2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3) *
            (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
      _ = 2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
          rw [mul_inv_cancel₀ hne, mul_one]
  unfold secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
  simp only [if_pos hn]
  have hq :
      (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
        (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2 =
      secantQuadTerm n - secantQuadTerm (n + 1) := by
    unfold secantQuadTerm
    push_cast
    rw [add_sub_cancel_right]
  have hc :
      (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
        (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3 =
      secantCubeTerm n - secantCubeTerm (n + 1) := by
    unfold secantCubeTerm
    push_cast
    rw [add_sub_cancel_right]
  rw [hq, hc, sub_mul, hterm2]
  congr 1
  ring

/-- **Exact Zero-Loss Telescoping Step on `2 ≤ n ≤ M`**:
for every `2 ≤ n ≤ M`, `secantStagePotential M n - secantStagePotential M (n + 1)` equals
`secantCombinedSecularWeight n * (2 / Real.sqrt n)` with exact equality. -/
theorem secantStagePotential_sub_succ_eq_of_le {M n : ℕ} (hn : 2 ≤ n) (hnM : n ≤ M) :
    secantStagePotential M n - secantStagePotential M (n + 1) =
      secantCombinedSecularWeight n * (2 / Real.sqrt n) := by
  rw [secantCombinedSecularWeight_mul_two_div_sqrt_eq hn]
  unfold secantStagePotential
  rw [sum_Icc_eq_add_sum_Icc_succ _ hnM,
    Nat.max_eq_right (by omega : n ≤ M + 1),
    Nat.max_eq_right (by omega : n + 1 ≤ M + 1)]
  ring

/-- When `M + 1 ≤ n`, the finite sum in `secantStagePotential M n` is empty and
`secantStagePotential M n = secantQuadTerm n / Real.sqrt (M + 1) - 2 * secantCubeTerm n / 3`. -/
theorem secantStagePotential_eq_of_succ_le {M n : ℕ} (hn : M + 1 ≤ n) :
    secantStagePotential M n =
      secantQuadTerm n / Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 * secantCubeTerm n / 3 := by
  unfold secantStagePotential
  have hemp : Finset.Icc n M = ∅ := Finset.Icc_eq_empty (by omega)
  rw [hemp, Finset.sum_empty, zero_add, Nat.max_eq_left hn]

/-- **General `M`-Stage Telescoping Step Bound**:
for every `M : ℕ` and `2 ≤ n`,
`secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ secantStagePotential M n - secantStagePotential M (n + 1)`. -/
theorem secantCombinedSecularWeight_mul_two_div_sqrt_le_secantStagePotential_sub_succ
    (M : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤
      secantStagePotential M n - secantStagePotential M (n + 1) := by
  by_cases hnM : n ≤ M
  · rw [secantStagePotential_sub_succ_eq_of_le hn hnM]
  · have hMn : M + 1 ≤ n := by omega
    have hMn1 : M + 1 ≤ n + 1 := by omega
    rw [secantCombinedSecularWeight_mul_two_div_sqrt_eq hn,
      secantStagePotential_eq_of_succ_le hMn,
      secantStagePotential_eq_of_succ_le hMn1]
    have hsqrt_pos : (0 : ℝ) < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hsqrt_le : Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt n :=
      Real.sqrt_le_sqrt (by exact_mod_cast hMn)
    have hinv_le : (Real.sqrt n)⁻¹ ≤ (Real.sqrt ((M + 1 : ℕ) : ℝ))⁻¹ :=
      inv_anti₀ hsqrt_pos hsqrt_le
    have hΔ2_nonneg := secantQuadTerm_sub_succ_nonneg (by omega : 1 ≤ n)
    have hdiv_le :
        (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n ≤
          (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt ((M + 1 : ℕ) : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv_le hΔ2_nonneg
    linarith [sub_div (secantQuadTerm n) (secantQuadTerm (n + 1)) (Real.sqrt ((M + 1 : ℕ) : ℝ))]

/-- Monotonicity of `secantStagePotential M` in `n` for `2 ≤ n`:
`secantStagePotential M (n + d) ≤ secantStagePotential M n`. -/
theorem secantStagePotential_add_le (M : ℕ) {n : ℕ} (hn : 2 ≤ n) (d : ℕ) :
    secantStagePotential M (n + d) ≤ secantStagePotential M n := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep :=
      secantCombinedSecularWeight_mul_two_div_sqrt_le_secantStagePotential_sub_succ M
        (by omega : 2 ≤ n + d)
    have hnn : 0 ≤ secantCombinedSecularWeight (n + d) * (2 / Real.sqrt ((n + d : ℕ) : ℝ)) :=
      mul_nonneg (secantCombinedSecularWeight_nonneg (n + d)) (by positivity)
    change secantStagePotential M (n + d + 1) ≤ secantStagePotential M n
    linarith

/-- For every `M : ℕ` and `n ≥ max 2 (M + 1)`, `0 ≤ secantStagePotential M n`. -/
theorem secantStagePotential_nonneg_of_succ_le (M : ℕ) {n : ℕ} (hn2 : 2 ≤ n) (hnM : M + 1 ≤ n) :
    0 ≤ secantStagePotential M n := by
  rw [secantStagePotential_eq_of_succ_le hnM]
  unfold secantQuadTerm secantCubeTerm
  set d := Real.sqrt n - Real.sqrt ((n : ℝ) - 1)
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hd_nonneg : 0 ≤ d := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsqrtM_pos : (0 : ℝ) < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hd_le : d * Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ 1 := by
    have hMn_real : ((M + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
    have hconj : d * (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
      have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
      have hsq1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
      dsimp [d]
      linear_combination hsq0 - hsq1
    have hsum_ge : Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt n + Real.sqrt ((n : ℝ) - 1) := by
      have hsqrt_n : Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt n := Real.sqrt_le_sqrt hMn_real
      have hsqrt_pred : 0 ≤ Real.sqrt ((n : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_ge hd_nonneg
    linarith
  have hfactor :
      d ^ 2 / Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 * d ^ 3 / 3 =
        (d ^ 2 / (3 * Real.sqrt ((M + 1 : ℕ) : ℝ))) *
          (3 - 2 * (d * Real.sqrt ((M + 1 : ℕ) : ℝ))) := by
    have hne : Real.sqrt ((M + 1 : ℕ) : ℝ) ≠ 0 := hsqrtM_pos.ne'
    field_simp [hne]
  rw [hfactor]
  exact mul_nonneg (by positivity) (by linarith)

/-- **Universal Nonnegativity of `secantStagePotential M n`**:
for every `M : ℕ` and `2 ≤ n`, `0 ≤ secantStagePotential M n`. -/
theorem secantStagePotential_nonneg (M : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ secantStagePotential M n := by
  by_cases hnM : M + 1 ≤ n
  · exact secantStagePotential_nonneg_of_succ_le M hn hnM
  · have hle : n ≤ M + 1 := by omega
    have htail : 0 ≤ secantStagePotential M (M + 1) :=
      secantStagePotential_nonneg_of_succ_le M (by omega) (le_refl _)
    have hmono := secantStagePotential_add_le M hn (M + 1 - n)
    rw [Nat.add_sub_of_le hle] at hmono
    exact htail.trans hmono

/-- **Stage Increment Identity (`M → M + 1`)**:
for any `M, n : ℕ` with `n ≤ M + 1`, increasing the stage horizon from `M` to `M + 1` decreases
`secantStagePotential` by the exact positive quantity
`secantQuadTerm (M + 2) * (1 / Real.sqrt (M + 1) - 1 / Real.sqrt (M + 2))`. -/
theorem secantStagePotential_sub_succ_stage_eq {M n : ℕ} (hn : n ≤ M + 1) :
    secantStagePotential M n - secantStagePotential (M + 1) n =
      secantQuadTerm (M + 2) *
        (1 / Real.sqrt ((M + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((M + 2 : ℕ) : ℝ)) := by
  unfold secantStagePotential
  rw [Finset.sum_Icc_succ_top hn,
    Nat.max_eq_right hn,
    Nat.max_eq_right (by omega : n ≤ M + 1 + 1)]
  change
    (∑ k ∈ Finset.Icc n M, (secantQuadTerm k - secantQuadTerm (k + 1)) / Real.sqrt k) +
      secantQuadTerm (M + 1) / Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 * secantCubeTerm n / 3 -
    (((∑ k ∈ Finset.Icc n M, (secantQuadTerm k - secantQuadTerm (k + 1)) / Real.sqrt k) +
      (secantQuadTerm (M + 1) - secantQuadTerm (M + 2)) / Real.sqrt ((M + 1 : ℕ) : ℝ)) +
      secantQuadTerm (M + 2) / Real.sqrt ((M + 2 : ℕ) : ℝ) - 2 * secantCubeTerm n / 3) =
    secantQuadTerm (M + 2) *
      (1 / Real.sqrt ((M + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((M + 2 : ℕ) : ℝ))
  ring

/-- **Stage Monotonicity (`secantStagePotential (M + 1) n ≤ secantStagePotential M n`)**:
for any `M, n : ℕ` with `n ≤ M + 1`, `secantStagePotential (M + 1) n ≤ secantStagePotential M n`. -/
theorem secantStagePotential_succ_stage_le {M n : ℕ} (hn : n ≤ M + 1) :
    secantStagePotential (M + 1) n ≤ secantStagePotential M n := by
  have hdiff := secantStagePotential_sub_succ_stage_eq hn
  have hq_nn : 0 ≤ secantQuadTerm (M + 2) := by
    unfold secantQuadTerm
    exact sq_nonneg _
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_le : Real.sqrt ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt ((M + 2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ (M + 1)))
  have hinv_le : 1 / Real.sqrt ((M + 2 : ℕ) : ℝ) ≤ 1 / Real.sqrt ((M + 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le
  have hprod_nn :
      0 ≤ secantQuadTerm (M + 2) *
        (1 / Real.sqrt ((M + 1 : ℕ) : ℝ) - 1 / Real.sqrt ((M + 2 : ℕ) : ℝ)) :=
    mul_nonneg hq_nn (sub_nonneg.mpr hinv_le)
  linarith

/-- Multi-step stage monotonicity: for `n ≤ M + 1`, `secantStagePotential (M + d) n ≤ secantStagePotential M n`. -/
theorem secantStagePotential_add_stage_le {M n : ℕ} (hn : n ≤ M + 1) (d : ℕ) :
    secantStagePotential (M + d) n ≤ secantStagePotential M n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ]
    exact (secantStagePotential_succ_stage_le (by omega : n ≤ M + d + 1)).trans ih

/-- **Exact Agreement of `secantStagePotential 4 2` with `secantFourStagePotential 2`**: -/
theorem secantStagePotential_four_two_eq :
    secantStagePotential 4 2 = secantFourStagePotential 2 := by
  unfold secantStagePotential secantFourStagePotential
  rw [sum_Icc_eq_add_sum_Icc_succ _ (by omega : 2 ≤ 4),
    sum_Icc_eq_add_sum_Icc_succ _ (by omega : 3 ≤ 4),
    Finset.Icc_self, Finset.sum_singleton,
    Nat.max_eq_right (by omega : 2 ≤ 4 + 1)]
  simp only [↓reduceIte]
  have hsqrt4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    norm_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt4]
  norm_num
  ring

/-- For every stage horizon `4 ≤ M`, `secantStagePotential M 2 ≤ secantFourStagePotential 2`, and
consequently the `M`-stage origin surplus satisfies
`247 / 300 ≤ (16 * Real.sqrt 2 - 20) / 3 - secantStagePotential M 2`. -/
theorem two_forty_seven_three_hundredths_le_stage_surplus {M : ℕ} (hM : 4 ≤ M) :
    secantStagePotential M 2 ≤ secantFourStagePotential 2 ∧
      (247 / 300 : ℝ) ≤ (16 * Real.sqrt 2 - 20) / 3 - secantStagePotential M 2 := by
  have hle : secantStagePotential M 2 ≤ secantFourStagePotential 2 := by
    rw [← secantStagePotential_four_two_eq]
    have h := secantStagePotential_add_stage_le (by omega : 2 ≤ 4 + 1) (M - 4)
    rwa [Nat.add_sub_of_le hM] at h
  have hsurplus4 := two_forty_seven_three_hundredths_le_fourStage_surplus
  have hpot4 := secantFourStagePotential_two_eq
  refine ⟨hle, ?_⟩
  linarith

/-- **Exact Adaptive Support-Matched Telescoping (`1 ≤ N ≤ M`)**:
when the stage horizon `M` is at least the support cutoff `N`, the secular counterterm sum on
`Finset.Icc 2 N` telescopes with **zero square-root relaxation loss**:
`∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n) = secantStagePotential M 2 - secantStagePotential M (N + 1)`. -/
theorem sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_eq_of_le_stage
    {M N : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) =
      secantStagePotential M 2 - secantStagePotential M (N + 1) := by
  rw [← sum_Icc_two_sub_succ_nat (secantStagePotential M) hN]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact (secantStagePotential_sub_succ_eq_of_le hn.1 (hn.2.trans hNM)).symm

/-- **General `M`-Stage Telescoping Upper Bound on `∑_{n=2}^N secantCombinedSecularWeight n * (2 / √n)`**:
for every `M : ℕ` and `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ secantStagePotential M 2 - secantStagePotential M (N + 1) ≤ secantStagePotential M 2`. -/
theorem sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_stage
    (M : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
        secantStagePotential M 2 - secantStagePotential M (N + 1) ∧
      (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
        secantStagePotential M 2 := by
  have hle_sum :
      (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
        ∑ n ∈ Finset.Icc 2 N,
          (secantStagePotential M n - secantStagePotential M (n + 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact secantCombinedSecularWeight_mul_two_div_sqrt_le_secantStagePotential_sub_succ M hn.1
  rw [sum_Icc_two_sub_succ_nat (secantStagePotential M) hN] at hle_sum
  have hN1 : 0 ≤ secantStagePotential M (N + 1) :=
    secantStagePotential_nonneg M (by omega)
  exact ⟨hle_sum, by linarith⟩

/-- **General `M`-Stage Uniform Bound on `primeBlindCounterterm secantCombinedSecularWeight f`**:
for every `f : WeilTestFn`, stage horizon `M : ℕ`, and support cutoff `1 ≤ N`,
`|primeBlindCounterterm secantCombinedSecularWeight f| ≤ secantStagePotential M 2 * ∫ u, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_secantCombinedSecularWeight_le_stage
    (M : ℕ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm secantCombinedSecularWeight f| ≤
      secantStagePotential M 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      |secantCombinedSecularWeight n * logValue f.1 n| ≤
        (secantCombinedSecularWeight n * (2 / Real.sqrt n)) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [abs_mul, abs_of_nonneg (secantCombinedSecularWeight_nonneg n), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f (by omega : 1 ≤ n))
      (secantCombinedSecularWeight_nonneg n)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_stage M hN1).2 hnorm_nonneg

/-- **General `M`-Stage Origin Surplus Lower Bound for `rightCellQuadratureDefect`**:
for every `f : WeilTestFn`, stage horizon `M : ℕ`, and support cutoff `1 ≤ N` with
`EF.weilTest f.1 f.1 (±log N) = 0`,
`((16 * Real.sqrt 2 - 20) / 3 - secantStagePotential M 2) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem stage_surplus_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (M : ℕ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    ((16 * Real.sqrt 2 - 20) / 3 - secantStagePotential M 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have habs :=
    (abs_le.mp (abs_primeBlindCounterterm_secantCombinedSecularWeight_le_stage M f hN1 hN)).1
  linarith

/-! ## Section 2: All-Ratio (`S / L` Unrestricted) Sinh-Square Crossover Conservation and `markovEnergy ≥ 0` Closure -/

/-- **All-Ratio Conservation Inequality on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
for every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` (including all odd tests) and support cutoff
`1 ≤ N` with `EF.weilTest F F (±log N) = 0`, with **no upper bound on `spectralSecondMoment F`**:
`(247 / 300) * ∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 + primeBlindCounterterm unitStepCountertermWeight F ≤ (7 / 480) * S + (71 / 3600) * √(S(S + 2L))`. -/
theorem all_ratio_conservation_bound_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (247 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 +
        primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) ≤
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  linarith

/-- **All-Ratio Conservation Inequality on the Nonnegative Log-Value Cone (`1261 / 1440 = 0.875694...`)**:
for every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, `0 ≤ logValue F n` on `Finset.Icc 2 N`, and
**arbitrary ratio `S / L`**:
`(1261 / 1440) * ∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 ≤ (7 / 480) * S + (71 / 3600) * √(S(S + 2L))`. -/
theorem all_ratio_conservation_bound_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n) :
    (1261 / 1440) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 ≤
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hunit_nonneg :
      0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight (realWeilTestFn f hf hfc)
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn)
  linarith

/-- **All-Ratio Conservation Inequality on the Prime-Blind Cone (`logVector F = 0`)**:
for every prime-blind `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and **arbitrary ratio `S / L`**:
`(1261 / 1440) * ∫ ‖F‖² + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 ≤ (7 / 480) * S + (71 / 3600) * √(S(S + 2L))`. -/
theorem all_ratio_conservation_bound_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0) :
    (1261 / 1440) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 ≤
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  linarith

/-- **All-Ratio Prime-Blind Vanishing Law (`∫ ‖F‖² = 0`) under Sinh-Square Dominance**:
for any prime-blind `f ∈ C²_c(ℝ)` (`logVector F = 0`) with `coshHalfMoment f = 0` and **arbitrary
ratio `S / L`**, if `2 * sinhHalfMoment f ^ 2 + bochnerResolventEnergy k_F` covers the secant
excess `(7 / 480) * S + (71 / 3600) * √(S(S + 2L)) - (7 / 8) * L` (`7 / 8 = 1260 / 1440`), then
`∫ u, ‖F u‖ ^ 2 = 0`. -/
theorem all_ratio_l2_eq_zero_of_cosh_zero_of_logVector_eq_zero_of_sinh_sq_dominates
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hdom :
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          (71 / 3600) *
            Real.sqrt
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
                (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                  2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (7 / 8) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
          2 * sinhHalfMoment f ^ 2) :
    (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = 0 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hcons :=
    all_ratio_conservation_bound_of_cosh_zero_of_logVector_eq_zero
      hf hfc hcosh hint2 hN1 hN0 hN hblind
  linarith

/-- **All-Ratio `markovEnergy ≥ (1 / 100) * ∫ ‖F‖² ≥ 0` Closure on the Primitive Hyperplane**:
for every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, any Cesàro order `m : ℕ` with
`0 ≤ iteratedForwardDiff m (logValue F) n` on `Finset.Icc 2 N`, and **arbitrary ratio `S / L`**,
whenever the plastic bonus `2 * sinhHalfMoment f ^ 2` covers the high-frequency secant excess
`(7 / 480) * S + (71 / 3600) * √(S(S + 2L)) - (41 / 50) * L` (`41 / 50 = 246 / 300`), we have
`(1 / 100) * ∫ ‖F‖² ≤ markovEnergy F` and `0 ≤ markovEnergy F`. -/
theorem all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hdom :
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          (71 / 3600) *
            Real.sqrt
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
                (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                  2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (41 / 50) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          2 * sinhHalfMoment f ^ 2) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        markovEnergy (realWeilTestFn f hf hfc).1 ∧
      0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 600
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (600 : ℝ) ≤ θ := le_max_right _ _
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hquad_sinh :
      (1 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
          2 * sinhHalfMoment f ^ 2 := by
    linarith
  have hθ_mul :
      (600 : ℝ) * ((1 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        θ *
          (rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
            2 * sinhHalfMoment f ^ 2) :=
    mul_le_mul hθ_large hquad_sinh (by positivity) (by linarith)
  have hres_nn :
      0 ≤ (θ - 1) * bochnerResolventEnergy
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc))
  refine ⟨by linarith, by linarith⟩

/-- **All-Ratio `markovEnergy ≥ (1 / 100) * ∫ ‖F‖² ≥ 0` Closure on the Nonnegative Log-Value Cone**:
for every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, `0 ≤ logValue F n` on `Finset.Icc 2 N`, and
**arbitrary ratio `S / L`**, whenever `2 * sinhHalfMoment f ^ 2` covers the high-frequency secant
excess `(7 / 480) * S + (71 / 3600) * √(S(S + 2L)) - (7 / 8) * L` (`7 / 8 = 1260 / 1440`), we have
`(1 / 100) * ∫ ‖F‖² ≤ markovEnergy F` and `0 ≤ markovEnergy F`. -/
theorem all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hdom :
      (7 / 480) * spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          (71 / 3600) *
            Real.sqrt
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
                (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                  2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (7 / 8) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          2 * sinhHalfMoment f ^ 2) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        markovEnergy (realWeilTestFn f hf hfc).1 ∧
      0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2880
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2880 : ℝ) ≤ θ := le_max_right _ _
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh hN1 hθlog hN (fun n hn => by simpa [iteratedForwardDiff] using hpos n hn)
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hquad_sinh :
      (1 / 1440) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
          2 * sinhHalfMoment f ^ 2 := by
    linarith
  have hθ_mul :
      (2880 : ℝ) * ((1 / 1440) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        θ *
          (rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
            2 * sinhHalfMoment f ^ 2) :=
    mul_le_mul hθ_large hquad_sinh (by positivity) (by linarith)
  have hres_nn :
      0 ≤ (θ - 1) * bochnerResolventEnergy
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc))
  refine ⟨by linarith, by linarith⟩

/-! ## Section 3: Odd-Shift Window (`oddShift g h`) All-Ratio Exponential Sinh-Square Closure -/

/-- **All-Ratio Odd-Shift Window Conservation Bound**:
for any even `g ∈ C²_c(ℝ)` (`∀ x, g (-x) = g x`) and shift `h ∈ ℝ`, `oddShift g h` has
`coshHalfMoment (oddShift g h) = 0` and exponential plastic bonus
`2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2`, giving for **arbitrary ratio `S / L`**:
`(247 / 300) * ∫ ‖F_h‖² + bochnerResolventEnergy k_{F_h} + 2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 + primeBlindCounterterm unitStepCountertermWeight F_h ≤ (7 / 480) * S_h + (71 / 3600) * √(S_h(S_h + 2L_h))`. -/
theorem oddShift_all_ratio_conservation_bound_of_even
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ x, g (-x) = g x) (h : ℝ)
    (hint2 : Integrable fun r : ℝ =>
      ‖paperFT (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 :
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (Real.log N) = 0 ∧
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (Real.log x) = 0 ∧
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (-Real.log x) = 0) :
    let F_h := realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
      (hasCompactSupport_oddShift hgc h)
    (247 / 300) * (∫ u : ℝ, ‖F_h.1 u‖ ^ 2) +
        bochnerResolventEnergy (EF.weilTest F_h.1 F_h.1) +
        2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 +
        primeBlindCounterterm unitStepCountertermWeight F_h ≤
      (7 / 480) * spectralSecondMoment F_h.1 +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment F_h.1 *
              (spectralSecondMoment F_h.1 + 2 * ∫ u : ℝ, ‖F_h.1 u‖ ^ 2)) := by
  dsimp only
  have hcosh : coshHalfMoment (oddShift g h) = 0 :=
    coshHalfMoment_eq_zero_of_odd (oddShift_neg heven h)
  have hsinh :
      2 * sinhHalfMoment (oddShift g h) ^ 2 =
        2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 := by
    rw [sinhHalfMoment_oddShift hg.continuous hgc h]
    ring
  have hbase :=
    all_ratio_conservation_bound_of_cosh_zero (contDiff_oddShift hg h)
      (hasCompactSupport_oddShift hgc h) hcosh hint2 hN1 hN0 hN
  linarith

/-- **All-Ratio Odd-Shift Window `markovEnergy ≥ 0` Closure**:
for any even `g ∈ C²_c(ℝ)` (`∀ x, g (-x) = g x`), shift `h ∈ ℝ`, and Cesàro order `m : ℕ` with
`0 ≤ iteratedForwardDiff m (logValue F_h) n` on `Finset.Icc 2 N`, whenever the exponential plastic
bonus `2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2` covers the high-frequency secant excess of
`F_h = oddShift g h`, we have `(1 / 100) * ∫ ‖F_h‖² ≤ markovEnergy F_h` and `0 ≤ markovEnergy F_h`. -/
theorem oddShift_all_ratio_markovEnergy_nonneg_of_even
    (m : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ x, g (-x) = g x) (h : ℝ)
    (hint2 : Integrable fun r : ℝ =>
      ‖paperFT (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 :
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (Real.log N) = 0 ∧
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (Real.log x) = 0 ∧
      EF.weilTest
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1
        (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m
        (logValue (realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
          (hasCompactSupport_oddShift hgc h)).1) n)
    (hdom :
      let F_h := realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
        (hasCompactSupport_oddShift hgc h)
      (7 / 480) * spectralSecondMoment F_h.1 +
          (71 / 3600) *
            Real.sqrt
              (spectralSecondMoment F_h.1 *
                (spectralSecondMoment F_h.1 + 2 * ∫ u : ℝ, ‖F_h.1 u‖ ^ 2)) ≤
        (41 / 50) * (∫ u : ℝ, ‖F_h.1 u‖ ^ 2) +
          2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2) :
    let F_h := realWeilTestFn (oddShift g h) (contDiff_oddShift hg h)
      (hasCompactSupport_oddShift hgc h)
    (1 / 100) * (∫ u : ℝ, ‖F_h.1 u‖ ^ 2) ≤ markovEnergy F_h.1 ∧
      0 ≤ markovEnergy F_h.1 := by
  dsimp only at hdom ⊢
  have hcosh : coshHalfMoment (oddShift g h) = 0 :=
    coshHalfMoment_eq_zero_of_odd (oddShift_neg heven h)
  have hsinh :
      2 * sinhHalfMoment (oddShift g h) ^ 2 =
        2 * Real.sinh (h / 4) ^ 2 * coshHalfMoment g ^ 2 := by
    rw [sinhHalfMoment_oddShift hg.continuous hgc h]
    ring
  exact all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess
    m (contDiff_oddShift hg h) (hasCompactSupport_oddShift hgc h) hcosh hint2 hN1 hN0 hN hdiff
    (by linarith)

end RHTower

end
