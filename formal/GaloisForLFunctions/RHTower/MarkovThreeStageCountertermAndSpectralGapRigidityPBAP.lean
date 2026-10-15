import GaloisForLFunctions.RHTower.MarkovExactFirstCellLogIntegralAndResolventCoercivityPBAP

/-!
# Three-Stage Secular Counterterm Telescoping, the `2953 / 3600` Origin Surplus, Coercivity up to `67 / 4 = 16.75`, and Universal Spectral Gap Rigidity on the Primitive Hyperplane for Route HF / PBAP

In Module 49 (`MarkovSecantCombinedCountertermAndFourFifthsSurplusPBAP`), we bounded the secular
counterterm `|primeBlindCounterterm secantCombinedSecularWeight f|` by replacing `1 / √n` with
`1 / √2` on all `n ≥ 2`, yielding `(16 - 11√2) / 6 < 3 / 40 = 0.075` and an origin $L^2$ surplus
of `(43√2 - 56) / 6 > 433 / 540 ≈ 0.80185`.

In this module, we isolate `n = 2` and `n = 3` in the secular counterterm and bound `1 / √n ≤ 1 / 2`
for `n ≥ 4` (which is also exact at `n = 4` since `√4 = 2`!), and we combine our Resolvent-Enhanced
Quadrature Coercivity laws with the exact Euler–Maclaurin–Resolvent–Pole conservation law to uncover
a family of **Universal Spectral Poincaré / Uncertainty Gap Rigidity Theorems** on the Primitive
Hyperplane:

1. **Section 1 (The Three-Stage Counterterm Potential `secantThreeStagePotential`, the
   `(61 - 38√2 - 4√3) / 6 ≤ 1 / 18` Counterterm Bound, and the `2953 / 3600 > 0.82027` General
   Origin $L^2$ Surplus):**
   - We define `secantThreeStagePotential n` so that `secantCombinedSecularWeight n * (2 / √n)`
     equals `secantThreeStagePotential n - secantThreeStagePotential (n + 1)` **exactly** at
     `n = 2, 3, 4` and is bounded by `secantThreeStagePotential n - secantThreeStagePotential (n + 1)`
     for all `n ≥ 2` (`secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage`), with
     `0 ≤ secantThreeStagePotential n` for all `n ≥ 2` (`secantThreeStagePotential_nonneg`).
   - Evaluating `secantThreeStagePotential 2 = (61 - 38 * √2 - 4 * √3) / 6 ≤ 1 / 18`
     (`secantThreeStagePotential_two_eq`, `secantThreeStagePotential_two_le_one_eighteenth`) cuts
     the counterterm bound by `25%` (`abs_primeBlindCounterterm_secantCombinedSecularWeight_le_threeStage`)
     and boosts the unconditional origin $L^2$ surplus from `433 / 540 ≈ 0.80185` to
     `(70 * √2 + 4 * √3 - 101) / 6 ≥ 2953 / 3600 > 0.82027`
     (`two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect`).

2. **Section 2 (Upgraded Coercivity Laws: Pure `rightCellQuadratureDefect ≥ 0` up to `131 / 9 > 14.555`,
   Resolvent-Enhanced Coercivity up to `67 / 4 = 16.75`, and Unconditional `markovEnergy ≥ 0` up to
   `67 / 4 = 16.75`):**
   - Pure `0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` holds up to
     `spectralSecondMoment f.1 ≤ (131 / 9) * ∫ ‖f.1‖²` (`131 / 9 > 14.5555`,
     `rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_thirty_one_ninths`).
   - Resolvent-enhanced coercivity
     `(1 / 1500) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy k_f + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     and unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane (`coshHalfMoment f = 0`)
     hold for general Cesàro order `m : ℕ` up to
     `spectralSecondMoment f.1 ≤ (67 / 4) * ∫ ‖f.1‖² = 16.75 * ∫ ‖f.1‖²`
     (`one_fifteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_seven_fourths`,
     `markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero`).

3. **Section 3 (Universal Unit-Step Negativity, Vanishing Rigidity, and the `67 / 4 = 16.75` &
   `53 / 3 > 17.666` Spectral Poincaré / Uncertainty Gap Laws on the Primitive Hyperplane):**
   - Combining `unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm`
     with Section 2 and Module 61 on the Primitive Hyperplane (`coshHalfMoment f = 0`) proves:
     - For **any** signed test `f ∈ C²_c(ℝ)` on the Primitive Hyperplane (with **no** sign or Cesàro
       hypothesis on `logValue`!), if `spectralSecondMoment F ≤ (67 / 4) * ∫ ‖F‖²`, then
       `primeBlindCounterterm unitStepCountertermWeight F + 2 * sinhHalfMoment f ^ 2 + (1 / 1500) * ∫ ‖F‖² ≤ 0`
       (`unitStep_add_two_sinh_sq_add_one_fifteen_hundredth_l2_le_zero_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero`).
     - Consequently, every nonzero `f ∈ C²_c(ℝ)` (`0 < ∫ ‖F‖²`) on the Primitive Hyperplane with
       `0 ≤ primeBlindCounterterm unitStepCountertermWeight F` satisfies the strict spectral gap
       `(67 / 4) * ∫ ‖F‖² < spectralSecondMoment F`
       (`sixty_seven_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg`), and every
       nonzero `f ∈ C²_c(ℝ)` on the Primitive Hyperplane in the Nonnegative Log-Value Cone (in
       particular, every nonzero `f` in the Prime-Blind Cone `logVector F = 0` on the Primitive
       Hyperplane) satisfies the strict spectral gap
       `(53 / 3) * ∫ ‖F‖² < spectralSecondMoment F`
       (`fifty_three_thirds_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg`,
       `fifty_three_thirds_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero`)!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Three-Stage Counterterm Potential `secantThreeStagePotential`, the `(61 - 38√2 - 4√3) / 6 ≤ 1 / 18` Counterterm Bound, and the `2953 / 3600` General Origin $L^2$ Surplus -/

/-- The quadratic square-root difference `(√n - √(n - 1)) ^ 2`. -/
def secantQuadTerm (n : ℕ) : ℝ :=
  (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2

/-- The cubic square-root difference `(√n - √(n - 1)) ^ 3`. -/
def secantCubeTerm (n : ℕ) : ℝ :=
  (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3

/-- The **Three-Stage Secular Counterterm Potential** `secantThreeStagePotential n`:
isolates `n = 2` (with denominator `√2`) and `n = 3` (with denominator `√3`), and uses denominator
`2 = √4` for `n ≥ 4`. -/
def secantThreeStagePotential (n : ℕ) : ℝ :=
  if n = 2 then
    (secantQuadTerm 2 - secantQuadTerm 3) / Real.sqrt 2 +
      (secantQuadTerm 3 - secantQuadTerm 4) / Real.sqrt 3 +
      secantQuadTerm 4 / 2 - 2 * secantCubeTerm 2 / 3
  else if n = 3 then
    (secantQuadTerm 3 - secantQuadTerm 4) / Real.sqrt 3 +
      secantQuadTerm 4 / 2 - 2 * secantCubeTerm 3 / 3
  else
    secantQuadTerm n / 2 - 2 * secantCubeTerm n / 3

/-- For every `1 ≤ n`, `0 ≤ secantQuadTerm n - secantQuadTerm (n + 1)`. -/
theorem secantQuadTerm_sub_succ_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ secantQuadTerm n - secantQuadTerm (n + 1) := by
  unfold secantQuadTerm
  push_cast
  rw [add_sub_cancel_right]
  have hle := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred hn
  have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  exact sub_nonneg.mpr (pow_le_pow_left₀ hnonneg hle 2)

/-- **Three-Stage Telescoping Step Bound**:
for every `2 ≤ n`,
`secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ secantThreeStagePotential n - secantThreeStagePotential (n + 1)`. -/
theorem secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage {n : ℕ} (hn : 2 ≤ n) :
    secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤
      secantThreeStagePotential n - secantThreeStagePotential (n + 1) := by
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
  have hlhs :
      secantCombinedSecularWeight n * (2 / Real.sqrt n) =
        (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n -
          2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
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
  rw [hlhs]
  by_cases hn2 : n = 2
  · subst hn2
    unfold secantThreeStagePotential
    norm_num
    ring_nf
    exact le_rfl
  · by_cases hn3 : n = 3
    · subst hn3
      unfold secantThreeStagePotential
      norm_num
      ring_nf
      exact le_rfl
    · have hn4 : 4 ≤ n := by omega
      have h1 : n ≠ 2 := hn2
      have h2 : n ≠ 3 := hn3
      have h3 : n + 1 ≠ 2 := by omega
      have h4 : n + 1 ≠ 3 := by omega
      unfold secantThreeStagePotential
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      have hsqrt_ge : (2 : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn4)
      have hinv_le : (Real.sqrt n)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hsqrt_ge
      have hΔ2_nonneg := secantQuadTerm_sub_succ_nonneg (by omega : 1 ≤ n)
      have hdiv_le :
          (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n ≤
            (secantQuadTerm n - secantQuadTerm (n + 1)) / 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv_le hΔ2_nonneg
      linarith

/-- For every `4 ≤ n`, `0 ≤ secantThreeStagePotential n`. -/
theorem secantThreeStagePotential_nonneg_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ secantThreeStagePotential n := by
  have h1 : n ≠ 2 := by omega
  have h2 : n ≠ 3 := by omega
  unfold secantThreeStagePotential
  rw [if_neg h1, if_neg h2]
  unfold secantQuadTerm secantCubeTerm
  set d := Real.sqrt n - Real.sqrt ((n : ℝ) - 1)
  have hd_nonneg : 0 ≤ d := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hd_le : d ≤ 1 / 2 := by
    have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hconj : d * (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
      have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
      have hsq1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
      dsimp [d]
      linear_combination hsq0 - hsq1
    have hsum_ge : 2 ≤ Real.sqrt n + Real.sqrt ((n : ℝ) - 1) := by
      have hsqrt_n : (2 : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by linarith)
      have hsqrt_pred : 0 ≤ Real.sqrt ((n : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    nlinarith
  have hfactor : d ^ 2 / 2 - 2 * d ^ 3 / 3 = d ^ 2 * (1 / 2 - (2 / 3) * d) := by ring
  rw [hfactor]
  exact mul_nonneg (sq_nonneg d) (by linarith)

/-- For every `2 ≤ n`, `0 ≤ secantThreeStagePotential n`. -/
theorem secantThreeStagePotential_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ secantThreeStagePotential n := by
  have hstep : ∀ k : ℕ, 2 ≤ k → secantThreeStagePotential (k + 1) ≤ secantThreeStagePotential k := by
    intro k hk
    have h1 := secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage hk
    have h2 : 0 ≤ secantCombinedSecularWeight k * (2 / Real.sqrt k) :=
      mul_nonneg (secantCombinedSecularWeight_nonneg k) (by positivity)
    linarith
  have h4 : 0 ≤ secantThreeStagePotential 4 :=
    secantThreeStagePotential_nonneg_of_four_le (by omega)
  have h3 : 0 ≤ secantThreeStagePotential 3 := le_trans h4 (hstep 3 (by omega))
  have h2 : 0 ≤ secantThreeStagePotential 2 := le_trans h3 (hstep 2 (by omega))
  by_cases hn2 : n = 2
  · subst hn2; exact h2
  · by_cases hn3 : n = 3
    · subst hn3; exact h3
    · exact secantThreeStagePotential_nonneg_of_four_le (by omega)

/-- **Exact Closed Form of `secantThreeStagePotential 2`**:
`secantThreeStagePotential 2 = (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6`. -/
theorem secantThreeStagePotential_two_eq :
    secantThreeStagePotential 2 = (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 := by
  unfold secantThreeStagePotential secantQuadTerm secantCubeTerm
  simp only [↓reduceIte]
  norm_num
  set s2 := Real.sqrt 2
  set s3 := Real.sqrt 3
  have h2 : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs2_ne : s2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs3_ne : s3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hinv2 : ∀ x : ℝ, x / s2 = x * s2 / 2 := by
    intro x
    apply mul_right_cancel₀ hs2_ne
    calc (x / s2) * s2 = x := div_mul_cancel₀ x hs2_ne
      _ = (x * s2 / 2) * s2 := by linear_combination -(x / 2) * h2
  have hinv3 : ∀ x : ℝ, x / s3 = x * s3 / 3 := by
    intro x
    apply mul_right_cancel₀ hs3_ne
    calc (x / s3) * s3 = x := div_mul_cancel₀ x hs3_ne
      _ = (x * s3 / 3) * s3 := by linear_combination -(x / 3) * h3
  rw [hinv2, hinv3]
  linear_combination
    ((4 / 3) * s3 - (2 / 3) * s2 + 1) * h2 +
    (-(7 / 6) * s2 + 11 / 6) * h3

/-- **Sharp Rational Upper Bound `secantThreeStagePotential 2 ≤ 1 / 18`**:
since `1393 / 985 ≤ √2` and `989 / 571 ≤ √3`,
`(61 - 38 * √2 - 4 * √3) / 6 ≤ 1 / 18`. -/
theorem secantThreeStagePotential_two_le_one_eighteenth :
    secantThreeStagePotential 2 ≤ 1 / 18 := by
  rw [secantThreeStagePotential_two_eq]
  have hsqrt2 : (1393 / 985 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1393 / 985)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3 : (989 / 571 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 989 / 571)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Three-Stage Telescoping Upper Bound on `∑_{n=2}^N secantCombinedSecularWeight n * (2 / √n)`**:
for every `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6`. -/
theorem sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
      (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 := by
  have hle_sum :
      (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
        ∑ n ∈ Finset.Icc 2 N,
          (secantThreeStagePotential n - secantThreeStagePotential (n + 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage hn.1
  rw [sum_Icc_two_sub_succ_nat secantThreeStagePotential hN] at hle_sum
  have h2 := secantThreeStagePotential_two_eq
  have hN1 : 0 ≤ secantThreeStagePotential (N + 1) :=
    secantThreeStagePotential_nonneg (by omega)
  linarith

/-- **Upgraded Three-Stage Uniform Bound on `primeBlindCounterterm secantCombinedSecularWeight f`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`|primeBlindCounterterm secantCombinedSecularWeight f| ≤ ((61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_secantCombinedSecularWeight_le_threeStage
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm secantCombinedSecularWeight f| ≤
      ((61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
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
    (sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_threeStage hN1) hnorm_nonneg

/-- **Sharp Rational Lower Bound `2953 / 3600 ≤ (70 * Real.sqrt 2 + 4 * Real.sqrt 3 - 101) / 6`
(`> 0.820277`)**: -/
theorem two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_le_threeStage_surplus :
    (2953 / 3600 : ℝ) ≤ (70 * Real.sqrt 2 + 4 * Real.sqrt 3 - 101) / 6 := by
  have hsqrt2 : (1393 / 985 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1393 / 985)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3 : (989 / 571 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 989 / 571)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Upgraded `2953 / 3600` (`> 0.82027`) Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(2953 / 3600) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (2953 / 3600) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have habs :=
    (abs_le.mp (abs_primeBlindCounterterm_secantCombinedSecularWeight_le_threeStage f hN1 hN)).1
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsurplus := mul_le_mul_of_nonneg_right
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_le_threeStage_surplus hnorm_nonneg
  linarith

/-! ## Section 2: Upgraded Coercivity Laws up to `131 / 9 > 14.555` and `67 / 4 = 16.75` -/

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity at Critical Ratio `131 / 9 > 14.5555`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_thirty_one_ninths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (131 / 9) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((2953 / 190) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (149 / 9) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((131 / 9) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((131 / 9) * L) * (S + 2 * L) ≤ ((131 / 9) * L) * ((149 / 9) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((131 / 9) * L) * ((149 / 9) * L) ≤ ((2953 / 190) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (2953 / 190) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (2953 / 190) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `67 / 4 = 16.75`**:
whenever `spectralSecondMoment f.1 ≤ (67 / 4) * ∫ ‖f.1‖²`, we have
`(1 / 1500) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_fifteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_seven_fourths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (67 / 4) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1500) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hres_nonneg : 0 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) :=
    bochnerResolventEnergy_weilTest_nonneg f
  have hres_cs :=
    four_mul_sq_l2_le_bochnerResolventEnergy_mul_two_spectralSecondMoment_add_l2 f hint2
  have hdenom_le : 2 * S + L ≤ (69 / 2) * L := by linarith [hsec]
  have hres_mul_le :
      bochnerResolventEnergy (EF.weilTest f.1 f.1) * (2 * S + L) ≤
        bochnerResolventEnergy (EF.weilTest f.1 f.1) * ((69 / 2) * L) :=
    mul_le_mul_of_nonneg_left hdenom_le hres_nonneg
  have hres_ge : (8 / 69) * L ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) := by
    rcases eq_or_lt_of_le hL_nonneg with hL0 | hL_pos
    · rw [← hL0, mul_zero]
      exact hres_nonneg
    · have hcomb : 4 * L ^ 2 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) * ((69 / 2) * L) :=
        hres_cs.trans hres_mul_le
      nlinarith
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((709 / 40) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (75 / 4) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((67 / 4) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((67 / 4) * L) * (S + 2 * L) ≤ ((67 / 4) * L) * ((75 / 4) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((67 / 4) * L) * ((75 / 4) * L) ≤ ((709 / 40) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (709 / 40) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (709 / 40) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (67 / 4) * ∫ ‖F‖² = 16.75 * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero
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
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 3201
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (3201 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (3200 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hprod_le :
      spectralSecondMoment (realWeilTestFn f hf hfc).1 *
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
            2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        ((709 / 40) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
    have hS2L_le :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          2 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        (75 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      linarith [hsec_bound]
    have hmul1 :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsec_bound (by positivity)
    have hmul2 :
        ((67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((75 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth :
        ((67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((75 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((709 / 40) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
      have hsq : 0 ≤ (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := sq_nonneg _
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le :
      Real.sqrt
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (709 / 40) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rw [← Real.sqrt_sq
      (by positivity : 0 ≤ (709 / 40) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)]
    exact Real.sqrt_le_sqrt hprod_le
  have hcomb :=
    one_fifteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_seven_fourths
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (3200 : ℝ) * ((1 / 1500) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-! ## Section 3: Universal Unit-Step Negativity, Vanishing Rigidity, and the `67 / 4 = 16.75` & `53 / 3 > 17.666` Spectral Poincaré / Uncertainty Gap Laws on the Primitive Hyperplane -/

/-- **Universal Unit-Step Negativity on the Primitive Hyperplane for `S ≤ (67 / 4) L`**:
for **every** signed test `f ∈ C²_c(ℝ)` on the Primitive Hyperplane (`coshHalfMoment f = 0`) — with
**no** sign or Cesàro condition on `logValue` — if `spectralSecondMoment F ≤ (67 / 4) * ∫ ‖F‖²`,
then
`primeBlindCounterterm unitStepCountertermWeight F + 2 * sinhHalfMoment f ^ 2 + (1 / 1500) * ∫ ‖F‖² ≤ 0`. -/
theorem unitStep_add_two_sinh_sq_add_one_fifteen_hundredth_l2_le_zero_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hsec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        2 * sinhHalfMoment f ^ 2 +
        (1 / 1500) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤ 0 := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_fifteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_sixty_seven_fourths
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec
  linarith

/-- **Vanishing Rigidity on the Primitive Hyperplane under `0 ≤ primeBlindCounterterm unitStepCountertermWeight`**:
if `coshHalfMoment f = 0`, `0 ≤ primeBlindCounterterm unitStepCountertermWeight F`, and
`spectralSecondMoment F ≤ (67 / 4) * ∫ ‖F‖²`, then `∫ ‖F‖² = 0` and `sinhHalfMoment f = 0`. -/
theorem l2_eq_zero_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hsec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (67 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = 0 := by
  have h1 :=
    unitStep_add_two_sinh_sq_add_one_fifteen_hundredth_l2_le_zero_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero
      hf hfc hcosh hint2 hN1 hN0 hN hsec
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `67 / 4 = 16.75` Spectral Poincaré / Uncertainty Gap Law on the Primitive Hyperplane**:
for every nonzero `f ∈ C²_c(ℝ)` (`0 < ∫ ‖F‖²`) on the Primitive Hyperplane (`coshHalfMoment f = 0`)
with `0 ≤ primeBlindCounterterm unitStepCountertermWeight F`,
`(67 / 4) * ∫ ‖F‖² < spectralSecondMoment F`! -/
theorem sixty_seven_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (67 / 4) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hzero :=
    l2_eq_zero_of_spectralSecondMoment_le_sixty_seven_fourths_of_cosh_zero_of_unitStep_nonneg
      hf hfc hcosh hint2 hN1 hN0 hN hunit hle
  linarith

/-- **Vanishing Rigidity on the Nonnegative Log-Value Cone of the Primitive Hyperplane up to
`53 / 3 > 17.6666`**:
for every `f ∈ C²_c(ℝ)` on the Primitive Hyperplane (`coshHalfMoment f = 0`) with
`0 ≤ logValue F n` on `Finset.Icc 2 N` and `spectralSecondMoment F ≤ (53 / 3) * ∫ ‖F‖²`,
we have `∫ ‖F‖² = 0`! -/
theorem l2_eq_zero_of_spectralSecondMoment_le_fifty_three_thirds_of_cosh_zero_of_logValue_nonneg
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
    (hsec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = 0 := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_eighteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_three_thirds_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec
  have hunit_nonneg :
      0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight (realWeilTestFn f hf hfc)
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn)
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `53 / 3 > 17.6666` Spectral Poincaré / Uncertainty Gap Law on the Nonnegative Log-Value
Cone of the Primitive Hyperplane**:
for every nonzero `f ∈ C²_c(ℝ)` (`0 < ∫ ‖F‖²`) on the Primitive Hyperplane (`coshHalfMoment f = 0`)
with `0 ≤ logValue F n` on `Finset.Icc 2 N`,
`(53 / 3) * ∫ ‖F‖² < spectralSecondMoment F`! -/
theorem fifty_three_thirds_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
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
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (53 / 3) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hzero :=
    l2_eq_zero_of_spectralSecondMoment_le_fifty_three_thirds_of_cosh_zero_of_logValue_nonneg
      hf hfc hcosh hint2 hN1 hN0 hN hpos hle
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to
Critical Ratio `53 / 3 > 17.6666`**: -/
theorem one_eighteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_three_thirds_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (53 / 3) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1800) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (6 / 109)
  have hprod_le : S * (S + 2 * L) ≤ ((56 / 3) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (59 / 3) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((53 / 3) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((53 / 3) * L) * (S + 2 * L) ≤ ((53 / 3) * L) * ((59 / 3) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((53 / 3) * L) * ((59 / 3) * L) ≤ ((56 / 3) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (56 / 3) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (56 / 3) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **The `53 / 3 > 17.6666` Spectral Poincaré / Uncertainty Gap Law on the Prime-Blind Cone
(`logVector F = 0`) of the Primitive Hyperplane**:
every nonzero `f ∈ C²_c(ℝ)` (`0 < ∫ ‖F‖²`) on the Primitive Hyperplane (`coshHalfMoment f = 0`)
lying in the Prime-Blind Cone (`logVector (realWeilTestFn f hf hfc) = 0`) satisfies
`(53 / 3) * ∫ ‖F‖² < spectralSecondMoment F`! -/
theorem fifty_three_thirds_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
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
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (53 / 3) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_eighteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_three_thirds_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
