import GaloisForLFunctions.RHTower.MarkovSecantMatchedCombAndSpectralCauchySchwarzPBAP

/-!
# Hybrid First/Second-Order Cell Splitting, Isolation of the $n = 2$ Cell $[1, 2]$, and the `-(1 / 16) spectralSecondMoment - (19 / 48) spectralFirstMoment` Coercivity Law

In Module 50 and Module 51, we bounded `secantNumeratorCellDefect f.1 N` in two pure ways across all
cells `n ∈ Finset.Icc 2 N`:
- Using the **first-order** logarithmic-Lipschitz bound on every cell `n ≥ 2` triggered the $p = 3/2$
  series `(4 / 12) * ∑_{n=2}^N (n - 1)^{-3/2} ≤ (1 / 3) * 3 = 1`, giving
  `-spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`.
- Using the **second-order** Peano bound on every cell `n ≥ 2` triggered the $p = 5/2$ series
  `(1 / 12) * ∑_{n=2}^N (n - 1)^{-5/2} ≤ (1 / 12) * (7 / 4) = 7 / 24`, giving
  `-(7 / 24) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`.

Observe why the $p = 5/2$ series `∑_{n=2}^N (n - 1)^{-5/2} ≤ 1 + 1 / √2 ≤ 7 / 4` is dominated by a
single cell:
- The **first cell `n = 2` (`[1, 2]`)** contributes `(2 - 1)^{-5/2} = 1`, which is `4 / 7 > 57%` of
  the entire infinite series!
- All **tail cells `n ≥ 3` (`[2, N]`)** together contribute at most
  `∑_{n=3}^N (n - 1)^{-5/2} ≤ 1 / √2 ≤ 3 / 4`, so `(1 / 12) * ∑_{n=3}^N (n - 1)^{-5/2} ≤ 1 / 16`!

In this module, we exploit Module 47's cell-by-cell Peano theorem
`neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave` with a **hybrid cell-wise
curvature assignment** that uses the first-order logarithmic-Lipschitz bound on `n = 2` (`[1, 2]`)
and the second-order Peano bound on `n ≥ 3` (`[2, N]`):

1. **Section 1 (The Tail $p = 5/2$ Series Bound `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 1 / √2 ≤ 3 / 4`
   and the General Hybrid Cell-Split Semiconcavity Theorem):**
   - Splitting `Finset.Icc 2 N` into `n = 2` and `Finset.Icc 3 N` (`sum_Icc_two_eq_add_sum_Icc_three`)
     and subtracting the `n = 2` term `1` from Module 50's `sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_sub`
     proves that for all `N : ℕ` (`sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_inv_sqrt_two` and
     `sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_three_fourths`):
     `∑ n ∈ Finset.Icc 3 N, 1 / ((n - 1) ^ 2 * √(n - 1)) ≤ 1 / √2 ≤ 3 / 4`.
   - Using the hybrid curvature sequence `K n := if n = 2 then 4 * L else M / ((n : ℝ) - 1) ^ 2`,
     where `K 2 / (12 * √1) = (1 / 3) * L` and `∑_{n=3}^N K n / (12 * √(n - 1)) ≤ (1 / 16) * M`,
     we prove (`neg_third_first_sub_sixteenth_second_le_secantNumeratorCellDefect_of_hybrid`):
     `-(1 / 3) * L - (1 / 16) * M ≤ secantNumeratorCellDefect f.1 N`!

2. **Section 2 (The Hybrid Spectral Secant Numerator Bound
   `-(1 / 16) spectralSecondMoment f.1 - (19 / 48) spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`):**
   - Combining the `n = 2` logarithmic-Lipschitz bound (`L = spectralFirstMoment f.1`) with the
     `n ≥ 3` second-derivative Peano bound (`M = spectralSecondMoment f.1 + spectralFirstMoment f.1`)
     slashes the coefficient of `spectralSecondMoment f.1` from `7 / 24 ≈ 0.2917` down to
     `1 / 16 = 0.0625` (a nearly `5×` reduction!) while keeping the `spectralFirstMoment f.1`
     coefficient at `1 / 3 + 1 / 16 = 19 / 48`
     (`neg_sixteenth_second_sub_nineteen_forty_eighths_first_le_secantNumeratorCellDefect`).

3. **Section 3 (Expanded Second-Moment Coercivity on `rightCellQuadratureDefect`, the Prime-Blind
   Cone, and `markovEnergy ≥ 0` on the Primitive Hyperplane):**
   - At spectral scale `λ = 1`, absorbing `(19 / 48) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²`
     positive surplus gives
     (`ninety_seven_two_fortieths_l2_sub_twenty_five_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(97 / 240) * ∫ ‖f.1‖² - (25 / 96) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     raising the critical `spectralSecondMoment / L^2` ratio to `194 / 125 = 1.552`!
   - On the Prime-Blind Cone (`logVector f = 0`), absorbing `(19 / 48) * ∫ ‖f.1‖²` into Module 52's
     `(7 / 8) * ∫ ‖f.1‖²` surplus gives
     (`twenty_three_forty_eighths_l2_sub_twenty_five_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero`):
     `(23 / 48) * ∫ ‖f.1‖² - (25 / 96) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     (critical ratio `46 / 25 = 1.84`!).
   - At spectral scale `λ = 19 / 16` (`19 / (48 * λ) = 1 / 3`), we obtain
     (`seven_fifteenths_l2_sub_four_fifty_seven_fifteen_thirty_sixths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(7 / 15) * ∫ ‖f.1‖² - (457 / 1536) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     (critical ratio `3584 / 2285 > 1.5684`!), and prove unconditional `0 ≤ markovEnergy F` on the
     primitive hyperplane whenever `spectralSecondMoment F ≤ (194 / 125 - δ) * ∫ ‖F‖²`
     (`markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_one_ninety_four_one_twenty_fifths_of_cosh_zero`).
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

/-! ## Section 1: The Tail $p = 5/2$ Series Bound `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 1 / √2 ≤ 3 / 4` and the General Hybrid Cell-Split Semiconcavity Theorem -/

/-- Splitting a finite sum over `Finset.Icc 2 N` (`2 ≤ N`) into its `n = 2` head term and its
`Finset.Icc 3 N` tail sum: -/
theorem sum_Icc_two_eq_add_sum_Icc_three (g : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, g n) = g 2 + ∑ n ∈ Finset.Icc 3 N, g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hk2 : 2 ≤ 2 + k := by omega
    have hsucc2 : 2 ≤ 2 + k + 1 := by omega
    have hsucc3 : 3 ≤ 2 + k + 1 := by omega
    rw [show 2 + (k + 1) = 2 + k + 1 by omega,
      Finset.sum_Icc_succ_top hsucc2, Finset.sum_Icc_succ_top hsucc3, ih hk2]
    ring

/-- **Sharp Telescoping Bound on the Tail $p = 5/2$ Series `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1))`
for `2 ≤ N`**:
subtracting the `n = 2` term `1` from `sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_sub` gives
`∑ n ∈ Finset.Icc 3 N, 1 / ((n - 1) ^ 2 * √(n - 1)) ≤ (1 / √2) * (1 - 1 / (N - 1))`. -/
theorem sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_sub {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 3 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤
      (1 / Real.sqrt 2) * (1 - 1 / ((N : ℝ) - 1)) := by
  have htwo := sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_sub hN
  have hsplit := sum_Icc_two_eq_add_sum_Icc_three
    (fun n : ℕ => 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) hN
  have hterm2 : 1 / (((2 : ℕ) : ℝ) - 1) ^ 2 * Real.sqrt (((2 : ℕ) : ℝ) - 1) = 1 := by
    norm_num
  have hterm2' : 1 / ((((2 : ℕ) : ℝ) - 1) ^ 2 * Real.sqrt (((2 : ℕ) : ℝ) - 1)) = 1 := by
    norm_num
  linarith

/-- **Uniform Cutoff-Independent Bound `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 1 / √2` for All `N : ℕ`**: -/
theorem sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_inv_sqrt_two (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤
      1 / Real.sqrt 2 := by
  by_cases hN : 2 ≤ N
  · have h := sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_sub hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hinv_nonneg : 0 ≤ (1 / Real.sqrt 2) * (1 / ((N : ℝ) - 1)) :=
      mul_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (div_nonneg zero_le_one (by linarith))
    linarith
  · have hN3 : ¬ 3 ≤ N := by omega
    rw [Finset.Icc_eq_empty hN3, Finset.sum_empty]
    exact div_nonneg zero_le_one (Real.sqrt_nonneg 2)

/-- **Rational Cutoff-Independent Bound `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 3 / 4` for All `N : ℕ`**: -/
theorem sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_three_fourths (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤ 3 / 4 := by
  have h := sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_inv_sqrt_two N
  have hsqrt2_gt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hinv_le : 1 / Real.sqrt 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hsqrt2_pos]
    linarith
  linarith

/-- **General Hybrid Cell-Split Semiconcavity Theorem**:
if `weilSymmetricLogNumerator f.1` satisfies a Peano parabola bound with constant `4 * L` on the
first cell `n = 2` (`[1, 2]`) and `M / (n - 1) ^ 2` on all higher cells `n ∈ Finset.Icc 3 N`, then
`-(1 / 3) * L - (1 / 16) * M ≤ secantNumeratorCellDefect f.1 N` uniformly in `N`! -/
theorem neg_third_first_sub_sixteenth_second_le_secantNumeratorCellDefect_of_hybrid
    (f : WeilTestFn) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℕ)
    (hcell2 : ∀ x ∈ Icc (1 : ℝ) 2,
      -(2 * L) * cellParabola 2 x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x)
    (hcell3 : ∀ n ∈ Finset.Icc 3 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(1 / 3) * L - (1 / 16) * M ≤ secantNumeratorCellDefect f.1 N := by
  let K : ℕ → ℝ := fun n => if n = 2 then 4 * L else M / ((n : ℝ) - 1) ^ 2
  have hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n := by
    intro n _
    dsimp [K]
    split_ifs
    · linarith
    · exact div_nonneg hM (sq_nonneg _)
  have hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x := by
    intro n hn x hx
    rw [Finset.mem_Icc] at hn
    dsimp [K]
    split_ifs with hn2
    · subst hn2
      have hx' : x ∈ Icc (1 : ℝ) 2 := by
        convert hx using 2 <;> norm_num
      have h2 := hcell2 x hx'
      linarith
    · have hn3 : n ∈ Finset.Icc 3 N := Finset.mem_Icc.mpr ⟨by omega, hn.2⟩
      have h3 := hcell3 n hn3 x hx
      have halg : -(M / ((n : ℝ) - 1) ^ 2 / 2) * cellParabola n x =
          -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x := by
        rw [div_div, mul_comm (((n : ℝ) - 1) ^ 2) 2]
      rwa [halg]
  have hpeano := neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    f K hK0 hsemi
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤
        (1 / 3) * L + (1 / 16) * M := by
    by_cases hN : 2 ≤ N
    · rw [sum_Icc_two_eq_add_sum_Icc_three _ hN]
      have hhead : K 2 / (12 * Real.sqrt (((2 : ℕ) : ℝ) - 1)) = (1 / 3) * L := by
        dsimp [K]
        norm_num
        ring
      have htail_eq :
          (∑ n ∈ Finset.Icc 3 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) =
            (M / 12) * ∑ n ∈ Finset.Icc 3 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hne2 : n ≠ 2 := by omega
        dsimp [K]
        rw [if_neg hne2]
        simp only [div_eq_mul_inv, mul_inv]
        ring
      rw [hhead, htail_eq]
      have h34 := sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_three_fourths N
      have hmul := mul_le_mul_of_nonneg_left h34 (by linarith : 0 ≤ M / 12)
      linarith
    · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
      linarith
  linarith

/-! ## Section 2: The Hybrid Spectral Secant Numerator Bound `-(1 / 16) spectralSecondMoment f.1 - (19 / 48) spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N` -/

/-- **Hybrid Spectral Lower Bound on `secantNumeratorCellDefect`**:
using the first-order logarithmic-Lipschitz bound on the `n = 2` cell `[1, 2]` (costing
`(1 / 3) * spectralFirstMoment f.1`) and the second-order Peano bound on `n ≥ 3` (costing
`(1 / 16) * (spectralSecondMoment f.1 + spectralFirstMoment f.1)`) proves that for every `N : ℕ`,
`-(1 / 16) * spectralSecondMoment f.1 - (19 / 48) * spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`! -/
theorem neg_sixteenth_second_sub_nineteen_forty_eighths_first_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(1 / 16) * spectralSecondMoment f.1 - (19 / 48) * spectralFirstMoment f.1 ≤
      secantNumeratorCellDefect f.1 N := by
  have hhyb := neg_third_first_sub_sixteenth_second_le_secantNumeratorCellDefect_of_hybrid
    f (spectralFirstMoment_nonneg f.1)
    (add_nonneg (spectralSecondMoment_nonneg f.1) (spectralFirstMoment_nonneg f.1)) N
    (fun x hx => by
      have hx2 : x ∈ Icc (((2 : ℕ) : ℝ) - 1) (2 : ℕ) := by
        convert hx using 2 <;> norm_num
      have hcell := neg_two_mul_div_pred_mul_cellParabola_le_sub_cellSecant_of_log_lipschitz
        (weilSymmetricLogNumerator f.1) (spectralFirstMoment_nonneg f.1) (le_refl 2)
        (fun y hy z _ hyz =>
          abs_weilSymmetricLogNumerator_sub_le_spectralFirstMoment_mul_log_sub
            f hint1 (by norm_num at hy; linarith [hy.1]) hyz) hx2
      have halg : -((4 * spectralFirstMoment f.1 / (((2 : ℕ) : ℝ) - 1)) / 2) * cellParabola 2 x =
          -(2 * spectralFirstMoment f.1) * cellParabola 2 x := by
        push_cast
        ring
      rwa [halg] at hcell)
    (fun n hn x hx => by
      rw [Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n := by omega
      have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectral_second_add_first
        f hint1 hint2 hn2 hx
      linarith [(abs_le.mp h).1])
  linarith

/-! ## Section 3: Expanded Second-Moment Coercivity on `rightCellQuadratureDefect`, the Prime-Blind Cone, and `markovEnergy ≥ 0` on the Primitive Hyperplane -/

/-- **Cutoff-Independent `-(25 / 96) spectralSecondMoment f.1 - (19 / 48) ∫ ‖f.1‖² ≤ secantNumeratorCellDefect f.1 N`
at Spectral Scale `λ = 1`**: -/
theorem neg_twenty_five_ninety_sixths_spectralSecondMoment_sub_nineteen_forty_eighths_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(25 / 96) * spectralSecondMoment f.1 - (19 / 48) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have h1 := neg_sixteenth_second_sub_nineteen_forty_eighths_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h2 := spectralFirstMoment_le_half_spectralSecondMoment_add_l2 f hint1 hint2
  linarith

/-- **Pure Second-Moment `(97 / 240) ∫ ‖f.1‖² - (25 / 96) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (`λ = 1`, Critical Ratio `194 / 125 = 1.552`)**:
absorbing `(19 / 48) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²` positive surplus leaves
`4 / 5 - 19 / 48 = 97 / 240 > 2 / 5` and `1 / 16 + 19 / 96 = 25 / 96`! -/
theorem ninety_seven_two_fortieths_l2_sub_twenty_five_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (97 / 240) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (25 / 96) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_twenty_five_ninety_sixths_spectralSecondMoment_sub_nineteen_forty_eighths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- **Prime-Blind Cone `(23 / 48) ∫ ‖f.1‖² - (25 / 96) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `46 / 25 = 1.84`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(19 / 48) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖²` origin surplus leaves `7 / 8 - 19 / 48 = 23 / 48`! -/
theorem twenty_three_forty_eighths_l2_sub_twenty_five_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (23 / 48) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (25 / 96) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_twenty_five_ninety_sixths_spectralSecondMoment_sub_nineteen_forty_eighths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- Specializing `spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2` at
`lam = 19 / 16` (where `19 / (48 * lam) = 1 / 3` cancels the `19`!) gives
`spectralFirstMoment f.1 ≤ (19 / 32) * spectralSecondMoment f.1 + (16 / 19) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectralFirstMoment_le_nineteen_thirty_seconds_spectralSecondMoment_add_sixteen_nineteenths_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ≤
      (19 / 32) * spectralSecondMoment f.1 + (16 / 19) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have h := spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2
    f hint1 hint2 (by norm_num : (0 : ℝ) < 19 / 16)
  linarith

/-- **Pure Second-Moment `(7 / 15) ∫ ‖f.1‖² - (457 / 1536) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (`λ = 19 / 16`, Critical Ratio `3584 / 2285 > 1.5684`)**: -/
theorem seven_fifteenths_l2_sub_four_fifty_seven_fifteen_thirty_sixths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (7 / 15) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (457 / 1536) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_sixteenth_second_sub_nineteen_forty_eighths_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h3 := spectralFirstMoment_le_nineteen_thirty_seconds_spectralSecondMoment_add_sixteen_nineteenths_l2
    f hint1 hint2
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (194 / 125 - δ) ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_one_ninety_four_one_twenty_fifths_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint1 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (194 / 125 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (192 / (25 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h25δ : 0 < 25 * δ := by linarith
  have hθδ_le : 192 / (25 * δ) ≤ θ := le_max_right _ _
  have hθδ : 192 ≤ θ * (25 * δ) := (div_le_iff₀ h25δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_twenty_five_ninety_sixths_spectralSecondMoment_sub_nineteen_forty_eighths_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint1 hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (25 / 96) * θ)
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hθδ_norm := mul_le_mul_of_nonneg_right hθδ hnorm_nonneg
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
