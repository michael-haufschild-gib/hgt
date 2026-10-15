import GaloisForLFunctions.RHTower.MarkovHybridCellSplitAndOneSixteenthSecondMomentPBAP

/-!
# Exact Isolation of $n = 2, 3, 4$ in the $p = 5/2$ Series, the `-(17 / 144) (spectralSecondMoment + spectralFirstMoment)` Bound, and Unconditional Coercivity up to `spectralSecondMoment / L² < 224 / 57 > 3.929`

In Module 50 and Module 53, we observed two sources of slack in our $p = 5/2$ curvature bounds:
1. When telescoping `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) = ∑_{m=2}^{N-1} 1 / (m^2 √m)` starting at
   `m = 2`, the inequality `1 / (m^2 √m) ≤ (1 / √2) * (1 / (m - 1) - 1 / m)` replaces `2^2 = 4` by
   `2 * (2 - 1) = 2` (doubling the `m = 2` term from `1 / (4√2)` to `1 / (2√2)`) and bounds `√m` by
   `√2` instead of `√4 = 2` on the `m ≥ 4` tail.
2. In Module 50 (`neg_seven_twenty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave`),
   multiplying `∑_{n=2}^N (n - 1)^{-5/2} ≤ 7 / 4` by `M / 12` was recorded as `(7 / 24) * M` rather
   than `(7 / 48) * M`, leaving an immediate factor of `2` on the table!

In this module, we recover both factors simultaneously:

1. **Section 1 (Exact Isolation of $n = 2, 3, 4$ in the $p = 5/2$ Series and the Rational $m \ge 4$
   Telescoping Bound `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 17 / 12`):**
   - For `m ≥ 4`, `√m ≥ √4 = 2` (an exact integer!) and `m^2 ≥ m * (m - 1)`, so
     `1 / (m^2 √m) ≤ (1 / 2) * (1 / (m - 1) - 1 / m)` (`inv_sq_mul_sqrt_le_half_mul_inv_sub_of_four_le`).
   - Summing over `n ∈ Finset.Icc 5 N` (`m ∈ [4, N - 1]`) telescopes to at most
     `(1 / 2) * (1 / 3 - 1 / (N - 1)) ≤ 1 / 6` (`sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_one_sixth`).
   - Isolating the `n = 3` (`m = 2`) term `1 / (4√2)` and the `n = 4` (`m = 3`) term `1 / (9√3)`,
     the rational certificates `181 / 128 ≤ √2` and `19 / 11 ≤ √3` (`19^2 = 361 < 363 = 3 * 11^2`)
     prove `1 / (4√2) + 1 / (9√3) ≤ 32 / 181 + 11 / 171 = 7463 / 30951 < 1 / 4`
     (`inv_four_sqrt_two_add_inv_nine_sqrt_three_le_one_fourth`).
   - Consequently, for all `N : ℕ`:
     - `∑ n ∈ Finset.Icc 3 N, 1 / ((n - 1)^2 √(n - 1)) ≤ 1 / 4 + 1 / 6 = 5 / 12`
       (`sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_five_twelfths`), and
     - `∑ n ∈ Finset.Icc 2 N, 1 / ((n - 1)^2 √(n - 1)) ≤ 1 + 5 / 12 = 17 / 12`
       (`sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seventeen_twelfths`).

2. **Section 2 (The Sharp `-(17 / 144) (spectralSecondMoment + spectralFirstMoment) ≤ secantNumeratorCellDefect`
   and Hybrid `-(5 / 144) spectralSecondMoment - (53 / 144) spectralFirstMoment ≤ secantNumeratorCellDefect` Bounds):**
   - Dividing `17 / 12` by `12` improves Module 50/51's `7 / 24 = 42 / 144` coefficient by more than
     `2.47×` to `17 / 144 < 0.1181`
     (`neg_seventeen_one_forty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect`):
     `-(17 / 144) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`.
   - Dividing the tail `5 / 12` by `12` also upgrades Module 53's hybrid cell-split second-moment
     coefficient from `1 / 16 = 9 / 144` down to `5 / 144 < 0.0348`
     (`neg_five_one_forty_fourths_second_sub_fifty_three_one_forty_fourths_first_le_secantNumeratorCellDefect`).

3. **Section 3 (Unconditional Coercivity up to `spectralSecondMoment F / ∫ ‖F‖² < 224 / 57 > 3.9298`
   and `218 / 51 > 4.2745` on the Prime-Blind Cone):**
   - At spectral scale `λ = 1`, absorbing `(17 / 144) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²`
     surplus yields (`four_ninety_one_seven_twentieths_l2_sub_seventeen_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(491 / 720) * ∫ ‖f.1‖² - (17 / 96) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     (critical ratio `982 / 255 > 3.8509`!), and on the Prime-Blind Cone (`logVector f = 0`),
     `(109 / 144) * ∫ ‖f.1‖² - (17 / 96) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     (critical ratio `218 / 51 > 4.2745`!).
   - At spectral scale `λ = 17 / 20`, where `17` cancels in both `(17 / 144) * (20 / 17) = 5 / 36`
     and `119 / 323 = (7 * 17) / (19 * 17) = 7 / 19`, we obtain
     (`one_nineteen_one_eightieths_l2_sub_three_twenty_three_nineteen_twentieths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(119 / 180) * ∫ ‖f.1‖² - (323 / 1920) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     boosting the critical `spectralSecondMoment / L^2` ratio from `194 / 125 = 1.552` to
     **`224 / 57 > 3.9298`** (`markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_two_twenty_four_fifty_sevenths_of_cosh_zero`)!
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

/-! ## Section 1: Exact Isolation of $n = 2, 3, 4$ in the $p = 5/2$ Series and the Rational $m \ge 4$ Telescoping Bound `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 17 / 12` -/

/-- General head-splitting lemma for `Finset.Icc a N` when `a ≤ N`: -/
theorem sum_Icc_eq_add_sum_Icc_succ (g : ℕ → ℝ) {a N : ℕ} (haN : a ≤ N) :
    (∑ n ∈ Finset.Icc a N, g n) = g a + ∑ n ∈ Finset.Icc (a + 1) N, g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le haN
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have hak : a ≤ a + k := by omega
    have hsucc_a : a ≤ a + k + 1 := by omega
    have hsucc_a1 : a + 1 ≤ a + k + 1 := by omega
    rw [show a + (k + 1) = a + k + 1 by omega,
      Finset.sum_Icc_succ_top hsucc_a, Finset.sum_Icc_succ_top hsucc_a1, ih hak]
    ring

/-- **Rational Telescoping $p = 5/2$ Majorant for `4 ≤ m`**:
since `2 = √4 ≤ √m` and `m * (m - 1) ≤ m ^ 2`,
`1 / ((m : ℝ) ^ 2 * Real.sqrt m) ≤ (1 / 2) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ))`. -/
theorem inv_sq_mul_sqrt_le_half_mul_inv_sub_of_four_le {m : ℕ} (hm : 4 ≤ m) :
    1 / ((m : ℝ) ^ 2 * Real.sqrt m) ≤
      (1 / 2) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hsqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hsub : 1 / ((m : ℝ) - 1) - 1 / (m : ℝ) = 1 / (((m : ℝ) - 1) * (m : ℝ)) := by
    rw [div_sub_div _ _ (ne_of_gt hm1_pos) (ne_of_gt hm_pos)]
    ring
  rw [hsub, one_div_mul_one_div]
  refine one_div_le_one_div_of_le (mul_pos (by norm_num) (mul_pos hm1_pos hm_pos)) ?_
  have hsqrt_le : (2 : ℝ) ≤ Real.sqrt m := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hprod_le : ((m : ℝ) - 1) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul hsqrt_le hprod_le (mul_nonneg hm1_pos.le hm_pos.le) hsqrtm_pos.le
  linarith

/-- **Sharp Telescoping Bound on `∑_{n=5}^N 1 / ((n - 1)^2 √(n - 1))` for `4 ≤ N`**:
`∑ n ∈ Finset.Icc 5 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) ≤ (1 / 2) * (1 / 3 - 1 / ((N : ℝ) - 1))`. -/
theorem sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_sub {N : ℕ} (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Icc 5 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤
      (1 / 2) * (1 / 3 - 1 / ((N : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero =>
    have hempty : Finset.Icc 5 (4 + 0) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    norm_num
  | succ k ih =>
    have hk4 : 4 ≤ 4 + k := by omega
    have hsucc5 : 5 ≤ 4 + k + 1 := by omega
    rw [show 4 + (k + 1) = 4 + k + 1 by omega, Finset.sum_Icc_succ_top hsucc5]
    have hih := ih hk4
    have hterm : 1 / ((((4 + k + 1 : ℕ) : ℝ) - 1) ^ 2 * Real.sqrt (((4 + k + 1 : ℕ) : ℝ) - 1)) ≤
        (1 / 2) * (1 / (((4 + k : ℕ) : ℝ) - 1) - 1 / (((4 + k + 1 : ℕ) : ℝ) - 1)) := by
      have hcast : (((4 + k + 1 : ℕ) : ℝ) - 1) = ((4 + k : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      exact inv_sq_mul_sqrt_le_half_mul_inv_sub_of_four_le hk4
    linarith

/-- **Uniform Cutoff-Independent Bound `∑_{n=5}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 1 / 6` for All `N : ℕ`**: -/
theorem sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_one_sixth (N : ℕ) :
    (∑ n ∈ Finset.Icc 5 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤ 1 / 6 := by
  by_cases hN : 4 ≤ N
  · have h := sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_sub hN
    have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hinv_nonneg : 0 ≤ (1 / 2 : ℝ) * (1 / ((N : ℝ) - 1)) :=
      mul_nonneg (by norm_num) (div_nonneg zero_le_one (by linarith))
    linarith
  · have hN5 : ¬ 5 ≤ N := by omega
    rw [Finset.Icc_eq_empty hN5, Finset.sum_empty]
    norm_num

/-- **Rational Bound on the Isolated `n = 3` and `n = 4` Terms**:
`1 / (4 * Real.sqrt 2) + 1 / (9 * Real.sqrt 3) ≤ 1 / 4` via `181 / 128 ≤ √2` and `19 / 11 ≤ √3`
(`19^2 = 361 < 363 = 3 * 11^2`). -/
theorem inv_four_sqrt_two_add_inv_nine_sqrt_three_le_one_fourth :
    1 / (4 * Real.sqrt 2) + 1 / (9 * Real.sqrt 3) ≤ 1 / 4 := by
  have hsqrt2_ge : (181 / 128 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 181 / 128)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (19 / 11 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19 / 11)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_pos : 0 < 4 * Real.sqrt 2 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt3_pos : 0 < 9 * Real.sqrt 3 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have h1 : 1 / (4 * Real.sqrt 2) ≤ 32 / 181 := by
    rw [div_le_iff₀ hsqrt2_pos]
    linarith
  have h2 : 1 / (9 * Real.sqrt 3) ≤ 11 / 171 := by
    rw [div_le_iff₀ hsqrt3_pos]
    linarith
  linarith

/-- **Sharp Tail Bound `∑_{n=3}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 5 / 12` for All `N : ℕ`**:
combining the `n = 3` and `n = 4` bound `≤ 1 / 4` with the `n ≥ 5` telescoping bound `≤ 1 / 6`
gives `1 / 4 + 1 / 6 = 5 / 12`! -/
theorem sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_five_twelfths (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤ 5 / 12 := by
  let g : ℕ → ℝ := fun n => 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))
  have hg3 : g 3 = 1 / (4 * Real.sqrt 2) := by
    dsimp [g]
    norm_num
  have hg4 : g 4 = 1 / (9 * Real.sqrt 3) := by
    dsimp [g]
    norm_num
  have hg4_nonneg : 0 ≤ g 4 := by
    rw [hg4]
    positivity
  have h34 := inv_four_sqrt_two_add_inv_nine_sqrt_three_le_one_fourth
  by_cases hN4 : 4 ≤ N
  · have hsplit3 := sum_Icc_eq_add_sum_Icc_succ g (by omega : 3 ≤ N)
    have hsplit4 := sum_Icc_eq_add_sum_Icc_succ g hN4
    have h5 := sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_one_sixth N
    change (∑ n ∈ Finset.Icc 3 N, g n) ≤ 5 / 12
    rw [hsplit3, hsplit4, hg3, hg4]
    linarith
  · by_cases hN3 : 3 ≤ N
    · have hN_eq : N = 3 := by omega
      subst hN_eq
      change (∑ n ∈ Finset.Icc 3 3, g n) ≤ 5 / 12
      rw [Finset.Icc_self, Finset.sum_singleton]
      linarith [hg3, hg4, hg4_nonneg, h34]
    · rw [Finset.Icc_eq_empty hN3, Finset.sum_empty]
      norm_num

/-- **Sharp Full $p = 5/2$ Series Bound `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ 17 / 12` for All `N : ℕ`**: -/
theorem sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seventeen_twelfths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤ 17 / 12 := by
  by_cases hN : 2 ≤ N
  · rw [sum_Icc_two_eq_add_sum_Icc_three _ hN]
    have h2 : 1 / ((((2 : ℕ) : ℝ) - 1) ^ 2 * Real.sqrt (((2 : ℕ) : ℝ) - 1)) = 1 := by norm_num
    have htail := sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_five_twelfths N
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num

/-! ## Section 2: The Sharp `-(17 / 144) (spectralSecondMoment + spectralFirstMoment) ≤ secantNumeratorCellDefect` and Hybrid `-(5 / 144) spectralSecondMoment - (53 / 144) spectralFirstMoment ≤ secantNumeratorCellDefect` Bounds -/

/-- **Cutoff-Independent `-(17 / 144) M ≤ secantNumeratorCellDefect f.1 N` for `O(1 / (n - 1)^2)`-Curved
Profiles**:
dividing `17 / 12` by `12` improves Module 50's `7 / 24 = 42 / 144` coefficient by more than `2.47×`
to `17 / 144`! -/
theorem neg_seventeen_one_forty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    (f : WeilTestFn) {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(17 / 144) * M ≤ secantNumeratorCellDefect f.1 N := by
  let K : ℕ → ℝ := fun n => M / ((n : ℝ) - 1) ^ 2
  have hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n := fun n _ => div_nonneg hM (sq_nonneg _)
  have hsemi' : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x := by
    intro n hn x hx
    have hpt := hsemi n hn x hx
    have halg : -(K n / 2) * cellParabola n x =
        -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x := by
      dsimp [K]
      rw [div_div, mul_comm (((n : ℝ) - 1) ^ 2) 2]
    rwa [halg]
  have hpeano := neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    f K hK0 hsemi'
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤ (17 / 144) * M := by
    have hcongr : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) =
        (M / 12) * ∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [K]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hcongr]
    have h17 := sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seventeen_twelfths N
    have hmul := mul_le_mul_of_nonneg_left h17 (by linarith : 0 ≤ M / 12)
    linarith
  linarith

/-- **Cutoff-Independent `-(17 / 144) (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_seventeen_one_forty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(17 / 144) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤
      secantNumeratorCellDefect f.1 N := by
  refine neg_seventeen_one_forty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    f (add_nonneg (spectralSecondMoment_nonneg f.1) (spectralFirstMoment_nonneg f.1)) N
    fun n hn x hx => ?_
  rw [Finset.mem_Icc] at hn
  have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectral_second_add_first
    f hint1 hint2 hn.1 hx
  linarith [(abs_le.mp h).1]

/-- **Upgraded Hybrid Cell-Split Semiconcavity Theorem (`-(1 / 3) L - (5 / 144) M ≤ secantNumeratorCellDefect`)**: -/
theorem neg_third_first_sub_five_one_forty_fourths_second_le_secantNumeratorCellDefect_of_hybrid
    (f : WeilTestFn) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℕ)
    (hcell2 : ∀ x ∈ Icc (1 : ℝ) 2,
      -(2 * L) * cellParabola 2 x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x)
    (hcell3 : ∀ n ∈ Finset.Icc 3 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(1 / 3) * L - (5 / 144) * M ≤ secantNumeratorCellDefect f.1 N := by
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
      linarith [hcell2 x hx']
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
        (1 / 3) * L + (5 / 144) * M := by
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
      have h512 := sum_Icc_three_inv_sq_pred_mul_sqrt_pred_le_five_twelfths N
      have hmul := mul_le_mul_of_nonneg_left h512 (by linarith : 0 ≤ M / 12)
      linarith
    · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
      linarith
  linarith

/-- **Upgraded Hybrid Spectral Bound `-(5 / 144) spectralSecondMoment f.1 - (53 / 144) spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_five_one_forty_fourths_second_sub_fifty_three_one_forty_fourths_first_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(5 / 144) * spectralSecondMoment f.1 - (53 / 144) * spectralFirstMoment f.1 ≤
      secantNumeratorCellDefect f.1 N := by
  have hhyb := neg_third_first_sub_five_one_forty_fourths_second_le_secantNumeratorCellDefect_of_hybrid
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

/-! ## Section 3: Unconditional Coercivity up to `spectralSecondMoment F / ∫ ‖F‖² < 224 / 57 > 3.9298` and `218 / 51 > 4.2745` on the Prime-Blind Cone -/

/-- **Cutoff-Independent `-(17 / 96) spectralSecondMoment f.1 - (17 / 144) ∫ ‖f.1‖² ≤ secantNumeratorCellDefect f.1 N`
at Spectral Scale `λ = 1`**: -/
theorem neg_seventeen_ninety_sixths_spectralSecondMoment_sub_seventeen_one_forty_fourths_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(17 / 96) * spectralSecondMoment f.1 - (17 / 144) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have h1 := neg_seventeen_one_forty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h2 := spectralFirstMoment_le_half_spectralSecondMoment_add_l2 f hint1 hint2
  linarith

/-- **Pure Second-Moment `(491 / 720) ∫ ‖f.1‖² - (17 / 96) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (`λ = 1`, Critical Ratio `982 / 255 > 3.8509`)**:
absorbing `(17 / 144) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²` positive surplus leaves
`4 / 5 - 17 / 144 = 491 / 720 > 2 / 3` and `(17 / 144) * (3 / 2) = 17 / 96`! -/
theorem four_ninety_one_seven_twentieths_l2_sub_seventeen_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (491 / 720) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (17 / 96) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_seventeen_ninety_sixths_spectralSecondMoment_sub_seventeen_one_forty_fourths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- **Prime-Blind Cone `(109 / 144) ∫ ‖f.1‖² - (17 / 96) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `218 / 51 > 4.2745`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(17 / 144) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖²` origin surplus leaves `7 / 8 - 17 / 144 = 109 / 144 > 3 / 4`! -/
theorem one_hundred_nine_one_forty_fourths_l2_sub_seventeen_ninety_sixths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (109 / 144) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (17 / 96) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_seventeen_ninety_sixths_spectralSecondMoment_sub_seventeen_one_forty_fourths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- Specializing `spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2` at
`lam = 17 / 20` (where `17 / (144 * lam) = 5 / 36` cancels the `17`!) gives
`spectralFirstMoment f.1 ≤ (17 / 40) * spectralSecondMoment f.1 + (20 / 17) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectralFirstMoment_le_seventeen_fortieths_spectralSecondMoment_add_twenty_seventeenths_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ≤
      (17 / 40) * spectralSecondMoment f.1 + (20 / 17) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have h := spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2
    f hint1 hint2 (by norm_num : (0 : ℝ) < 17 / 20)
  linarith

/-- **Cutoff-Independent `-(323 / 1920) spectralSecondMoment f.1 - (5 / 36) ∫ ‖f.1‖² ≤ secantNumeratorCellDefect f.1 N`
at Spectral Scale `λ = 17 / 20`**: -/
theorem neg_three_twenty_three_nineteen_twentieths_spectralSecondMoment_sub_five_thirty_sixths_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(323 / 1920) * spectralSecondMoment f.1 - (5 / 36) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have h1 := neg_seventeen_one_forty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h2 := spectralFirstMoment_le_seventeen_fortieths_spectralSecondMoment_add_twenty_seventeenths_l2
    f hint1 hint2
  linarith

/-- **Pure Second-Moment `(119 / 180) ∫ ‖f.1‖² - (323 / 1920) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (`λ = 17 / 20`, Critical Ratio `224 / 57 > 3.9298`)**:
because `119 = 7 * 17` and `323 = 19 * 17`, the factor `17` cancels identically in the critical
ratio `(119 / 180) / (323 / 1920) = 224 / 57`! -/
theorem one_nineteen_one_eightieths_l2_sub_three_twenty_three_nineteen_twentieths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (119 / 180) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (323 / 1920) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_three_twenty_three_nineteen_twentieths_spectralSecondMoment_sub_five_thirty_sixths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (224 / 57 - δ) ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_two_twenty_four_fifty_sevenths_of_cosh_zero
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
      (224 / 57 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (3840 / (323 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h323δ : 0 < 323 * δ := by linarith
  have hθδ_le : 3840 / (323 * δ) ≤ θ := le_max_right _ _
  have hθδ : 3840 ≤ θ * (323 * δ) := (div_le_iff₀ h323δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_three_twenty_three_nineteen_twentieths_spectralSecondMoment_sub_five_thirty_sixths_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint1 hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (323 / 1920) * θ)
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
