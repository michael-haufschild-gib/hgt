import GaloisForLFunctions.RHTower.MarkovEuclideanCosLogCurvatureAndFivePointSevenRatioPBAP

/-!
# The Exact Logarithmic Secant Comparison Theorem, the `1 / ((n - 1)(2n - 1))` Parabola Bound for `log x - cellSecant log n x`, and Coercivity up to `spectralSecondMoment / L² < 257 / 31 > 8.290`

In Module 51 through Module 55, we bounded `cosLogProfileDeriv2 r t` on each unit cell `[n - 1, n]`
by replacing the exact `1 / t ^ 2` factor with its left-endpoint value `1 / (n - 1) ^ 2`. On the
first cell `n = 2` (`[1, 2]`), however, `1 / t ^ 2` drops by a factor of `4` from `1` at `t = 1`
down to `1 / 4` at `t = 2`, so replacing `1 / t ^ 2` by `1` on `[1, 2]` accounted for `12 / 17 > 70%`
of the entire curvature cost `17 / 144`!

In this module, we eliminate the left-endpoint constant replacement `1 / t ^ 2 ≤ 1 / (n - 1) ^ 2`
by comparing `g x - cellSecant g n x` directly against the **exact logarithmic secant defect**
`log x - cellSecant log n x`, whose second derivative is `-1 / x ^ 2` **identically**:

1. **Section 1 (The Exact Logarithmic Secant Comparison Theorem and the `1 / ((n - 1)(2n - 1))`
   Parabola Bound for `log x - cellSecant log n x`):**
   - For any `0 < a ≤ b`, applying the Mean Value Theorem to `t ↦ log t - t / (2a) + a / (2t)` and
     `t ↦ log t - (2 / m) * t + t ^ 2 / (2 m ^ 2)` (`m = (a + b) / 2`) proves the sharp two-sided
     Hermite–Hadamard logarithmic inequalities (`log_sub_log_le_half_mul_inv_add_inv` and
     `two_mul_sub_div_add_le_log_sub_log`):
     `2 * (b - a) / (a + b) ≤ log b - log a ≤ ((b - a) / 2) * (1 / a + 1 / b)`.
   - Substituting these into Module 50's divided-difference factorization
     `sub_cellSecant_eq_cellParabola_mul_slope_diff` for `log` on `[n - 1, n]` (`2 ≤ n`) and using
     the polynomial positivity identity `(2n - 1)(x + n) - 4(n - 1)x = (2n - 3)(n - x) + 2n > 0`
     proves (`log_sub_cellSecant_log_le_inv_pred_mul_two_mul_sub_one_mul_cellParabola`):
     `log x - cellSecant log n x ≤ (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x`!
     At `n = 2` (`[1, 2]`), this cuts the parabola coefficient from `1 / 2` down to `1 / 3` (an
     exact `2 / 3` reduction!), and at `n = 3` (`[2, 3]`) from `1 / 8` down to `1 / 10`.
   - Applying Module 51's `neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le` with `B = 0`
     to `g t ± A * log t` proves the **Exact Logarithmic Secant Comparison Theorem**
     (`abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq`): if `|g'' t| ≤ A / t ^ 2`
     on `[n - 1, n]`, then
     `|g x - cellSecant g n x| ≤ A * (log x - cellSecant log n x) ≤ (A / ((n - 1) * (2n - 1))) * cellParabola n x`!

2. **Section 2 (The `31 / 360` Series Bound for `1 / ((n - 1)(2n - 1) √(n - 1))` and
   `-(31 / 360) (spectralSecondMoment + L²) ≤ secantNumeratorCellDefect`):**
   - Summing `1 / ((n - 1)(2n - 1) √(n - 1))` by isolating `n = 2` (`1 / 3`), `n = 3` (`1 / (10√2)`),
     and `n = 4` (`1 / (21√3)`), with `1 / (10√2) + 1 / (21√3) ≤ 1 / 10` and the `n ≥ 5` tail bounded
     by `(1 / 2) * (1 / 6) = 1 / 12`, yields (`sum_Icc_two_inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_thirty_one_sixtieths`):
     `∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * √((n : ℝ) - 1)) ≤ 1 / 3 + 1 / 10 + 1 / 12 = 31 / 60`.
   - Multiplying by `1 / 6` (from `∫ cellParabola = 1 / 6`) reduces the curvature coefficient from
     `17 / 144 ≈ 0.11806` to **`31 / 360 ≈ 0.08611`**
     (`neg_thirty_one_three_sixtieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect`):
     `-(31 / 360) * (spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) ≤ secantNumeratorCellDefect f.1 N`!

3. **Section 3 (The `(257 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Coercivity Law,
   the `(284 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Prime-Blind Cone Law, and
   Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (257 / 31 - δ) ∫ ‖F‖² > 8.290 ∫ ‖F‖²`):**
   - Because both `5` and `8` divide `360` (`4 / 5 = 288 / 360` and `7 / 8 = 315 / 360`), absorbing
     `(31 / 360) * ∫ ‖f.1‖²` yields common-denominator coercivity laws:
     - `(257 / 360) * ∫ ‖f.1‖² - (31 / 360) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`257 / 31 > 8.2903`**!), and
     - on the Prime-Blind Cone (`logVector f = 0`),
       `(284 / 360) * ∫ ‖f.1‖² - (31 / 360) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
       (critical ratio **`284 / 31 > 9.1612`**!).
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

/-! ## Section 1: The Exact Logarithmic Secant Comparison Theorem and the `1 / ((n - 1)(2n - 1))` Parabola Bound for `log x - cellSecant log n x` -/

/-- **Trapezoidal / Hermite–Hadamard Upper Bound for `Real.log b - Real.log a`**:
for any `0 < a ≤ b`, `Real.log b - Real.log a ≤ ((b - a) / 2) * (1 / a + 1 / b)`. -/
theorem log_sub_log_le_half_mul_inv_add_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ ((b - a) / 2) * (1 / a + 1 / b) := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let φ : ℝ → ℝ := fun t => Real.log t - (1 / (2 * a)) * t + (a / 2) * t⁻¹
  let φ' : ℝ → ℝ := fun t => t⁻¹ - (1 / (2 * a)) * 1 + (a / 2) * (-(t ^ 2)⁻¹)
  have hd : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    exact ((Real.hasDerivAt_log ht_pos.ne').sub
      ((hasDerivAt_id t).const_mul (1 / (2 * a)))).add
      ((hasDerivAt_inv ht_pos.ne').const_mul (a / 2))
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope φ φ' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hφ'_le : φ' c ≤ 0 := by
    have hφ'_eq : φ' c = -(c - a) ^ 2 / (2 * a * c ^ 2) := by
      dsimp [φ']
      have ha0 : a ≠ 0 := ha.ne'
      have hc0 : c ≠ 0 := hc_pos.ne'
      field_simp [ha0, hc0]
      ring
    rw [hφ'_eq, neg_div]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hdiff_eq : φ b - φ a = φ' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_le : φ b - φ a ≤ 0 := by
    rw [hdiff_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hφ'_le hba_pos.le
  have halg : φ b - φ a =
      (Real.log b - Real.log a) - ((b - a) / 2) * (1 / a + 1 / b) := by
    dsimp [φ]
    have ha0 : a ≠ 0 := ha.ne'
    have hb0 : b ≠ 0 := hb.ne'
    field_simp [ha0, hb0]
    ring
  linarith

/-- **Midpoint / Hermite–Hadamard Lower Bound for `Real.log b - Real.log a`**:
for any `0 < a ≤ b`, `2 * (b - a) / (a + b) ≤ Real.log b - Real.log a`. -/
theorem two_mul_sub_div_add_le_log_sub_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) ≤ Real.log b - Real.log a := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · norm_num
  have hb : 0 < b := ha.trans hab_lt
  let m : ℝ := (a + b) / 2
  have hm_pos : 0 < m := by dsimp [m]; linarith
  let η : ℝ → ℝ := fun t => Real.log t - (2 / m) * t + (1 / (2 * m ^ 2)) * (t * t)
  let η' : ℝ → ℝ := fun t => t⁻¹ - (2 / m) * 1 + (1 / (2 * m ^ 2)) * (1 * t + t * 1)
  have hd : ∀ t ∈ Icc a b, HasDerivAt η (η' t) t := by
    intro t ht
    have ht_pos : 0 < t := ha.trans_le ht.1
    exact ((Real.hasDerivAt_log ht_pos.ne').sub
      ((hasDerivAt_id t).const_mul (2 / m))).add
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (1 / (2 * m ^ 2)))
  obtain ⟨c, hc, hc_slope⟩ := exists_hasDerivAt_eq_slope η η' hab_lt
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩)
  have hc_pos : 0 < c := ha.trans hc.1
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  have hη'_nonneg : 0 ≤ η' c := by
    have hη'_eq : η' c = (c - m) ^ 2 / (m ^ 2 * c) := by
      dsimp [η']
      have hm0 : m ≠ 0 := hm_pos.ne'
      have hc0 : c ≠ 0 := hc_pos.ne'
      field_simp [hm0, hc0]
      ring
    rw [hη'_eq]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hdiff_eq : η b - η a = η' c * (b - a) := ((eq_div_iff hba_pos.ne').mp hc_slope).symm
  have hdiff_nonneg : 0 ≤ η b - η a := by
    rw [hdiff_eq]
    exact mul_nonneg hη'_nonneg hba_pos.le
  have halg : η b - η a =
      (Real.log b - Real.log a) - 2 * (b - a) / (a + b) := by
    dsimp [η, m]
    have hab0 : a + b ≠ 0 := (add_pos ha hb).ne'
    field_simp [hab0]
    ring
  linarith

/-- **Sharp `1 / ((n - 1)(2n - 1))` Parabola Bound for `Real.log x - cellSecant Real.log n x` on `[n - 1, n]`**:
for every `2 ≤ n` and `x ∈ Icc (n - 1) n`,
`Real.log x - cellSecant Real.log n x ≤ (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x`. -/
theorem log_sub_cellSecant_log_le_inv_pred_mul_two_mul_sub_one_mul_cellParabola
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    Real.log x - cellSecant Real.log n x ≤
      (1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx1
  · rw [cellParabola_left_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  rcases eq_or_lt_of_le hx.2 with rfl | hx2
  · rw [cellParabola_right_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hx_pos : 0 < x := hn1_pos.trans hx1
  have h2n1_pos : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hxn_pos : 0 < x + (n : ℝ) := by linarith
  have hx1_pos : 0 < x - ((n : ℝ) - 1) := sub_pos.mpr hx1
  have hx2_pos : 0 < (n : ℝ) - x := sub_pos.mpr hx2
  have hleft_slope :
      (Real.log x - Real.log ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) ≤
        (1 / 2) * (1 / ((n : ℝ) - 1) + 1 / x) := by
    rw [div_le_iff₀ hx1_pos]
    have htrap := log_sub_log_le_half_mul_inv_add_inv hn1_pos hx.1
    linarith
  have hright_slope :
      2 / (x + (n : ℝ)) ≤ (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) := by
    rw [le_div_iff₀ hx2_pos]
    have hmid := two_mul_sub_div_add_le_log_sub_log hx_pos hx.2
    have heq : 2 / (x + (n : ℝ)) * ((n : ℝ) - x) = 2 * ((n : ℝ) - x) / (x + (n : ℝ)) := by ring
    linarith
  have hmono :
      (1 / 2) * (1 / ((n : ℝ) - 1) + 1 / x) - 2 / (x + (n : ℝ)) ≤
        1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
    have hpf : 1 / ((n : ℝ) - 1) - 2 / (2 * (n : ℝ) - 1) =
        1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
      rw [div_sub_div 1 2 hn1_pos.ne' h2n1_pos.ne']
      ring
    have hdiff1 : 1 / ((n : ℝ) - 1) - 1 / x =
        (x - ((n : ℝ) - 1)) / (((n : ℝ) - 1) * x) := by
      rw [div_sub_div 1 1 hn1_pos.ne' hx_pos.ne']
      ring
    have hdiff2 : 2 / (2 * (n : ℝ) - 1) - 2 / (x + (n : ℝ)) =
        (2 * (x - ((n : ℝ) - 1))) / ((2 * (n : ℝ) - 1) * (x + (n : ℝ))) := by
      rw [div_sub_div 2 2 h2n1_pos.ne' hxn_pos.ne']
      ring
    have hden_cmp :
        4 / ((2 * (n : ℝ) - 1) * (x + (n : ℝ))) ≤ 1 / (((n : ℝ) - 1) * x) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hden_cmp
      (by positivity : 0 ≤ (1 / 2) * (x - ((n : ℝ) - 1)))
    have hmul_lhs :
        (1 / 2) * (x - ((n : ℝ) - 1)) * (4 / ((2 * (n : ℝ) - 1) * (x + (n : ℝ)))) =
          (2 * (x - ((n : ℝ) - 1))) / ((2 * (n : ℝ) - 1) * (x + (n : ℝ))) := by ring
    have hmul_rhs :
        (1 / 2) * (x - ((n : ℝ) - 1)) * (1 / (((n : ℝ) - 1) * x)) =
          (1 / 2) * ((x - ((n : ℝ) - 1)) / (((n : ℝ) - 1) * x)) := by ring
    linarith
  have hslope_le :
      (Real.log x - Real.log ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) -
        (Real.log (n : ℝ) - Real.log x) / ((n : ℝ) - x) ≤
      1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) := by
    linarith
  rw [sub_cellSecant_eq_cellParabola_mul_slope_diff Real.log n ⟨hx1, hx2⟩, mul_comm]
  exact mul_le_mul_of_nonneg_right hslope_le (cellParabola_nonneg_of_mem_Icc hx)

/-- **Exact Logarithmic Secant Comparison Theorem (One-Sided Form)**:
if `g'' t ≤ A / t ^ 2` on `[n - 1, n]` (`2 ≤ n`), then for every `x ∈ [n - 1, n]`,
`-A * (Real.log x - cellSecant Real.log n x) ≤ g x - cellSecant g n x`. -/
theorem neg_mul_log_sub_cellSecant_le_sub_cellSecant_of_deriv2_le_div_sq
    {g g' g'' : ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n) {A : ℝ}
    (hd1 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g (g' t) t)
    (hd2 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g' (g'' t) t)
    (hA : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), g'' t ≤ A / t ^ 2)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    -A * (Real.log x - cellSecant Real.log n x) ≤ g x - cellSecant g n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t := fun t ht => by linarith [ht.1]
  have h := neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le
    (g := fun t => g t + A * Real.log t)
    (g' := fun t => g' t + A * t⁻¹)
    (g'' := fun t => g'' t + A * (-(t ^ 2)⁻¹))
    (B := 0) n
    (fun t ht => (hd1 t ht).add ((Real.hasDerivAt_log (ht_pos t ht).ne').const_mul A))
    (fun t ht => (hd2 t ht).add ((hasDerivAt_inv (ht_pos t ht).ne').const_mul A))
    (fun t ht => by
      have hAt := hA t ht
      rw [div_eq_mul_inv] at hAt
      linarith) hx
  have hsec :
      (g x + A * Real.log x) - cellSecant (fun t => g t + A * Real.log t) n x =
        (g x - cellSecant g n x) + A * (Real.log x - cellSecant Real.log n x) := by
    unfold cellSecant
    ring
  linarith

/-- **Exact Logarithmic Secant Comparison Theorem (Two-Sided Form)**:
if `|g'' t| ≤ A / t ^ 2` on `[n - 1, n]` (`2 ≤ n`), then for every `x ∈ [n - 1, n]`,
`|g x - cellSecant g n x| ≤ A * (Real.log x - cellSecant Real.log n x)`. -/
theorem abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq
    {g g' g'' : ℝ → ℝ} {n : ℕ} (hn : 2 ≤ n) {A : ℝ}
    (hd1 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g (g' t) t)
    (hd2 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g' (g'' t) t)
    (hA : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), |g'' t| ≤ A / t ^ 2)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |g x - cellSecant g n x| ≤ A * (Real.log x - cellSecant Real.log n x) := by
  have hlow := neg_mul_log_sub_cellSecant_le_sub_cellSecant_of_deriv2_le_div_sq hn hd1 hd2
    (fun t ht => (le_abs_self _).trans (hA t ht)) hx
  have hneg := neg_mul_log_sub_cellSecant_le_sub_cellSecant_of_deriv2_le_div_sq
    (g := fun t => -g t) (g' := fun t => -g' t) (g'' := fun t => -g'' t) hn
    (fun t ht => (hd1 t ht).neg) (fun t ht => (hd2 t ht).neg)
    (fun t ht => (neg_le_abs _).trans (hA t ht)) hx
  have hsec_neg : (-g x) - cellSecant (fun t => -g t) n x = -(g x - cellSecant g n x) := by
    unfold cellSecant
    ring
  rw [hsec_neg] at hneg
  exact abs_le.mpr ⟨by linarith [hlow], by linarith [hneg]⟩

/-! ## Section 2: The `31 / 360` Series Bound for `1 / ((n - 1)(2n - 1) √(n - 1))` and `-(31 / 360) (spectralSecondMoment + L²) ≤ secantNumeratorCellDefect` -/

/-- **Rational Bound on the Isolated `n = 3` and `n = 4` Terms**:
`1 / (10 * Real.sqrt 2) + 1 / (21 * Real.sqrt 3) ≤ 1 / 10` via `181 / 128 ≤ √2` and `19 / 11 ≤ √3`
(`64 / 905 + 11 / 399 = 35491 / 361095 < 1 / 10`). -/
theorem inv_ten_sqrt_two_add_inv_twenty_one_sqrt_three_le_one_tenth :
    1 / (10 * Real.sqrt 2) + 1 / (21 * Real.sqrt 3) ≤ 1 / 10 := by
  have hsqrt2_ge : (181 / 128 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 181 / 128)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (19 / 11 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19 / 11)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_pos : 0 < 10 * Real.sqrt 2 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt3_pos : 0 < 21 * Real.sqrt 3 := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  have h1 : 1 / (10 * Real.sqrt 2) ≤ 64 / 905 := by
    rw [div_le_iff₀ hsqrt2_pos]
    linarith
  have h2 : 1 / (21 * Real.sqrt 3) ≤ 11 / 399 := by
    rw [div_le_iff₀ hsqrt3_pos]
    linarith
  linarith

/-- For every `2 ≤ n`,
`1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) ≤ (1 / 2) * (1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)))`. -/
theorem inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_half_inv_sq {n : ℕ} (hn : 2 ≤ n) :
    1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) ≤
      (1 / 2) * (1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr hn1_pos
  rw [one_div_mul_one_div]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hle : 2 * ((n : ℝ) - 1) ^ 2 ≤ ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hle hsqrt_pos.le
  linarith

/-- **Uniform Cutoff-Independent Bound
`∑_{n=2}^N 1 / ((n - 1)(2n - 1) √(n - 1)) ≤ 31 / 60` for All `N : ℕ`**:
combining `n = 2` (`1 / 3`), `n = 3, 4` (`≤ 1 / 10`), and `n ≥ 5` (`≤ (1 / 2) * (1 / 6) = 1 / 12`)
gives `1 / 3 + 1 / 10 + 1 / 12 = 31 / 60`! -/
theorem sum_Icc_two_inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_thirty_one_sixtieths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) ≤ 31 / 60 := by
  let g : ℕ → ℝ := fun n => 1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))
  have hg2 : g 2 = 1 / 3 := by dsimp [g]; norm_num
  have hg3 : g 3 = 1 / (10 * Real.sqrt 2) := by dsimp [g]; norm_num
  have hg4 : g 4 = 1 / (21 * Real.sqrt 3) := by dsimp [g]; norm_num
  have hg4_nonneg : 0 ≤ g 4 := by rw [hg4]; positivity
  have h34 := inv_ten_sqrt_two_add_inv_twenty_one_sqrt_three_le_one_tenth
  have htail5 : (∑ n ∈ Finset.Icc 5 N, g n) ≤ 1 / 12 := by
    have hle : (∑ n ∈ Finset.Icc 5 N, g n) ≤
        (1 / 2) * ∑ n ∈ Finset.Icc 5 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      exact inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_half_inv_sq (by omega)
    have h5 := sum_Icc_five_inv_sq_pred_mul_sqrt_pred_le_one_sixth N
    linarith
  have htail3 : (∑ n ∈ Finset.Icc 3 N, g n) ≤ 11 / 60 := by
    by_cases hN4 : 4 ≤ N
    · have hsplit3 := sum_Icc_eq_add_sum_Icc_succ g (by omega : 3 ≤ N)
      have hsplit4 := sum_Icc_eq_add_sum_Icc_succ g hN4
      rw [hsplit3, hsplit4, hg3, hg4]
      linarith
    · by_cases hN3 : 3 ≤ N
      · have hN_eq : N = 3 := by omega
        subst hN_eq
        rw [Finset.Icc_self, Finset.sum_singleton]
        linarith [hg3, hg4, hg4_nonneg, h34]
      · rw [Finset.Icc_eq_empty hN3, Finset.sum_empty]
        norm_num
  by_cases hN2 : 2 ≤ N
  · change (∑ n ∈ Finset.Icc 2 N, g n) ≤ 31 / 60
    rw [sum_Icc_eq_add_sum_Icc_succ g hN2, hg2]
    linarith
  · rw [Finset.Icc_eq_empty hN2, Finset.sum_empty]
    norm_num

/-- **Cutoff-Independent `-(31 / 360) M ≤ secantNumeratorCellDefect f.1 N` for
`M / ((n - 1)(2n - 1))`-Parabola Bounded Profiles**: -/
theorem neg_thirty_one_three_sixtieths_mul_le_secantNumeratorCellDefect_of_inv_pred_two_mul_sub_one
    (f : WeilTestFn) {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(31 / 360) * M ≤ secantNumeratorCellDefect f.1 N := by
  let K : ℕ → ℝ := fun n => (2 * M) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))
  have hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    dsimp [K]
    exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hsemi' : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x := by
    intro n hn x hx
    have hpt := hsemi n hn x hx
    have halg : -(K n / 2) * cellParabola n x =
        -(M / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x := by
      dsimp [K]
      ring
    rwa [halg]
  have hpeano := neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    f K hK0 hsemi'
  have hsum_le :
      (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤ (31 / 360) * M := by
    have hcongr : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) =
        (M / 6) * ∑ n ∈ Finset.Icc 2 N,
          1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [K]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hcongr]
    have h31 := sum_Icc_two_inv_pred_mul_two_mul_sub_one_mul_sqrt_pred_le_thirty_one_sixtieths N
    have hmul := mul_le_mul_of_nonneg_left h31 (by linarith : 0 ≤ M / 6)
    linarith
  linarith

/-- **Pointwise `(r ^ 2 + 1 / 2) / t ^ 2` Bound on `cosLogProfileDeriv2 r t` for `0 < t`**: -/
theorem abs_cosLogProfileDeriv2_le_sq_add_half_div_sq
    (r : ℝ) {t : ℝ} (ht : 0 < t) :
    |cosLogProfileDeriv2 r t| ≤ (r ^ 2 + 1 / 2) / t ^ 2 := by
  unfold cosLogProfileDeriv2
  rw [abs_mul, abs_inv, abs_of_pos (sq_pos_of_pos ht), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right
    (abs_neg_sq_mul_cos_add_mul_sin_le_sq_add_half r (r * Real.log t)) (sq_nonneg t)

/-- **Sharp `(r ^ 2 + 1 / 2) / ((n - 1)(2n - 1))` Parabola Bound for `cosLogProfile r` on `[n - 1, n]`**: -/
theorem abs_cosLogProfile_sub_cellSecant_le_sq_add_half_div_pred_mul_two_mul_sub_one
    (r : ℝ) {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤
      ((r ^ 2 + 1 / 2) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t := fun t ht => by linarith [ht.1]
  have hcmp := abs_sub_cellSecant_le_mul_log_sub_cellSecant_of_abs_deriv2_le_div_sq hn
    (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
    (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
    (fun t ht => abs_cosLogProfileDeriv2_le_sq_add_half_div_sq r (ht_pos t ht)) hx
  have hlog := log_sub_cellSecant_log_le_inv_pred_mul_two_mul_sub_one_mul_cellParabola hn hx
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ r ^ 2 + 1 / 2)
  have halg : (r ^ 2 + 1 / 2) * ((1 / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x) =
      ((r ^ 2 + 1 / 2) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x := by ring
  linarith

/-- **Sharp `(spectralSecondMoment f.1 + ∫ ‖f.1‖²) / ((n - 1)(2n - 1))` Parabola Bound for
`weilSymmetricLogNumerator f.1` on `[n - 1, n]` (`2 ≤ n`)**: -/
theorem abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2_div_pred_two_mul_sub_one
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
      ((spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) /
        (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x := by
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
  have hint_diff : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x)) := by
    have hlin :
        (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))) =
        fun r : ℝ =>
          ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r x) -
            (((n : ℝ) - x) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r ((n : ℝ) - 1))) +
              (x - ((n : ℝ) - 1)) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r (n : ℝ)))) := by
      ext r
      unfold cellSecant
      ring
    rw [hlin]
    exact (hcos x).sub (((hcos ((n : ℝ) - 1)).const_mul _).add ((hcos (n : ℝ)).const_mul _))
  rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f n x,
    abs_mul, abs_of_pos (div_pos one_pos Real.two_pi_pos)]
  have hrhs_eq :
      ((spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) /
        (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x =
      (1 / (2 * π)) * ∫ r : ℝ,
        (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
          (cellParabola n x / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) := by
    have hplanch' : (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        (1 / (2 * π)) * ((1 / 2) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) := by
      linarith [hplanch]
    unfold spectralSecondMoment
    rw [integral_mul_const, integral_add hint2 ((hsq.mul_const 2).const_mul (1 / 2)),
      integral_const_mul, hplanch']
    ring
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans ?_)
    (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono hint_diff.abs
    ((hint2.add ((hsq.mul_const 2).const_mul (1 / 2))).mul_const _) fun r => ?_
  dsimp
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpeano := abs_cosLogProfile_sub_cellSecant_le_sq_add_half_div_pred_mul_two_mul_sub_one r hn hx
  have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hpeano hweight
  have halg : ‖paperFT f.1 r‖ ^ 2 * 2 *
      (((r ^ 2 + 1 / 2) / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) * cellParabola n x) =
      (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
        (cellParabola n x / (((n : ℝ) - 1) * (2 * (n : ℝ) - 1))) := by ring
  linarith

/-- **Cutoff-Independent `-(31 / 360) (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_thirty_one_three_sixtieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(31 / 360) * (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine neg_thirty_one_three_sixtieths_mul_le_secantNumeratorCellDefect_of_inv_pred_two_mul_sub_one
    f (add_nonneg (spectralSecondMoment_nonneg f.1) hnorm_nonneg) N
    fun n hn x hx => ?_
  rw [Finset.mem_Icc] at hn
  have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2_div_pred_two_mul_sub_one
    f hint2 hn.1 hx
  linarith [(abs_le.mp h).1]

/-! ## Section 3: The `(257 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Coercivity Law, the `(284 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Prime-Blind Cone Law, and Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (257 / 31 - δ) ∫ ‖F‖² > 8.290 ∫ ‖F‖²` -/

/-- **Pure Second-Moment `(257 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `257 / 31 > 8.2903`)**:
absorbing `(31 / 360) * ∫ ‖f.1‖²` into `(4 / 5) * ∫ ‖f.1‖² = (288 / 360) * ∫ ‖f.1‖²` leaves
`257 / 360 > 5 / 7` with matching denominator `360`! -/
theorem two_fifty_seven_three_sixtieths_l2_sub_thirty_one_three_sixtieths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (257 / 360) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (31 / 360) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_thirty_one_three_sixtieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Prime-Blind Cone `(284 / 360) ∫ ‖f.1‖² - (31 / 360) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `284 / 31 > 9.1612`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(31 / 360) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖² = (315 / 360) * ∫ ‖f.1‖²` origin surplus leaves `284 / 360 = 71 / 90`! -/
theorem two_eighty_four_three_sixtieths_l2_sub_thirty_one_three_sixtieths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (284 / 360) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (31 / 360) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_thirty_one_three_sixtieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (257 / 31 - δ) ∫ ‖F‖² > 8.290 ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_two_fifty_seven_thirty_firsts_of_cosh_zero
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
    {δ : ℝ} (hδ : 0 < δ)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (257 / 31 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (720 / (31 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h31δ : 0 < 31 * δ := by linarith
  have hθδ_le : 720 / (31 * δ) ≤ θ := le_max_right _ _
  have hθδ : 720 ≤ θ * (31 * δ) := (div_le_iff₀ h31δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_thirty_one_three_sixtieths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (31 / 360) * θ)
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
