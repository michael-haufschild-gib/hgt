import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Curvature of the complete trivial-zero correction

The first two derivative series converge uniformly on every half-line bounded away from one.
The second derivative sums to `1 / (x² (x² - 1))`. This is smaller than half the curvature of
`x log x` for `x ≥ 2`, uniformly over the affine terms of every arithmetic lag cell.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

private def trivialZeroTerm (k : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(2 * (k : ℤ) + 2)) / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3))

private def trivialZeroSlopeTerm (k : ℕ) (x : ℝ) : ℝ :=
  -(x ^ (-(2 * (k : ℤ) + 3))) / (2 * (k : ℝ) + 3)

/-- The first derivative of the complete trivial-zero correction. -/
def trivialZeroSlope (x : ℝ) : ℝ := ∑' k : ℕ, trivialZeroSlopeTerm k x

private theorem trivialZeroTerm_eq (k : ℕ) (x : ℝ) :
    trivialZeroTerm k x =
      (x ^ (2 * (k + 1)))⁻¹ / (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by
  rw [trivialZeroTerm, show 2 * (k : ℤ) + 2 = ((2 * (k + 1) : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]

private theorem trivialZeroSeriesReal_eq_tsum (x : ℝ) :
    RHTower.trivialZeroSeriesReal x = ∑' k : ℕ, trivialZeroTerm k x := by
  unfold RHTower.trivialZeroSeriesReal
  exact tsum_congr fun k => (trivialZeroTerm_eq k x).symm

private theorem hasDerivAt_trivialZeroTerm (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (trivialZeroTerm k) (trivialZeroSlopeTerm k x) x := by
  unfold trivialZeroTerm trivialZeroSlopeTerm
  convert! (hasDerivAt_zpow (-(2 * (k : ℤ) + 2)) x (Or.inl hx.ne')).div_const
    (2 * ((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) using 1
  rw [show -(2 * (k : ℤ) + 2) - 1 = -(2 * (k : ℤ) + 3) by ring]
  push_cast
  have hk2 : 2 * ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk3 : 2 * (k : ℝ) + 3 ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_trivialZeroSlopeTerm (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (trivialZeroSlopeTerm k) (x ^ (-(2 * (k : ℤ) + 4))) x := by
  unfold trivialZeroSlopeTerm
  convert! ((hasDerivAt_zpow (-(2 * (k : ℤ) + 3)) x (Or.inl hx.ne')).neg).div_const
    (2 * (k : ℝ) + 3) using 1
  rw [show -(2 * (k : ℤ) + 3) - 1 = -(2 * (k : ℤ) + 4) by ring]
  push_cast
  have hk3 : 2 * (k : ℝ) + 3 ≠ 0 := by positivity
  field_simp

private theorem inversePower_le_geometric {r x : ℝ} (hr : 1 < r) (hrx : r ≤ x)
    {k p : ℕ} (hkp : k ≤ p) : x ^ (-(p : ℤ)) ≤ (r⁻¹) ^ k := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := hr0.trans_le hrx
  rw [zpow_neg, zpow_natCast, inv_pow]
  apply (inv_le_inv₀ (pow_pos hx0 p) (pow_pos hr0 k)).mpr
  exact (pow_le_pow_left₀ hr0.le hrx k).trans (pow_le_pow_right₀ (hr.le.trans hrx) hkp)

private theorem norm_trivialZeroSlopeTerm_le {r x : ℝ} (hr : 1 < r) (hrx : r ≤ x)
    (k : ℕ) : ‖trivialZeroSlopeTerm k x‖ ≤ (r⁻¹) ^ k := by
  have hx0 : 0 < x := (zero_lt_one.trans hr).trans_le hrx
  have hd : 0 < 2 * (k : ℝ) + 3 := by positivity
  rw [Real.norm_eq_abs, trivialZeroSlopeTerm, abs_div, abs_neg,
    abs_of_pos (zpow_pos hx0 _), abs_of_pos hd]
  calc x ^ (-(2 * (k : ℤ) + 3)) / (2 * (k : ℝ) + 3)
      ≤ x ^ (-(2 * (k : ℤ) + 3)) := by
        apply (div_le_iff₀ hd).mpr
        exact le_mul_of_one_le_right (zpow_pos hx0 _).le
          (by linarith only [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k])
    _ ≤ (r⁻¹) ^ k := by
      rw [show 2 * (k : ℤ) + 3 = ((2 * k + 3 : ℕ) : ℤ) by push_cast; ring]
      exact inversePower_le_geometric hr hrx (by omega)

private theorem norm_trivialZeroCurvatureTerm_le {r x : ℝ} (hr : 1 < r) (hrx : r ≤ x)
    (k : ℕ) : ‖x ^ (-(2 * (k : ℤ) + 4))‖ ≤ (r⁻¹) ^ k := by
  rw [Real.norm_eq_abs, abs_of_pos (zpow_pos ((zero_lt_one.trans hr).trans_le hrx) _),
    show 2 * (k : ℤ) + 4 = ((2 * k + 4 : ℕ) : ℤ) by push_cast; ring]
  exact inversePower_le_geometric hr hrx (by omega)

private theorem summable_trivialZeroSlopeTerm {x : ℝ} (hx : 1 < x) :
    Summable (fun k => trivialZeroSlopeTerm k x) :=
  (summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hx)).le
    (inv_lt_one_of_one_lt₀ hx)).of_norm_bounded
      (fun k => norm_trivialZeroSlopeTerm_le hx le_rfl k)

/-- Differentiating the complete trivial-zero series once is valid on `(1, infinity)`. -/
theorem hasDerivAt_trivialZeroSeriesReal {x : ℝ} (hx : 1 < x) :
    HasDerivAt RHTower.trivialZeroSeriesReal (trivialZeroSlope x) x := by
  let r : ℝ := (x + 1) / 2
  have hr : 1 < r := by dsimp [r]; linarith only [hx]
  have hrx : r < x := by dsimp [r]; linarith only [hx]
  have hmajor := summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hr)).le
    (inv_lt_one_of_one_lt₀ hr)
  have hs : Summable (fun k => trivialZeroTerm k x) :=
    (RHTower.summable_trivialZeroSeriesReal_term hx.le).congr
      (fun k => (trivialZeroTerm_eq k x).symm)
  have h := hasDerivAt_tsum_of_isPreconnected (t := Ioi r)
    (g := trivialZeroTerm) (g' := trivialZeroSlopeTerm) (y₀ := x) (y := x)
    hmajor isOpen_Ioi isPreconnected_Ioi
    (fun k y hy => hasDerivAt_trivialZeroTerm k ((zero_lt_one.trans hr).trans hy))
    (fun k y hy => norm_trivialZeroSlopeTerm_le hr hy.le k) hrx hs hrx
  change HasDerivAt (fun y => RHTower.trivialZeroSeriesReal y) (trivialZeroSlope x) x
  simpa only [trivialZeroSeriesReal_eq_tsum, trivialZeroSlope] using! h

private theorem tsum_trivialZeroCurvature {x : ℝ} (hx : 1 < x) :
    (∑' k : ℕ, x ^ (-(2 * (k : ℤ) + 4))) = 1 / (x ^ 2 * (x ^ 2 - 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : 0 < x⁻¹ := inv_pos.mpr hx0
  have hi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hq : (x⁻¹) ^ 2 < 1 := by
    have h := mul_pos hi (sub_pos.mpr hi1)
    nlinarith only [hi1, h]
  have heq : (fun k : ℕ => x ^ (-(2 * (k : ℤ) + 4))) =
      fun k => (x⁻¹) ^ 4 * ((x⁻¹) ^ 2) ^ k := by
    funext k
    rw [show 2 * (k : ℤ) + 4 = ((2 * k + 4 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, ← inv_pow, pow_add, pow_mul]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hq]
  have hx2 : x ^ 2 - 1 ≠ 0 := by nlinarith only [hx]
  have hq0 : 1 - (x⁻¹) ^ 2 ≠ 0 := (sub_pos.mpr hq).ne'
  field_simp

/-- The second derivative of the complete trivial-zero correction is a rational function. -/
theorem hasDerivAt_trivialZeroSlope {x : ℝ} (hx : 1 < x) :
    HasDerivAt trivialZeroSlope (1 / (x ^ 2 * (x ^ 2 - 1))) x := by
  let r : ℝ := (x + 1) / 2
  have hr : 1 < r := by dsimp [r]; linarith only [hx]
  have hrx : r < x := by dsimp [r]; linarith only [hx]
  have hmajor := summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hr)).le
    (inv_lt_one_of_one_lt₀ hr)
  have h := hasDerivAt_tsum_of_isPreconnected (t := Ioi r)
    (g := trivialZeroSlopeTerm) (g' := fun k y => y ^ (-(2 * (k : ℤ) + 4)))
    (y₀ := x) (y := x) hmajor isOpen_Ioi isPreconnected_Ioi
    (fun k y hy => hasDerivAt_trivialZeroSlopeTerm k ((zero_lt_one.trans hr).trans hy))
    (fun k y hy => norm_trivialZeroCurvatureTerm_le hr hy.le k)
    hrx (summable_trivialZeroSlopeTerm hx) hrx
  rwa [tsum_trivialZeroCurvature hx] at h

/-- Beyond two, the logarithmic curvature exceeds the complete trivial-zero curvature by
at least half its reciprocal scale. -/
theorem half_reciprocal_le_log_sub_trivialZero_curvature {x : ℝ} (hx : 2 ≤ x) :
    1 / (2 * x) ≤ x⁻¹ - 1 / (x ^ 2 * (x ^ 2 - 1)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hsq : 3 ≤ x ^ 2 - 1 := by nlinarith only [hx]
  have hprod := mul_le_mul hx hsq (by norm_num : (0 : ℝ) ≤ 3) hx0.le
  have hden : 2 * x ≤ x ^ 2 * (x ^ 2 - 1) := by
    have h := mul_le_mul_of_nonneg_left (show 2 ≤ x * (x ^ 2 - 1) by linarith only [hprod]) hx0.le
    nlinarith only [h]
  have hsmall := one_div_le_one_div_of_le (mul_pos (by norm_num : (0 : ℝ) < 2) hx0) hden
  have heq : x⁻¹ = 2 * (1 / (2 * x)) := by field_simp
  linarith only [hsmall, heq]

#print axioms hasDerivAt_trivialZeroSeriesReal
#print axioms hasDerivAt_trivialZeroSlope
#print axioms half_reciprocal_le_log_sub_trivialZero_curvature

end GaloisForLFunctions.InfiniteRankWeilTheory
