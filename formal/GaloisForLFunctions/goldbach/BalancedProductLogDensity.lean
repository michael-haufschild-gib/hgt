import GaloisForLFunctions.RHTower.LogarithmicLinearEntryConvolution
import Mathlib.Data.PNat.Basic

/-!
# The balanced product density in logarithmic entry coordinates

The difference of two causal entries is the actual logarithmic window.
Its reflection convolution is a compensated sum of four ramps, hence a
nonnegative triangular profile with height `log 2` and exact support.
-/

namespace GaloisForLFunctions.Goldbach

open MeasureTheory

noncomputable section
set_option autoImplicit false

/-- The logarithmic window of the balanced interval, with its literal step endpoints. -/
def balancedLogWindow (X : ℕ+) (s : ℝ) : ℝ :=
  _root_.RHTower.logarithmicUnitEntry (Real.log (X : ℝ)) s -
    _root_.RHTower.logarithmicUnitEntry (Real.log (2 * (X : ℝ))) s

/-- The four entry ramps retain the signed endpoint compensation of the product window. -/
def balancedLogProductDensity (X : ℕ+) (t : ℝ) : ℝ :=
  _root_.RHTower.logarithmicLinearRamp (t - Real.log (X : ℝ) - Real.log (X : ℝ)) -
    _root_.RHTower.logarithmicLinearRamp (t - Real.log (X : ℝ) - Real.log (2 * (X : ℝ))) -
      _root_.RHTower.logarithmicLinearRamp (t - Real.log (2 * (X : ℝ)) - Real.log (X : ℝ)) +
        _root_.RHTower.logarithmicLinearRamp
          (t - Real.log (2 * (X : ℝ)) - Real.log (2 * (X : ℝ)))

private theorem balanced_log_width (X : ℕ+) :
    Real.log (2 * (X : ℝ)) - Real.log (X : ℝ) = Real.log 2 := by
  have hX : (X : ℝ) ≠ 0 := by exact_mod_cast X.pos.ne'
  rw [Real.log_mul (by norm_num) hX]
  ring

private theorem balanced_log_endpoints (X : ℕ+) :
    Real.log (X : ℝ) ≤ Real.log (2 * (X : ℝ)) := by
  have hw := balanced_log_width X
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  linarith only [hw, h2]

/-- The entry difference is precisely the half-open logarithmic interval. -/
theorem balancedLogWindow_eq_indicator (X : ℕ+) (s : ℝ) :
    balancedLogWindow X s =
      (Set.Ico (Real.log (X : ℝ)) (Real.log (2 * (X : ℝ)))).indicator
        (fun _ : ℝ => 1) s := by
  by_cases ha : Real.log (X : ℝ) ≤ s
  · by_cases hb : Real.log (2 * (X : ℝ)) ≤ s
    · simp [balancedLogWindow, _root_.RHTower.logarithmicUnitEntry,
        Set.indicator, ha, hb, not_lt.mpr hb]
    · simp [balancedLogWindow, _root_.RHTower.logarithmicUnitEntry,
        Set.indicator, ha, hb, lt_of_not_ge hb]
  · have hb : ¬ Real.log (2 * (X : ℝ)) ≤ s :=
      fun hb => ha ((balanced_log_endpoints X).trans hb)
    simp [balancedLogWindow, _root_.RHTower.logarithmicUnitEntry, Set.indicator, ha, hb]

private theorem balanced_log_pair_expansion (X : ℕ+) (T s : ℝ) :
    balancedLogWindow X s * balancedLogWindow X (T - s) =
      _root_.RHTower.logarithmicUnitEntry (Real.log (X : ℝ)) s *
          _root_.RHTower.logarithmicUnitEntry (Real.log (X : ℝ)) (T - s) -
        _root_.RHTower.logarithmicUnitEntry (Real.log (X : ℝ)) s *
          _root_.RHTower.logarithmicUnitEntry (Real.log (2 * (X : ℝ))) (T - s) -
        _root_.RHTower.logarithmicUnitEntry (Real.log (2 * (X : ℝ))) s *
          _root_.RHTower.logarithmicUnitEntry (Real.log (X : ℝ)) (T - s) +
        _root_.RHTower.logarithmicUnitEntry (Real.log (2 * (X : ℝ))) s *
          _root_.RHTower.logarithmicUnitEntry (Real.log (2 * (X : ℝ))) (T - s) := by
  unfold balancedLogWindow
  ring

/-- Every finite reflection interval is integrable, including reversed intervals. -/
theorem intervalIntegrable_balancedLogWindow_pair (X : ℕ+) (T l r : ℝ) :
    IntervalIntegrable (fun s => balancedLogWindow X s * balancedLogWindow X (T - s))
      volume l r := by
  have haa := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (X : ℝ)) (Real.log (X : ℝ)) T l r
  have hab := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (X : ℝ)) (Real.log (2 * (X : ℝ))) T l r
  have hba := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (2 * (X : ℝ))) (Real.log (X : ℝ)) T l r
  have hbb := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (2 * (X : ℝ))) (Real.log (2 * (X : ℝ))) T l r
  simp_rw [balanced_log_pair_expansion]
  exact ((haa.sub hab).sub hba).add hbb

/-- The actual window convolution equals the complete signed four-ramp density. -/
theorem integral_balancedLogWindow_pair (X : ℕ+) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, balancedLogWindow X s * balancedLogWindow X (T - s)) =
      balancedLogProductDensity X T := by
  have haa := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (X : ℝ)) (Real.log (X : ℝ)) T 0 T
  have hab := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (X : ℝ)) (Real.log (2 * (X : ℝ))) T 0 T
  have hba := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (2 * (X : ℝ))) (Real.log (X : ℝ)) T 0 T
  have hbb := _root_.RHTower.intervalIntegrable_logarithmicUnitEntry_pair
    (Real.log (2 * (X : ℝ))) (Real.log (2 * (X : ℝ))) T 0 T
  have ha : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg (X : ℕ)
  have hb : 0 ≤ Real.log (2 * (X : ℝ)) := ha.trans (balanced_log_endpoints X)
  simp_rw [balanced_log_pair_expansion]
  rw [intervalIntegral.integral_add ((haa.sub hab).sub hba) hbb,
    intervalIntegral.integral_sub (haa.sub hab) hba,
    intervalIntegral.integral_sub haa hab,
    _root_.RHTower.integral_logarithmicUnitEntry_pair ha ha,
    _root_.RHTower.integral_logarithmicUnitEntry_pair ha hb,
    _root_.RHTower.integral_logarithmicUnitEntry_pair hb ha,
    _root_.RHTower.integral_logarithmicUnitEntry_pair hb hb]
  rfl

/-- Exact endpoint compensation turns four signed ramps into one clipped triangular profile. -/
theorem balancedLogProductDensity_eq_tent (X : ℕ+) (t : ℝ) :
    balancedLogProductDensity X t =
      max (min (t - 2 * Real.log (X : ℝ)) (2 * Real.log (2 * (X : ℝ)) - t)) 0 := by
  let a : ℝ := Real.log (X : ℝ)
  let b : ℝ := Real.log (2 * (X : ℝ))
  have hab : a ≤ b := balanced_log_endpoints X
  change max (t - a - a) 0 - max (t - a - b) 0 - max (t - b - a) 0 +
      max (t - b - b) 0 = max (min (t - 2 * a) (2 * b - t)) 0
  rw [show t - a - a = t - 2 * a by ring,
    show t - b - a = t - a - b by ring,
    show t - b - b = t - 2 * b by ring]
  by_cases hlow : t ≤ 2 * a
  · have h1 : t - 2 * a ≤ 0 := by linarith only [hlow]
    have h2 : t - a - b ≤ 0 := by linarith only [hlow, hab]
    have h3 : t - 2 * b ≤ 0 := by linarith only [hlow, hab]
    have hm : t - 2 * a ≤ 2 * b - t := by linarith only [hlow, hab]
    rw [max_eq_right h1, max_eq_right h2, max_eq_right h3,
      min_eq_left hm, max_eq_right h1] <;> ring
  · have h1 : 0 ≤ t - 2 * a := by linarith only [not_le.mp hlow]
    by_cases hmid : t ≤ a + b
    · have h2 : t - a - b ≤ 0 := by linarith only [hmid]
      have h3 : t - 2 * b ≤ 0 := by linarith only [hmid, hab]
      have hm : t - 2 * a ≤ 2 * b - t := by linarith only [hmid]
      rw [max_eq_left h1, max_eq_right h2, max_eq_right h3,
        min_eq_left hm, max_eq_left h1] <;> ring
    · have h2 : 0 ≤ t - a - b := by linarith only [not_le.mp hmid]
      have hm : 2 * b - t ≤ t - 2 * a := by linarith only [not_le.mp hmid]
      by_cases hhigh : t ≤ 2 * b
      · have h3 : t - 2 * b ≤ 0 := by linarith only [hhigh]
        have h4 : 0 ≤ 2 * b - t := by linarith only [hhigh]
        rw [max_eq_left h1, max_eq_left h2, max_eq_right h3,
          min_eq_right hm, max_eq_left h4] <;> ring
      · have h3 : 0 ≤ t - 2 * b := by linarith only [not_le.mp hhigh]
        have h4 : 2 * b - t ≤ 0 := by linarith only [not_le.mp hhigh]
        rw [max_eq_left h1, max_eq_left h2, max_eq_left h3,
          min_eq_right hm, max_eq_right h4] <;> ring

/-- The density is nonnegative and its height is independent of the balanced scale. -/
theorem balancedLogProductDensity_bounds (X : ℕ+) (t : ℝ) :
    0 ≤ balancedLogProductDensity X t ∧ balancedLogProductDensity X t ≤ Real.log 2 := by
  rw [balancedLogProductDensity_eq_tent]
  refine ⟨le_max_right _ _, max_le_iff.mpr ⟨?_, ?_⟩⟩
  · have h1 := min_le_left (t - 2 * Real.log (X : ℝ)) (2 * Real.log (2 * (X : ℝ)) - t)
    have h2 := min_le_right (t - 2 * Real.log (X : ℝ)) (2 * Real.log (2 * (X : ℝ)) - t)
    have hw := balanced_log_width X
    linarith only [h1, h2, hw]
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The strict support is exactly the open logarithmic product interval. -/
theorem balancedLogProductDensity_pos_iff (X : ℕ+) (t : ℝ) :
    0 < balancedLogProductDensity X t ↔
      2 * Real.log (X : ℝ) < t ∧ t < 2 * Real.log (2 * (X : ℝ)) := by
  rw [balancedLogProductDensity_eq_tent]
  simp only [lt_max_iff, lt_min_iff, lt_self_iff_false, or_false]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

end
end GaloisForLFunctions.Goldbach

#print axioms GaloisForLFunctions.Goldbach.balancedLogWindow_eq_indicator
#print axioms GaloisForLFunctions.Goldbach.intervalIntegrable_balancedLogWindow_pair
#print axioms GaloisForLFunctions.Goldbach.integral_balancedLogWindow_pair
#print axioms GaloisForLFunctions.Goldbach.balancedLogProductDensity_eq_tent
#print axioms GaloisForLFunctions.Goldbach.balancedLogProductDensity_bounds
#print axioms GaloisForLFunctions.Goldbach.balancedLogProductDensity_pos_iff
