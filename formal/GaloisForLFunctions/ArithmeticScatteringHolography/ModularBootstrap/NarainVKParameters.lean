import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanVKStrip

/-!
# Width and reciprocal bounds for arithmetic Narain rectangles

The admissible strip narrows with height, retains a fixed fraction of the raw
zero-free width, and has a reciprocal-zeta envelope bounded below by one.
-/

open RHTower Set
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Raising the contour height narrows the admissible arithmetic strip. -/
theorem narainVKWidth_anti (δ : ℝ) {S T : ℝ}
    (hS : Real.exp (Real.exp 1) ≤ 2 * S + 1) (hST : S ≤ T) :
    narainVKWidth δ T ≤ narainVKWidth δ S := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 8)
  exact min_le_min le_rfl (vkHadamardWidth_anti hS (by linarith only [hST]))

/-- The reciprocal-zeta envelope is at least one above the elementary height threshold. -/
theorem one_le_narainVKCost {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ 2 * T + 1) :
    1 ≤ narainVKCost T := by
  have hw : 0 < vkHadamardWidth (2 * T + 1) := vkHadamardWidth_pos hT
  have hlog : Real.exp 1 ≤ Real.log (2 * T + 1) := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hT
  have hlog1 : 1 ≤ Real.log (2 * T + 1) := by
    have he := Real.add_one_le_exp (1 : ℝ)
    linarith only [he, hlog]
  have hleft : 1 ≤ Real.log (2 * T + 1) ^ 7 := one_le_pow₀ hlog1
  have hright : 1 ≤ (1 + 2 / vkHadamardWidth (2 * T + 1)) ^ 7 :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  exact one_le_mul_of_one_le_of_one_le hleft hright

/-- Keeping a fixed fraction of the raw zero-free width avoids an eventual minimum split. -/
theorem narainVKWidth_ge_fraction {δ T : ℝ} (hδ : 0 < δ)
    (hT : Real.exp (Real.exp 1) ≤ 2 * T + 1) :
    min δ 1 / 8 * vkHadamardWidth (2 * T + 1) ≤ narainVKWidth δ T := by
  have hw := vkHadamardWidth_pos hT
  have hw1 : vkHadamardWidth (2 * T + 1) ≤ 1 :=
    (RHTower.Sieve.vkHadamardWidth_le_inv hT).trans (by norm_num)
  have hδ0 : 0 ≤ min δ 1 := (lt_min hδ zero_lt_one).le
  have hmin : min δ 1 * vkHadamardWidth (2 * T + 1) ≤
      min (min δ 1) (vkHadamardWidth (2 * T + 1)) := by
    apply le_min
    · exact mul_le_of_le_one_right hδ0 hw1
    · exact mul_le_of_le_one_left hw.le (min_le_right δ 1)
  unfold narainVKWidth
  linarith only [hmin]

#print axioms narainVKWidth_ge_fraction
#print axioms narainVKWidth_anti
#print axioms one_le_narainVKCost
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
