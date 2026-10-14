import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Summable hyperbolic diagonal weights

The reciprocal hyperbolic square is dominated by a geometric sequence. The
associated positive perturbation product has an exact shifted-factor form.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter
open scoped Topology

def hyperbolicResolventWeight (a : ℝ) (n : ℕ) : ℝ := (Real.cosh (n * a) ^ 2)⁻¹

theorem hyperbolicResolventWeight_pos (a : ℝ) (n : ℕ) :
    0 < hyperbolicResolventWeight a n := inv_pos.mpr (sq_pos_of_pos (Real.cosh_pos _))

theorem hyperbolicResolventWeight_le_one (a : ℝ) (n : ℕ) :
    hyperbolicResolventWeight a n ≤ 1 := by
  apply (inv_le_one₀ (sq_pos_of_pos (Real.cosh_pos _))).mpr
  rw [Real.cosh_sq']
  linarith [sq_nonneg (Real.sinh (n * a))]

theorem hyperbolicResolventWeight_exp_bound (a : ℝ) (n : ℕ) :
    hyperbolicResolventWeight a n ≤ 4 * Real.exp (-2 * (n * a)) := by
  let x : ℝ := n * a
  have he : 0 < Real.exp x / 2 := by positivity
  have hc : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hs : (Real.exp x / 2) ^ 2 ≤ Real.cosh x ^ 2 := by
    nlinarith [Real.cosh_pos x]
  calc
    _ ≤ ((Real.exp x / 2) ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos he) hs
    _ = 4 * Real.exp (-2 * x) := by
      rw [show -2 * x = -(x + x) by ring, Real.exp_neg, Real.exp_add]
      field_simp
      ring

theorem summable_hyperbolicResolventWeight {a : ℝ} (ha : 0 < a) :
    Summable (hyperbolicResolventWeight a) := by
  have hs := (Real.summable_exp_nat_mul_iff.mpr (by linarith : -2 * a < 0)).mul_left 4
  apply Summable.of_nonneg_of_le (fun n => (hyperbolicResolventWeight_pos a n).le)
    (hyperbolicResolventWeight_exp_bound a)
  exact hs.congr (fun n => by congr 2; ring)

theorem cosh_add_mul_cosh_sub (x b : ℝ) :
    Real.cosh (x + b) * Real.cosh (x - b) = Real.cosh x ^ 2 + Real.sinh b ^ 2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  calc
    _ = Real.cosh x ^ 2 * Real.cosh b ^ 2 - Real.sinh x ^ 2 * Real.sinh b ^ 2 := by ring
    _ = _ := by rw [Real.cosh_sq b, Real.sinh_sq x]; ring

def hyperbolicFredholmFactor (a b : ℝ) (n : ℕ) : ℝ :=
  1 + Real.sinh b ^ 2 * hyperbolicResolventWeight a n

theorem hyperbolicFredholmFactor_pos (a b : ℝ) (n : ℕ) :
    0 < hyperbolicFredholmFactor a b n := by
  unfold hyperbolicFredholmFactor
  have hw := (hyperbolicResolventWeight_pos a n).le
  positivity

theorem hyperbolicFredholmFactor_eq_cosh (a b : ℝ) (n : ℕ) :
    hyperbolicFredholmFactor a b n =
      Real.cosh (n * a + b) * Real.cosh (n * a - b) / Real.cosh (n * a) ^ 2 := by
  rw [cosh_add_mul_cosh_sub]
  dsimp only [hyperbolicFredholmFactor, hyperbolicResolventWeight]
  field_simp [ne_of_gt (Real.cosh_pos _)]

theorem multipliable_hyperbolicFredholmFactor {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Multipliable (hyperbolicFredholmFactor a b) := by
  change Multipliable (fun n => 1 + Real.sinh b ^ 2 * hyperbolicResolventWeight a n)
  apply multipliable_one_add_of_summable
  simpa only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg (Real.sinh b)) (hyperbolicResolventWeight_pos a _).le)] using
      (summable_hyperbolicResolventWeight ha).mul_left (Real.sinh b ^ 2)

end
end GaloisForLFunctions.HTGeometry
