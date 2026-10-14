import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Tactic

/-! # Centered curvature of inverse-power primitives

The normalization cancels both derivative factors. A quadratic majorant
therefore bounds the centered second difference by one endpoint inverse power.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Set

def inversePowerPrimitive (m : ℕ) (x : ℝ) : ℝ :=
  (x ^ (m + 2))⁻¹ / (((m : ℝ) + 2) * (m + 3))

theorem inversePowerPrimitive_hasDerivAt (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (inversePowerPrimitive m) (-(x ^ (m + 3))⁻¹ / (m + 3)) x := by
  have he : -((m + 2 : ℕ) : ℤ) - 1 = -((m + 3 : ℕ) : ℤ) := by omega
  have h := (hasDerivAt_zpow (-((m + 2 : ℕ) : ℤ)) x (Or.inl hx.ne')).div_const
    (((m : ℝ) + 2) * (m + 3))
  rw [he] at h
  simp only [zpow_neg, zpow_natCast] at h
  push_cast at h
  convert! h using 1
  have hm : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp

theorem inversePowerPrimitive_hasDerivAt_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(y ^ (m + 3))⁻¹ / (m + 3))
      (x ^ (m + 4))⁻¹ x := by
  have he : -((m + 3 : ℕ) : ℤ) - 1 = -((m + 4 : ℕ) : ℤ) := by omega
  have h := ((hasDerivAt_zpow (-((m + 3 : ℕ) : ℤ)) x (Or.inl hx.ne')).neg).div_const
    ((m : ℝ) + 3)
  rw [he] at h
  simp only [zpow_neg, zpow_natCast, Pi.neg_apply] at h
  push_cast at h
  convert! h using 1
  have hm : (m : ℝ) + 3 ≠ 0 := by positivity
  field_simp

theorem inversePowerPrimitive_centered_le (m : ℕ) {c : ℝ} (hc : 1 < c) :
    inversePowerPrimitive m (c + 1) - 2 * inversePowerPrimitive m c +
      inversePowerPrimitive m (c - 1) ≤ ((c - 1) ^ (m + 4))⁻¹ := by
  let C := ((c - 1) ^ (m + 4))⁻¹
  let g := fun x : ℝ => C * x ^ 2 / 2 - inversePowerPrimitive m x
  let g' := fun x : ℝ => C * x - (-(x ^ (m + 3))⁻¹ / (m + 3))
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    have h := ((((hasDerivAt_id' x).pow 2).const_mul C).div_const 2).sub
      (inversePowerPrimitive_hasDerivAt m hx)
    convert! h using 1
    dsimp [g, g']
    ring
  have hconv : ConvexOn ℝ (Icc (c - 1) (c + 1)) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g')
      (f'' := fun x => C - (x ^ (m + 4))⁻¹) (convex_Icc _ _)
    · intro x hx
      exact (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      have hxI := interior_subset hx
      exact (hder x (by linarith [hxI.1])).hasDerivWithinAt
    · intro x hx
      have hxI := interior_subset hx
      simpa only [g', mul_one] using! (((hasDerivAt_id' x).const_mul C).sub
        (inversePowerPrimitive_hasDerivAt_deriv m (by linarith [hxI.1]))).hasDerivWithinAt
    · intro x hx
      have hxI := interior_subset hx
      have hc0 : 0 < c - 1 := by linarith
      have hx0 : 0 < x := by linarith [hxI.1]
      apply sub_nonneg.mpr
      exact (inv_le_inv₀ (pow_pos hx0 _) (pow_pos hc0 _)).mpr
        (pow_le_pow_left₀ hc0.le hxI.1 _)
  have h := hconv.2 (show c - 1 ∈ Icc (c - 1) (c + 1) by constructor <;> linarith)
    (show c + 1 ∈ Icc (c - 1) (c + 1) by constructor <;> linarith)
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * (c - 1) + (1 / 2 : ℝ) * (c + 1) = c by ring] at h
  dsimp only [g] at h
  change _ ≤ C
  nlinarith only [h]

end
end GaloisForLFunctions.HTGeometry
