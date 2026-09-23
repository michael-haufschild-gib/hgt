import GaloisForLFunctions.HTGeometry.HausdorffMomentTheorem

/-!
# Strict interior of the Hausdorff CDD cone

A nonempty positive shell configuration whose radii lie strictly inside the unit interval makes
every finite-difference inequality strict, so it is an interior point of the positivity cone rather
than a boundary one.  This is the finite-configuration companion of
`hausdorffMoment_strict_completelyMonotone`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Strict complete monotonicity of a positive geometric combination.** -/
theorem geometricCombination_strict_completelyMonotone {ι : Type*} (s : Finset ι) (w y : ι → ℝ)
    (hs : s.Nonempty) (hw : ∀ j ∈ s, 0 < w j) (hy0 : ∀ j ∈ s, 0 < y j) (hy1 : ∀ j ∈ s, y j < 1)
    (m k : ℕ) :
    0 < (-1) ^ k * ((fwdDiff 1)^[k] (fun n : ℕ => ∑ j ∈ s, w j * (y j) ^ n) m) := by
  rw [fwdDiff_iter_geometricCombination s w y k m, Finset.mul_sum]
  refine Finset.sum_pos (fun j hj => ?_) hs
  have hsign : (-1 : ℝ) ^ k * (w j * ((y j - 1) ^ k * (y j) ^ m))
      = w j * ((1 - y j) ^ k * (y j) ^ m) := by
    rw [show (1 - y j) ^ k = (-1) ^ k * (y j - 1) ^ k from by rw [← neg_sub, neg_pow]]
    ring
  rw [hsign]
  exact mul_pos (hw j hj)
    (mul_pos (pow_pos (by linarith [hy1 j hj]) k) (pow_pos (hy0 j hj) m))

/-- **The strict CDD positivity cone.**  A nonempty positive shell configuration with radii
strictly between `0` and `1` satisfies every inequality of the cone strictly. -/
theorem cddCoupling_strict_completelyMonotone {ι : Type*} (s : Finset ι) (w r : ι → ℝ)
    (hs : s.Nonempty) (hw : ∀ j ∈ s, 0 < w j) (hr0 : ∀ j ∈ s, 0 < r j) (hr1 : ∀ j ∈ s, r j < 1)
    (m k : ℕ) :
    0 < (-1) ^ k * ((fwdDiff 1)^[k] (fun n : ℕ => ∑ j ∈ s, w j * (r j) ^ (2 * n)) m) := by
  have hrw : (fun n : ℕ => ∑ j ∈ s, w j * (r j) ^ (2 * n))
      = fun n : ℕ => ∑ j ∈ s, w j * ((r j) ^ (2 : ℕ)) ^ n := by
    funext n
    exact Finset.sum_congr rfl fun j _ => by rw [pow_mul]
  rw [hrw]
  refine geometricCombination_strict_completelyMonotone s w (fun j => (r j) ^ (2 : ℕ)) hs hw
    (fun j hj => pow_pos (hr0 j hj) 2) (fun j hj => ?_) m k
  nlinarith [hr0 j hj, hr1 j hj]

end GaloisForLFunctions.HTGeometry
