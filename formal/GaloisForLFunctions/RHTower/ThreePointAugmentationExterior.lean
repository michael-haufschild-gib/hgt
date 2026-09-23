import GaloisForLFunctions.RHTower.DivisorAugmentationExactSequence
import GaloisForLFunctions.RHTower.XiApertureCubicExteriorMatching

/-!
# The three-point augmentation exterior

The first oriented scalar carried by three labels is their Vandermonde product.  It depends only
on pairwise augmentation coordinates, is invariant under common translation, reverses under an
odd label exchange, and vanishes exactly at a collision.

Both the positive cubic source determinant and the negative Poisson-response determinant factor
through the square of this same oriented augmentation coordinate.
-/

namespace RHTower

noncomputable section

/-- Oriented determinant coordinate of three scalar labels after deleting their common
translation mode. -/
def threePointAugmentationExterior (x y z : ℝ) : ℝ :=
  (y - x) * (z - x) * (z - y)

/-- The three-point exterior descends to the augmentation quotient: common translation is
invisible. -/
theorem threePointAugmentationExterior_add_common
    (x y z c : ℝ) :
    threePointAugmentationExterior (x + c) (y + c) (z + c) =
      threePointAugmentationExterior x y z := by
  unfold threePointAugmentationExterior
  ring

/-- An odd exchange reverses the exterior orientation. -/
theorem threePointAugmentationExterior_swap
    (x y z : ℝ) :
    threePointAugmentationExterior y x z =
      -threePointAugmentationExterior x y z := by
  unfold threePointAugmentationExterior
  ring

/-- The oriented augmentation coordinate vanishes exactly when two labels collide. -/
theorem threePointAugmentationExterior_eq_zero_iff
    (x y z : ℝ) :
    threePointAugmentationExterior x y z = 0 ↔
      x = y ∨ x = z ∨ y = z := by
  unfold threePointAugmentationExterior
  simp only [mul_eq_zero, sub_eq_zero]
  aesop

/-- The cubic positive-source determinant is a positive radial factor times the square of the
oriented three-label augmentation coordinate. -/
theorem symmetricThreePointDet_cubicApertureSourceKernel_eq_augmentationExteriorSq
    {kappa x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    symmetricThreePointDet (cubicApertureSourceKernel kappa) x y z =
      kappa ^ (3 : ℕ) * x ^ (3 : ℕ) * y ^ (3 : ℕ) * z ^ (3 : ℕ) *
          threePointAugmentationExterior x y z ^ (2 : ℕ) /
        (8 * (x + y) ^ (2 : ℕ) * (x + z) ^ (2 : ℕ) * (y + z) ^ (2 : ℕ)) := by
  rw [symmetricThreePointDet_cubicApertureSourceKernel hx hy hz]
  unfold threePointAugmentationExterior
  congr 1
  ring

/-- The correctly oriented Poisson-response determinant factors through the same augmentation
exterior line, with an explicit positive gain. -/
theorem neg_symmetricThreePointDet_poissonScaleRefinementKernel_eq_augmentationExteriorSq
    {kappa a b x y z : ℝ} (hkappa : 0 < kappa)
    (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    -symmetricThreePointDet (poissonScaleRefinementKernel a b) x y z =
      xiApertureCubicResponseExteriorGainSq kappa a b x y z *
        (kappa ^ (3 : ℕ) * x ^ (3 : ℕ) * y ^ (3 : ℕ) * z ^ (3 : ℕ) *
            threePointAugmentationExterior x y z ^ (2 : ℕ) /
          (8 * (x + y) ^ (2 : ℕ) * (x + z) ^ (2 : ℕ) * (y + z) ^ (2 : ℕ))) := by
  rw [
    neg_symmetricThreePointDet_poissonScaleRefinementKernel_eq_exteriorGainSq_mul
      hkappa ha hb hx hy hz,
    symmetricThreePointDet_cubicApertureSourceKernel_eq_augmentationExteriorSq
      hx hy hz]

end

end RHTower
