import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicOrbits
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectionFunctoriality

/-!
# Affine covariance of cyclic translation projections

Fixed projections commute with translations, are unchanged by reversing the step, and transform by slope rescaling under affine transport.
-/

open Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Rational translations commute in the column representation. -/
theorem kernelColumnRepresentation_translation_commute (k : AffineGroupQ → ℂ) (b c : ℚ) :
    Commute (kernelColumnRepresentation k (translation b))
      (kernelColumnRepresentation k (translation c)) := by
  change kernelColumnRepresentation k (translation b) * kernelColumnRepresentation k (translation c) = _
  rw [← map_mul, ← map_mul, ← translation_add, ← translation_add, add_comm]

/-- Cyclic fixed projections commute with every rational translation. -/
theorem translationFixedProjection_translation (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b c : ℚ) (x : kernelColumnSpan k) :
    translationFixedProjection k hp b (kernelColumnRepresentation k (translation c) x) =
      kernelColumnRepresentation k (translation c) (translationFixedProjection k hp b x) := by
  have h := locallyPeriodicProjection_commute (kernelColumnRepresentation k (translation b))
    (kernel_translation_locally_periodic hp b) (kernelColumnRepresentation k (translation c))
    (kernelColumnRepresentation_translation_commute k b c)
  exact LinearMap.congr_fun h.eq x

/-- Reversing a translation step preserves its fixed projection. -/
theorem translationFixedProjection_neg (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) :
    translationFixedProjection k hp (-b) = translationFixedProjection k hp b := by
  apply locallyPeriodicProjection_eq_of_inverse
  · rw [← map_mul, ← translation_add, neg_add_cancel, translation_zero, map_one]
  · rw [← map_mul, ← translation_add, add_neg_cancel, translation_zero, map_one]

/-- Affine transport rescales the cyclic projection step by the slope. -/
theorem translationFixedProjection_affine (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (g : AffineGroupQ)
    (x : kernelColumnSpan k) :
    translationFixedProjection k hp b (kernelColumnRepresentation k g x) =
      kernelColumnRepresentation k g (translationFixedProjection k hp (b / affSlope g) x) := by
  apply locallyPeriodicProjection_intertwine
  rw [← map_mul, ← map_mul, translation_mul_affine_eq]

/-- Averaging removes every integral multiple of its translation step. -/
theorem translationFixedProjection_int_multiple (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (m : ℤ) (x : kernelColumnSpan k) :
    translationFixedProjection k hp b (kernelColumnRepresentation k (translation ((m : ℚ) * b)) x) =
      translationFixedProjection k hp b x := by
  cases m with
  | ofNat n =>
    change translationFixedProjection k hp b
      (kernelColumnRepresentation k (translation ((n : ℚ) * b)) x) = _
    rw [← rational_affine_translation_pow (kernelColumnRepresentation k) b n]
    exact locallyPeriodicProjection_pow_apply _ (kernel_translation_locally_periodic hp b) n x
  | negSucc n =>
    have he : (Int.negSucc n : ℚ) * b = ((n + 1 : ℕ) : ℚ) * (-b) := by
      push_cast
      ring
    rw [he, ← rational_affine_translation_pow, ← translationFixedProjection_neg k hp b]
    exact locallyPeriodicProjection_pow_apply _ (kernel_translation_locally_periodic hp (-b)) (n + 1) x

/-- Every integral multiple of the step fixes the projected vector. -/
theorem translationFixedProjection_fixed_int_multiple (k : AffineGroupQ → ℂ)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (m : ℤ) (x : kernelColumnSpan k) :
    kernelColumnRepresentation k (translation ((m : ℚ) * b)) (translationFixedProjection k hp b x) =
      translationFixedProjection k hp b x := by
  rw [← translationFixedProjection_translation, translationFixedProjection_int_multiple]

#print axioms translationFixedProjection_neg
#print axioms translationFixedProjection_affine
#print axioms translationFixedProjection_int_multiple
end GaloisForLFunctions.AdelicKreinGeometry
