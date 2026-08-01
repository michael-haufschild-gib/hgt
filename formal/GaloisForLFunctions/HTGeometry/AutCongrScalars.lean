import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Changing the base along an isomorphism of base fields

Two base fields acting on the same field through the same subfield have the same automorphism
group over them: an automorphism fixes one base pointwise exactly when it fixes the other, the
underlying map being unchanged.

This is what lets a base field be replaced by its image inside the ambient field, where it is an
intermediate field and the compositum arguments apply.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L T : Type*} [Field F] [Field L] [Field T] [Algebra F L] [Algebra T L]
variable [Algebra F T]

/-- **The automorphism group only depends on the image of the base.** -/
def autCongrScalars {M : IntermediateField F L} (e : T ≃ₐ[F] M)
    (h : ∀ x : T, (algebraMap M L) (e x) = algebraMap T L x) :
    (L ≃ₐ[T] L) ≃* (L ≃ₐ[M] L) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun m => by
    obtain ⟨x, rfl⟩ := e.surjective m
    rw [h]
    exact σ.commutes x)
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => by
    rw [← h]
    exact σ.commutes (e x))
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

end GaloisForLFunctions.HTGeometry
