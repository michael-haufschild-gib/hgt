import GaloisForLFunctions.HTGeometry.MixedAdditiveProjectionClassification

/-!
# Tensor presentation by the two projection images

The classified torus and additive projection coordinate algebras jointly generate the coordinate
quotient of every mixed affine-exponential subgroup.  This file constructs the canonical tensor
map and proves it surjective.  Mixed-factor splitting is therefore exactly injectivity of this
single explicit map.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedProjectionTensorPresentation

noncomputable section

open AffineExponentialGroup AffineExponentialProjectionImages
open AffineExponentialProjectionClassification
open GroupAlgebraHopfIdealClassification
open SymmetricAlgebraSubmoduleQuotient
open SymmetricHopfIdealClassification
open MixedTorusProjectionSaturation
open MixedAdditiveProjectionClassification

variable (k : Type*) [Field k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance torusProjectionHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k :=
  torusProjectionIdeal_isHopfIdeal k I

local instance additiveProjectionHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k :=
  additiveProjectionIdeal_isHopfIdeal k I

/-- Canonical multiplication map from the tensor product of the two classified projection
coordinate algebras into the mixed subgroup quotient. -/
noncomputable def mixedProjectionTensorAlgHom :
    AddMonoidAlgebra k
        ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
      SymmetricAlgebra k
        ((Fin n → k) ⧸ additiveRelationSubspace k I) →ₐ[k]
      CoordinateAlgebra k n ⧸ I :=
  Algebra.TensorProduct.lift
    (torusRelationGroupAlgHomIntoSubgroupQuotient k I)
    (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I)
    (fun x y => (commute_iff_eq _ _).2
      (mul_comm
        (torusRelationGroupAlgHomIntoSubgroupQuotient k I x)
        (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I y)))

@[simp] theorem mixedProjectionTensorAlgHom_tmul
    (x : AddMonoidAlgebra k
      ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (y : SymmetricAlgebra k
      ((Fin n → k) ⧸ additiveRelationSubspace k I)) :
    mixedProjectionTensorAlgHom k I (x ⊗ₜ[k] y) =
      torusRelationGroupAlgHomIntoSubgroupQuotient k I x *
        additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I y := by
  simp [mixedProjectionTensorAlgHom]

theorem torusRelationGroupAlgHomIntoSubgroupQuotient_quotientGroupMap
    (x : TorusCoordinateAlgebra k n) :
    torusRelationGroupAlgHomIntoSubgroupQuotient k I
        (quotientGroupMap (torusProjectionIdeal k I) x) =
      torusProjectionMap k I x := by
  change torusProjectionQuotientAlgHom k I
      (quotientGroupAlgHom (torusProjectionIdeal k I)
        (quotientGroupMap (torusProjectionIdeal k I) x)) =
    torusProjectionMap k I x
  have h := DFunLike.congr_fun
    (quotientGroupAlgHom_comp_quotientGroupMap (torusProjectionIdeal k I)) x
  have h' : quotientGroupAlgHom (torusProjectionIdeal k I)
      (quotientGroupMap (torusProjectionIdeal k I) x) =
      Ideal.Quotient.mk (torusProjectionIdeal k I) x := h
  rw [h', torusProjectionQuotientAlgHom_mk]

theorem additiveRelationSymmetricAlgHomIntoSubgroupQuotient_quotientMap
    (x : AdditiveCoordinateAlgebra k n) :
    additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I
        (quotientMap (additiveRelationSubspace k I) x) =
      additiveProjectionMap k I x := by
  change additiveProjectionQuotientAlgHom k I
      (quotientBialgHom (additiveProjectionIdeal k I)
        (quotientMap (linearPart (additiveProjectionIdeal k I)) x)) =
    additiveProjectionMap k I x
  have h := DFunLike.congr_fun
    (quotientBialgHom_comp_quotientMap (additiveProjectionIdeal k I)) x
  have h' : quotientBialgHom (additiveProjectionIdeal k I)
      (quotientMap (linearPart (additiveProjectionIdeal k I)) x) =
      Ideal.Quotient.mk (additiveProjectionIdeal k I) x := h
  rw [h', additiveProjectionQuotientAlgHom_mk]

/-- The two classified projection images jointly generate the entire mixed subgroup coordinate
quotient. -/
theorem mixedProjectionTensorAlgHom_surjective :
    Function.Surjective (mixedProjectionTensorAlgHom k I) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by simpa only [map_add] using congrArg₂ (· + ·) hx' hy'⟩
  | tmul x y =>
      refine ⟨quotientGroupMap (torusProjectionIdeal k I) x ⊗ₜ[k]
        quotientMap (additiveRelationSubspace k I) y, ?_⟩
      rw [mixedProjectionTensorAlgHom_tmul,
        torusRelationGroupAlgHomIntoSubgroupQuotient_quotientGroupMap,
        additiveRelationSymmetricAlgHomIntoSubgroupQuotient_quotientMap]
      simp only [torusProjectionMap, additiveProjectionMap, subgroupQuotientMap]
      change Ideal.Quotient.mk I (x ⊗ₜ[k] 1) *
          Ideal.Quotient.mk I (1 ⊗ₜ[k] y) =
        Ideal.Quotient.mk I (x ⊗ₜ[k] y)
      rw [← map_mul]
      congr 1
      simp

end
end MixedProjectionTensorPresentation
end GaloisForLFunctions.HTGeometry
