import GaloisForLFunctions.HTGeometry.SymmetricHopfIdealClassification
import GaloisForLFunctions.HTGeometry.MixedTorusProjectionSaturation

/-!
# Classification of additive projection images of mixed subgroups

The scheme-theoretic additive projection of a mixed affine-exponential subgroup is cut out exactly
by its additive-linear relations.  Its classified symmetric coordinate algebra embeds into the
coordinate quotient of the original mixed subgroup.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedAdditiveProjectionClassification

noncomputable section

open AffineExponentialGroup AffineExponentialSubgroups
open AffineExponentialProjectionImages
open SymmetricHopfIdealClassification

variable (k : Type*) [Field k] [CharZero k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance additiveProjectionHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k :=
  additiveProjectionIdeal_isHopfIdeal k I

/-- Additive-linear relations annihilating the scheme-theoretic additive projection. -/
noncomputable def additiveRelationSubspace : Submodule k (Fin n → k) :=
  linearPart (additiveProjectionIdeal k I)

omit [CharZero k] in
theorem mem_additiveRelationSubspace_iff (v : Fin n → k) :
    v ∈ additiveRelationSubspace k I ↔ additiveLinear k v ∈ I := by
  rw [additiveRelationSubspace, mem_linearPart,
    mem_additiveProjectionIdeal_iff]
  rfl

/-- The additive projection ideal is generated exactly by its additive-linear relations. -/
theorem additiveProjectionIdeal_eq_linearIdeal_additiveRelationSubspace :
    additiveProjectionIdeal k I =
      SymmetricAlgebraSubmoduleQuotient.linearIdeal
        (additiveRelationSubspace k I) :=
  eq_linearIdeal_linearPart (additiveProjectionIdeal k I)

/-- The quotient by the contracted additive ideal maps canonically into the mixed subgroup
quotient. -/
noncomputable def additiveProjectionQuotientAlgHom :
    AdditiveCoordinateAlgebra k n ⧸ additiveProjectionIdeal k I →ₐ[k]
      CoordinateAlgebra k n ⧸ I :=
  Ideal.Quotient.liftₐ (additiveProjectionIdeal k I)
    (additiveProjectionMap k I).toAlgHom (by
      intro x hx
      exact hx)

omit [CharZero k] in
@[simp] theorem additiveProjectionQuotientAlgHom_mk
    (x : AdditiveCoordinateAlgebra k n) :
    additiveProjectionQuotientAlgHom k I (Ideal.Quotient.mk _ x) =
      additiveProjectionMap k I x := rfl

omit [CharZero k] in
theorem additiveProjectionQuotientAlgHom_injective :
    Function.Injective (additiveProjectionQuotientAlgHom k I) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq]
  change additiveProjectionMap k I (a - b) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- The symmetric algebra on additive coordinates modulo all additive-linear relations, embedded
in the actual mixed subgroup coordinate quotient. -/
noncomputable def additiveRelationSymmetricAlgHomIntoSubgroupQuotient :
    SymmetricAlgebra k ((Fin n → k) ⧸ additiveRelationSubspace k I) →ₐ[k]
      CoordinateAlgebra k n ⧸ I :=
  (additiveProjectionQuotientAlgHom k I).comp
    (quotientBialgHom (additiveProjectionIdeal k I)).toAlgHom

theorem additiveRelationSymmetricAlgHomIntoSubgroupQuotient_injective :
    Function.Injective (additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I) :=
  (additiveProjectionQuotientAlgHom_injective k I).comp
    (quotientBialgHom_injective (additiveProjectionIdeal k I))

end
end MixedAdditiveProjectionClassification
end GaloisForLFunctions.HTGeometry
