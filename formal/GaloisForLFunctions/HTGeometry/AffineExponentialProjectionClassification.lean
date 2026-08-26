import GaloisForLFunctions.HTGeometry.AffineExponentialProjectionImages
import GaloisForLFunctions.HTGeometry.GroupAlgebraHopfIdealClassification
import GaloisForLFunctions.HTGeometry.SymmetricHopfIdealLinear

/-!
# Classification of projection images in the affine exponential group

For an arbitrary Hopf ideal in the coordinate algebra of `Gₐⁿ × Gₘⁿ`, the torus
projection is classified exactly by its integral character-relation lattice.  On the additive
side, every nontrivial projection ideal already contains a nonzero linear relation.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialProjectionClassification

noncomputable section

open AffineExponentialGroup AffineExponentialSubgroups
open AffineExponentialProjectionImages
open GroupAlgebraHopfIdealClassification

variable (k : Type*) [Field k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance torusProjectionHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k :=
  torusProjectionIdeal_isHopfIdeal k I

local instance additiveProjectionHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k :=
  additiveProjectionIdeal_isHopfIdeal k I

/-- Integral characters annihilating the scheme-theoretic torus projection of a closed subgroup
of `Gₐⁿ × Gₘⁿ`. -/
noncomputable def torusRelationLattice : AddSubgroup (Fin n →₀ ℤ) :=
  relationSubgroup (torusProjectionIdeal k I)

/-- Membership in the torus relation lattice is exactly membership of the corresponding character
equation in the original mixed Hopf ideal. -/
theorem mem_torusRelationLattice_iff (m : Fin n →₀ ℤ) :
    m ∈ torusRelationLattice k I ↔ torusRelation k m ∈ I := by
  rw [torusRelationLattice, mem_relationSubgroup_iff,
    torusCharacterRelation_mem_projection_iff]

/-- The torus projection ideal is exactly the kernel obtained by quotienting the full character
lattice by the characters annihilating the projection. -/
theorem torusProjectionIdeal_eq_ker_quotientGroupMap :
    torusProjectionIdeal k I =
      RingHom.ker
        (quotientGroupMap (torusProjectionIdeal k I)).toAlgHom.toRingHom :=
  eq_ker_quotientGroupMap (torusProjectionIdeal k I)

/-- A nontrivial additive projection of a mixed closed subgroup has a nonzero additive-linear
annihilator already in the original mixed Hopf ideal. -/
theorem additiveProjectionIdeal_eq_bot_or_exists_nonzero_relation [CharZero k] :
    additiveProjectionIdeal k I = ⊥ ∨
      ∃ v : Fin n → k, v ≠ 0 ∧ additiveLinear k v ∈ I := by
  by_cases hJ : additiveProjectionIdeal k I = ⊥
  · exact Or.inl hJ
  · right
    obtain ⟨v, hv, hmem⟩ :=
      SymmetricHopfIdealLinear.nonzero_exists_nonzero_generator
        (Module.Free.chooseBasis k (Fin n → k)) (additiveProjectionIdeal k I) hJ
    exact ⟨v, hv, (additiveLinear_mem_projection_iff k I v).mp hmem⟩

end
end AffineExponentialProjectionClassification
end GaloisForLFunctions.HTGeometry
