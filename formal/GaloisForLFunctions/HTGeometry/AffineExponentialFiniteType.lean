import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf
import Mathlib

/-!
# Finite-type additive-exponential coordinate algebras

The free character lattice `ℤⁿ`, its group algebra, the symmetric additive coordinate algebra,
and their tensor-product coordinate algebra are finitely generated over the base field.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialFiniteType

noncomputable section

open AffineExponentialGroup

/-- The finite-rank character lattice is a finitely generated additive group. -/
instance instCharacterLatticeFG (n : ℕ) : AddGroup.FG (Fin n →₀ ℤ) := by
  let e := Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)
  letI : AddGroup.FG (Fin n → ℤ) := by infer_instance
  exact AddGroup.fg_of_surjective (G := Fin n → ℤ) (G' := Fin n →₀ ℤ)
    (f := ((e.symm : (Fin n → ℤ) →ₗ[ℤ] (Fin n →₀ ℤ)).toAddHom)) e.symm.surjective

/-- The finite-rank split-torus group algebra is finite type over its coefficient field. -/
instance instTorusCoordinateFiniteType (k : Type*) [Field k] (n : ℕ) :
    Algebra.FiniteType k (TorusCoordinateAlgebra k n) :=
  AddMonoidAlgebra.finiteType_of_fg k (Fin n →₀ ℤ)

/-- The finite-dimensional symmetric additive coordinate algebra is finite type. -/
instance instAdditiveCoordinateFiniteType (k : Type*) [Field k] (n : ℕ) :
    Algebra.FiniteType k (AdditiveCoordinateAlgebra k n) := by
  let e := SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin n))
  exact Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective

/-- The coordinate algebra of `Gₐⁿ × Gₘⁿ` is finite type over the base field. -/
instance instCoordinateFiniteType (k : Type*) [Field k] (n : ℕ) :
    Algebra.FiniteType k (CoordinateAlgebra k n) := by
  letI : Algebra.FiniteType (TorusCoordinateAlgebra k n) (CoordinateAlgebra k n) :=
    Algebra.FiniteType.baseChange (TorusCoordinateAlgebra k n)
  exact Algebra.FiniteType.trans (R := k) (S := TorusCoordinateAlgebra k n)
    (A := CoordinateAlgebra k n) inferInstance inferInstance

end
end AffineExponentialFiniteType
end GaloisForLFunctions.HTGeometry
