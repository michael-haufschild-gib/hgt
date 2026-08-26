import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Point derivations of additive group algebras

An additive homomorphism `ell : M →+ k` defines a derivation at the identity of the group algebra
`k[M]`: on a monomial it is `D([m]) = ell(m)`.  Equivalently, it defines a linear functional on
the co-Lie module of the diagonalizable group with character group `M`.

This is the coefficientwise detection mechanism for character-lattice directions.  In particular,
it applies unchanged when `M` is a quotient character group with torsion.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupAlgebraPointDerivation

noncomputable section

open AffineGroupScheme

variable {k M : Type*} [Field k] [AddCommGroup M]

/-- Linear functional on the group algebra attached to an additive character `M →+ k`. -/
noncomputable def pointLinearMap (ell : M →+ k) :
    AddMonoidAlgebra k M →ₗ[k] k :=
  (Finsupp.linearCombination k ell).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem pointLinearMap_single (ell : M →+ k) (m : M) (c : k) :
    pointLinearMap ell (AddMonoidAlgebra.single m c) = c * ell m := by
  simp [pointLinearMap, smul_eq_mul]

/-- The monomial-weight functional obeys the Leibniz rule at the counit. -/
theorem pointLinearMap_mul (ell : M →+ k) (p q : AddMonoidAlgebra k M) :
    pointLinearMap ell (p * q) =
      Coalgebra.counit (R := k) p * pointLinearMap ell q +
      Coalgebra.counit (R := k) q * pointLinearMap ell p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ hp₁ hp₂ =>
      simp only [add_mul, map_add, hp₁, hp₂]
      ring
  | single m a =>
      induction q using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add q₁ q₂ hq₁ hq₂ =>
          simp only [mul_add, map_add, hq₁, hq₂]
          ring
      | single n b =>
          simp [AddMonoidAlgebra.single_mul_single]
          ring

/-- The monomial-weight functional, bundled as a point derivation at the identity. -/
noncomputable def pointDerivation (ell : M →+ k) :
    pointDerivations k (AddMonoidAlgebra k M) :=
  ⟨pointLinearMap ell, pointLinearMap_mul ell⟩

/-- The induced functional on the co-Lie module of `k[M]`. -/
noncomputable def coLieFunctional (ell : M →+ k) :
    coLie k (AddMonoidAlgebra k M) →ₗ[k] k :=
  pointDerivationEquiv (pointDerivation ell)

@[simp] theorem coLieFunctional_d_single
    (ell : M →+ k) (m : M) (c : k) :
    coLieFunctional ell
        (d k (AddMonoidAlgebra k M) (AddMonoidAlgebra.single m c)) =
      c * ell m := by
  simp [coLieFunctional, pointDerivationEquiv, d_apply, toAug_coe, pointDerivation]

end
end GroupAlgebraPointDerivation
end GaloisForLFunctions.HTGeometry
