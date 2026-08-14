import GaloisForLFunctions.HTGeometry.SymmetricHopfPrimitive
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Group-like elements of a symmetric Hopf algebra

The only group-like element of `Sym(V)` over a field is `1`.  The proof uses
the antipode to make a group-like element a unit, then classifies polynomial
units after choosing a basis.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The additive vector group has no nontrivial algebraic characters. -/
theorem symmetric_groupLike_eq_one
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) (p : SymmetricAlgebra k V)
    (hp : IsGroupLikeElem k p) : p = 1 := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have hu : IsUnit (e p) := hp.isUnit.map e
  obtain ⟨c, hc, hpc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hpC : p = algebraMap k (SymmetricAlgebra k V) c := by
    apply e.injective
    rw [hpc]
    simp [e]
  have hc1 : c = 1 := by
    have h := hp.counit_eq_one
    rw [hpC] at h
    simpa using h
  rw [hpC, hc1, map_one]

end
end GaloisForLFunctions.HTGeometry
