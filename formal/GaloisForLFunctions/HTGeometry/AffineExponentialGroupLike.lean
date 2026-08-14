import GaloisForLFunctions.HTGeometry.GroupGradedHopfGroupLike
import GaloisForLFunctions.HTGeometry.TensorGroupHopfEquiv
import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf

/-!
# Group-like functions on the affine exponential group

Every group-like regular function on `Gₘⁿ × Gₐⁿ` is exactly a torus character.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Group-like regular functions on `Gₘⁿ × Gₐⁿ` are precisely torus characters. -/
theorem coordinateAlgebra_groupLike_eq_torusCharacter
    {k : Type*} [Field k] {n : ℕ}
    (p : AffineExponentialGroup.CoordinateAlgebra k n)
    (hp : IsGroupLikeElem k p) :
    ∃ m : Fin n →₀ ℤ, p = AffineExponentialGroup.torusCharacter k m := by
  let e := TensorGroupEquiv.tensorGroupBialgEquiv
    (k := k) (B := SymmetricAlgebra k (Fin n → k))
    (M := Fin n →₀ ℤ)
  have hep : IsGroupLikeElem k (e p) := hp.map e
  obtain ⟨m, hm⟩ :=
    GroupGradedGroupLike.groupLike_group_symmetric_eq_monomial
      (Module.Free.chooseBasis k (Fin n → k)) (e p) hep
  refine ⟨m, e.injective ?_⟩
  change e p = e (AffineExponentialGroup.torusCharacter k m)
  rw [hm]
  change AddMonoidAlgebra.single m 1 =
    TensorGroupEquiv.tensorGroupAlgEquiv
      (AddMonoidAlgebra.single m 1 ⊗ₜ[k] (1 : SymmetricAlgebra k (Fin n → k)))
  simp

end
end GaloisForLFunctions.HTGeometry
