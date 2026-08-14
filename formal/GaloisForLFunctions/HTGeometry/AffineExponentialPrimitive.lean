import GaloisForLFunctions.HTGeometry.TensorGroupHopfEquiv
import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf

/-!
# Primitive functions on the affine exponential group

Every primitive regular function on `Gₘⁿ × Gₐⁿ` over a characteristic-zero field
is pulled back from a linear function on the additive factor.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Primitive regular functions on `Gₘⁿ × Gₐⁿ` are additive-linear. -/
theorem coordinateAlgebra_primitive_eq_additive
    {k : Type*} [Field k] [CharZero k] {n : ℕ}
    (p : AffineExponentialGroup.CoordinateAlgebra k n)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    ∃ v : Fin n → k,
      p = (1 : AffineExponentialGroup.TorusCoordinateAlgebra k n) ⊗ₜ[k]
        SymmetricAlgebra.ι k (Fin n → k) v := by
  let e := TensorGroupEquiv.tensorGroupBialgEquiv
    (k := k) (B := SymmetricAlgebra k (Fin n → k))
    (M := Fin n →₀ ℤ)
  have hp' : Coalgebra.comul (R := k) (e p) =
      e p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] e p := by
    rw [← CoalgHomClass.map_comp_comul_apply e p, hp]
    simp
  obtain ⟨v, hv⟩ :=
    GroupGradedPrimitive.primitive_group_symmetric_eq_single_generator
      (Module.Free.chooseBasis k (Fin n → k)) (e p) hp'
  refine ⟨v, e.injective ?_⟩
  change e p = e ((1 : AddMonoidAlgebra k (Fin n →₀ ℤ)) ⊗ₜ[k]
    SymmetricAlgebra.ι k (Fin n → k) v)
  rw [hv]
  change AddMonoidAlgebra.single 0 (SymmetricAlgebra.ι k (Fin n → k) v) =
    TensorGroupEquiv.tensorGroupAlgEquiv
      ((1 : AddMonoidAlgebra k (Fin n →₀ ℤ)) ⊗ₜ[k]
        SymmetricAlgebra.ι k (Fin n → k) v)
  rw [AddMonoidAlgebra.one_def]
  simp

end
end GaloisForLFunctions.HTGeometry
