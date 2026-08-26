import GaloisForLFunctions.HTGeometry.GroupGradedHopfPrimitive

/-!
# Tensor/group-graded Hopf equivalence

The tensor coordinate algebra `k[M] ⊗ B` is canonically bialgebra-equivalent
to the group-graded coefficient algebra `B[M]`.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace TensorGroupEquiv

noncomputable section

variable {k B M : Type*} [Field k] [CommSemiring B]
  [Bialgebra k B] [AddCommGroup M]

noncomputable def tensorGroupAlgEquiv :
    AddMonoidAlgebra k M ⊗[k] B ≃ₐ[k] AddMonoidAlgebra B M :=
  (Algebra.TensorProduct.comm k (AddMonoidAlgebra k M) B).trans
    ((AddMonoidAlgebra.scalarTensorEquiv k B).restrictScalars k)

@[simp] theorem tensorGroupAlgEquiv_tmul_single (m : M) (c : k) (b : B) :
    tensorGroupAlgEquiv (AddMonoidAlgebra.single m c ⊗ₜ[k] b) =
      AddMonoidAlgebra.single m (algebraMap k B c * b) := by
  simp [tensorGroupAlgEquiv, Algebra.smul_def, mul_comm]

theorem tensorGroupAlgEquiv_map_one_tmul (z : B ⊗[k] B) :
    (Algebra.TensorProduct.map
      (tensorGroupAlgEquiv (k := k) (B := B) (M := M)).toAlgHom
      (tensorGroupAlgEquiv (k := k) (B := B) (M := M)).toAlgHom)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
        k k k k (AddMonoidAlgebra k M) (AddMonoidAlgebra k M) B B
        ((1 : AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M) ⊗ₜ[k] z)) =
      TensorProduct.map
        (AddMonoidAlgebra.lsingle (R := k) (0 : M))
        (AddMonoidAlgebra.lsingle (R := k) (0 : M)) z := by
  induction z with
  | zero => simp
  | add z w hz hw =>
      rw [TensorProduct.tmul_add, map_add, map_add, hz, hw]
      rw [map_add]
  | tmul z w =>
      simp [tensorGroupAlgEquiv, Algebra.smul_def, Algebra.TensorProduct.one_def,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]

/-- Canonical bialgebra equivalence `k[M] ⊗ B ≃ B[M]`. -/
noncomputable def tensorGroupBialgEquiv :
    AddMonoidAlgebra k M ⊗[k] B ≃ₐc[k] AddMonoidAlgebra B M :=
  BialgEquiv.ofAlgEquiv tensorGroupAlgEquiv (by
    ext <;> simp [tensorGroupAlgEquiv, Algebra.smul_def, mul_comm]) (by
    ext
    · simp [tensorGroupAlgEquiv, Algebra.smul_def, mul_comm,
        AddMonoidAlgebra.comul_single, Algebra.TensorProduct.one_def,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    · rename_i x
      change (Algebra.TensorProduct.map
          (tensorGroupAlgEquiv (k := k) (B := B) (M := M)).toAlgHom
          (tensorGroupAlgEquiv (k := k) (B := B) (M := M)).toAlgHom)
          (Coalgebra.comul (R := k)
            ((1 : AddMonoidAlgebra k M) ⊗ₜ[k] x)) =
        Coalgebra.comul (R := k)
          (tensorGroupAlgEquiv ((1 : AddMonoidAlgebra k M) ⊗ₜ[k] x))
      rw [TensorProduct.comul_tmul]
      simp only [comul_one]
      rw [tensorGroupAlgEquiv_map_one_tmul]
      simp [tensorGroupAlgEquiv, Algebra.smul_def,
        AddMonoidAlgebra.comul_single])

/-- The inverse tensor/group-graded equivalence sends one homogeneous coefficient to its canonical
pure tensor. -/
@[simp] theorem tensorGroupBialgEquiv_symm_single (m : M) (b : B) :
    (tensorGroupBialgEquiv (k := k) (B := B) (M := M)).symm
        (AddMonoidAlgebra.single m b) =
      AddMonoidAlgebra.single m (1 : k) ⊗ₜ[k] b := by
  change (tensorGroupAlgEquiv (k := k) (B := B) (M := M)).symm
      (AddMonoidAlgebra.single m b) = _
  rw [AlgEquiv.symm_apply_eq]
  simp

end
end TensorGroupEquiv
end GaloisForLFunctions.HTGeometry
