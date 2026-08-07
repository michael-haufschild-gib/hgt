import GaloisForLFunctions.HTGeometry.CDGARelTensorDescent
import GaloisForLFunctions.HTGeometry.CDGAUnitor
import GaloisForLFunctions.HTGeometry.CDGATensorConst

/-!
# The free cell computed over the algebra

A free cell is the shift of the algebra tensored with the coefficient module, so tensoring it over
the algebra is computed by the three equivalences already built: the shift passes through, the
constant coefficients pass through, and what is left is the algebra tensored over itself, which the
unitor identifies with the module.

* `HTGeometry.relTensorFreeCellEquiv` : `M ⊗_A (A[−k] ⊗ V) ≃ (M ⊗ V)[−k]`, degreewise.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- **The free cell computed over the algebra.**  Composite of the shift descent, the constant
descent and the unitor. -/
noncomputable def relTensorFreeCellEquiv (P : CDGAModuleStructure A M) (u : CDGAUnit A)
    (hP : CDGAModuleUnital u P) (k n : ℕ) :
    RelTensorCarrier P (freeCellModule A V k) n
      ≃ₗ[R] ShiftCarrier (fun m => TensorProduct R (M m) V) k n :=
  (relTensorShiftEquiv P (tensorConstModule (CDGAStructure.selfModule A) V) k n).trans
    (LinearEquiv.piCongrRight fun r =>
      (relTensorConstEquiv P (CDGAStructure.selfModule A) (V := V) r.1).symm.trans
        (TensorProduct.congr (relUnitorEquiv P u hP r.1) (LinearEquiv.refl R V)))

end GaloisForLFunctions.HTGeometry
