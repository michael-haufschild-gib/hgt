import GaloisForLFunctions.HTGeometry.CDGARelTensorDescent
import GaloisForLFunctions.HTGeometry.CDGATensorConstHom

/-!
# The constant descent is a map of differential graded modules

The constant exchange respects the action and the differential and carries relations to relations,
so the induced map on the tensor products over the algebra respects them too.  Being degreewise
bijective, it is a full quasi-isomorphism.

* `HTGeometry.relTensorConstHom` : `(M ⊗_A N) ⊗ V ≅ M ⊗_A (N ⊗ V)` as differential graded modules.
* `HTGeometry.relTensorConstHom_naturality` : naturality in the left variable.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {V : Type w} [AddCommGroup V] [Module R V]

variable (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
  (Q : CDGAModuleStructure A N)

/-- **A constant coefficient module passes through the tensor product over the algebra**, as
differential graded modules. -/
noncomputable def relTensorConstHom :
    CDGAModuleHom (tensorConstModule (relTensorModule P Q) V)
      (relTensorModule P (tensorConstModule Q V)) where
  toFun n y := relTensorConstMap P Q (V := V) n y
  map_add n y y' := map_add (relTensorConstMap P Q (V := V) n) y y'
  map_smul n c y := map_smul (relTensorConstMap P Q (V := V) n) c y
  map_act := by
    intro c a n h x y
    show relTensorConstMap P Q (V := V) n
        ((tensorConstModule (relTensorModule P Q) V).actₗ h x y)
      = (relTensorModule P (tensorConstModule Q V)).actₗ h x
        (relTensorConstMap P Q (V := V) a y)
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul q w =>
        refine Quotient.inductionOn' q fun z => ?_
        exact congrArg Submodule.Quotient.mk
          (tensorConstExchange_tensorAct P Q h x (z ⊗ₜ[R] w))
  map_d := by
    intro n y
    show relTensorConstMap P Q (V := V) (n + 1)
        ((tensorConstModule (relTensorModule P Q) V).dₗ n y)
      = (relTensorModule P (tensorConstModule Q V)).dₗ n
        (relTensorConstMap P Q (V := V) n y)
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul q w =>
        refine Quotient.inductionOn' q fun z => ?_
        exact congrArg Submodule.Quotient.mk
          (tensorConstExchange_tensorD P Q n (z ⊗ₜ[R] w))

@[simp] theorem relTensorConstHom_toFun (n : ℕ)
    (y : TensorProduct R (RelTensorCarrier P Q n) V) :
    (relTensorConstHom P Q (V := V)).toFun n y = relTensorConstMap P Q (V := V) n y := rfl

theorem relTensorConstHom_isQuasiIsoFull : (relTensorConstHom P Q (V := V)).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => relTensorConstMap_bijective P Q n

/-- The constant descent is natural in the left variable. -/
theorem relTensorConstHom_naturality (φ : CDGAModuleHom P P') :
    (relTensorMapLeft φ (tensorConstModule Q V)).comp (relTensorConstHom P Q (V := V))
      = (relTensorConstHom P' Q (V := V)).comp (tensorConstMap (relTensorMapLeft φ Q) V) := by
  refine CDGAModuleHom.hom_ext fun n y => ?_
  show (relTensorMapLeft φ (tensorConstModule Q V)).mapₗ n
      (relTensorConstMap P Q (V := V) n y)
    = relTensorConstMap P' Q (V := V) n
      ((tensorConstMap (relTensorMapLeft φ Q) V).mapₗ n y)
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul q w =>
      refine Quotient.inductionOn' q fun z => ?_
      exact congrArg Submodule.Quotient.mk
        (tensorConstExchange_naturality φ Q n (z ⊗ₜ[R] w))

end GaloisForLFunctions.HTGeometry
