import GaloisForLFunctions.HTGeometry.CDGARelTensorDescent
import GaloisForLFunctions.HTGeometry.CDGATensorShiftHom
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The shift descent is a map of differential graded modules

The comparison of `M ⊗ N[−k]` with `(M ⊗ N)[−k]` respects the action and the differential, and it
carries relations to relations, so the induced map on the tensor products over the algebra respects
them too.  Being degreewise bijective, it is a full quasi-isomorphism.

* `HTGeometry.relTensorShiftHom` : `M ⊗_A N[−k] ≅ (M ⊗_A N)[−k]` as differential graded modules.
* `HTGeometry.relTensorShiftHom_naturality` : naturality in the left variable.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

variable (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
  (Q : CDGAModuleStructure A N) (k : ℕ)

/-- **The shift passes through the tensor product over the algebra**, as differential graded
modules. -/
noncomputable def relTensorShiftHom :
    CDGAModuleHom (relTensorModule P (shiftModule Q k)) (shiftModule (relTensorModule P Q) k) where
  toFun n f := relTensorShiftMap P Q k n f
  map_add n f f' := map_add (relTensorShiftMap P Q k n) f f'
  map_smul n c f := map_smul (relTensorShiftMap P Q k n) c f
  map_act := by
    intro b n m h x f
    refine Quotient.inductionOn' f fun z => ?_
    funext r
    obtain ⟨a, ha⟩ := r
    show Submodule.Quotient.mk
        (tensorShiftMap (R := R) (M := M) (N := N) k m
          (tensorAct P (shiftModule Q k) h x z) ⟨a, ha⟩)
      = shiftAct (relTensorModule P Q) k h x
          (relTensorShiftMap P Q k n (Submodule.Quotient.mk z)) ⟨a, ha⟩
    rw [tensorShiftMap_tensorAct P Q k h x z]
    by_cases hb : b ≤ a
    · obtain ⟨i, rfl⟩ := Nat.le.dest hb
      have hi : i + k = n := by omega
      rw [shiftAct_apply_add (tensorModule P Q) k h x _ hi ha,
        shiftAct_apply_add (relTensorModule P Q) k h x _ hi ha]
      rfl
    · rw [shiftAct_of_lt (tensorModule P Q) k h x _ ha hb,
        shiftAct_of_lt (relTensorModule P Q) k h x _ ha hb]
      rfl
  map_d := by
    intro n f
    refine Quotient.inductionOn' f fun z => ?_
    funext r
    obtain ⟨a, ha⟩ := r
    show Submodule.Quotient.mk
        (tensorShiftMap (R := R) (M := M) (N := N) k (n + 1)
          (tensorD P (shiftModule Q k) n z) ⟨a, ha⟩)
      = shiftD (relTensorModule P Q) k n
          (relTensorShiftMap P Q k n (Submodule.Quotient.mk z)) ⟨a, ha⟩
    rw [show tensorShiftMap (R := R) (M := M) (N := N) k (n + 1)
        (tensorD P (shiftModule Q k) n z)
      = shiftD (tensorModule P Q) k n (tensorShiftMap (R := R) (M := M) (N := N) k n z) from
      (tensorShiftHom P Q k).map_d n z]
    cases a with
    | zero => rw [shiftD_zero, shiftD_zero]; rfl
    | succ a' => rw [shiftD_succ, shiftD_succ]; rfl

@[simp] theorem relTensorShiftHom_toFun (n : ℕ)
    (f : RelTensorCarrier P (shiftModule Q k) n) :
    (relTensorShiftHom P Q k).toFun n f = relTensorShiftMap P Q k n f := rfl

theorem relTensorShiftHom_isQuasiIsoFull : (relTensorShiftHom P Q k).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => relTensorShiftMap_bijective P Q k n

/-- The shift descent is natural in the left variable. -/
theorem relTensorShiftHom_naturality (φ : CDGAModuleHom P P') :
    (relTensorShiftHom P' Q k).comp (relTensorMapLeft φ (shiftModule Q k))
      = (shiftMap (relTensorMapLeft φ Q) k).comp (relTensorShiftHom P Q k) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  refine Quotient.inductionOn' f fun z => ?_
  funext r
  obtain ⟨a, ha⟩ := r
  show Submodule.Quotient.mk
      (tensorShiftMap (R := R) (M := M') (N := N) k n
        ((tensorMapLeft φ (shiftModule Q k)).toFun n z) ⟨a, ha⟩)
    = (relTensorMapLeft φ Q).toFun a
        (Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨a, ha⟩))
  exact congrArg Submodule.Quotient.mk
    (tensorMapLeft_tensorShiftMap φ Q k n z ⟨a, ha⟩)

end GaloisForLFunctions.HTGeometry
