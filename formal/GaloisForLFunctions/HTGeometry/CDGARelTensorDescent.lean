import GaloisForLFunctions.HTGeometry.CDGARelTensorShift

/-!
# The shift comparison descends to the tensor product over the algebra

The relations are stable under the shift comparison, which is exactly the hypothesis of
`Submodule.liftQ`, so the comparison descends: `M ⊗_A N[−k]` maps to the shift of `M ⊗_A N`.

* `HTGeometry.relTensorShiftMap` : the descended comparison.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

section ShiftDescent

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (k : ℕ)

/-- The shift comparison composed with the quotient maps, before descent. -/
noncomputable def relTensorShiftPre (n : ℕ) :
    TensorCarrier (R := R) M (ShiftCarrier N k) n →ₗ[R]
      ShiftCarrier (fun m => RelTensorCarrier P Q m) k n where
  toFun z := fun r => Submodule.Quotient.mk
    (tensorShiftMap (R := R) (M := M) (N := N) k n z r)
  map_add' z z' := by
    funext r
    show Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n (z + z') r) = _
    rw [map_add]
    rfl
  map_smul' c z := by
    funext r
    show Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n (c • z) r) = _
    rw [map_smul]
    rfl

theorem relTensorShiftPre_ker (n : ℕ) (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    (hz : z ∈ relTensorRel P (shiftModule Q k) n) :
    relTensorShiftPre P Q k n z = 0 := by
  funext r
  exact (Submodule.Quotient.mk_eq_zero _).2 (relTensorRel_tensorShiftMap P Q k n z hz r)

/-- **The shift comparison descends to the tensor product over the algebra.** -/
noncomputable def relTensorShiftMap (n : ℕ) :
    RelTensorCarrier P (shiftModule Q k) n →ₗ[R]
      ShiftCarrier (fun m => RelTensorCarrier P Q m) k n :=
  Submodule.liftQ _ (relTensorShiftPre P Q k n)
    (fun z hz => relTensorShiftPre_ker P Q k n z hz)

@[simp] theorem relTensorShiftMap_mk (n : ℕ)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n) (r : {a : ℕ // a + k = n}) :
    relTensorShiftMap P Q k n (Submodule.Quotient.mk z) r
      = Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n z r) := rfl

/-- **The descended comparison is surjective**, because the comparison and the quotient maps are. -/
theorem relTensorShiftMap_surjective (n : ℕ) :
    Function.Surjective (relTensorShiftMap P Q k n) := by
  intro g
  obtain ⟨z, hz⟩ : ∃ z : TensorCarrier (R := R) M (ShiftCarrier N k) n,
      ∀ r, Submodule.Quotient.mk
        (tensorShiftMap (R := R) (M := M) (N := N) k n z r) = g r := by
    classical
    obtain ⟨y, hy⟩ : ∃ y : ShiftCarrier (TensorCarrier (R := R) M N) k n,
        ∀ r, Submodule.Quotient.mk (y r) = g r := by
      refine ⟨fun r => Quotient.out (g r), fun r => ?_⟩
      exact Quotient.out_eq (g r)
    obtain ⟨z, hz⟩ := tensorShiftMap_surjective (R := R) (M := M) (N := N) k n y
    exact ⟨z, fun r => by rw [hz]; exact hy r⟩
  exact ⟨Submodule.Quotient.mk z, funext hz⟩

end ShiftDescent

end GaloisForLFunctions.HTGeometry
