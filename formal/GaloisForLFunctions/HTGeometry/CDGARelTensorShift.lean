import GaloisForLFunctions.HTGeometry.CDGATensorShift
import GaloisForLFunctions.HTGeometry.CDGARelTensor

/-!
# The relations of a tensor product with a shifted factor

Under the comparison of `M ⊗ N[−k]` with `(M ⊗ N)[−k]` a relator becomes a relator, one degree
lower: the shift moves the cell argument but changes neither the sign nor the shape, because the
action on a shift is the action, read off above the shift.

* `HTGeometry.tensorShiftMap_relTensorRelator` : the relator correspondence.
* `HTGeometry.relTensorRel_tensorShiftMap` : the relations are stable under the comparison.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **A relator of a tensor product with a shifted factor is a relator, one degree lower.** -/
theorem tensorShiftMap_relTensorRelator (P : CDGAModuleStructure A M)
    (Q : CDGAModuleStructure A N) (k : ℕ) {c a n γ : ℕ}
    (hn : (c + a, γ + k).1 + (c + a, γ + k).2 = n)
    (hn' : (a, c + γ + k).1 + (a, c + γ + k).2 = n)
    (x : X c) (m : M a) (v : ShiftCarrier N k (γ + k))
    (r : {a' : ℕ // a' + k = n}) :
    tensorShiftMap (R := R) (M := M) (N := N) k n
        (relTensorRelator P (shiftModule Q k) (rfl : c + a = c + a)
          (show c + (γ + k) = c + γ + k by omega) hn hn' x m v) r
      = relTensorRelator P Q (rfl : c + a = c + a) (rfl : c + γ = c + γ)
          (show (c + a, γ).1 + (c + a, γ).2 = r.1 by have := r.2; omega)
          (show (a, c + γ).1 + (a, c + γ).2 = r.1 by have := r.2; omega)
          x m (shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl v) := by
  have hr := r.2
  have hsub : ∀ f g : TensorCarrier (R := R) M (ShiftCarrier N k) n,
      tensorShiftMap (R := R) (M := M) (N := N) k n (f - g) r
        = tensorShiftMap (R := R) (M := M) (N := N) k n f r
          - tensorShiftMap (R := R) (M := M) (N := N) k n g r := by
    intro f g
    rw [map_sub]
    rfl
  have hsmul : ∀ (c' : R) (f : TensorCarrier (R := R) M (ShiftCarrier N k) n),
      tensorShiftMap (R := R) (M := M) (N := N) k n (c' • f) r
        = c' • tensorShiftMap (R := R) (M := M) (N := N) k n f r := by
    intro c' f
    rw [map_smul]
    rfl
  have hi1 : (c + a, γ).1 + (c + a, γ).2 = r.1 := by omega
  have hi2 : (a, c + γ).1 + (a, c + γ).2 = r.1 := by omega
  simp only [relTensorRelator]
  rw [hsub, hsmul, tensorShiftMap_tensorSingle, tensorShiftMap_tensorSingle,
    TensorProduct.map_tmul, TensorProduct.map_tmul]
  show ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(c + a, γ), hi1⟩
      ((LinearMap.id (P.act (rfl : c + a = c + a) x m) : M (c + a)) ⊗ₜ[R]
        (shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl v))
    - tensorSingle (N := N) ⟨(a, c + γ), hi2⟩
      ((LinearMap.id m : M a) ⊗ₜ[R]
        (shiftEvalAt (R := R) (M := N) k (c + γ) (c + γ + k) rfl
          (shiftAct Q k (show c + (γ + k) = c + γ + k by omega) x v))) = _
  rw [shiftEvalAt_shiftAct Q k (show c + (γ + k) = c + γ + k by omega) (rfl : γ + k = γ + k)
    (rfl : c + γ + k = c + γ + k) (rfl : c + γ = c + γ) x v]
  rfl

section Stability

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- A relator vanishes when its cell argument does. -/
theorem relTensorRelator_zero_cell {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n) (x : X c) (m : M a) :
    relTensorRelator P Q hα hβ hn hn' x m (0 : N b) = 0 := by
  simp only [relTensorRelator]
  rw [show Q.act hβ x (0 : N b) = 0 from (Q.actₗ hβ x).map_zero,
    TensorProduct.tmul_zero, TensorProduct.tmul_zero, tensorSingle_zero, tensorSingle_zero,
    smul_zero, sub_zero]

/-- **The comparison preserves the relations.** -/
theorem relTensorRel_tensorShiftMap (k n : ℕ)
    (f : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    (hf : f ∈ relTensorRel P (shiftModule Q k) n) (r : {a' : ℕ // a' + k = n}) :
    tensorShiftMap (R := R) (M := M) (N := N) k n f r ∈ relTensorRel P Q r.1 := by
  refine Submodule.span_induction
    (p := fun g _ => tensorShiftMap (R := R) (M := M) (N := N) k n g r
      ∈ relTensorRel P Q r.1) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    subst hα
    by_cases hb : k ≤ b
    · obtain ⟨γ, rfl⟩ : ∃ γ, γ + k = b := ⟨b - k, by omega⟩
      obtain rfl : β = c + γ + k := by omega
      rw [tensorShiftMap_relTensorRelator P Q k hn hn' x m v r]
      exact relTensorRelator_mem P Q _ _ _ _ x m _
    · haveI := shiftCarrier_subsingleton (M := N) (k := k) (n := b) (by omega)
      rw [show v = 0 from Subsingleton.elim _ _,
        relTensorRelator_zero_cell P (shiftModule Q k) rfl hβ hn hn' x m, map_zero]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [map_add]
    exact Submodule.add_mem _ hg hg'
  · intro r' g _ hg
    rw [map_smul]
    exact Submodule.smul_mem _ _ hg

end Stability

end GaloisForLFunctions.HTGeometry
