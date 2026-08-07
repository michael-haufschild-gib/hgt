import GaloisForLFunctions.HTGeometry.CDGATensorShift

/-!
# The shift comparison is a map of differential graded modules

The comparison of `M ⊗ N[−k]` with `(M ⊗ N)[−k]` respects the action and the differential.  The
action is diagonal on both sides, and the differential splits: the left half is untouched by the
shift, and the right half is intertwined by `shiftEvalAt_shiftD`, the identity that already made the
shift a differential graded module.

* `HTGeometry.tensorShiftHom` : the comparison as a morphism.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

section Compat

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (k : ℕ)

/-- The comparison is equivariant. -/
theorem tensorShiftMap_tensorAct {b n m : ℕ} (h : b + n = m) (x : X b)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n) :
    tensorShiftMap (R := R) (M := M) (N := N) k m (tensorAct P (shiftModule Q k) h x z)
      = shiftAct (tensorModule P Q) k h x
        (tensorShiftMap (R := R) (M := M) (N := N) k n z) := by
  funext r p'
  obtain ⟨c', hc'⟩ := r
  obtain ⟨⟨α, γ⟩, hp'⟩ := p'
  have hp2 : α + γ = c' := hp'
  have hidx : (α, γ + k).1 + (α, γ + k).2 = m := by omega
  show TensorProduct.map LinearMap.id
      ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
        ShiftCarrier N k (γ + k) →ₗ[R] N γ))
      (tensorAct P (shiftModule Q k) h x z ⟨(α, γ + k), hidx⟩)
    = shiftAct (tensorModule P Q) k h x
      (tensorShiftMap (R := R) (M := M) (N := N) k n z) ⟨c', hc'⟩ ⟨(α, γ), hp'⟩
  by_cases hb : b ≤ α
  · obtain ⟨i, hi⟩ : ∃ i, b + i = α := Nat.le.dest hb
    have hcb : b ≤ c' := by omega
    obtain ⟨j, hj⟩ : ∃ j, b + j = c' := Nat.le.dest hcb
    have hjk : j + k = n := by omega
    have hij : (i, γ).1 + (i, γ).2 = j := by omega
    have hidx2 : (i, γ + k).1 + (i, γ + k).2 = n := by omega
    rw [tensorAct_apply_eq P (shiftModule Q k) h x z hi hidx2 hidx,
      shiftAct_apply_eq (tensorModule P Q) k h x _ hj hjk hc']
    show TensorProduct.map LinearMap.id _
        (TensorProduct.map (P.actₗ hi x) LinearMap.id (z ⟨(i, γ + k), hidx2⟩))
      = tensorAct P Q hj x (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨j, hjk⟩)
        ⟨(α, γ), hp'⟩
    rw [tensorAct_apply_eq P Q hj x _ hi hij hp']
    show _ = TensorProduct.map (P.actₗ hi x) LinearMap.id
      (TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
          ShiftCarrier N k (γ + k) →ₗ[R] N γ)) (z ⟨(i, γ + k), hidx2⟩))
    have hcomm : (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α)
            ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
              ShiftCarrier N k (γ + k) →ₗ[R] N γ))).comp
          (TensorProduct.map (P.actₗ hi x)
            (LinearMap.id : ShiftCarrier N k (γ + k) →ₗ[R] ShiftCarrier N k (γ + k)))
        = (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N γ →ₗ[R] N γ)).comp
          (TensorProduct.map (LinearMap.id : M i →ₗ[R] M i)
            ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
              ShiftCarrier N k (γ + k) →ₗ[R] N γ))) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
    exact congrArg (fun L => L (z ⟨(i, γ + k), hidx2⟩)) hcomm
  · rw [tensorAct_of_lt P (shiftModule Q k) h x z hidx hb, map_zero]
    by_cases hbc : b ≤ c'
    · obtain ⟨j, hj⟩ : ∃ j, b + j = c' := Nat.le.dest hbc
      have hjk : j + k = n := by omega
      rw [shiftAct_apply_eq (tensorModule P Q) k h x _ hj hjk hc']
      show 0 = tensorAct P Q hj x (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨j, hjk⟩)
        ⟨(α, γ), hp'⟩
      rw [tensorAct_of_lt P Q hj x _ hp' hb]
    · rw [shiftAct_of_lt (tensorModule P Q) k h x _ hc' hbc]
      rfl

/-- The comparison commutes with the left half-differential. -/
theorem tensorShiftMap_tensorDL (n : ℕ) (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    {α γ d' : ℕ} (hidx : (α, γ + k).1 + (α, γ + k).2 = n + 1)
    (hp' : (α, γ).1 + (α, γ).2 = d' + 1) (hdk : d' + k = n) :
    TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
          ShiftCarrier N k (γ + k) →ₗ[R] N γ))
        (tensorDL P (shiftModule Q k) n z ⟨(α, γ + k), hidx⟩)
      = tensorDL P Q d' (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨d', hdk⟩)
        ⟨(α, γ), hp'⟩ := by
  cases α with
  | zero => rw [tensorDL_zero, map_zero, tensorDL_zero]
  | succ a'' =>
      have hi : (a'', γ + k).1 + (a'', γ + k).2 = n := by omega
      have hi' : (a'', γ).1 + (a'', γ).2 = d' := by omega
      rw [tensorDL_succ, tensorDL_succ]
      show TensorProduct.map LinearMap.id _
          (TensorProduct.map (P.dₗ a'') LinearMap.id (z ⟨(a'', γ + k), hi⟩))
        = TensorProduct.map (P.dₗ a'') LinearMap.id
          (TensorProduct.map LinearMap.id
            ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
              ShiftCarrier N k (γ + k) →ₗ[R] N γ)) (z ⟨(a'', γ + k), hi⟩))
      have hcomm : (TensorProduct.map (LinearMap.id : M (a'' + 1) →ₗ[R] M (a'' + 1))
              ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
                ShiftCarrier N k (γ + k) →ₗ[R] N γ))).comp
            (TensorProduct.map (P.dₗ a'')
              (LinearMap.id : ShiftCarrier N k (γ + k) →ₗ[R] ShiftCarrier N k (γ + k)))
          = (TensorProduct.map (P.dₗ a'') (LinearMap.id : N γ →ₗ[R] N γ)).comp
            (TensorProduct.map (LinearMap.id : M a'' →ₗ[R] M a'')
              ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
                ShiftCarrier N k (γ + k) →ₗ[R] N γ))) := by
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
          LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
      exact congrArg (fun L => L (z ⟨(a'', γ + k), hi⟩)) hcomm

end Compat

end GaloisForLFunctions.HTGeometry
