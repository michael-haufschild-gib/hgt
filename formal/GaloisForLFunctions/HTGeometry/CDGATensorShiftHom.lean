import GaloisForLFunctions.HTGeometry.CDGATensorShift
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The shift comparison is a map of differential graded modules

The comparison of `M ⊗ N[−k]` with `(M ⊗ N)[−k]` respects the action and the differential.  The
action is diagonal on both sides, and the differential splits: the left half is untouched by the
shift, and the right half is intertwined by `shiftEvalAt_shiftD`, the identity that already made the
shift a differential graded module.

* `HTGeometry.tensorShiftHom` : the comparison as a morphism.
* `HTGeometry.tensorMapLeft_tensorShiftMap` : naturality in the left variable.
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

/-- The comparison commutes with the right half-differential. -/
theorem tensorShiftMap_tensorDR (n : ℕ) (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    {α γ d' β : ℕ} (hβ : γ + k = β) (hidx : (α, β).1 + (α, β).2 = n + 1)
    (hp' : (α, γ).1 + (α, γ).2 = d' + 1) (hdk : d' + k = n) :
    TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ β hβ : ShiftCarrier N k β →ₗ[R] N γ))
        (tensorDR P (shiftModule Q k) n z ⟨(α, β), hidx⟩)
      = tensorDR P Q d' (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨d', hdk⟩)
        ⟨(α, γ), hp'⟩ := by
  cases γ with
  | zero =>
      subst hβ
      rw [tensorDR_zero]
      cases k with
      | zero => rw [tensorDR_zero, map_zero]
      | succ k'' =>
          have hzi : (α, 0 + k'').1 + (α, 0 + k'').2 = n := by omega
          have h0 : z ⟨(α, 0 + k''), hzi⟩ = 0 := by
            haveI := shiftCarrier_subsingleton (M := N) (k := k'' + 1) (n := 0 + k'')
              (by omega)
            haveI := tensorShift_component_subsingleton (R := R) (M := M) (N := N)
              (k := k'' + 1) (b := 0 + k'') (by omega) α
            exact Subsingleton.elim _ _
          have hval : tensorDR P (shiftModule Q (k'' + 1)) n z ⟨(α, 0 + (k'' + 1)), hidx⟩
              = 0 := by
            show ((-1 : R)) ^ α • TensorProduct.map LinearMap.id
              ((shiftModule Q (k'' + 1)).dₗ (0 + k'')) (z ⟨(α, 0 + k''), hzi⟩) = 0
            rw [h0, map_zero, smul_zero]
          rw [hval, map_zero]
  | succ γ'' =>
      obtain rfl : β = γ'' + k + 1 := by omega
      have hz : (α, γ'' + k).1 + (α, γ'' + k).2 = n := by omega
      have hz' : (α, γ'').1 + (α, γ'').2 = d' := by omega
      rw [tensorDR_succ, tensorDR_succ, map_smul]
      show ((-1 : R)) ^ α • TensorProduct.map LinearMap.id
          ((shiftEvalAt (R := R) (M := N) k (γ'' + 1) (γ'' + k + 1) hβ :
            ShiftCarrier N k (γ'' + k + 1) →ₗ[R] N (γ'' + 1)))
          (TensorProduct.map LinearMap.id
            ((shiftModule Q k).dₗ (γ'' + k)) (z ⟨(α, γ'' + k), hz⟩))
        = ((-1 : R)) ^ α • TensorProduct.map LinearMap.id (Q.dₗ γ'')
          (TensorProduct.map LinearMap.id
            ((shiftEvalAt (R := R) (M := N) k γ'' (γ'' + k) rfl :
              ShiftCarrier N k (γ'' + k) →ₗ[R] N γ'')) (z ⟨(α, γ'' + k), hz⟩))
      congr 1
      have hcomp : ((shiftEvalAt (R := R) (M := N) k (γ'' + 1) (γ'' + k + 1) hβ :
              ShiftCarrier N k (γ'' + k + 1) →ₗ[R] N (γ'' + 1))).comp
            ((shiftModule Q k).dₗ (γ'' + k))
          = (Q.dₗ γ'').comp
            ((shiftEvalAt (R := R) (M := N) k γ'' (γ'' + k) rfl :
              ShiftCarrier N k (γ'' + k) →ₗ[R] N γ'')) :=
        LinearMap.ext fun f => shiftEvalAt_shiftD Q k γ'' (γ'' + k) rfl f
      have hmaps : (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α)
              ((shiftEvalAt (R := R) (M := N) k (γ'' + 1) (γ'' + k + 1) hβ :
                ShiftCarrier N k (γ'' + k + 1) →ₗ[R] N (γ'' + 1)))).comp
            (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α)
              ((shiftModule Q k).dₗ (γ'' + k)))
          = (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α) (Q.dₗ γ'')).comp
            (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α)
              ((shiftEvalAt (R := R) (M := N) k γ'' (γ'' + k) rfl :
                ShiftCarrier N k (γ'' + k) →ₗ[R] N γ''))) := by
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp]
      exact congrArg (fun L => L (z ⟨(α, γ'' + k), hz⟩)) hmaps

/-- **The shift comparison as a map of differential graded modules.** -/
noncomputable def tensorShiftHom :
    CDGAModuleHom (tensorModule P (shiftModule Q k)) (shiftModule (tensorModule P Q) k) where
  toFun n z := tensorShiftMap (R := R) (M := M) (N := N) k n z
  map_add n z z' := map_add (tensorShiftMap (R := R) (M := M) (N := N) k n) z z'
  map_smul n c z := map_smul (tensorShiftMap (R := R) (M := M) (N := N) k n) c z
  map_act h x z := tensorShiftMap_tensorAct P Q k h x z
  map_d n z := by
    funext r p'
    obtain ⟨c', hc'⟩ := r
    obtain ⟨⟨α, γ⟩, hp'⟩ := p'
    have hp2 : α + γ = c' := hp'
    have hidx : (α, γ + k).1 + (α, γ + k).2 = n + 1 := by omega
    show TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
          ShiftCarrier N k (γ + k) →ₗ[R] N γ))
        (tensorD P (shiftModule Q k) n z ⟨(α, γ + k), hidx⟩)
      = shiftD (tensorModule P Q) k n
        (tensorShiftMap (R := R) (M := M) (N := N) k n z) ⟨c', hc'⟩ ⟨(α, γ), hp'⟩
    have hsplit : tensorD P (shiftModule Q k) n z ⟨(α, γ + k), hidx⟩
        = tensorDL P (shiftModule Q k) n z ⟨(α, γ + k), hidx⟩
          + tensorDR P (shiftModule Q k) n z ⟨(α, γ + k), hidx⟩ := rfl
    rw [hsplit, map_add]
    cases c' with
    | zero =>
        obtain rfl : α = 0 := by omega
        obtain rfl : γ = 0 := by omega
        rw [shiftD_zero, tensorDL_zero, map_zero]
        cases k with
        | zero => omega
        | succ k'' =>
            have hzi : (0, 0 + k'').1 + (0, 0 + k'').2 = n := by omega
            have h0 : z ⟨(0, 0 + k''), hzi⟩ = 0 := by
              haveI := shiftCarrier_subsingleton (M := N) (k := k'' + 1) (n := 0 + k'')
                (by omega)
              haveI := tensorShift_component_subsingleton (R := R) (M := M) (N := N)
                (k := k'' + 1) (b := 0 + k'') (by omega) 0
              exact Subsingleton.elim _ _
            have hval : tensorDR P (shiftModule Q (k'' + 1)) n z ⟨(0, 0 + (k'' + 1)), hidx⟩
                = 0 := by
              show ((-1 : R)) ^ (0 : ℕ) • TensorProduct.map LinearMap.id
                ((shiftModule Q (k'' + 1)).dₗ (0 + k'')) (z ⟨(0, 0 + k''), hzi⟩) = 0
              rw [h0, map_zero, smul_zero]
            rw [hval, map_zero, add_zero]
            rfl
    | succ d' =>
        have hdk : d' + k = n := by omega
        rw [shiftD_succ, tensorShiftMap_tensorDL P Q k n z hidx hp' hdk,
          tensorShiftMap_tensorDR P Q k n z rfl hidx hp' hdk]
        rfl

@[simp] theorem tensorShiftHom_toFun (n : ℕ)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n) :
    (tensorShiftHom P Q k).toFun n z
      = tensorShiftMap (R := R) (M := M) (N := N) k n z := rfl

theorem tensorShiftHom_isQuasiIsoFull : (tensorShiftHom P Q k).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => tensorShiftMap_bijective k n

end Compat


section Naturality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The shift comparison is natural in the left variable. -/
theorem tensorMapLeft_tensorShiftMap (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N)
    (k n : ℕ) (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    (r : {a : ℕ // a + k = n}) :
    tensorShiftMap (R := R) (M := M') (N := N) k n
        ((tensorMapLeft φ (shiftModule Q k)).toFun n z) r
      = (tensorMapLeft φ Q).toFun r.1 (tensorShiftMap (R := R) (M := M) (N := N) k n z r) := by
  funext p'
  obtain ⟨⟨α, γ⟩, hp'⟩ := p'
  have hidx : (α, γ + k).1 + (α, γ + k).2 = n := by
    have h1 := r.2
    have h2 : α + γ = r.1 := hp'
    omega
  show TensorProduct.map LinearMap.id
      ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
        ShiftCarrier N k (γ + k) →ₗ[R] N γ))
      (TensorProduct.map (φ.mapₗ α) LinearMap.id (z ⟨(α, γ + k), hidx⟩))
    = TensorProduct.map (φ.mapₗ α) LinearMap.id
      (TensorProduct.map LinearMap.id
        ((shiftEvalAt (R := R) (M := N) k γ (γ + k) rfl :
          ShiftCarrier N k (γ + k) →ₗ[R] N γ)) (z ⟨(α, γ + k), hidx⟩))
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id]

end Naturality

end GaloisForLFunctions.HTGeometry
