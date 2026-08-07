import GaloisForLFunctions.HTGeometry.CDGARelTensorConst
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The constant exchange is a map of differential graded modules

Moving a constant coefficient module out of the second graded factor respects the action and the
differential.  The action and the left half-differential act through the first factor, which the
exchange does not touch; the right half-differential acts through the second factor, and there the
exchange only reorders a tensor.

* `HTGeometry.tensorConstHom` : the exchange as a morphism.
* `HTGeometry.tensorConstHom_naturality` : naturality in the left variable.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {V : Type w} [AddCommGroup V] [Module R V]

section Compat

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- The exchange is equivariant. -/
theorem tensorConstExchange_tensorAct {b n m : ℕ} (h : b + n = m) (x : X b)
    (y : TensorProduct R (TensorCarrier (R := R) M N n) V) :
    tensorConstExchange (R := R) (M := M) (N := N) V m
        ((tensorConstModule (tensorModule P Q) V).actₗ h x y)
      = (tensorModule P (tensorConstModule Q V)).actₗ h x
        (tensorConstExchange (R := R) (M := M) (N := N) V n y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact (((tensorModule P (tensorConstModule Q V)).actₗ h x).map_zero).symm
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul f w =>
      have hsrc : (tensorConstModule (tensorModule P Q) V).actₗ h x (f ⊗ₜ[R] w)
          = tensorAct P Q h x f ⊗ₜ[R] w := rfl
      rw [hsrc]
      funext p
      obtain ⟨⟨α, c⟩, hp⟩ := p
      rw [tensorConstExchange_tmul]
      show TensorProduct.map LinearMap.id ((TensorProduct.mk R (N c) V).flip w)
          (tensorAct P Q h x f ⟨(α, c), hp⟩)
        = tensorAct P (tensorConstModule Q V) h x
          (tensorConstExchange (R := R) (M := M) (N := N) V n (f ⊗ₜ[R] w)) ⟨(α, c), hp⟩
      by_cases hb : b ≤ α
      · obtain ⟨i, hi⟩ : ∃ i, b + i = α := Nat.le.dest hb
        have hin : (i, c).1 + (i, c).2 = n := by
          have : α + c = m := hp
          omega
        rw [tensorAct_apply_eq P Q h x f hi hin hp,
          tensorAct_apply_eq P (tensorConstModule Q V) h x _ hi hin hp,
          tensorConstExchange_tmul]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
          ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
          LinearMap.id_comp, LinearMap.comp_id]
      · rw [tensorAct_of_lt P Q h x f hp hb, map_zero,
          tensorAct_of_lt P (tensorConstModule Q V) h x _ hp hb]

/-- The exchange commutes with the differential. -/
theorem tensorConstExchange_tensorD (n : ℕ)
    (y : TensorProduct R (TensorCarrier (R := R) M N n) V) :
    tensorConstExchange (R := R) (M := M) (N := N) V (n + 1)
        ((tensorConstModule (tensorModule P Q) V).dₗ n y)
      = (tensorModule P (tensorConstModule Q V)).dₗ n
        (tensorConstExchange (R := R) (M := M) (N := N) V n y) := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact (((tensorModule P (tensorConstModule Q V)).dₗ n).map_zero).symm
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul f w =>
      have hsrc : (tensorConstModule (tensorModule P Q) V).dₗ n (f ⊗ₜ[R] w)
          = tensorD P Q n f ⊗ₜ[R] w := rfl
      rw [hsrc]
      funext p
      obtain ⟨⟨α, c⟩, hp⟩ := p
      rw [tensorConstExchange_tmul]
      show TensorProduct.map LinearMap.id ((TensorProduct.mk R (N c) V).flip w)
          (tensorDL P Q n f ⟨(α, c), hp⟩ + tensorDR P Q n f ⟨(α, c), hp⟩)
        = tensorDL P (tensorConstModule Q V) n
            (tensorConstExchange (R := R) (M := M) (N := N) V n (f ⊗ₜ[R] w)) ⟨(α, c), hp⟩
          + tensorDR P (tensorConstModule Q V) n
            (tensorConstExchange (R := R) (M := M) (N := N) V n (f ⊗ₜ[R] w)) ⟨(α, c), hp⟩
      rw [map_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · cases α with
        | zero => rw [tensorDL_zero, tensorDL_zero, map_zero]
        | succ α' =>
            have hprev : (α', c).1 + (α', c).2 = n := by
              have : α' + 1 + c = n + 1 := hp
              omega
            rw [tensorDL_succ, tensorDL_succ, tensorConstExchange_tmul]
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
              ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
              LinearMap.id_comp, LinearMap.comp_id]
      · cases c with
        | zero => rw [tensorDR_zero, tensorDR_zero, map_zero]
        | succ c' =>
            have hprev : (α, c').1 + (α, c').2 = n := by
              have : α + (c' + 1) = n + 1 := hp
              omega
            rw [tensorDR_succ, tensorDR_succ, tensorConstExchange_tmul, map_smul]
            refine congrArg (fun z => ((-1 : R)) ^ α • z) ?_
            have hL : ((TensorProduct.mk R (N (c' + 1)) V).flip w) ∘ₗ Q.dₗ c'
                = ((tensorConstModule Q V).dₗ c') ∘ₗ ((TensorProduct.mk R (N c') V).flip w) :=
              LinearMap.ext fun v => rfl
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
              ← TensorProduct.map_comp, LinearMap.id_comp]
            exact congrArg
              (fun L : N c' →ₗ[R] TensorProduct R (N (c' + 1)) V =>
                (TensorProduct.map (LinearMap.id : M α →ₗ[R] M α) L) (f ⟨(α, c'), hprev⟩)) hL

/-- **The constant exchange as a morphism of differential graded modules.** -/
noncomputable def tensorConstHom :
    CDGAModuleHom (tensorConstModule (tensorModule P Q) V)
      (tensorModule P (tensorConstModule Q V)) where
  toFun n y := tensorConstExchange (R := R) (M := M) (N := N) V n y
  map_add n y y' := map_add (tensorConstExchange (R := R) (M := M) (N := N) V n) y y'
  map_smul n c y := map_smul (tensorConstExchange (R := R) (M := M) (N := N) V n) c y
  map_act h x y := tensorConstExchange_tensorAct P Q h x y
  map_d n y := tensorConstExchange_tensorD P Q n y

@[simp] theorem tensorConstHom_toFun (n : ℕ)
    (y : TensorProduct R (TensorCarrier (R := R) M N n) V) :
    (tensorConstHom P Q (V := V)).toFun n y
      = tensorConstExchange (R := R) (M := M) (N := N) V n y := rfl

theorem tensorConstHom_isQuasiIsoFull : (tensorConstHom P Q (V := V)).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n =>
    tensorConstExchange_bijective (R := R) (M := M) (N := N) V n

end Compat

section Naturality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The constant exchange is natural in the left variable. -/
theorem tensorConstExchange_naturality (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N)
    (n : ℕ) (y : TensorProduct R (TensorCarrier (R := R) M N n) V) :
    (tensorMapLeft φ (tensorConstModule Q V)).mapₗ n
        (tensorConstExchange (R := R) (M := M) (N := N) V n y)
      = tensorConstExchange (R := R) (M := M') (N := N) V n
        ((tensorConstMap (tensorMapLeft φ Q) V).mapₗ n y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | tmul f w =>
      funext p
      obtain ⟨⟨α, c⟩, hp⟩ := p
      have hsrc : (tensorConstMap (tensorMapLeft φ Q) V).mapₗ n (f ⊗ₜ[R] w)
          = (tensorMapLeft φ Q).toFun n f ⊗ₜ[R] w := rfl
      rw [hsrc]
      show TensorProduct.map (φ.mapₗ α) LinearMap.id
          (tensorConstExchange (R := R) (M := M) (N := N) V n (f ⊗ₜ[R] w) ⟨(α, c), hp⟩)
        = tensorConstExchange (R := R) (M := M') (N := N) V n
          ((tensorMapLeft φ Q).toFun n f ⊗ₜ[R] w) ⟨(α, c), hp⟩
      rw [tensorConstExchange_tmul, tensorConstExchange_tmul]
      show TensorProduct.map (φ.mapₗ α) LinearMap.id
          (TensorProduct.map LinearMap.id ((TensorProduct.mk R (N c) V).flip w)
            (f ⟨(α, c), hp⟩))
        = TensorProduct.map LinearMap.id ((TensorProduct.mk R (N c) V).flip w)
          (TensorProduct.map (φ.mapₗ α) LinearMap.id (f ⟨(α, c), hp⟩))
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
        ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.id_comp, LinearMap.comp_id]

theorem tensorConstHom_naturality (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) :
    (tensorMapLeft φ (tensorConstModule Q V)).comp (tensorConstHom P Q (V := V))
      = (tensorConstHom P' Q (V := V)).comp (tensorConstMap (tensorMapLeft φ Q) V) :=
  CDGAModuleHom.hom_ext fun n y => tensorConstExchange_naturality φ Q n y

end Naturality

end GaloisForLFunctions.HTGeometry
