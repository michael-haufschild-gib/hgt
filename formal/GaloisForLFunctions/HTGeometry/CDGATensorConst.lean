import GaloisForLFunctions.HTGeometry.CDGAShift

/-!
# Tensoring a differential graded module with a constant module

Tensoring degreewise with a fixed `R`-module changes neither the grading nor which structure map
does what: the differential and the action act on the left factor and the second factor is carried
along.  With the degree shift this is the whole of a free cell — `freeCellModule A V k` is literally
the shift by `k` of the algebra tensored with `V`, which is what `freeCellModule_eq` records.

* `HTGeometry.tensorConstModule` : the tensor product with a constant module.
* `HTGeometry.tensorConstMap` : its functoriality.
* `HTGeometry.freeCellModule_eq` : the free cell is the shift of the algebra tensored with `V`.
-/

universe u v w w'

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- **The tensor product of a differential graded module with a constant module.** -/
def tensorConstModule (P : CDGAModuleStructure A M) (V : Type w') [AddCommGroup V] [Module R V] :
    CDGAModuleStructure A (fun n => TensorProduct R (M n) V) where
  act h x z := TensorProduct.map (P.actₗ h x) LinearMap.id z
  d n z := TensorProduct.map (P.dₗ n) LinearMap.id z
  act_add_left h x x' z := by
    rw [show P.actₗ h (x + x') = P.actₗ h x + P.actₗ h x' from
      LinearMap.ext fun m => P.act_add_left h x x' m, TensorProduct.map_add_left]
    rfl
  act_add_right h x z z' := map_add _ z z'
  act_smul_left h c x z := by
    rw [show P.actₗ h (c • x) = c • P.actₗ h x from
      LinearMap.ext fun m => P.act_smul_left h c x m, TensorProduct.map_smul_left]
    rfl
  act_smul_right h c x z := map_smul _ c z
  act_assoc h₁ h₂ h₃ h₄ x y z := by
    have hcomp : P.actₗ h₂ (A.mul h₁ x y) = (P.actₗ h₄ x).comp (P.actₗ h₃ y) :=
      LinearMap.ext fun m => P.act_assoc h₁ h₂ h₃ h₄ x y m
    have hmaps : TensorProduct.map (P.actₗ h₂ (A.mul h₁ x y)) (LinearMap.id : V →ₗ[R] V)
        = (TensorProduct.map (P.actₗ h₄ x) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (P.actₗ h₃ y) (LinearMap.id : V →ₗ[R] V)) := by
      rw [← TensorProduct.map_comp, hcomp, LinearMap.id_comp]
    exact congrArg (fun L => L z) hmaps
  d_add n z z' := map_add _ z z'
  d_smul n c z := map_smul _ c z
  d_d n z := by
    have hcomp : (P.dₗ (n + 1)).comp (P.dₗ n) = 0 := LinearMap.ext fun m => P.d_d n m
    have hmaps : (TensorProduct.map (P.dₗ (n + 1)) (LinearMap.id : V →ₗ[R] V)).comp
        (TensorProduct.map (P.dₗ n) (LinearMap.id : V →ₗ[R] V)) = 0 := by
      rw [← TensorProduct.map_comp, hcomp, TensorProduct.map_zero_left]
    exact congrArg (fun L => L z) hmaps
  d_act := by
    intro a b n h x z
    have hpt : (P.dₗ n).comp (P.actₗ h x)
        = P.actₗ (show a + 1 + b = n + 1 by omega) (A.d a x)
          + ((-1 : R)) ^ a • (P.actₗ (show a + (b + 1) = n + 1 by omega) x).comp (P.dₗ b) :=
      LinearMap.ext fun m => P.d_act h x m
    have hmaps : (TensorProduct.map (P.dₗ n) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (P.actₗ h x) (LinearMap.id : V →ₗ[R] V))
        = TensorProduct.map (P.actₗ (show a + 1 + b = n + 1 by omega) (A.d a x))
            (LinearMap.id : V →ₗ[R] V)
          + ((-1 : R)) ^ a • (TensorProduct.map
              (P.actₗ (show a + (b + 1) = n + 1 by omega) x) (LinearMap.id : V →ₗ[R] V)).comp
              (TensorProduct.map (P.dₗ b) (LinearMap.id : V →ₗ[R] V)) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hpt,
        TensorProduct.map_add_left, TensorProduct.map_smul_left, LinearMap.id_comp]
    exact congrArg (fun L => L z) hmaps

@[simp] theorem tensorConstModule_d (P : CDGAModuleStructure A M) (V : Type w')
    [AddCommGroup V] [Module R V] (n : ℕ) (z : TensorProduct R (M n) V) :
    (tensorConstModule P V).d n z = TensorProduct.map (P.dₗ n) LinearMap.id z := rfl

@[simp] theorem tensorConstModule_act (P : CDGAModuleStructure A M) (V : Type w')
    [AddCommGroup V] [Module R V] {a b n : ℕ} (h : a + b = n)
    (x : X a) (z : TensorProduct R (M b) V) :
    (tensorConstModule P V).act h x z = TensorProduct.map (P.actₗ h x) LinearMap.id z := rfl

/-- **The free cell is the shift of the algebra tensored with the coefficient module.** -/
theorem freeCellModule_eq (A : CDGAStructure R X) (V : Type v) [AddCommGroup V] [Module R V]
    (k : ℕ) :
    freeCellModule A V k
      = shiftModule (tensorConstModule (CDGAStructure.selfModule A) V) k := rfl

section Functoriality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- **Tensoring with a constant module is functorial.** -/
def tensorConstMap (φ : CDGAModuleHom P P') (V : Type w') [AddCommGroup V] [Module R V] :
    CDGAModuleHom (tensorConstModule P V) (tensorConstModule P' V) where
  toFun n z := TensorProduct.map (φ.mapₗ n) LinearMap.id z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act h x z := by
    have hcomm : (TensorProduct.map (φ.mapₗ _) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (P.actₗ h x) (LinearMap.id : V →ₗ[R] V))
        = (TensorProduct.map (P'.actₗ h x) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (φ.mapₗ _) (LinearMap.id : V →ₗ[R] V)) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
      congr 1
      exact LinearMap.ext fun m => φ.map_act h x m
    exact congrArg (fun L => L z) hcomm
  map_d n z := by
    have hcomm : (TensorProduct.map (φ.mapₗ (n + 1)) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (P.dₗ n) (LinearMap.id : V →ₗ[R] V))
        = (TensorProduct.map (P'.dₗ n) (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (φ.mapₗ n) (LinearMap.id : V →ₗ[R] V)) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
      congr 1
      exact LinearMap.ext fun m => φ.map_d n m
    exact congrArg (fun L => L z) hcomm

@[simp] theorem tensorConstMap_toFun (φ : CDGAModuleHom P P') (V : Type w') [AddCommGroup V]
    [Module R V] (n : ℕ) (z : TensorProduct R (M n) V) :
    (tensorConstMap φ V).toFun n z = TensorProduct.map (φ.mapₗ n) LinearMap.id z := rfl

/-- **Tensoring with a constant module is functorial in that module too.** -/
def tensorConstVMap (P : CDGAModuleStructure A M) {V W : Type w'} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (ψ : V →ₗ[R] W) :
    CDGAModuleHom (tensorConstModule P V) (tensorConstModule P W) where
  toFun n z := TensorProduct.map LinearMap.id ψ z
  map_add n z z' := map_add _ z z'
  map_smul n c z := map_smul _ c z
  map_act h x z := by
    have hcomm : (TensorProduct.map (LinearMap.id : M _ →ₗ[R] M _) ψ).comp
          (TensorProduct.map (P.actₗ h x) (LinearMap.id : V →ₗ[R] V))
        = (TensorProduct.map (P.actₗ h x) (LinearMap.id : W →ₗ[R] W)).comp
          (TensorProduct.map (LinearMap.id : M _ →ₗ[R] M _) ψ) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
    exact congrArg (fun L => L z) hcomm
  map_d n z := by
    have hcomm : (TensorProduct.map (LinearMap.id : M (n + 1) →ₗ[R] M (n + 1)) ψ).comp
          (TensorProduct.map (P.dₗ n) (LinearMap.id : V →ₗ[R] V))
        = (TensorProduct.map (P.dₗ n) (LinearMap.id : W →ₗ[R] W)).comp
          (TensorProduct.map (LinearMap.id : M n →ₗ[R] M n) ψ) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
    exact congrArg (fun L => L z) hcomm

@[simp] theorem tensorConstVMap_toFun (P : CDGAModuleStructure A M) {V W : Type w'}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (ψ : V →ₗ[R] W) (n : ℕ)
    (z : TensorProduct R (M n) V) :
    (tensorConstVMap P ψ).toFun n z = TensorProduct.map LinearMap.id ψ z := rfl

/-- A linear isomorphism of coefficient modules gives a degreewise bijection. -/
theorem tensorConstVMap_bijective (P : CDGAModuleStructure A M) {V W : Type w'}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (n : ℕ) :
    Function.Bijective ((tensorConstVMap P (e : V →ₗ[R] W)).toFun n) :=
  (TensorProduct.congr (LinearEquiv.refl R (M n)) e).bijective

end Functoriality

end GaloisForLFunctions.HTGeometry
