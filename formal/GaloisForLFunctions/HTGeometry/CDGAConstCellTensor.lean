import GaloisForLFunctions.HTGeometry.CDGATensor
import GaloisForLFunctions.HTGeometry.CDGAConstCell
import GaloisForLFunctions.HTGeometry.CDGAFreeCoefficients
import GaloisForLFunctions.HTGeometry.CDGADerivedTensor

/-!
# Tensoring with a single-degree cell

A module tensored with a cell concentrated in degree `k` is the module tensored with the coefficients
and shifted by `k`: all bidegree components with second index different from `k` are trivial, so the
product over bidegrees collapses to the product over `{a // a + k = n}`.

The right half-differential vanishes because the cell has zero differential, which is exactly why
the comparison is a map of differential graded modules and not merely of graded ones.

* `HTGeometry.constCellTensorEquiv` : the comparison, degreewise.
* `HTGeometry.constCellTensorHom` : it is a map of differential graded modules.
* `HTGeometry.tensorMapLeft_constCell_isQuasiIsoFull` : tensoring with a single-degree cell with
  free coefficients preserves full quasi-isomorphisms — the `hcell` hypothesis of the tower theorem.
* `HTGeometry.tensorMapLeft_constCellTower_isQuasiIsoFull` : hence the derived tensor product against
  a tower of such cells is invariant.
-/

universe v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- A tensor product with a trivial module is trivial. -/
theorem tensorProduct_subsingleton_right {N : Type w} [AddCommGroup N] [Module R N]
    [Subsingleton N] (Mo : Type w) [AddCommGroup Mo] [Module R Mo] :
    Subsingleton (TensorProduct R Mo N) := by
  have h : ∀ z : TensorProduct R Mo N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [show n = 0 from Subsingleton.elim _ _, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun z w => by rw [h z, h w]⟩

/-- **A module tensored with a single-degree cell is the module tensored with the coefficients and
shifted.** -/
def constCellTensorEquiv (k n : ℕ) :
    TensorCarrier (R := R) (M := M) (N := ConstCellCarrier V k) n
      ≃ₗ[R] ShiftCarrier (fun a => TensorProduct R (M a) V) k n where
  toFun f := fun q =>
    TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
      (f ⟨(q.1, k), by have := q.2; omega⟩)
  map_add' f g := by
    funext q
    show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
        ((f + g) ⟨(q.1, k), by have := q.2; omega⟩) = _
    rw [tensorCarrier_add_apply, map_add]
    rfl
  map_smul' c f := by
    funext q
    show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
        ((c • f) ⟨(q.1, k), by have := q.2; omega⟩) = _
    rw [tensorCarrier_smul_apply, map_smul]
    rfl
  invFun g := fun p =>
    if h : p.1.2 = k then
      TensorProduct.map LinearMap.id (constCellConst : V →ₗ[R] ConstCellCarrier V k p.1.2)
        (g ⟨p.1.1, by have := p.2; omega⟩)
    else 0
  left_inv f := by
    funext p
    obtain ⟨⟨a, b⟩, hp⟩ := p
    by_cases hb : b = k
    · subst hb
      show (if _h : b = b then
          TensorProduct.map LinearMap.id (constCellConst : V →ₗ[R] ConstCellCarrier V b b)
            (TensorProduct.map LinearMap.id (constCellEval b : ConstCellCarrier V b b →ₗ[R] V)
              (f ⟨(a, b), by omega⟩))
        else 0) = f ⟨(a, b), hp⟩
      rw [dif_pos rfl]
      have hid : (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
            (constCellConst : V →ₗ[R] ConstCellCarrier V b b)).comp
          (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
            (constCellEval b : ConstCellCarrier V b b →ₗ[R] V))
          = LinearMap.id := by
        rw [← TensorProduct.map_comp, LinearMap.id_comp,
          show (constCellConst : V →ₗ[R] ConstCellCarrier V b b).comp
              (constCellEval b : ConstCellCarrier V b b →ₗ[R] V) = LinearMap.id from
            LinearMap.ext fun z => funext fun _ => rfl,
          TensorProduct.map_id]
      exact congrArg (fun L => L (f ⟨(a, b), hp⟩)) hid
    · haveI := constCellCarrier_subsingleton (V := V) (k := k) (n := b) hb
      haveI := tensorProduct_subsingleton_right (R := R) (N := ConstCellCarrier V k b) (M a)
      exact Subsingleton.elim _ _
  right_inv g := by
    funext q
    obtain ⟨a, hq⟩ := q
    show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
        (if _h : k = k then
          TensorProduct.map LinearMap.id (constCellConst : V →ₗ[R] ConstCellCarrier V k k)
            (g ⟨a, by omega⟩)
        else 0) = g ⟨a, hq⟩
    rw [dif_pos rfl]
    have hid : (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
          (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
          (constCellConst : V →ₗ[R] ConstCellCarrier V k k)) = LinearMap.id := by
      rw [← TensorProduct.map_comp, LinearMap.id_comp,
        show (constCellEval k : ConstCellCarrier V k k →ₗ[R] V).comp
            (constCellConst : V →ₗ[R] ConstCellCarrier V k k) = LinearMap.id from
          LinearMap.ext fun _ => rfl,
        TensorProduct.map_id]
    exact congrArg (fun L => L (g ⟨a, hq⟩)) hid

@[simp] theorem constCellTensorEquiv_apply (k n : ℕ)
    (f : TensorCarrier (R := R) (M := M) (N := ConstCellCarrier V k) n)
    (q : {a : ℕ // a + k = n}) :
    constCellTensorEquiv (R := R) (M := M) (V := V) k n f q
      = TensorProduct.map LinearMap.id ((constCellEval k : ConstCellCarrier V k k →ₗ[R] V))
        (f ⟨(q.1, k), by have := q.2; omega⟩) := rfl

section Hom

variable (P : CDGAModuleStructure A M)

/-- The right half-differential vanishes on a tensor product with a single-degree cell, because the
cell has zero differential. -/
theorem tensorDR_constCell (k n a b : ℕ)
    (f : TensorCarrier (R := R) (M := M) (N := ConstCellCarrier V k) n)
    (h : (a, b).1 + (a, b).2 = n + 1) :
    tensorDR P (constCellModule A V k) n f ⟨(a, b), h⟩ = 0 := by
  cases b with
  | zero => rw [tensorDR_zero]
  | succ b' =>
      rw [tensorDR_succ]
      have hz : ((constCellModule A V k).dₗ b' : ConstCellCarrier V k b' →ₗ[R]
          ConstCellCarrier V k (b' + 1)) = 0 := LinearMap.ext fun _ => rfl
      rw [hz]
      have hmap : TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
          (0 : ConstCellCarrier V k b' →ₗ[R] ConstCellCarrier V k (b' + 1)) = 0 := by
        refine TensorProduct.ext' fun m z => ?_
        rw [TensorProduct.map_tmul]
        show m ⊗ₜ[R] (0 : ConstCellCarrier V k (b' + 1)) = 0
        rw [TensorProduct.tmul_zero]
      rw [hmap, LinearMap.zero_apply, smul_zero]

/-- **The comparison is a map of differential graded modules.** -/
def constCellTensorHom (k : ℕ) :
    CDGAModuleHom (tensorModule P (constCellModule A V k))
      (shiftModule (tensorConstModule P V) k) where
  toFun n f := constCellTensorEquiv (R := R) (M := M) (V := V) k n f
  map_add n f g := map_add (constCellTensorEquiv (R := R) (M := M) (V := V) k n) f g
  map_smul n c f := map_smul (constCellTensorEquiv (R := R) (M := M) (V := V) k n) c f
  map_act := by
    intro bA nS mS h x f
    funext q
    obtain ⟨c', hc'⟩ := q
    show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
        (tensorAct P (constCellModule A V k) h x f ⟨(c', k), by omega⟩)
      = shiftAct (tensorConstModule P V) k h x
        (constCellTensorEquiv (R := R) (M := M) (V := V) k nS f) ⟨c', hc'⟩
    by_cases hb : bA ≤ c'
    · obtain ⟨i, hi⟩ : ∃ i, bA + i = c' := Nat.le.dest hb
      rw [tensorAct_apply_eq P (constCellModule A V k) h x f hi (by omega) (by omega),
        shiftAct_apply_eq (tensorConstModule P V) k h x _ hi (by omega) hc']
      show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
          (TensorProduct.map (P.actₗ hi x) LinearMap.id (f ⟨(i, k), by omega⟩))
        = TensorProduct.map (P.actₗ hi x) LinearMap.id
          (TensorProduct.map LinearMap.id
            (constCellEval k : ConstCellCarrier V k k →ₗ[R] V) (f ⟨(i, k), by omega⟩))
      have hcomm : (TensorProduct.map (LinearMap.id : M c' →ₗ[R] M c')
              (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)).comp
            (TensorProduct.map (P.actₗ hi x)
              (LinearMap.id : ConstCellCarrier V k k →ₗ[R] ConstCellCarrier V k k))
          = (TensorProduct.map (P.actₗ hi x) (LinearMap.id : V →ₗ[R] V)).comp
            (TensorProduct.map (LinearMap.id : M i →ₗ[R] M i)
              (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)) := by
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
          LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
      exact congrArg (fun L => L (f ⟨(i, k), by omega⟩)) hcomm
    · rw [tensorAct_of_lt P (constCellModule A V k) h x f (by omega) hb,
        shiftAct_of_lt (tensorConstModule P V) k h x _ hc' hb, map_zero]
  map_d := by
    intro n f
    funext q
    obtain ⟨c', hc'⟩ := q
    have hck : (c', k).1 + (c', k).2 = n + 1 := by omega
    show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
        (tensorD P (constCellModule A V k) n f ⟨(c', k), hck⟩)
      = shiftD (tensorConstModule P V) k n
        (constCellTensorEquiv (R := R) (M := M) (V := V) k n f) ⟨c', hc'⟩
    have hsplit : tensorD P (constCellModule A V k) n f ⟨(c', k), hck⟩
        = tensorDL P (constCellModule A V k) n f ⟨(c', k), hck⟩ := by
      show tensorDL P (constCellModule A V k) n f ⟨(c', k), hck⟩
        + tensorDR P (constCellModule A V k) n f ⟨(c', k), hck⟩ = _
      rw [tensorDR_constCell P k n c' k f hck, add_zero]
    rw [hsplit]
    cases c' with
    | zero => rw [tensorDL_zero, map_zero, shiftD_zero]
    | succ a' =>
        have hak : (a', k).1 + (a', k).2 = n := by omega
        rw [tensorDL_succ, shiftD_succ]
        show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
            (TensorProduct.map (P.dₗ a') LinearMap.id (f ⟨(a', k), hak⟩))
          = TensorProduct.map (P.dₗ a') LinearMap.id
            (TensorProduct.map LinearMap.id
              (constCellEval k : ConstCellCarrier V k k →ₗ[R] V) (f ⟨(a', k), hak⟩))
        have hcomm : (TensorProduct.map (LinearMap.id : M (a' + 1) →ₗ[R] M (a' + 1))
                (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)).comp
              (TensorProduct.map (P.dₗ a')
                (LinearMap.id : ConstCellCarrier V k k →ₗ[R] ConstCellCarrier V k k))
            = (TensorProduct.map (P.dₗ a') (LinearMap.id : V →ₗ[R] V)).comp
              (TensorProduct.map (LinearMap.id : M a' →ₗ[R] M a')
                (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
            LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
        exact congrArg (fun L => L (f ⟨(a', k), hak⟩)) hcomm

theorem constCellTensorHom_bijective (k n : ℕ) :
    Function.Bijective ((constCellTensorHom (V := V) P k).toFun n) :=
  (constCellTensorEquiv (R := R) (M := M) (V := V) k n).bijective

end Hom

section Invariance

variable {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- The comparison is natural in the module. -/
theorem constCellTensorHom_naturality (φ : CDGAModuleHom P P') (k : ℕ) :
    (constCellTensorHom (V := V) P' k).comp (tensorMapLeft φ (constCellModule A V k))
      = (shiftMap (tensorConstMap φ V) k).comp (constCellTensorHom (V := V) P k) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  funext q
  obtain ⟨c', hc'⟩ := q
  have hck : (c', k).1 + (c', k).2 = n := by omega
  show TensorProduct.map LinearMap.id (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)
      (TensorProduct.map (φ.mapₗ c') LinearMap.id (f ⟨(c', k), hck⟩))
    = TensorProduct.map (φ.mapₗ c') LinearMap.id
      (TensorProduct.map LinearMap.id
        (constCellEval k : ConstCellCarrier V k k →ₗ[R] V) (f ⟨(c', k), hck⟩))
  have hcomm : (TensorProduct.map (LinearMap.id : M' c' →ₗ[R] M' c')
          (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)).comp
        (TensorProduct.map (φ.mapₗ c')
          (LinearMap.id : ConstCellCarrier V k k →ₗ[R] ConstCellCarrier V k k))
      = (TensorProduct.map (φ.mapₗ c') (LinearMap.id : V →ₗ[R] V)).comp
        (TensorProduct.map (LinearMap.id : M c' →ₗ[R] M c')
          (constCellEval k : ConstCellCarrier V k k →ₗ[R] V)) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
  exact congrArg (fun L => L (f ⟨(c', k), hck⟩)) hcomm

/-- **Tensoring with a single-degree cell with free coefficients preserves full
quasi-isomorphisms.**  This is the `hcell` hypothesis of the tower theorem, for the cells of a
tower that is semi-free over the ground ring. -/
theorem tensorMapLeft_constCell_isQuasiIsoFull (φ : CDGAModuleHom P P') (hφ : φ.IsQuasiIsoFull)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V) (k : ℕ) :
    (tensorMapLeft φ (constCellModule A V k)).IsQuasiIsoFull := by
  have hP : (constCellTensorHom (V := V) P k).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (constCellTensorHom_bijective P k)
  have hP' : (constCellTensorHom (V := V) P' k).IsQuasiIsoFull :=
    CDGAModuleHom.IsQuasiIsoFull.of_bijective (constCellTensorHom_bijective P' k)
  have h1 : ((constCellTensorHom (V := V) P' k).comp
      (tensorMapLeft φ (constCellModule A V k))).IsQuasiIsoFull := by
    rw [constCellTensorHom_naturality φ k]
    exact CDGAModuleHom.IsQuasiIsoFull.comp (freeCellFunctor_isQuasiIsoFull φ hφ b k) hP
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_right h1 hP'

/-- **The derived tensor product against a tower of single-degree cells with free coefficients is
invariant.**  Both hypotheses of the tower theorem are now available: the base is assumed, and the
cells are discharged by `tensorMapLeft_constCell_isQuasiIsoFull`.  A tower of such cells is what
"semi-free over the ground ring" means. -/
theorem tensorMapLeft_constCellTower_isQuasiIsoFull (φ : CDGAModuleHom P P')
    (hφ : φ.IsQuasiIsoFull)
    {Mb : ℕ → Type w} [∀ n, AddCommGroup (Mb n)] [∀ n, Module R (Mb n)]
    (P₀ : CDGAModuleStructure A Mb)
    {W : ℕ → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {kk : ℕ → ℕ} {ι : ℕ → Type w} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (bb : ∀ i, Module.Basis (ι i) R (W i))
    (τ : ∀ (i : ℕ) (S : CDGAModuleStructure A
        (towerCarrier Mb (fun j => ConstCellCarrier (W j) (kk j)) i)),
      CDGATwist S (constCellModule A (W i) (kk i)))
    (h₀ : (tensorMapLeft φ P₀).IsQuasiIsoFull) :
    ∀ i, (tensorMapLeft φ
      (towerMod P₀ (fun j => constCellModule A (W j) (kk j)) τ i)).IsQuasiIsoFull :=
  tensorMapLeft_tower_isQuasiIsoFull P P' φ P₀ (fun j => constCellModule A (W j) (kk j)) τ h₀
    (fun i => tensorMapLeft_constCell_isQuasiIsoFull φ hφ (bb i) (kk i))

end Invariance

end GaloisForLFunctions.HTGeometry
