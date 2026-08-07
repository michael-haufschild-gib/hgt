import GaloisForLFunctions.HTGeometry.CDGATensor
import GaloisForLFunctions.HTGeometry.CDGAConstCell
import GaloisForLFunctions.HTGeometry.CDGAFreeCoefficients

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
  free coefficients preserves full quasi-isomorphisms.
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

end GaloisForLFunctions.HTGeometry
