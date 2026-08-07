import GaloisForLFunctions.HTGeometry.CDGATensorConst

/-!
# A module placed in a single degree

The cells of a tower that is semi-free over the *ground ring* are modules concentrated in one
degree, with zero differential and zero action — the algebra acts trivially, which is a legitimate
differential graded module because every axiom is an identity between zeros.

Indexing the concentration by `PLift (n = k)` makes the component in the wrong degree an empty
product, so it is trivial with no separate case, exactly as in `ShiftCarrier`.

* `HTGeometry.ConstCellCarrier`, `HTGeometry.constCellModule` : the cell.
* `HTGeometry.constCellEval` : its component in the concentration degree.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {V : Type w} [AddCommGroup V] [Module R V]

/-- The underlying graded module of a module placed in a single degree. -/
def ConstCellCarrier (V : Type w) (k n : ℕ) : Type w := ∀ _ : PLift (n = k), V

instance (k n : ℕ) : AddCommGroup (ConstCellCarrier V k n) :=
  inferInstanceAs (AddCommGroup (∀ _ : PLift (n = k), V))

instance (k n : ℕ) : Module R (ConstCellCarrier V k n) :=
  inferInstanceAs (Module R (∀ _ : PLift (n = k), V))

@[simp] theorem constCellCarrier_add_apply {k n : ℕ} (f g : ConstCellCarrier V k n)
    (p : PLift (n = k)) : (f + g) p = f p + g p := rfl

@[simp] theorem constCellCarrier_smul_apply {k n : ℕ} (c : R) (f : ConstCellCarrier V k n)
    (p : PLift (n = k)) : (c • f) p = c • f p := rfl

/-- Away from the concentration degree the cell is trivial. -/
theorem constCellCarrier_subsingleton {k n : ℕ} (h : n ≠ k) :
    Subsingleton (ConstCellCarrier V k n) :=
  ⟨fun f g => funext fun p => absurd p.down h⟩

/-- **A module placed in a single degree**, with zero differential and zero action. -/
def constCellModule (A : CDGAStructure R X) (V : Type w) [AddCommGroup V] [Module R V] (k : ℕ) :
    CDGAModuleStructure A (ConstCellCarrier V k) where
  act _ _ _ := 0
  d _ _ := 0
  act_add_left _ _ _ _ := (add_zero 0).symm
  act_add_right _ _ _ _ := (add_zero 0).symm
  act_smul_left _ _ _ _ := (smul_zero _).symm
  act_smul_right _ _ _ _ := (smul_zero _).symm
  act_assoc _ _ _ _ _ _ _ := rfl
  d_add _ _ _ := (add_zero 0).symm
  d_smul _ _ _ := (smul_zero _).symm
  d_d _ _ := rfl
  d_act _ _ _ := by
    rw [smul_zero, add_zero]

@[simp] theorem constCellModule_d (k n : ℕ) (f : ConstCellCarrier V k n) :
    (constCellModule A V k).d n f = 0 := rfl

@[simp] theorem constCellModule_act (k : ℕ) {a b n : ℕ} (h : a + b = n) (x : X a)
    (f : ConstCellCarrier V k b) : (constCellModule A V k).act h x f = 0 := rfl

/-- Evaluation of the cell in its concentration degree. -/
def constCellEval (k : ℕ) : ConstCellCarrier V k k →ₗ[R] V where
  toFun f := f (PLift.up rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cell in its concentration degree is the coefficient module. -/
def constCellEvalEquiv (k : ℕ) : ConstCellCarrier V k k ≃ₗ[R] V where
  toFun f := f (PLift.up rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := fun _ => v
  left_inv f := by
    funext p
    rfl
  right_inv _ := rfl

/-- The constant embedding of the coefficient module into a component of the cell. -/
def constCellConst {k n : ℕ} : V →ₗ[R] ConstCellCarrier V k n where
  toFun v := fun _ => v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem constCellEval_constCellConst (k : ℕ) (v : V) :
    constCellEval (R := R) k (constCellConst (R := R) (V := V) (k := k) (n := k) v) = v := rfl

end GaloisForLFunctions.HTGeometry
