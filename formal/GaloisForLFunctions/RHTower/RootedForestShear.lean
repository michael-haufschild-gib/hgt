import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceTargetMeasure
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Forest coordinates on a finite phase torus

A rooted forest on a finite vertex set is a parent map together with a depth that strictly
decreases along it.  The associated *forest shear* replaces every nonroot phase by its chord to the
phase of its parent and leaves the roots alone.  It is a continuous group automorphism of the phase
torus, hence preserves normalized Haar measure, and it turns the forest chords into independent
coordinates.

This is the coordinate system in which a coherence-graph sublevel set becomes a product of circle
chord balls.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- A rooted forest on a vertex type: a parent map with a strictly decreasing depth. -/
structure RootedForest (V : Type*) where
  /-- The parent of a vertex; a root is its own parent. -/
  parent : V → V
  /-- The depth of a vertex; roots are exactly the vertices of depth zero. -/
  depth : V → ℕ
  /-- Depth strictly decreases from a nonroot to its parent. -/
  depth_parent_lt : ∀ v, depth v ≠ 0 → depth (parent v) < depth v
  /-- A root is its own parent. -/
  parent_root : ∀ v, depth v = 0 → parent v = v

namespace RootedForest

variable {V : Type*} {A : Type*} [AddCommGroup A]

/-- The vertices of depth zero. -/
def IsRoot (T : RootedForest V) (v : V) : Prop := T.depth v = 0

/-- The forest shear: every nonroot phase is replaced by its chord to its parent. -/
def shear (T : RootedForest V) (x : V → A) : V → A :=
  fun v => if T.depth v = 0 then x v else x v - x (T.parent v)

set_option linter.unusedVariables false in
/-- The inverse of the forest shear, obtained by summing chords down to the root. -/
def unshear (T : RootedForest V) (y : V → A) : V → A
  | v => if h : T.depth v = 0 then y v else y v + T.unshear y (T.parent v)
  termination_by v => T.depth v
  decreasing_by exact T.depth_parent_lt _ h

theorem shear_root (T : RootedForest V) (x : V → A) {v : V} (h : T.depth v = 0) :
    T.shear x v = x v := by
  simp [shear, h]

theorem shear_of_ne (T : RootedForest V) (x : V → A) {v : V} (h : T.depth v ≠ 0) :
    T.shear x v = x v - x (T.parent v) := by
  simp [shear, h]

theorem unshear_root (T : RootedForest V) (y : V → A) {v : V} (h : T.depth v = 0) :
    T.unshear y v = y v := by
  rw [unshear]
  simp [h]

theorem unshear_of_ne (T : RootedForest V) (y : V → A) {v : V} (h : T.depth v ≠ 0) :
    T.unshear y v = y v + T.unshear y (T.parent v) := by
  rw [unshear]
  simp [h]

theorem unshear_shear (T : RootedForest V) (x : V → A) : T.unshear (T.shear x) = x := by
  funext v
  induction hn : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
      by_cases h : T.depth v = 0
      · rw [unshear_root _ _ h, shear_root _ _ h]
      · rw [unshear_of_ne _ _ h, shear_of_ne _ _ h,
          ih (T.depth (T.parent v)) (by rw [← hn]; exact T.depth_parent_lt v h) (T.parent v) rfl]
        abel

theorem shear_unshear (T : RootedForest V) (y : V → A) : T.shear (T.unshear y) = y := by
  funext v
  by_cases h : T.depth v = 0
  · rw [shear_root _ _ h, unshear_root _ _ h]
  · rw [shear_of_ne _ _ h, unshear_of_ne _ _ h]
    abel

theorem shear_add (T : RootedForest V) (x y : V → A) :
    T.shear (x + y) = T.shear x + T.shear y := by
  funext v
  by_cases h : T.depth v = 0
  · simp [shear, h]
  · simp only [shear, h, ↓reduceIte, Pi.add_apply]
    abel

/-- The forest shear as an additive automorphism of the phase group. -/
def shearEquiv (T : RootedForest V) : (V → A) ≃+ (V → A) where
  toFun := T.shear
  invFun := T.unshear
  left_inv := fun x => T.unshear_shear x
  right_inv := fun y => T.shear_unshear y
  map_add' := T.shear_add

@[simp] theorem shearEquiv_apply (T : RootedForest V) (x : V → A) :
    T.shearEquiv x = T.shear x := rfl

section Topology

variable [Fintype V]

omit [Fintype V] in
theorem continuous_shear (T : RootedForest V) :
    Continuous (T.shear : (V → UnitAddCircle) → (V → UnitAddCircle)) := by
  classical
  refine continuous_pi fun v => ?_
  by_cases h : T.depth v = 0
  · simp only [shear, h, ↓reduceIte]
    exact continuous_apply v
  · simp only [shear, h, ↓reduceIte]
    fun_prop

omit [Fintype V] in
theorem continuous_unshear (T : RootedForest V) :
    Continuous (T.unshear : (V → UnitAddCircle) → (V → UnitAddCircle)) := by
  classical
  refine continuous_pi fun v => ?_
  induction hn : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
      by_cases h : T.depth v = 0
      · simp only [funext fun y : V → UnitAddCircle => unshear_root T y h]
        exact continuous_apply v
      · have hcont : Continuous
            fun y : V → UnitAddCircle => T.unshear y (T.parent v) :=
          ih (T.depth (T.parent v)) (by rw [← hn]; exact T.depth_parent_lt v h)
            (T.parent v) rfl
        simp only [funext fun y : V → UnitAddCircle => unshear_of_ne T y h]
        exact (continuous_apply v).add hcont

/-- **The forest shear preserves normalized Haar measure exactly.** -/
theorem measurePreserving_shear (T : RootedForest V) :
    MeasurePreserving (T.shear : (V → UnitAddCircle) → (V → UnitAddCircle)) :=
  (T.shearEquiv (A := UnitAddCircle)).toAddMonoidHom.measurePreserving
    T.continuous_shear (T.shearEquiv (A := UnitAddCircle)).surjective rfl

end Topology

end RootedForest

end

end RHTower

namespace RHTower

namespace RootedForest

noncomputable section

variable {V : Type*}

/-- The undirected graph whose edges are the parent links of the forest. -/
def forestGraph (T : RootedForest V) : SimpleGraph V where
  Adj p q := p ≠ q ∧ (T.parent p = q ∨ T.parent q = p)
  symm := by
    constructor
    rintro p q ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩
  loopless := by
    constructor
    rintro p ⟨hne, -⟩
    exact hne rfl

theorem forestGraph_adj_parent (T : RootedForest V) {v : V} (h : v ≠ T.parent v) :
    (T.forestGraph).Adj v (T.parent v) := ⟨h, Or.inl rfl⟩

theorem depth_ne_zero_of_parent_ne (T : RootedForest V) {v : V} (h : T.parent v ≠ v) :
    T.depth v ≠ 0 := fun hd => h (T.parent_root v hd)

/-- **Chord bound along a forest walk.**  A phase family whose forest chords are at most `δ` has
every walk chord at most the walk length times `δ`. -/
theorem norm_sub_le_walk_length_mul {A : Type*} [NormedAddCommGroup A]
    (T : RootedForest V) (f : V → A) {δ : ℝ}
    (hchord : ∀ p q : V, (T.forestGraph).Adj p q → ‖f p - f q‖ ≤ δ)
    {u v : V} (w : (T.forestGraph).Walk u v) :
    ‖f u - f v‖ ≤ (w.length : ℝ) * δ := by
  induction w with
  | nil => simp
  | @cons u b v hadj w ih =>
      have hsplit : f u - f v = (f u - f b) + (f b - f v) := by abel
      calc ‖f u - f v‖ = ‖(f u - f b) + (f b - f v)‖ := by rw [hsplit]
        _ ≤ ‖f u - f b‖ + ‖f b - f v‖ := norm_add_le _ _
        _ ≤ δ + (w.length : ℝ) * δ := add_le_add (hchord u b hadj) ih
        _ = ((w.length + 1 : ℕ) : ℝ) * δ := by push_cast; ring
        _ = ((SimpleGraph.Walk.cons hadj w).length : ℝ) * δ := by
              rw [SimpleGraph.Walk.length_cons]

end

end RootedForest

end RHTower
