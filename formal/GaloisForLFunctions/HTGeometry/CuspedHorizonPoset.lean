import GaloisForLFunctions.HTGeometry.ProjectiveFlagDimension
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The all-depth horizon poset

A vertex of the all-depth horizon poset is a nonzero proper subspace together with a derivative
depth; a vertex of depth beyond the first is carried only by a line.  Depth-one vertices are ordered
by reverse inclusion, and a deeper vertex is comparable only to vertices carried by the **same**
line, where the order is by depth.

That is the classification: the poset is the depth-one building poset with one disjoint chain
attached below each line, distinct cusps meeting nowhere.  Everything here is order theory; the
homotopy statements the card draws from it are not.
-/

namespace GaloisForLFunctions.HTGeometry

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

/-- A vertex of the all-depth horizon poset: a nonzero proper subspace with a depth, where any depth
beyond the first is carried by a line. -/
structure CuspedVertex where
  /-- The subspace of covectors cutting out the horizon. -/
  space : Submodule K V
  /-- The derivative depth, counted from zero. -/
  depth : ℕ
  ne_bot : space ≠ ⊥
  ne_top : space ≠ ⊤
  finrank_of_depth : depth ≠ 0 → Module.finrank K space = 1

variable {K V}

namespace CuspedVertex

/-- The all-depth order: depth never decreases downwards, depth-one vertices are ordered by reverse
inclusion, and a deeper vertex sits below its own line only. -/
instance : LE (CuspedVertex K V) where
  le v w := w.depth ≤ v.depth ∧ (v.depth = 0 → w.space ≤ v.space) ∧
    (v.depth ≠ 0 → w.space = v.space)

theorem le_def {v w : CuspedVertex K V} :
    v ≤ w ↔ w.depth ≤ v.depth ∧ (v.depth = 0 → w.space ≤ v.space) ∧
      (v.depth ≠ 0 → w.space = v.space) := Iff.rfl

theorem ext' {v w : CuspedVertex K V} (hs : v.space = w.space) (hd : v.depth = w.depth) :
    v = w := by
  cases v
  cases w
  simp only [mk.injEq]
  exact ⟨hs, hd⟩

variable [FiniteDimensional K V]

/-- **A nonzero subspace of a line is that line.** -/
theorem eq_of_le_line {S ℓ : Submodule K V} (hS : S ≠ ⊥) (hline : Module.finrank K ℓ = 1)
    (hle : S ≤ ℓ) : S = ℓ := by
  have hfin : Module.finrank K S ≤ Module.finrank K ℓ := Submodule.finrank_mono hle
  have hpos : Module.finrank K S ≠ 0 := fun hcon => hS (Submodule.finrank_eq_zero.1 hcon)
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

instance : PartialOrder (CuspedVertex K V) where
  le_refl v := ⟨le_rfl, fun _ => le_rfl, fun _ => rfl⟩
  le_trans u v w huv hvw := by
    obtain ⟨hd1, hs1, ht1⟩ := huv
    obtain ⟨hd2, hs2, ht2⟩ := hvw
    refine ⟨le_trans hd2 hd1, ?_, ?_⟩
    · intro hu0
      have hv0 : v.depth = 0 := by omega
      exact le_trans (hs2 hv0) (hs1 hu0)
    · intro hu0
      have hvu : v.space = u.space := ht1 hu0
      by_cases hv0 : v.depth = 0
      · have hle : w.space ≤ u.space := hvu ▸ hs2 hv0
        exact eq_of_le_line w.ne_bot (u.finrank_of_depth hu0) hle
      · rw [ht2 hv0, hvu]
  le_antisymm v w hvw hwv := by
    obtain ⟨hd1, hs1, ht1⟩ := hvw
    obtain ⟨hd2, hs2, ht2⟩ := hwv
    have hd : v.depth = w.depth := by omega
    refine ext' ?_ hd
    by_cases hv0 : v.depth = 0
    · exact le_antisymm (hs2 (hd ▸ hv0)) (hs1 hv0)
    · exact (ht1 hv0).symm

/-! ## The classification -/

omit [FiniteDimensional K V] in
/-- **A deeper vertex is comparable only to vertices carried by its own line.**  This is the
statement that distinct cusps meet nowhere. -/
theorem space_eq_of_le_of_depth_ne_zero {v w : CuspedVertex K V} (hv : v.depth ≠ 0) (h : v ≤ w) :
    w.space = v.space := h.2.2 hv

omit [FiniteDimensional K V] in
/-- **Two deeper vertices carried by different lines are incomparable.** -/
theorem not_le_of_space_ne {v w : CuspedVertex K V} (hv : v.depth ≠ 0) (hne : w.space ≠ v.space) :
    ¬ v ≤ w := fun h => hne (space_eq_of_le_of_depth_ne_zero hv h)

omit [FiniteDimensional K V] in
/-- **A deeper vertex is below a depth-one vertex only when that vertex is its own line.** -/
theorem eq_space_of_le_depthOne {v w : CuspedVertex K V} (hv : v.depth ≠ 0) (_hw : w.depth = 0)
    (h : v ≤ w) : w.space = v.space := space_eq_of_le_of_depth_ne_zero hv h

omit [FiniteDimensional K V] in
/-- **Each cusp is a chain.**  The vertices carried by one line are totally ordered, by depth. -/
theorem le_total_of_space_eq {v w : CuspedVertex K V} (h : v.space = w.space) :
    v ≤ w ∨ w ≤ v := by
  rcases le_total w.depth v.depth with hd | hd
  · exact Or.inl ⟨hd, fun _ => le_of_eq h.symm, fun _ => h.symm⟩
  · exact Or.inr ⟨hd, fun _ => le_of_eq h, fun _ => h⟩

omit [FiniteDimensional K V] in
/-- **The cusp of a line is a chain in the all-depth poset.** -/
theorem isChain_cusp (ℓ : Submodule K V) :
    IsChain (· ≤ ·) {v : CuspedVertex K V | v.space = ℓ} := by
  intro v hv w hw _
  exact le_total_of_space_eq (by rw [hv, hw])

/-! ## Simplices of the all-depth poset -/

omit [FiniteDimensional K V] in
/-- **Two deeper vertices of a chain lie on the same line.**  A simplex of the all-depth poset meets
at most one cusp. -/
theorem space_eq_of_chain_of_depth_ne_zero {v w : CuspedVertex K V}
    (hv : v.depth ≠ 0) (hw : w.depth ≠ 0) (h : v ≤ w ∨ w ≤ v) :
    v.space = w.space := by
  rcases h with h | h
  · exact (space_eq_of_le_of_depth_ne_zero hv h).symm
  · exact space_eq_of_le_of_depth_ne_zero hw h

omit [FiniteDimensional K V] in
/-- **A depth-one vertex is determined by its subspace.** -/
theorem eq_of_depthOne_of_space_eq {v w : CuspedVertex K V} (hv : v.depth = 0) (hw : w.depth = 0)
    (h : v.space = w.space) : v = w :=
  ext' h (by rw [hv, hw])

variable [DecidableEq (Submodule K V)]

/-- **The depth-one subspaces of a chain form a flag.**  So a simplex of the all-depth poset has at
most `N - 1` depth-one vertices, however deep its cusp segment runs: the topological width is carried
by the depth-one skeleton. -/
theorem card_image_depthOne_le (S : Finset (CuspedVertex K V))
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    ((S.filter (fun v => v.depth = 0)).image CuspedVertex.space).card
      ≤ Module.finrank K V - 1 := by
  refine card_le_finrank_sub_one _ ?_ ?_ ?_
  · intro W hW W' hW'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hW
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hW'
    rw [Finset.mem_filter] at hv hw
    rcases hchain v hv.1 w hw.1 with h | h
    · exact Or.inr (h.2.1 hv.2)
    · exact Or.inl (h.2.1 hw.2)
  · intro W hW
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hW
    exact v.ne_bot
  · intro W hW
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hW
    exact v.ne_top

/-- **And the depth-one vertices themselves are at most `N - 1`.** -/
theorem card_filter_depthOne_le (S : Finset (CuspedVertex K V))
    (hchain : ∀ v ∈ S, ∀ w ∈ S, v ≤ w ∨ w ≤ v) :
    (S.filter (fun v => v.depth = 0)).card ≤ Module.finrank K V - 1 := by
  have hinj : Set.InjOn CuspedVertex.space
      ((S.filter (fun v => v.depth = 0) : Finset (CuspedVertex K V)) :
        Set (CuspedVertex K V)) := by
    intro v hv w hw h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hv hw
    exact eq_of_depthOne_of_space_eq hv.2 hw.2 h
  rw [← Finset.card_image_of_injOn hinj]
  exact card_image_depthOne_le S hchain

/-! ## The retraction to the depth-one skeleton -/

/-- Forgetting the depth of a vertex: a cusp vertex is sent to the depth-one vertex of its own
line, and a depth-one vertex is fixed. -/
def retract (v : CuspedVertex K V) : CuspedVertex K V where
  space := v.space
  depth := 0
  ne_bot := v.ne_bot
  ne_top := v.ne_top
  finrank_of_depth h := absurd rfl h

omit [FiniteDimensional K V] [DecidableEq (Submodule K V)] in
@[simp] theorem retract_space (v : CuspedVertex K V) : (retract v).space = v.space := rfl

omit [FiniteDimensional K V] [DecidableEq (Submodule K V)] in
@[simp] theorem retract_depth (v : CuspedVertex K V) : (retract v).depth = 0 := rfl

omit [FiniteDimensional K V] [DecidableEq (Submodule K V)] in
theorem le_retract (v : CuspedVertex K V) : v ≤ retract v :=
  ⟨Nat.zero_le _, fun _ => le_rfl, fun _ => rfl⟩

omit [DecidableEq (Submodule K V)] in
theorem retract_monotone : Monotone (retract (K := K) (V := V)) := by
  intro v w h
  refine ⟨le_rfl, fun _ => ?_, fun hcon => absurd rfl hcon⟩
  by_cases hv : v.depth = 0
  · exact h.2.1 hv
  · exact le_of_eq (h.2.2 hv)

omit [FiniteDimensional K V] [DecidableEq (Submodule K V)] in
theorem retract_idem (v : CuspedVertex K V) : retract (retract v) = retract v := rfl

/-- **The all-depth poset closes onto its depth-one skeleton.**  Forgetting the depth is monotone,
increases every vertex, and is idempotent: it is a closure operator whose closed elements are exactly
the depth-one vertices.

This is the order-theoretic content of the retraction: a cusp is absorbed into the vertex it hangs
from, uniformly and monotonically. -/
def cuspClosure : ClosureOperator (CuspedVertex K V) :=
  ClosureOperator.mk' retract retract_monotone le_retract
    (fun v => le_of_eq (retract_idem v))

omit [DecidableEq (Submodule K V)] in
@[simp] theorem cuspClosure_apply (v : CuspedVertex K V) : cuspClosure v = retract v := rfl

omit [DecidableEq (Submodule K V)] in
/-- **The closed vertices are exactly the depth-one vertices.** -/
theorem cuspClosure_eq_self_iff (v : CuspedVertex K V) :
    cuspClosure v = v ↔ v.depth = 0 := by
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    exact ext' rfl h.symm

omit [DecidableEq (Submodule K V)] in
/-- **The image of the retraction is the depth-one skeleton.** -/
theorem range_cuspClosure :
    Set.range (fun v : CuspedVertex K V => cuspClosure v) = {v | v.depth = 0} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hv
    exact ⟨v, (cuspClosure_eq_self_iff v).2 hv⟩

/-! ## The retract is the building poset -/

omit [DecidableEq (Submodule K V)] in
/-- **The depth-one skeleton is the poset of nonzero proper subspaces under reverse inclusion.**  So
the retract of the all-depth poset is the depth-one building poset itself, not merely a copy of its
underlying set. -/
def depthOneOrderIso :
    {v : CuspedVertex K V // v.depth = 0} ≃o
      ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ where
  toFun v := OrderDual.toDual ⟨v.1.space, v.1.ne_bot, v.1.ne_top⟩
  invFun S := ⟨⟨(OrderDual.ofDual S).1, 0, (OrderDual.ofDual S).2.1, (OrderDual.ofDual S).2.2,
    fun h => absurd rfl h⟩, rfl⟩
  left_inv v := Subtype.ext (ext' rfl v.2.symm)
  right_inv S := rfl
  map_rel_iff' {v w} := by
    constructor
    · intro h
      exact ⟨le_of_eq (by rw [v.2, w.2]), fun _ => h, fun hcon => absurd v.2 hcon⟩
    · intro h
      exact h.2.1 v.2

/-! ## The homotopy realising the retraction -/

omit [DecidableEq (Submodule K V)] in
/-- **The elementary homotopy from the identity to the retraction.**  A monotone map
`P_infinity(V) × [1] → P_infinity(V)` which is the identity at one end of the interval and the
retraction at the other: the deformation retraction of the statement, at the level of poset maps.

Monotonicity in the time coordinate is exactly `x ≤ retract x`, and in the vertex coordinate exactly
that the retraction is monotone.  Geometric realisation of nerves turns such a map into a homotopy;
that step is general and is not about this poset. -/
def cuspHomotopy : (CuspedVertex K V × Bool) →o CuspedVertex K V where
  toFun p := if p.2 then retract p.1 else p.1
  monotone' := by
    rintro ⟨v, b⟩ ⟨w, c⟩ ⟨hvw, hbc⟩
    cases b
    · cases c
      · simpa using hvw
      · simpa using le_trans hvw (le_retract w)
    · cases c
      · exact absurd hbc (by simp)
      · simpa using retract_monotone hvw

omit [DecidableEq (Submodule K V)] in
@[simp] theorem cuspHomotopy_false (v : CuspedVertex K V) : cuspHomotopy (v, false) = v := rfl

omit [DecidableEq (Submodule K V)] in
@[simp] theorem cuspHomotopy_true (v : CuspedVertex K V) :
    cuspHomotopy (v, true) = retract v := rfl

/-! ## The homotopy over the simplicial interval -/

omit [DecidableEq (Submodule K V)] in
/-- **The elementary homotopy over the interval as mathlib models it.**  The same map as
`cuspHomotopy`, with the interval taken to be `ULift (Fin 2)`, which is the preordered type whose
nerve is the standard `1`-simplex. -/
def cuspHomotopyInterval : (CuspedVertex K V × ULift (Fin 2)) →o CuspedVertex K V where
  toFun p := if p.2.down = 0 then p.1 else retract p.1
  monotone' := by
    rintro ⟨v, i⟩ ⟨w, j⟩ ⟨hvw, hij⟩
    by_cases hi : i.down = 0
    · by_cases hj : j.down = 0
      · simpa [hi, hj] using hvw
      · simpa [hi, hj] using le_trans hvw (le_retract w)
    · have hj : j.down ≠ 0 := by
        intro hcon
        refine hi ?_
        have hle : i.down ≤ j.down := hij
        rw [hcon] at hle
        exact le_antisymm hle (Fin.zero_le _)
      simpa [hi, hj] using retract_monotone hvw

omit [DecidableEq (Submodule K V)] in
@[simp] theorem cuspHomotopyInterval_zero (v : CuspedVertex K V) :
    cuspHomotopyInterval (v, ⟨0⟩) = v := by
  simp [cuspHomotopyInterval]

/-! ## The homotopy as categorical data -/

omit [DecidableEq (Submodule K V)] in
/-- The retraction as a functor of the poset viewed as a category. -/
def retractFunctor : CategoryTheory.Functor (CuspedVertex K V) (CuspedVertex K V) :=
  Monotone.functor retract_monotone

omit [DecidableEq (Submodule K V)] in
/-- The homotopy as a functor out of the poset times the interval.  Its nerve is the map whose
endpoints are the identity and the retraction. -/
def cuspHomotopyFunctor :
    CategoryTheory.Functor (CuspedVertex K V × Bool) (CuspedVertex K V) :=
  Monotone.functor cuspHomotopy.monotone

omit [DecidableEq (Submodule K V)] in
/-- **The natural transformation from the identity to the retraction.**  In a poset every diagram
commutes, so the inequality `x ≤ retract x` is already a natural transformation — the categorical
input to the statement that the nerve of the retraction is homotopic to the identity. -/
def unitToRetract : CategoryTheory.Functor.id (CuspedVertex K V) ⟶ retractFunctor where
  app v := CategoryTheory.homOfLE (le_retract v)
  naturality _ _ _ := Subsingleton.elim _ _

end CuspedVertex

end GaloisForLFunctions.HTGeometry
