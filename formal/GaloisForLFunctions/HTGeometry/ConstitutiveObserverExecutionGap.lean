import GaloisForLFunctions.HTGeometry.ConstitutiveFailureAntichainQuotient
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect

/-!
# Observer transport of symbolic-execution gaps

Finite positive fibre aggregation transports both local admission and legal execution.  It cannot
create a symbolic-execution gap from an executable source law, but a noninjective observer can
erase the triangle gap by manufacturing a shared repair.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Image of one failure kernel under a possibly noninjective observer. -/
def observerFailureKernel {α : Type u} {β : Type v}
    [DecidableEq β] (f : α → β) (K : Finset α) : Finset β :=
  K.image f

/-- Observer image of a finite failure family. -/
def observerFailureFamily {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (H : Finset (Finset α)) : Finset (Finset β) :=
  H.image (observerFailureKernel f)

/-- Positive fibre-sum transport of a natural-valued repair weight. -/
def observerRepairWeight {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq β]
    (f : α → β) (a : α → ℕ) : β → ℕ :=
  fun y => ∑ x : α, if f x = y then a x else 0

/-- Fibre aggregation over an observed kernel equals source aggregation over its saturated
preimage. -/
theorem observerFailureKernel_sum_observerRepairWeight
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (K : Finset α) (a : α → ℕ) :
    (∑ y ∈ observerFailureKernel f K, observerRepairWeight f a y) =
      ∑ x : α, if f x ∈ observerFailureKernel f K then a x else 0 := by
  classical
  simp [observerRepairWeight, Finset.sum_comm]

/-- A source kernel's total repair weight is bounded by the total weight seen on its observer
image. -/
theorem failureKernel_sum_le_observerFailureKernel_sum
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (K : Finset α) (a : α → ℕ) :
    (∑ x ∈ K, a x) ≤
      ∑ y ∈ observerFailureKernel f K, observerRepairWeight f a y := by
  classical
  let S : Finset α := Finset.univ.filter fun x => f x ∈ observerFailureKernel f K
  have hKS : K ⊆ S := by
    intro x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    (∑ x ∈ K, a x) ≤ ∑ x ∈ S, a x := Finset.sum_le_sum_of_subset hKS
    _ = ∑ x : α, if f x ∈ observerFailureKernel f K then a x else 0 := by
      simp only [S, Finset.sum_filter]
    _ = ∑ y ∈ observerFailureKernel f K, observerRepairWeight f a y :=
      (observerFailureKernel_sum_observerRepairWeight f K a).symm

/-- Positive observer transport preserves local symbolic admission. -/
theorem weightedLocalRepair_observer_forward
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H m a) :
    WeightedLocalRepair (observerFailureFamily f H) m (observerRepairWeight f a) := by
  intro L hL
  rw [observerFailureFamily] at hL
  obtain ⟨K, hKH, rfl⟩ := Finset.mem_image.mp hL
  exact (hlocal K hKH).trans (failureKernel_sum_le_observerFailureKernel_sum f K a)

/-- Fibre summation transports pointwise domination of a finite execution. -/
theorem observerRepairWeight_piece_sum_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq β]
    (f : α → β) (m : ℕ) (pieces : Fin m → α → ℕ) (a : α → ℕ)
    (hdom : ∀ x, ∑ j : Fin m, pieces j x ≤ a x) :
    ∀ y, ∑ j : Fin m, observerRepairWeight f (pieces j) y ≤ observerRepairWeight f a y := by
  classical
  intro y
  simp only [observerRepairWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hxy : f x = y
  · simpa [hxy] using hdom x
  · simp [hxy]

/-- Positive observer transport preserves actual legal execution. -/
theorem weightedExecutableRepair_observer_forward
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (hexec : WeightedExecutableRepair H m a) :
    WeightedExecutableRepair (observerFailureFamily f H) m (observerRepairWeight f a) := by
  obtain ⟨pieces, hpieces, hdom⟩ := hexec
  exact ⟨fun j => observerRepairWeight f (pieces j),
    fun j => weightedLocalRepair_observer_forward f H 1 (pieces j) (hpieces j),
    observerRepairWeight_piece_sum_le f m pieces a hdom⟩

/-- An observed gap of a locally admitted source state must already have been a source gap. -/
theorem weightedSymbolicExecutionGap_observer_noncreation
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H m a)
    (hgap : WeightedSymbolicExecutionGap
      (observerFailureFamily f H) m (observerRepairWeight f a)) :
    WeightedSymbolicExecutionGap H m a := by
  exact ⟨hlocal, fun hexec =>
    hgap.2 (weightedExecutableRepair_observer_forward f H m a hexec)⟩

/-- Collapse the first two vertices of the triangle and retain the third. -/
def triangleCollapseObserver (i : Fin 3) : Fin 2 :=
  if i = 2 then 1 else 0

/-- The observed triangle failure family has one singleton and one two-point kernel. -/
theorem triangleCollapseObserver_failureFamily :
    observerFailureFamily triangleCollapseObserver triangleFailureFamily =
      {{0}, {0, 1}} := by
  ext K
  simp [observerFailureFamily, observerFailureKernel, triangleFailureFamily,
    triangleCollapseObserver]

/-- The central triangle weight becomes `(2,1)` after collapse. -/
theorem triangleCollapseObserver_weight :
    observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1) =
      fun y : Fin 2 => if y = 0 then 2 else 1 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext x
    fin_cases x <;> simp
  funext y
  fin_cases y <;>
    simp [observerRepairWeight, huniv, triangleCollapseObserver, triangleSymbolicWeight]

/-- Two copies of the shared observed repair execute the collapsed grade-two triangle law. -/
theorem triangleCollapseObserver_executable :
    WeightedExecutableRepair
      (observerFailureFamily triangleCollapseObserver triangleFailureFamily) 2
      (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1)) := by
  rw [triangleCollapseObserver_failureFamily, triangleCollapseObserver_weight]
  refine ⟨fun _j y => if y = 0 then 1 else 0, ?_, ?_⟩
  · intro j K hK
    simp at hK
    rcases hK with rfl | rfl <;> simp
  · intro y
    fin_cases y <;> simp

/-- The triangle is an exact source gap whose positive observer image is executable. -/
theorem triangleCollapseObserver_erases_gap :
    WeightedSymbolicExecutionGap triangleFailureFamily 2 (triangleSymbolicWeight 1) ∧
      ¬ WeightedSymbolicExecutionGap
        (observerFailureFamily triangleCollapseObserver triangleFailureFamily) 2
        (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1)) := by
  constructor
  · exact ⟨triangleSymbolicWeight_local 1,
      triangleSymbolicWeight_not_executable 1 (by omega)⟩
  · intro hgap
    exact hgap.2 triangleCollapseObserver_executable

/-- The two source vertices identified by the triangle observer carry disjoint unit profiles. -/
def triangleCollapseLeftProfile (i : Fin 3) : ℝ :=
  if i = 0 then 1 else 0

/-- The second unit profile identified with the first by the triangle observer. -/
def triangleCollapseRightProfile (i : Fin 3) : ℝ :=
  if i = 1 then 1 else 0

/-- The same identification that erases the execution gap manufactures one unit of false overlap. -/
theorem triangleCollapseObserver_falseOverlap :
    _root_.HTGeometry.finiteOverlapDefect
      triangleCollapseLeftProfile triangleCollapseRightProfile triangleCollapseObserver 0 = 1 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext x
    fin_cases x <;> simp
  simp [_root_.HTGeometry.finiteOverlapDefect, _root_.HTGeometry.finiteSignedFiberMass,
    _root_.HTGeometry.finiteProfileMeet, triangleCollapseLeftProfile,
    triangleCollapseRightProfile, triangleCollapseObserver, huniv]

/-- Closed capstone: positive observers preserve admission and execution, cannot create a gap, but
the triangle collapse erases a source gap while producing positive false overlap. -/
theorem observerExecutionGapMechanism_closed :
    (∀ (α β : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : DecidableEq β)
      (f : α → β) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ),
      WeightedLocalRepair H m a →
        WeightedLocalRepair (observerFailureFamily f H) m (observerRepairWeight f a)) ∧
    (∀ (α β : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : DecidableEq β)
      (f : α → β) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ),
      WeightedExecutableRepair H m a →
        WeightedExecutableRepair (observerFailureFamily f H) m (observerRepairWeight f a)) ∧
    WeightedSymbolicExecutionGap triangleFailureFamily 2 (triangleSymbolicWeight 1) ∧
    (¬ WeightedSymbolicExecutionGap
      (observerFailureFamily triangleCollapseObserver triangleFailureFamily) 2
      (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1))) ∧
    _root_.HTGeometry.finiteOverlapDefect
      triangleCollapseLeftProfile triangleCollapseRightProfile triangleCollapseObserver 0 = 1 := by
  refine ⟨?_, ?_, triangleCollapseObserver_erases_gap.1,
    triangleCollapseObserver_erases_gap.2, triangleCollapseObserver_falseOverlap⟩
  · intro α β instF instα instβ f H m a hlocal
    letI : Fintype α := instF
    letI : DecidableEq α := instα
    letI : DecidableEq β := instβ
    exact weightedLocalRepair_observer_forward f H m a hlocal
  · intro α β instF instα instβ f H m a hexec
    letI : Fintype α := instF
    letI : DecidableEq α := instα
    letI : DecidableEq β := instβ
    exact weightedExecutableRepair_observer_forward f H m a hexec

end GaloisForLFunctions.HTGeometry
