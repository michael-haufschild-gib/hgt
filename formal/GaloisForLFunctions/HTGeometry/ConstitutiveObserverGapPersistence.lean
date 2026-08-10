import GaloisForLFunctions.HTGeometry.ConstitutiveObserverExecutionGap

/-!
# Observer gap-death persistence

Positive fibre observers compose strictly.  Along any serial observer history issued from a
locally admitted law, symbolic--execution gaps propagate backward and their absence propagates
forward.  Hence a gap can die at most once and cannot revive under later positive observation.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- Kernel observation is the identity on coordinates. -/
@[simp] theorem observerFailureKernel_id
    {α : Type u} [DecidableEq α] (K : Finset α) :
    observerFailureKernel id K = K := by
  ext x
  simp [observerFailureKernel]

/-- Failure-family observation is the identity on coordinates. -/
@[simp] theorem observerFailureFamily_id
    {α : Type u} [DecidableEq α] (H : Finset (Finset α)) :
    observerFailureFamily id H = H := by
  ext K
  simp [observerFailureFamily]

/-- Fibre-sum observation is the identity on weights. -/
@[simp] theorem observerRepairWeight_id
    {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℕ) :
    observerRepairWeight id a = a := by
  funext x
  simp [observerRepairWeight]

/-- Kernel images compose strictly. -/
theorem observerFailureKernel_comp
    {α : Type u} {β : Type v} {γ : Type w}
    [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (K : Finset α) :
    observerFailureKernel (g ∘ f) K =
      observerFailureKernel g (observerFailureKernel f K) := by
  ext z
  simp [observerFailureKernel]

/-- Failure-family images compose strictly. -/
theorem observerFailureFamily_comp
    {α : Type u} {β : Type v} {γ : Type w}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (H : Finset (Finset α)) :
    observerFailureFamily (g ∘ f) H =
      observerFailureFamily g (observerFailureFamily f H) := by
  ext L
  simp [observerFailureFamily, observerFailureKernel]

/-- Positive fibre-sum weights compose strictly. -/
theorem observerRepairWeight_comp
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (a : α → ℕ) :
    observerRepairWeight (g ∘ f) a =
      observerRepairWeight g (observerRepairWeight f a) := by
  classical
  funext z
  simp only [observerRepairWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : g (f x) = z
  · simp [h]
  · simp [h]

/-- A two-stage observed gap persists backward through both observer stages. -/
theorem weightedSymbolicExecutionGap_twoStep_backward
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H m a)
    (hgap : WeightedSymbolicExecutionGap
      (observerFailureFamily g (observerFailureFamily f H)) m
      (observerRepairWeight g (observerRepairWeight f a))) :
    WeightedSymbolicExecutionGap
        (observerFailureFamily f H) m (observerRepairWeight f a) ∧
      WeightedSymbolicExecutionGap H m a := by
  have hlocal₁ : WeightedLocalRepair
      (observerFailureFamily f H) m (observerRepairWeight f a) :=
    weightedLocalRepair_observer_forward f H m a hlocal
  have hgap₁ : WeightedSymbolicExecutionGap
      (observerFailureFamily f H) m (observerRepairWeight f a) :=
    weightedSymbolicExecutionGap_observer_noncreation g
      (observerFailureFamily f H) m (observerRepairWeight f a) hlocal₁ hgap
  exact ⟨hgap₁,
    weightedSymbolicExecutionGap_observer_noncreation f H m a hlocal hgap₁⟩

/-- Once a gap has died after one positive observer, it cannot revive after a second. -/
theorem weightedSymbolicExecutionGap_twoStep_noRevival
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H m a)
    (hdead : ¬ WeightedSymbolicExecutionGap
      (observerFailureFamily f H) m (observerRepairWeight f a)) :
    ¬ WeightedSymbolicExecutionGap
      (observerFailureFamily g (observerFailureFamily f H)) m
      (observerRepairWeight g (observerRepairWeight f a)) := by
  intro hgap
  exact hdead (weightedSymbolicExecutionGap_twoStep_backward
    f g H m a hlocal hgap).1

/-- Any successor-hereditary obstruction predicate is an initial-segment predicate. -/
theorem hereditaryObstruction_of_le
    (alive : ℕ → Prop) (hstep : ∀ n, alive (n + 1) → alive n)
    {i j : ℕ} (hij : i ≤ j) (hj : alive j) : alive i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => simpa using hj
  | succ k ih =>
      apply ih
      apply hstep (i + k)
      simpa [Nat.add_assoc] using hj

/-- The triangle gap dies at its collapse observer and remains dead after every later positive
observer. -/
theorem triangleCollapseObserver_gapDeath_permanent
    {γ : Type w} [DecidableEq γ] (g : Fin 2 → γ) :
    WeightedSymbolicExecutionGap triangleFailureFamily 2 (triangleSymbolicWeight 1) ∧
      (¬ WeightedSymbolicExecutionGap
        (observerFailureFamily triangleCollapseObserver triangleFailureFamily) 2
        (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1))) ∧
      ¬ WeightedSymbolicExecutionGap
        (observerFailureFamily g
          (observerFailureFamily triangleCollapseObserver triangleFailureFamily)) 2
        (observerRepairWeight g
          (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1))) := by
  refine ⟨triangleCollapseObserver_erases_gap.1,
    triangleCollapseObserver_erases_gap.2, ?_⟩
  exact weightedSymbolicExecutionGap_twoStep_noRevival
    triangleCollapseObserver g triangleFailureFamily 2 (triangleSymbolicWeight 1)
    (triangleSymbolicWeight_local 1) triangleCollapseObserver_erases_gap.2

/-- Closed capstone: strict observer composition, hereditary gap history, no revival, and an exact
triangle death witness. -/
theorem observerGapDeathFiltrationMechanism_closed :
    (∀ (α β γ : Type) (_ : Fintype α) (_ : Fintype β)
      (_ : DecidableEq α) (_ : DecidableEq β) (_ : DecidableEq γ)
      (f : α → β) (g : β → γ) (H : Finset (Finset α)),
      observerFailureFamily (g ∘ f) H =
        observerFailureFamily g (observerFailureFamily f H)) ∧
    (∀ (α β γ : Type) (_ : Fintype α) (_ : Fintype β)
      (_ : DecidableEq β) (_ : DecidableEq γ)
      (f : α → β) (g : β → γ) (a : α → ℕ),
      observerRepairWeight (g ∘ f) a =
        observerRepairWeight g (observerRepairWeight f a)) ∧
    (∀ (alive : ℕ → Prop), (∀ n, alive (n + 1) → alive n) →
      ∀ i j, i ≤ j → alive j → alive i) ∧
    (∀ (γ : Type) (_ : DecidableEq γ) (g : Fin 2 → γ),
      WeightedSymbolicExecutionGap triangleFailureFamily 2 (triangleSymbolicWeight 1) ∧
        (¬ WeightedSymbolicExecutionGap
          (observerFailureFamily triangleCollapseObserver triangleFailureFamily) 2
          (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1))) ∧
        ¬ WeightedSymbolicExecutionGap
          (observerFailureFamily g
            (observerFailureFamily triangleCollapseObserver triangleFailureFamily)) 2
          (observerRepairWeight g
            (observerRepairWeight triangleCollapseObserver (triangleSymbolicWeight 1)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β γ instFα instFβ instα instβ instγ f g H
    letI : Fintype α := instFα
    letI : Fintype β := instFβ
    letI : DecidableEq α := instα
    letI : DecidableEq β := instβ
    letI : DecidableEq γ := instγ
    exact observerFailureFamily_comp f g H
  · intro α β γ instFα instFβ instβ instγ f g a
    letI : Fintype α := instFα
    letI : Fintype β := instFβ
    letI : DecidableEq β := instβ
    letI : DecidableEq γ := instγ
    exact observerRepairWeight_comp f g a
  · intro alive hstep i j hij hj
    exact hereditaryObstruction_of_le alive hstep hij hj
  · intro γ instγ g
    letI : DecidableEq γ := instγ
    exact triangleCollapseObserver_gapDeath_permanent g

end GaloisForLFunctions.HTGeometry
