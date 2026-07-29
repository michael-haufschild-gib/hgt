import Mathlib

/-!
# Event topological-debt conservation

This file proves the additive core of the kernel/image/cokernel index obstruction for an event.
The target is an arbitrary additive commutative group. It can therefore receive numerical rank,
a Grothendieck-group class, or any other additive invariant without building those interpretations
into the theorem.

If a source splits additively into kernel plus transmitted class and its target into transmitted
plus cokernel class, then kernel-minus-cokernel equals source-minus-target. These differences
telescope along every finite composable history, so a closed history has zero total absolute debt.

The theorem does not construct topological K-theory, vector bundles, a relative defect class,
spacetime, gravity, or event dynamics.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [AddCommGroup A]

/-- The signed difference between what an event removes and what it creates. -/
def eventDebt (kernel cokernel : A) : A :=
  kernel - cokernel

/-- Additivity through the transmitted sector makes event debt equal parent debt. -/
theorem eventDebt_eq_source_sub_target
    (source kernel transmitted target cokernel : A)
    (hsource : source = kernel + transmitted)
    (htarget : target = transmitted + cokernel) :
    eventDebt kernel cokernel = source - target := by
  simp only [eventDebt]
  rw [hsource, htarget]
  abel

/-- Kernel and cokernel classes agree exactly when source and target classes agree. -/
theorem kernel_eq_cokernel_iff_source_eq_target
    (source kernel transmitted target cokernel : A)
    (hsource : source = kernel + transmitted)
    (htarget : target = transmitted + cokernel) :
    kernel = cokernel ↔ source = target := by
  have hdebt :
      kernel - cokernel = source - target := by
    simpa only [eventDebt] using
      eventDebt_eq_source_sub_target source kernel transmitted target cokernel hsource htarget
  constructor
  · intro h
    rw [h, sub_self] at hdebt
    exact sub_eq_zero.mp hdebt.symm
  · intro h
    rw [h, sub_self] at hdebt
    exact sub_eq_zero.mp hdebt

/-- Adjacent differences telescope over every finite history. -/
theorem sum_range_state_sub_succ (state : ℕ → A) (n : ℕ) :
    (∑ j ∈ Finset.range n, (state j - state (j + 1))) = state 0 - state n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- Local event debts telescope to the difference between history endpoints. -/
theorem eventDebt_history_telescope
    (state kernel transmitted cokernel : ℕ → A) (n : ℕ)
    (hsource : ∀ j < n, state j = kernel j + transmitted j)
    (htarget : ∀ j < n, state (j + 1) = transmitted j + cokernel j) :
    (∑ j ∈ Finset.range n, eventDebt (kernel j) (cokernel j)) =
      state 0 - state n := by
  calc
    (∑ j ∈ Finset.range n, eventDebt (kernel j) (cokernel j)) =
        ∑ j ∈ Finset.range n, (state j - state (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact eventDebt_eq_source_sub_target
        (state j) (kernel j) (transmitted j) (state (j + 1)) (cokernel j)
        (hsource j hjn) (htarget j hjn)
    _ = state 0 - state n := sum_range_state_sub_succ state n

/-- A finite history that returns to its initial parent has zero total event debt. -/
theorem eventDebt_closed_history_eq_zero
    (state kernel transmitted cokernel : ℕ → A) (n : ℕ)
    (hsource : ∀ j < n, state j = kernel j + transmitted j)
    (htarget : ∀ j < n, state (j + 1) = transmitted j + cokernel j)
    (hclosed : state n = state 0) :
    (∑ j ∈ Finset.range n, eventDebt (kernel j) (cokernel j)) = 0 := by
  rw [eventDebt_history_telescope state kernel transmitted cokernel n hsource htarget,
    hclosed, sub_self]

end GaloisForLFunctions.HTGeometry
