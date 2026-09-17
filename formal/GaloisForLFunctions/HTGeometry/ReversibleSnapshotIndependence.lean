import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Reversible coordinate snapshots and order independence

A local update toggles one Boolean sample coordinate exactly when a permit test succeeds. If the
test is invariant under that same toggle, the update is an involution. Thus every fixed-order
trajectory is an equivalence from initial samples to snapshots. This isolates the reversible-state
mechanism behind the matroid paper's snapshot and conditional-independence lemmas.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- Toggle one coordinate of a Boolean sample vector. -/
def toggleCoordinate (e : α) (state : α → Bool) : α → Bool :=
  Function.update state e (!state e)

@[simp] theorem toggleCoordinate_self (e : α) (state : α → Bool) :
    toggleCoordinate e state e = !state e := by
  simp [toggleCoordinate]

theorem toggleCoordinate_involutive (e : α) :
    Function.Involutive (toggleCoordinate e : (α → Bool) → α → Bool) := by
  intro state
  funext x
  by_cases hx : x = e
  · subst x
    simp
  · simp [toggleCoordinate, hx]

/-- Toggle the current coordinate precisely when the state-dependent permit bit is true. -/
def snapshotStep (permit : α → (α → Bool) → Bool) (e : α)
    (state : α → Bool) : α → Bool :=
  if permit e state = true then toggleCoordinate e state else state

/-- A toggle-invariant permit test makes its local state update exactly reversible. -/
theorem snapshotStep_involutive (permit : α → (α → Bool) → Bool) (e : α)
    (hsym : ∀ state, permit e (toggleCoordinate e state) = permit e state) :
    Function.Involutive (snapshotStep permit e) := by
  intro state
  by_cases h : permit e state = true
  · simp only [snapshotStep, h, if_true, hsym]
    exact toggleCoordinate_involutive e state
  · simp [snapshotStep, h]

def snapshotStepEquiv (permit : α → (α → Bool) → Bool) (e : α)
    (hsym : ∀ state, permit e (toggleCoordinate e state) = permit e state) :
    (α → Bool) ≃ (α → Bool) :=
  (snapshotStep_involutive permit e hsym).toPerm

/-- Composition of all reversible updates in a fixed arrival order. -/
def snapshotEquiv (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state) :
    List α → (α → Bool) ≃ (α → Bool)
  | [] => Equiv.refl _
  | e :: order => (snapshotStepEquiv permit e (hsym e)).trans (snapshotEquiv permit hsym order)

@[simp] theorem snapshotEquiv_nil_apply
    (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state)
    (state : α → Bool) :
    snapshotEquiv permit hsym [] state = state := rfl

@[simp] theorem snapshotEquiv_cons_apply
    (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state)
    (e : α) (order : List α) (state : α → Bool) :
    snapshotEquiv permit hsym (e :: order) state =
      snapshotEquiv permit hsym order (snapshotStep permit e state) := by
  rfl

/-- **Snapshot reconstruction.** For every fixed order and final snapshot there is exactly one
initial sample producing it. -/
theorem existsUnique_sample_for_snapshot
    (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state)
    (order : List α) (snapshot : α → Bool) :
    ∃! sample, snapshotEquiv permit hsym order sample = snapshot := by
  let e := snapshotEquiv permit hsym order
  refine ⟨e.symm snapshot, e.apply_symm_apply snapshot, ?_⟩
  intro sample hsample
  apply e.injective
  rw [hsample, e.apply_symm_apply]

/-- For any family of reversible trajectories, a fixed-snapshot joint fiber contains exactly one
initial state above each order. -/
def snapshotFiberOrderEquiv {ι σ : Type*} (trajectory : ι → σ ≃ σ)
    (snapshot : σ) :
    {x : ι × σ // trajectory x.1 x.2 = snapshot} ≃ ι where
  toFun x := x.1.1
  invFun order := ⟨(order, (trajectory order).symm snapshot),
    (trajectory order).apply_symm_apply snapshot⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (trajectory x.1.1).injective
      rw [(trajectory x.1.1).apply_symm_apply, x.2]
  right_inv _ := rfl

/-- Cardinal form of conditional order independence: fixing the snapshot does not change the
number of possible orders. -/
theorem natCard_snapshotFiber_eq_natCard_order
    {ι σ : Type*} (trajectory : ι → σ ≃ σ) (snapshot : σ) :
    Nat.card {x : ι × σ // trajectory x.1 x.2 = snapshot} =
      Nat.card ι :=
  Nat.card_congr (snapshotFiberOrderEquiv trajectory snapshot)

end GaloisForLFunctions.HTGeometry
