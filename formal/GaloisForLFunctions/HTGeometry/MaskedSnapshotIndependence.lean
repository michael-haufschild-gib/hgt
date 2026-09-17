import GaloisForLFunctions.HTGeometry.ReversibleSnapshotIndependence

/-!
# Masked reversible snapshots

Replacing any fixed collection of reversible snapshot steps by identity steps preserves the
trajectory equivalence and unique reconstruction. This is the structural conditioning argument
behind the adversarial-order extension in the matroid paper's Theorem 4.1.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- Run the reversible snapshot step only when the current element is marked. -/
def maskedSnapshotStep (active : α → Bool) (permit : α → (α → Bool) → Bool)
    (e : α) (state : α → Bool) : α → Bool :=
  if active e = true then snapshotStep permit e state else state

@[simp] theorem maskedSnapshotStep_active
    (active : α → Bool) (permit : α → (α → Bool) → Bool)
    (e : α) (state : α → Bool) (he : active e = true) :
    maskedSnapshotStep active permit e state = snapshotStep permit e state := by
  simp [maskedSnapshotStep, he]

@[simp] theorem maskedSnapshotStep_inactive
    (active : α → Bool) (permit : α → (α → Bool) → Bool)
    (e : α) (state : α → Bool) (he : active e = false) :
    maskedSnapshotStep active permit e state = state := by
  simp [maskedSnapshotStep, he]

/-- Marking a reversible step or replacing it by the identity preserves reversibility. -/
theorem maskedSnapshotStep_involutive
    (active : α → Bool) (permit : α → (α → Bool) → Bool) (e : α)
    (hsym : ∀ state, permit e (toggleCoordinate e state) = permit e state) :
    Function.Involutive (maskedSnapshotStep active permit e) := by
  intro state
  by_cases he : active e = true
  · simp only [maskedSnapshotStep, he, if_true]
    exact snapshotStep_involutive permit e hsym state
  · simp [maskedSnapshotStep, he]

def maskedSnapshotStepEquiv
    (active : α → Bool) (permit : α → (α → Bool) → Bool) (e : α)
    (hsym : ∀ state, permit e (toggleCoordinate e state) = permit e state) :
    (α → Bool) ≃ (α → Bool) :=
  (maskedSnapshotStep_involutive active permit e hsym).toPerm

/-- Composition of marked reversible steps in a fixed order. -/
def maskedSnapshotEquiv
    (active : α → Bool) (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state) :
    List α → (α → Bool) ≃ (α → Bool)
  | [] => Equiv.refl _
  | e :: order =>
      (maskedSnapshotStepEquiv active permit e (hsym e)).trans
        (maskedSnapshotEquiv active permit hsym order)

/-- Snapshot reconstruction still holds when any fixed subset of iterations is inactive. -/
theorem existsUnique_sample_for_maskedSnapshot
    (active : α → Bool) (permit : α → (α → Bool) → Bool)
    (hsym : ∀ e state, permit e (toggleCoordinate e state) = permit e state)
    (order : List α) (snapshot : α → Bool) :
    ∃! sample, maskedSnapshotEquiv active permit hsym order sample = snapshot := by
  let trajectory := maskedSnapshotEquiv active permit hsym order
  refine ⟨trajectory.symm snapshot, trajectory.apply_symm_apply snapshot, ?_⟩
  intro sample hsample
  apply trajectory.injective
  rw [hsample, trajectory.apply_symm_apply]

end GaloisForLFunctions.HTGeometry
