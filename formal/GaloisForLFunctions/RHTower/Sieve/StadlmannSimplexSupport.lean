import GaloisForLFunctions.RHTower.Sieve.StadlmannBoundedGapsApplications

/-!
# Stadlmann simplex-support deletion laws

Definition 1 of arXiv:2608.31126 imposes a monotone cardinality budget whose one-step
growth is at most the large-coordinate cutoff.  The paper repeatedly uses the resulting
fact that every subset of the large coordinates remains within its own cardinality budget.
This file isolates that mechanism and applies it to the final `0.15, 0.15, 0.17, ...`
support profile.
-/

namespace RHTower.Sieve.StadlmannSimplexSupport

open Finset

noncomputable section

/-- Cardinality budget used in Definition 1 of the paper. -/
structure ThresholdProfile where
  cutoff : ℝ
  budget : ℕ → ℝ
  monotone_budget : Monotone budget
  step_le : ∀ m, budget (m + 1) ≤ budget m + cutoff

namespace ThresholdProfile

/-- Iterated form of the one-coordinate budget-growth condition. -/
theorem budget_add_le (P : ThresholdProfile) (m r : ℕ) :
    P.budget (m + r) ≤ P.budget m + r * P.cutoff := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        P.budget (m + (r + 1)) = P.budget ((m + r) + 1) := by rw [Nat.add_assoc]
        _ ≤ P.budget (m + r) + P.cutoff := P.step_le (m + r)
        _ ≤ (P.budget m + r * P.cutoff) + P.cutoff := by linarith
        _ = P.budget m + ((r + 1 : ℕ) : ℝ) * P.cutoff := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- **Definition 1 deletion law.**  If every coordinate of `I` is at least the cutoff and
the full sum fits its cardinality budget, then every subset `J ⊆ I` fits the budget indexed by
`J.card`.

This is the precise finite statement behind the paper's repeated support-stability claim. -/
theorem subset_sum_le_budget {P : ThresholdProfile} {α : Type*} [DecidableEq α]
    (t : α → ℝ) {I J : Finset α}
    (hlarge : ∀ i ∈ I, P.cutoff ≤ t i)
    (hsum : (∑ i ∈ I, t i) ≤ P.budget I.card)
    (hJI : J ⊆ I) :
    (∑ i ∈ J, t i) ≤ P.budget J.card := by
  have hdisjoint : Disjoint J (I \ J) := by
    rw [Finset.disjoint_left]
    intro i hiJ hiDiff
    exact (Finset.mem_sdiff.mp hiDiff).2 hiJ
  have hunion : J ∪ (I \ J) = I := Finset.union_sdiff_of_subset hJI
  have hsum_split : (∑ i ∈ I, t i) = (∑ i ∈ J, t i) + ∑ i ∈ I \ J, t i := by
    calc
      (∑ i ∈ I, t i) = ∑ i ∈ J ∪ (I \ J), t i := by rw [hunion]
      _ = (∑ i ∈ J, t i) + ∑ i ∈ I \ J, t i := sum_union hdisjoint
  have htail : (I \ J).card * P.cutoff ≤ ∑ i ∈ I \ J, t i := by
    calc
      (I \ J).card * P.cutoff = ∑ _i ∈ I \ J, P.cutoff := by simp
      _ ≤ ∑ i ∈ I \ J, t i := by
        refine sum_le_sum fun i hi => ?_
        exact hlarge i (Finset.mem_sdiff.mp hi).1
  have hcard : J.card + (I \ J).card = I.card := by
    calc
      J.card + (I \ J).card = (J ∪ (I \ J)).card :=
        (card_union_of_disjoint hdisjoint).symm
      _ = I.card := congrArg Finset.card hunion
  have hbudget := P.budget_add_le J.card (I \ J).card
  rw [hcard] at hbudget
  linarith

/-- Removing one large coordinate preserves the support budget. -/
theorem erase_sum_le_budget {P : ThresholdProfile} {α : Type*} [DecidableEq α]
    (t : α → ℝ) {I : Finset α} {i : α}
    (hlarge : ∀ j ∈ I, P.cutoff ≤ t j)
    (hsum : (∑ j ∈ I, t j) ≤ P.budget I.card) :
    (∑ j ∈ I.erase i, t j) ≤ P.budget (I.erase i).card :=
  P.subset_sum_le_budget t hlarge hsum (erase_subset i I)

/-- Every singleton selected from an admissible large-coordinate set meets the singleton budget. -/
theorem singleton_le_budget {P : ThresholdProfile} {α : Type*} [DecidableEq α]
    (t : α → ℝ) {I : Finset α}
    (hlarge : ∀ j ∈ I, P.cutoff ≤ t j)
    (hsum : (∑ j ∈ I, t j) ≤ P.budget I.card)
    {i : α} (hi : i ∈ I) :
    t i ≤ P.budget 1 := by
  simpa using P.subset_sum_le_budget t hlarge hsum (singleton_subset_iff.mpr hi)

end ThresholdProfile

open StadlmannBoundedGaps

/-- The exact final support budget is a Definition 1 threshold profile. -/
def finalThresholdProfile : ThresholdProfile where
  cutoff := delta
  budget := largeCoordinateBudget
  monotone_budget := largeCoordinateBudget_monotone
  step_le := largeCoordinateBudget_step

/-- Every subset of final-support large coordinates remains inside the final cardinality budget. -/
theorem finalSupport_subset_stable {α : Type*} [DecidableEq α]
    (t : α → ℝ) {I J : Finset α}
    (hlarge : ∀ i ∈ I, delta ≤ t i)
    (hsum : (∑ i ∈ I, t i) ≤ largeCoordinateBudget I.card)
    (hJI : J ⊆ I) :
    (∑ i ∈ J, t i) ≤ largeCoordinateBudget J.card := by
  exact finalThresholdProfile.subset_sum_le_budget t hlarge hsum hJI

/-- In particular, every final-support large coordinate is at most `0.15`. -/
theorem finalSupport_coordinate_le_three_twentieths {α : Type*} [DecidableEq α]
    (t : α → ℝ) {I : Finset α}
    (hlarge : ∀ i ∈ I, delta ≤ t i)
    (hsum : (∑ i ∈ I, t i) ≤ largeCoordinateBudget I.card)
    {i : α} (hi : i ∈ I) :
    t i ≤ 3 / 20 := by
  simpa [finalThresholdProfile, largeCoordinateBudget] using
    finalThresholdProfile.singleton_le_budget t hlarge hsum hi

/-- Every subset of the left block of a Proposition 3 `XiTuple` satisfies its own final budget. -/
theorem StadlmannBoundedGaps.XiTuple.left_subset_budget
    {m n : ℕ} (x : StadlmannBoundedGaps.XiTuple m n) (J : Finset (Fin m)) :
    (∑ i ∈ J, x.left i) ≤ largeCoordinateBudget J.card := by
  simpa using finalSupport_subset_stable x.left
    (I := (Finset.univ : Finset (Fin m))) (J := J)
    (by simpa using x.left_lower) (by simpa using x.left_sum_le)
    (Finset.subset_univ J)

/-- Every subset of the right block of a Proposition 3 `XiTuple` satisfies its own final budget. -/
theorem StadlmannBoundedGaps.XiTuple.right_subset_budget
    {m n : ℕ} (x : StadlmannBoundedGaps.XiTuple m n) (J : Finset (Fin n)) :
    (∑ i ∈ J, x.right i) ≤ largeCoordinateBudget J.card := by
  simpa using finalSupport_subset_stable x.right
    (I := (Finset.univ : Finset (Fin n))) (J := J)
    (by simpa using x.right_lower) (by simpa using x.right_sum_le)
    (Finset.subset_univ J)

/-- Each left `XiTuple` coordinate is automatically at most `0.15`, improving its stored `≤1`. -/
theorem StadlmannBoundedGaps.XiTuple.left_le_three_twentieths
    {m n : ℕ} (x : StadlmannBoundedGaps.XiTuple m n) (i : Fin m) :
    x.left i ≤ 3 / 20 := by
  simpa using finalSupport_coordinate_le_three_twentieths x.left
    (I := (Finset.univ : Finset (Fin m)))
    (by simpa using x.left_lower) (by simpa using x.left_sum_le) (Finset.mem_univ i)

/-- Each right `XiTuple` coordinate is automatically at most `0.15`. -/
theorem StadlmannBoundedGaps.XiTuple.right_le_three_twentieths
    {m n : ℕ} (x : StadlmannBoundedGaps.XiTuple m n) (i : Fin n) :
    x.right i ≤ 3 / 20 := by
  simpa using finalSupport_coordinate_le_three_twentieths x.right
    (I := (Finset.univ : Finset (Fin n)))
    (by simpa using x.right_lower) (by simpa using x.right_sum_le) (Finset.mem_univ i)

end

end RHTower.Sieve.StadlmannSimplexSupport
