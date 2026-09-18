import GaloisForLFunctions.RHTower.SuzukiOrientedPrunedPathChronology

/-!
# Literal word action of support-pruned Suzuki prime steps

The scalar Suzuki Eulerian bridge retains only a completed outgoing charge.  The physical source
itself has more structure: strict aperture pruning makes compositions of symmetric prime steps
depend on their order.  This file exposes that structure as the literal free-word action of the
existing support-pruned operators.

The action is the source-side domain for a future signed-Eulerian lift.  Its `2,3,7` witness proves
that no endpoint-only or scalar factorization can substitute for the history port.  No map to the
Route-P Cauchy-cubic word weight is asserted here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Apply a finite oriented word of literal support-pruned seam shifts.  Negative valuations are
genuine source orientations, so this is the signed source port relevant to a type-B lift. -/
def suzukiOrientedSupportPrunedHistoryAction (a : ℝ) :
    List SuzukiSeamValuation → SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert
  | [] => 1
  | δ :: word => suzukiOrientedSupportPrunedShift a δ ∘L
      suzukiOrientedSupportPrunedHistoryAction a word

@[simp] theorem suzukiOrientedSupportPrunedHistoryAction_nil
    (a : ℝ) : suzukiOrientedSupportPrunedHistoryAction a [] = 1 := rfl

@[simp] theorem suzukiOrientedSupportPrunedHistoryAction_cons
    (a : ℝ) (δ : SuzukiSeamValuation) (word : List SuzukiSeamValuation) :
    suzukiOrientedSupportPrunedHistoryAction a (δ :: word) =
      suzukiOrientedSupportPrunedShift a δ ∘L
        suzukiOrientedSupportPrunedHistoryAction a word := rfl

/-- The oriented history action represents word concatenation by composition. -/
theorem suzukiOrientedSupportPrunedHistoryAction_append
    (a : ℝ) (left right : List SuzukiSeamValuation) :
    suzukiOrientedSupportPrunedHistoryAction a (left ++ right) =
      suzukiOrientedSupportPrunedHistoryAction a left ∘L
        suzukiOrientedSupportPrunedHistoryAction a right := by
  induction left with
  | nil =>
      ext f q
      rfl
  | cons δ left ih =>
      simp only [List.cons_append, suzukiOrientedSupportPrunedHistoryAction_cons, ih]
      rw [ContinuousLinearMap.comp_assoc]

/-- **Physical signed-word witness.**  The actual `2,-3` oriented source word and its reversal
have values `1` and `0` at one retained source/readout pair. -/
theorem exists_suzukiOrientedSupportPrunedHistoryAction_ordered_value_asymmetry :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex),
      0 < a ∧
        suzukiOrientedSupportPrunedHistoryAction a [δ, η] f q = 1 ∧
        suzukiOrientedSupportPrunedHistoryAction a [η, δ] f q = 0 := by
  obtain ⟨a, δ, η, f, q, ha, hforward, hreverse⟩ :=
    exists_suzukiOrientedSupportPrunedShift_ordered_value_asymmetry
  exact ⟨a, δ, η, f, q, ha, by simpa using hforward, by simpa using hreverse⟩

/-- Apply a finite word of literal support-pruned symmetric seam steps, with the head step acting
after the tail.  Thus `[δ, η]` acts as `S_δ ∘ S_η`. -/
def suzukiSupportPrunedSymmetricHistoryAction (a : ℝ) :
    List SuzukiSeamValuation → SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert
  | [] => 1
  | δ :: word => suzukiSupportPrunedSymmetricSeamStep a δ ∘L
      suzukiSupportPrunedSymmetricHistoryAction a word

@[simp] theorem suzukiSupportPrunedSymmetricHistoryAction_nil
    (a : ℝ) : suzukiSupportPrunedSymmetricHistoryAction a [] = 1 := rfl

@[simp] theorem suzukiSupportPrunedSymmetricHistoryAction_cons
    (a : ℝ) (δ : SuzukiSeamValuation) (word : List SuzukiSeamValuation) :
    suzukiSupportPrunedSymmetricHistoryAction a (δ :: word) =
      suzukiSupportPrunedSymmetricSeamStep a δ ∘L
        suzukiSupportPrunedSymmetricHistoryAction a word := rfl

/-- The history action represents word concatenation by composition. -/
theorem suzukiSupportPrunedSymmetricHistoryAction_append
    (a : ℝ) (left right : List SuzukiSeamValuation) :
    suzukiSupportPrunedSymmetricHistoryAction a (left ++ right) =
      suzukiSupportPrunedSymmetricHistoryAction a left ∘L
        suzukiSupportPrunedSymmetricHistoryAction a right := by
  induction left with
  | nil =>
      ext f q
      rfl
  | cons δ left ih =>
      simp only [List.cons_append, suzukiSupportPrunedSymmetricHistoryAction_cons, ih]
      rw [ContinuousLinearMap.comp_assoc]

/-- **Physical ordered-history witness.**  The literal `2,3,7` source configuration has one
retained source/readout pair on which the two orders of two positive-label prime steps evaluate to
`1` and `0`. -/
theorem exists_suzukiSupportPrunedSymmetricHistoryAction_ordered_value_asymmetry :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex),
      0 < a ∧
        suzukiSupportPrunedSymmetricHistoryAction a [δ, η] f q = 1 ∧
        suzukiSupportPrunedSymmetricHistoryAction a [η, δ] f q = 0 := by
  obtain ⟨a, δ, η, f, q, ha, hforward, hreverse⟩ :=
    exists_suzukiSupportPrunedSymmetricSeamStep_ordered_value_asymmetry
  exact ⟨a, δ, η, f, q, ha, by simpa using hforward, by simpa using hreverse⟩

end

end GaloisForLFunctions.RHTower
