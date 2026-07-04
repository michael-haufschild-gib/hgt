/-
Moving-threshold SPUR-R / AMP carrier adapter.

`SpurCarrier` instantiates the stack for a fixed monotone/antitone dressing of
the reversed S-readings.  The intended outer-reversal reader compares each
reading `S(y_i)` with its own threshold `(d - a*y_i)^2 + b^2*y_i^2`.  This
module turns such paired data into the existing `SpurRAMPInput` shape by using
the margin differences `S(y_i) - threshold_i` and the fixed dressing `x ↦ x + 1`.
Thresholding that dressed margin at `1` is exactly the intended comparison
`threshold_i < S(y_i)`.
-/
import GaloisForLFunctions.RHTower.SpurCarrier

noncomputable section

namespace RHTower

/-- Pointwise margin differences for paired value/threshold lists. -/
def movingThresholdDiffsFromLists : List ℝ → List ℝ → List ℝ
  | v :: vs, t :: ts => (v - t) :: movingThresholdDiffsFromLists vs ts
  | _, _ => []

/-- Paired margin differences commute with mapping over a shared carrier list. -/
theorem movingThresholdDiffsFromLists_map {α : Type*} (value threshold : α → ℝ) :
    ∀ xs : List α,
      movingThresholdDiffsFromLists (xs.map value) (xs.map threshold) =
        xs.map fun x => value x - threshold x := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [movingThresholdDiffsFromLists, ih]

/-- The actual Boolean comparison for paired value/threshold lists. -/
def movingThresholdComparisonsFromLists : List ℝ → List ℝ → List Bool
  | v :: vs, t :: ts => decide (t < v) :: movingThresholdComparisonsFromLists vs ts
  | _, _ => []

/-- Convert a zero-threshold margin difference into the existing AMP threshold `1`. -/
def movingThresholdDressing (x : ℝ) : ℝ := x + 1

/-- AMP states produced from paired value/threshold lists through margin differences. -/
def movingThresholdAmpStatesFromLists (values thresholds : List ℝ) : List Bool :=
  ampMarginStates ((movingThresholdDiffsFromLists values thresholds).map movingThresholdDressing)

/-- Adjacent thresholds move oppositely to the increasing values. -/
def AdjacentAntitone : List ℝ → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => y ≤ x ∧ AdjacentAntitone (y :: xs)

/-- The moving-threshold dressing is monotone. -/
theorem monotone_movingThresholdDressing : Monotone movingThresholdDressing := by
  intro x y hxy
  dsimp [movingThresholdDressing]
  linarith

/--
Strictly increasing values and adjacent antitone thresholds give strictly increasing
margin differences.
-/
theorem smonoStepCerts_movingThresholdDiffsFromLists :
    ∀ (values thresholds : List ℝ),
      SMonoStepCerts values →
        AdjacentAntitone thresholds →
          SMonoStepCerts (movingThresholdDiffsFromLists values thresholds) := by
  intro values
  induction values with
  | nil =>
      intro thresholds _hsteps _hthresholds
      cases thresholds <;> trivial
  | cons v values ih =>
      intro thresholds hsteps hthresholds
      cases values with
      | nil =>
          cases thresholds <;> trivial
      | cons v' vs =>
          cases thresholds with
          | nil =>
              trivial
          | cons t thresholds' =>
              cases thresholds' with
              | nil =>
                  trivial
              | cons t' ts =>
                  rcases hsteps with ⟨hvv', htailSteps⟩
                  rcases hthresholds with ⟨htt', htailThresholds⟩
                  constructor
                  · dsimp [SMonoStepCert, movingThresholdDiffsFromLists]
                    have hvpos : 0 < v' - v := hvv'
                    linarith
                  · exact ih (t' :: ts) htailSteps htailThresholds

/--
The dressed-margin AMP states are definitionally the intended moving-threshold
comparisons, up to the elementary inequality `1 < (v - t) + 1 ↔ t < v`.
-/
theorem movingThresholdAmpStatesFromLists_eq_comparisons :
    ∀ (values thresholds : List ℝ),
      movingThresholdAmpStatesFromLists values thresholds =
        movingThresholdComparisonsFromLists values thresholds := by
  intro values
  induction values with
  | nil =>
      intro thresholds
      cases thresholds <;> rfl
  | cons v values ih =>
      intro thresholds
      cases thresholds with
      | nil =>
          rfl
      | cons t ts =>
          unfold movingThresholdAmpStatesFromLists ampMarginStates thresholdStates
          dsimp [movingThresholdDiffsFromLists, movingThresholdComparisonsFromLists,
            movingThresholdDressing]
          by_cases htv : t < v
          · have hmargin : (1 : ℝ) < v - t + 1 := by linarith
            have htail := ih ts
            unfold movingThresholdAmpStatesFromLists ampMarginStates thresholdStates at htail
            simp [htv, hmargin, htail]
          · have hmargin : ¬ (1 : ℝ) < v - t + 1 := by
              intro h
              exact htv (by linarith)
            have htail := ih ts
            unfold movingThresholdAmpStatesFromLists ampMarginStates thresholdStates at htail
            simp [htv, hmargin, htail]

/-- Generic moving-threshold data instantiate the fixed-threshold SPUR-R / AMP stack. -/
theorem spurRAMPInput_of_movingThresholdLists {values thresholds : List ℝ} {Z : ℕ}
    (hsteps : SMonoStepCerts values)
    (hthresholds : AdjacentAntitone thresholds)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound :
      Z ≤ 2 + copyFlipTransitions (movingThresholdAmpStatesFromLists values thresholds)) :
    SpurRAMPInput (movingThresholdDiffsFromLists values thresholds) Z movingThresholdDressing where
  steps := smonoStepCerts_movingThresholdDiffsFromLists values thresholds hsteps hthresholds
  dressing := Or.inl monotone_movingThresholdDressing
  visible := hvisible
  even := heven
  counting_bound := by
    simpa [movingThresholdAmpStatesFromLists] using hbound

/-- Exact reader pair for generic moving-threshold data. -/
theorem amp_reader_exact_pair_of_movingThresholdLists {values thresholds : List ℝ} {Z : ℕ}
    (hsteps : SMonoStepCerts values)
    (hthresholds : AdjacentAntitone thresholds)
    (hvisible : 0 < Z) (heven : Even Z)
    (hbound :
      Z ≤ 2 + copyFlipTransitions (movingThresholdAmpStatesFromLists values thresholds)) :
    Z = 2 :=
  amp_reader_exact_pair_of_spurRAMPInput
    (spurRAMPInput_of_movingThresholdLists hsteps hthresholds hvisible heven hbound)

/-- The intended reversed-carrier threshold `(d - a*y)^2 + b^2*y^2`. -/
def reversedCarrierAMPThreshold (d : ℕ) (a b y : ℝ) : ℝ :=
  ((d : ℝ) - a * y) ^ 2 + b ^ 2 * y ^ 2

/-- Threshold readings along a reversed one-sided-far carrier. -/
def reversedCarrierThresholds (d : ℕ) (a b : ℝ) (ys : List ℝ) : List ℝ :=
  ys.map (reversedCarrierAMPThreshold d a b)

/-- Intended SPUR-R moving-threshold margin differences along the reversed carrier. -/
def reversedCarrierMarginDiffs (β : Multiset ℝ) (d : ℕ) (a b : ℝ) (ys : List ℝ) :
    List ℝ :=
  movingThresholdDiffsFromLists (reversedCarrierReadings β ys)
    (reversedCarrierThresholds d a b ys)

/-- AMP states for the intended moving-threshold reversed carrier. -/
def reversedCarrierMovingAmpStates (β : Multiset ℝ) (d : ℕ) (a b : ℝ) (ys : List ℝ) :
    List Bool :=
  movingThresholdAmpStatesFromLists (reversedCarrierReadings β ys)
    (reversedCarrierThresholds d a b ys)

/-- Direct intended comparisons `threshold_i < S(y_i)` along the reversed carrier. -/
def reversedCarrierMovingComparisons (β : Multiset ℝ) (d : ℕ) (a b : ℝ) (ys : List ℝ) :
    List Bool :=
  movingThresholdComparisonsFromLists (reversedCarrierReadings β ys)
    (reversedCarrierThresholds d a b ys)

/-- The list form of the reversed-carrier margin differences. -/
theorem reversedCarrierMarginDiffs_eq_map (β : Multiset ℝ) (d : ℕ) (a b : ℝ) :
    ∀ ys : List ℝ,
      reversedCarrierMarginDiffs β d a b ys =
        ys.map fun y => reversedCarrierS β y - reversedCarrierAMPThreshold d a b y := by
  intro ys
  simpa [reversedCarrierMarginDiffs, reversedCarrierReadings, reversedCarrierThresholds] using
    movingThresholdDiffsFromLists_map (reversedCarrierS β) (reversedCarrierAMPThreshold d a b) ys

/-- Dressed-margin AMP states are exactly the intended reversed-carrier comparisons. -/
theorem reversedCarrierMovingAmpStates_eq_comparisons (β : Multiset ℝ) (d : ℕ)
    (a b : ℝ) (ys : List ℝ) :
    reversedCarrierMovingAmpStates β d a b ys =
      reversedCarrierMovingComparisons β d a b ys :=
  movingThresholdAmpStatesFromLists_eq_comparisons
    (reversedCarrierReadings β ys) (reversedCarrierThresholds d a b ys)

/--
The intended moving-threshold one-sided-far SPUR-R carrier input.  The carrier
chain proves strict increase of `S(y_i)`; the threshold-antitone field says the
REV threshold moves in the opposite direction on the same ordered window.
-/
structure SpurROneSidedFarMovingCarrierInput (β : Multiset ℝ) (ys : List ℝ)
    (Z d : ℕ) (a b : ℝ) : Type 2 where
  chain : SpurROneSidedFarChain (reversedCarrierReadings β ys)
  threshold_antitone : AdjacentAntitone (reversedCarrierThresholds d a b ys)
  visible : 0 < Z
  even : Even Z
  counting_bound :
    Z ≤ 2 + copyFlipTransitions (reversedCarrierMovingAmpStates β d a b ys)

/--
The intended moving-threshold reversed carrier instantiates the full fixed-threshold
SPUR-R / AMP provider by passing to margin differences and `x ↦ x + 1`.
-/
theorem spurRAMPInput_of_oneSidedFarMovingCarrierInput {β : Multiset ℝ} {ys : List ℝ}
    {Z d : ℕ} {a b : ℝ} (h : SpurROneSidedFarMovingCarrierInput β ys Z d a b) :
    SpurRAMPInput (reversedCarrierMarginDiffs β d a b ys) Z movingThresholdDressing :=
  spurRAMPInput_of_movingThresholdLists
    (smonoStepCerts_of_spurROneSidedFarChain h.chain)
    h.threshold_antitone h.visible h.even h.counting_bound

/-- Exact reader pair on the intended moving-threshold reversed carrier. -/
theorem amp_reader_exact_pair_of_oneSidedFarMovingCarrierInput {β : Multiset ℝ}
    {ys : List ℝ} {Z d : ℕ} {a b : ℝ}
    (h : SpurROneSidedFarMovingCarrierInput β ys Z d a b) :
    Z = 2 :=
  amp_reader_exact_pair_of_spurRAMPInput
    (spurRAMPInput_of_oneSidedFarMovingCarrierInput h)

end RHTower
