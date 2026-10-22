import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthBellHigherEvenAbsorption

/-!
# Algebraic ordered-pair trace behind Bell grade two

This module removes normalization from the first eight ordinary likelihood source jets.  The
second partial Bell polynomial is exactly the strictly positive-normalization image of the
interior ordered-pair trace: the two boundary allocations are `2 r U₈`.

The remaining analytic connector is equality of this algebraic trace with the atom-ray ordered
pair sector already bounded in `ThetaCuspLikelihoodEighthStablePairCompensation`.
-/

namespace RHTower

noncomputable section

def thetaCuspLikelihoodEighthRawJetOne (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetTwo (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetThree (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
    3 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetFour (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
    6 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
    7 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetFive (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 -
    10 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 +
    25 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
    15 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetSix (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (6 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 6 -
    15 * A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
    65 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
    90 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
    31 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetSeven (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (7 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 7 -
    21 * A ^ (6 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 6 +
    140 * A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 -
    350 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 +
    301 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 -
    63 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 +
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

def thetaCuspLikelihoodEighthRawJetEight (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  A ^ (8 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 8 -
    28 * A ^ (7 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 7 +
    266 * A ^ (6 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 6 -
    1050 * A ^ (5 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 5 +
    1701 * A ^ (4 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 4 -
    966 * A ^ (3 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 3 +
    127 * A ^ (2 : ℕ) * thetaCuspHigherLikelihoodSpectralMoment B 2 -
    A * thetaCuspHigherLikelihoodSpectralMoment B 1

/-- Full algebraic ordered-pair eighth score, including the two zero-derivative allocations. -/
def thetaCuspLikelihoodEighthAlgebraicPairTrace (x : ℝ) : ℝ :=
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  2 * r * thetaCuspLikelihoodEighthRawJetEight x +
    16 * thetaCuspLikelihoodEighthRawJetOne x *
      thetaCuspLikelihoodEighthRawJetSeven x +
    56 * thetaCuspLikelihoodEighthRawJetTwo x *
      thetaCuspLikelihoodEighthRawJetSix x +
    112 * thetaCuspLikelihoodEighthRawJetThree x *
      thetaCuspLikelihoodEighthRawJetFive x +
    70 * thetaCuspLikelihoodEighthRawJetFour x ^ (2 : ℕ)

/-- Ordinary normalized jets are raw response jets divided by the literal partition. -/
theorem thetaCuspLikelihoodEighthBellJets_eq_raw
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellJetOne x =
        2 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetOne x ∧
    thetaCuspLikelihoodEighthBellJetTwo x =
        4 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetTwo x ∧
    thetaCuspLikelihoodEighthBellJetThree x =
        8 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetThree x ∧
    thetaCuspLikelihoodEighthBellJetFour x =
        16 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetFour x ∧
    thetaCuspLikelihoodEighthBellJetFive x =
        32 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetFive x ∧
    thetaCuspLikelihoodEighthBellJetSix x =
        64 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetSix x ∧
    thetaCuspLikelihoodEighthBellJetSeven x =
        128 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
          thetaCuspLikelihoodEighthRawJetSeven x := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  unfold thetaCuspLikelihoodEighthBellJetOne thetaCuspLikelihoodEighthBellJetTwo
    thetaCuspLikelihoodEighthBellJetThree thetaCuspLikelihoodEighthBellJetFour
    thetaCuspLikelihoodEighthBellJetFive thetaCuspLikelihoodEighthBellJetSix
    thetaCuspLikelihoodEighthBellJetSeven
    thetaCuspLikelihoodEighthRawJetOne thetaCuspLikelihoodEighthRawJetTwo
    thetaCuspLikelihoodEighthRawJetThree thetaCuspLikelihoodEighthRawJetFour
    thetaCuspLikelihoodEighthRawJetFive thetaCuspLikelihoodEighthRawJetSix
    thetaCuspLikelihoodEighthRawJetSeven
    thetaCuspLikelihoodMean thetaCuspLikelihoodNormalizedMoment
  dsimp only [B, P]
  constructor
  · field_simp [hP.ne']
  constructor
  · field_simp [hP.ne']
  constructor
  · field_simp [hP.ne']
  constructor
  · field_simp [hP.ne']
  constructor
  · field_simp [hP.ne']
  constructor <;> field_simp [hP.ne']

/-- The leading raw eighth score is strictly positive on the physical source half-line. -/
theorem thetaCuspLikelihoodEighthRawJetEight_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodEighthRawJetEight x := by
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  let P := thetaCuspLikelihoodPartition B
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hsource := thetaCuspLikelihoodSourceOrdinaryJetEight_pos hx
  have hEq : thetaCuspLikelihoodSourceOrdinaryJetEight x =
      256 / P * thetaCuspLikelihoodEighthRawJetEight x := by
    unfold thetaCuspLikelihoodSourceOrdinaryJetEight
      thetaCuspLikelihoodEighthRawJetEight thetaCuspLikelihoodNormalizedMoment
      thetaCuspLikelihoodMean
    dsimp only [B, P]
    field_simp [hP.ne']
  rw [hEq] at hsource
  have hfactor : 0 < 256 / P := div_pos (by norm_num) hP
  rcases (mul_pos_iff.mp hsource) with h | h
  · exact h.2
  · exact (not_lt_of_ge hfactor.le h.1).elim

/-- Exact grade-two normalization: deleting the two boundary allocations from the ordered-pair
trace gives twice the second partial Bell polynomial. -/
theorem thetaCuspLikelihoodEighthBellGradeTwo_eq_algebraicPairTrace
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellGradeTwo x =
      128 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) ^ (2 : ℕ) *
        (thetaCuspLikelihoodEighthAlgebraicPairTrace x -
          2 * thetaCuspHigherLikelihoodSpectralResponse
              (thetaCuspLikelihoodCoordinate x) *
            thetaCuspLikelihoodEighthRawJetEight x) := by
  rcases thetaCuspLikelihoodEighthBellJets_eq_raw hx with
    ⟨h1, h2, h3, h4, h5, h6, h7⟩
  unfold thetaCuspLikelihoodEighthBellGradeTwo
    thetaCuspLikelihoodEighthAlgebraicPairTrace
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

/-- Bell grade two is bounded by the full algebraic ordered-pair trace. -/
theorem thetaCuspLikelihoodEighthBellGradeTwo_le_algebraicPairTrace
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellGradeTwo x ≤
      128 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) ^ (2 : ℕ) *
        thetaCuspLikelihoodEighthAlgebraicPairTrace x := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hU8 := thetaCuspLikelihoodEighthRawJetEight_pos hx
  have hfactor : 0 ≤ 128 / P ^ (2 : ℕ) := by positivity
  rw [thetaCuspLikelihoodEighthBellGradeTwo_eq_algebraicPairTrace hx]
  change 128 / P ^ (2 : ℕ) *
      (thetaCuspLikelihoodEighthAlgebraicPairTrace x - 2 * r *
        thetaCuspLikelihoodEighthRawJetEight x) ≤
    128 / P ^ (2 : ℕ) * thetaCuspLikelihoodEighthAlgebraicPairTrace x
  exact mul_le_mul_of_nonneg_left (by nlinarith) hfactor

end

end RHTower
