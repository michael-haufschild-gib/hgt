import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthOrdinaryPositivity

/-!
# Dominant two-particle compensation at order eight

The eighth one-particle score is negative at the low support edge, so sixth-order pointwise
binary fusion cannot extend to order eight.  The exact Dirac--ray decomposition instead gives a
two-ray transform.  Its dominant `(3,3)` core grows too quickly for any fixed seam-sharp fusion
constant, but a degree-twenty Taylor lower bound for `exp (3A)` absorbs it on the whole physical
source chamber.  Thus the complete dominant two-particle score mass is strictly smaller than the
dominant one-particle score mass.
-/

namespace RHTower

noncomputable section

/-- Degree-twenty Taylor lower polynomial for the reciprocal dominant decay. -/
def thetaCuspLikelihoodEighthDominantTaylorTwenty (A : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 21, (3 * A) ^ k / (k.factorial : ℝ)

/-- Exact stripped one-particle Dirac--ray core at the dominant gap `3`. -/
def thetaCuspLikelihoodEighthDominantSingleCore (A : ℝ) : ℝ :=
  let B := A - 3 / 2
  16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
    18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)

/-- Exact stripped two-particle core.  Its three terms are Dirac--Dirac, the two mixed
Dirac--ray sectors, and ray--ray. -/
def thetaCuspLikelihoodEighthDominantPairCore (A : ℝ) : ℝ :=
  let B := A - 3 / 2
  256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
    576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
    324 / B ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)

/-- Actual dominant one-particle score mass after restoring its exact exponential factor. -/
def thetaCuspLikelihoodEighthDominantSingleMass (A : ℝ) : ℝ :=
  Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantSingleCore A

/-- Actual dominant two-particle score mass after restoring both exponential factors. -/
def thetaCuspLikelihoodEighthDominantPairMass (A : ℝ) : ℝ :=
  Real.exp (-(6 * A)) * thetaCuspLikelihoodEighthDominantPairCore A

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The complete dominant two-particle core is strictly positive on the physical chamber. -/
theorem thetaCuspLikelihoodEighthDominantPairCore_pos
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    0 < thetaCuspLikelihoodEighthDominantPairCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  change 0 < 256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
    576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
    324 / B ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hmul : 0 < B ^ (10 : ℕ) *
      (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
        576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
        324 / B ^ (2 : ℕ) *
          thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) := by
    unfold thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hB.le 10)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Algebraic reserve certificate: the degree-twenty exponential Taylor lower polynomial times
the compensated one-particle core strictly dominates three halves of the complete two-particle
core. -/
theorem three_halves_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    (3 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        thetaCuspLikelihoodEighthDominantSingleCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  change
    (3 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
        576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
        324 / B ^ (2 : ℕ) *
          thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
          18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A))
  let s := A - 157 / 50
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hmul : 0 < B ^ (10 : ℕ) *
      (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (3 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ (2 : ℕ) *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A))) := by
    unfold thetaCuspLikelihoodEighthDominantTaylorTwenty
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    norm_num [Finset.sum_range_succ]
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 157 / 50 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (3 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ (2 : ℕ) *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) :=
    pos_of_mul_pos_right hmul (pow_nonneg hB.le 10)
  linarith

/-- The reserve certificate in particular gives unscaled dominant core absorption. -/
theorem thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    thetaCuspLikelihoodEighthDominantPairCore A <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        thetaCuspLikelihoodEighthDominantSingleCore A := by
  have hstrong :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore hA
  have hpair := thetaCuspLikelihoodEighthDominantPairCore_pos hA
  nlinarith

/-- The Taylor polynomial is bounded above by the exact reciprocal dominant decay. -/
theorem thetaCuspLikelihoodEighthDominantTaylorTwenty_le_exp
    {A : ℝ} (hA : 0 ≤ A) :
    thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤ Real.exp (3 * A) := by
  simpa only [thetaCuspLikelihoodEighthDominantTaylorTwenty] using
    Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num) hA) 21

/-- Exponential coupling leaves a sharp rational reserve: three halves of the dominant
two-particle core are absorbed by the one-particle core. -/
theorem three_halves_mul_exp_neg_three_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_singleCore
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    (3 / 2 : ℝ) *
        (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) <
      thetaCuspLikelihoodEighthDominantSingleCore A := by
  have hA0 : 0 ≤ A := by linarith
  have hsingle : 0 < thetaCuspLikelihoodEighthDominantSingleCore A := by
    simpa only [thetaCuspLikelihoodEighthDominantSingleCore] using
      thetaCuspLikelihoodDominantEighthScoreCore_pos hA
  have hcore :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore hA
  have hexp : Real.exp (-(3 * A)) *
      thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤ 1 := by
    calc
      Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤
          Real.exp (-(3 * A)) * Real.exp (3 * A) :=
        mul_le_mul_of_nonneg_left
          (thetaCuspLikelihoodEighthDominantTaylorTwenty_le_exp hA0)
          (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc
    (3 / 2 : ℝ) *
        (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
        Real.exp (-(3 * A)) *
          ((3 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A) := by ring
    _ <
        Real.exp (-(3 * A)) *
          (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
            thetaCuspLikelihoodEighthDominantSingleCore A) :=
      mul_lt_mul_of_pos_left hcore (Real.exp_pos _)
    _ = (Real.exp (-(3 * A)) *
          thetaCuspLikelihoodEighthDominantTaylorTwenty A) *
        thetaCuspLikelihoodEighthDominantSingleCore A := by ring
    _ ≤ 1 * thetaCuspLikelihoodEighthDominantSingleCore A :=
      mul_le_mul_of_nonneg_right hexp hsingle.le
    _ = thetaCuspLikelihoodEighthDominantSingleCore A := one_mul _

/-- Unscaled exponential absorption follows from the three-halves reserve. -/
theorem exp_neg_three_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_singleCore
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A <
      thetaCuspLikelihoodEighthDominantSingleCore A := by
  have hstrong :=
    three_halves_mul_exp_neg_three_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_singleCore hA
  have hpair : 0 < Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A :=
    mul_pos (Real.exp_pos _) (thetaCuspLikelihoodEighthDominantPairCore_pos hA)
  nlinarith

/-- Three halves of the actual dominant two-particle mass fit inside its one-particle mass. -/
theorem three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    (3 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairMass A <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have h :=
    three_halves_mul_exp_neg_three_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_singleCore hA
  have hscale := mul_lt_mul_of_pos_left h (Real.exp_pos (-(3 * A)))
  unfold thetaCuspLikelihoodEighthDominantPairMass
    thetaCuspLikelihoodEighthDominantSingleMass
  calc
    (3 / 2 : ℝ) *
        (Real.exp (-(6 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
        Real.exp (-(3 * A)) *
          ((3 / 2 : ℝ) *
            (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A)) := by
      rw [show Real.exp (-(6 * A)) =
        Real.exp (-(3 * A)) * Real.exp (-(3 * A)) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring
    _ < Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantSingleCore A := hscale

/-- The actual dominant two-particle mass is strictly smaller than its one-particle mass. -/
theorem thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass
    {A : ℝ} (hA : (157 / 50 : ℝ) ≤ A) :
    thetaCuspLikelihoodEighthDominantPairMass A <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hstrong :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hA
  have hpair : 0 < thetaCuspLikelihoodEighthDominantPairMass A :=
    mul_pos (Real.exp_pos _) (thetaCuspLikelihoodEighthDominantPairCore_pos hA)
  nlinarith

/-- The stripped single mass agrees exactly with the actual dominant atom score mass. -/
theorem thetaCuspLikelihoodEighthDominantSingleMass_eq_atomScoreMass
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodEighthDominantSingleMass A =
      thetaCuspLikelihoodAtomEighthScoreMass 2 A B := by
  have hB : 0 < B := by rw [hBA]; linarith
  rw [thetaCuspLikelihoodAtomEighthScoreMass_eq 2 (by norm_num) A hB]
  norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
    thetaCuspLikelihoodRayWeight]
  rw [hBA]
  unfold thetaCuspLikelihoodEighthDominantSingleMass
    thetaCuspLikelihoodEighthDominantSingleCore
  have hexp : Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3)) =
      Real.exp (-(3 * A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (-((A - 3 / 2) * 3)) = Real.exp (9 / 2 - 3 * A) by
    congr 1
    ring]
  rw [← hexp]
  ring

end

end RHTower
