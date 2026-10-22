import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthDominantPairCompensation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthStableTowerBound

/-!
# Stable two-particle compensation at order eight

The dominant `(2,2)` chamber needs the exact Taylor compensation proved in the preceding module.
Every other atom pair has total gap at least eleven, hence scaled support above `34`.  There the
point, one-ray, and two-ray eighth-score transforms have the sharp coarse envelopes `1`, `2`, and
`4` times the leading eighth monomial.  The normalized ray coefficient of every atom is at most
its point coefficient.  Together these facts give a uniform factor-nine bound for every
non-dominant pair.
-/

namespace RHTower

noncomputable section

/-- Above the positivity barrier, the eighth score is bounded by its leading monomial. -/
theorem thetaCuspLikelihoodEighthSourceScore_le_pow_eight
    {z : ℝ} (hz : 14 ≤ z) :
    thetaCuspLikelihoodEighthSourceScore z ≤ z ^ (8 : ℕ) := by
  let s := z - 14
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 14 + s by dsimp only [s]; ring]
  unfold thetaCuspLikelihoodEighthSourceScore
  apply sub_nonneg.mp
  ring_nf
  positivity

set_option maxRecDepth 20000 in
/-- On pair support, one exponential ray costs at most twice the leading monomial. -/
theorem thetaCuspLikelihoodEighthSourceScoreRayTransform_le_two_mul_pow_eight
    {r z : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hz : 34 ≤ z) :
    thetaCuspLikelihoodEighthSourceScoreRayTransform r z ≤ 2 * z ^ (8 : ℕ) := by
  let s := z - 34
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 34 + s by dsimp only [s]; ring]
  have h2 := pow_le_pow_left₀ hr0 hr2 2
  have h3 := pow_le_pow_left₀ hr0 hr2 3
  have h4 := pow_le_pow_left₀ hr0 hr2 4
  have h5 := pow_le_pow_left₀ hr0 hr2 5
  have h6 := pow_le_pow_left₀ hr0 hr2 6
  have h7 := pow_le_pow_left₀ hr0 hr2 7
  have h8 := pow_le_pow_left₀ hr0 hr2 8
  norm_num at h2 h3 h4 h5 h6 h7 h8
  have hmono :
      thetaCuspLikelihoodEighthSourceScoreRayTransform r (34 + s) ≤
        thetaCuspLikelihoodEighthSourceScoreRayTransform 2 (34 + s) := by
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    nlinarith [sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4,
      pow_nonneg hs 5, pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8]
  refine hmono.trans ?_
  unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  apply sub_nonneg.mp
  ring_nf
  positivity

set_option maxRecDepth 20000 in
/-- On pair support, two exponential rays cost at most four leading monomials. -/
theorem thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform_le_four_mul_pow_eight
    {r z : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hz : 34 ≤ z) :
    thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform r z ≤ 4 * z ^ (8 : ℕ) := by
  let s := z - 34
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  rw [show z = 34 + s by dsimp only [s]; ring]
  have h2 := pow_le_pow_left₀ hr0 hr2 2
  have h3 := pow_le_pow_left₀ hr0 hr2 3
  have h4 := pow_le_pow_left₀ hr0 hr2 4
  have h5 := pow_le_pow_left₀ hr0 hr2 5
  have h6 := pow_le_pow_left₀ hr0 hr2 6
  have h7 := pow_le_pow_left₀ hr0 hr2 7
  have h8 := pow_le_pow_left₀ hr0 hr2 8
  norm_num at h2 h3 h4 h5 h6 h7 h8
  have hmono :
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform r (34 + s) ≤
        thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform 2 (34 + s) := by
    unfold thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    nlinarith [sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4,
      pow_nonneg hs 5, pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8]
  refine hmono.trans ?_
  unfold thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Stripped score core of the convolution of atom `n` with atom `m`. -/
def thetaCuspLikelihoodAtomPairEighthScoreCore (n m : ℕ) (A B : ℝ) : ℝ :=
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  let un := (3 / 2 : ℝ) * (n : ℝ) ^ (2 : ℕ) * d / B
  let um := (3 / 2 : ℝ) * (m : ℝ) ^ (2 : ℕ) * e / B
  (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) *
      thetaCuspLikelihoodEighthSourceScore (A * (d + e)) +
    ((n : ℝ) ^ (4 : ℕ) * um + un * (m : ℝ) ^ (4 : ℕ)) *
      thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (A * (d + e)) +
    un * um *
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (A * (d + e))

/-- Actual calibrated score mass of the convolution of two mixed atom-ray measures. -/
def thetaCuspLikelihoodAtomPairEighthScoreMass (n m : ℕ) (A B : ℝ) : ℝ :=
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  Real.exp (-(3 / 2 : ℝ) * (d + e)) * Real.exp (-(B * (d + e))) *
    thetaCuspLikelihoodAtomPairEighthScoreCore n m A B

/-- Every non-dominant pair has scaled support above `34`. -/
theorem thirtyFour_le_mul_add_thetaCuspLikelihoodGap
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hstable : 3 ≤ n ∨ 3 ≤ m)
    {A : ℝ} (hA : Real.pi ≤ A) :
    34 ≤ A * (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsum : 11 ≤ thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m := by
    rcases hstable with hn3 | hm3
    · have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      unfold thetaCuspLikelihoodGap
      nlinarith [sq_nonneg ((n : ℝ) - 3), sq_nonneg ((m : ℝ) - 2)]
    · have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm3
      unfold thetaCuspLikelihoodGap
      nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg ((m : ℝ) - 3)]
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d2]
  have hA0 : 0 ≤ A := le_trans Real.pi_pos.le hA
  have hmul := mul_le_mul hA hsum (by norm_num : (0 : ℝ) ≤ 11) hA0
  nlinarith

/-- The normalized ray coefficient is no larger than the point coefficient. -/
theorem thetaCuspLikelihood_normalizedRayCoefficient_le_pow_four
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : (3 / 2 : ℝ) ≤ B) :
    (3 / 2 : ℝ) * (n : ℝ) ^ (2 : ℕ) * thetaCuspLikelihoodGap n / B ≤
      (n : ℝ) ^ (4 : ℕ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 < B := by linarith
  have hgap0 : 0 ≤ thetaCuspLikelihoodGap n :=
    (thetaCuspLikelihoodGap_pos hn).le
  have hnd : (n : ℝ) ^ (2 : ℕ) * thetaCuspLikelihoodGap n ≤ (n : ℝ) ^ (4 : ℕ) := by
    unfold thetaCuspLikelihoodGap
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    (3 / 2 : ℝ) * (n : ℝ) ^ (2 : ℕ) * thetaCuspLikelihoodGap n / B =
        ((3 / 2 : ℝ) / B) * ((n : ℝ) ^ (2 : ℕ) * thetaCuspLikelihoodGap n) := by ring
    _ ≤ 1 * (n : ℝ) ^ (4 : ℕ) := by
      gcongr
      exact (div_le_one hB0).2 hB
    _ = (n : ℝ) ^ (4 : ℕ) := one_mul _

/-- Uniform factor-nine core bound for every pair outside the dominant `(2,2)` chamber. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreCore_le
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hstable : 3 ≤ n ∨ 3 ≤ m)
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomPairEighthScoreCore n m A B ≤
      9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) *
        (A * (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m)) ^ (8 : ℕ) := by
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  let z := A * (d + e)
  let un := (3 / 2 : ℝ) * (n : ℝ) ^ (2 : ℕ) * d / B
  let um := (3 / 2 : ℝ) * (m : ℝ) ^ (2 : ℕ) * e / B
  have hApi : (157 / 50 : ℝ) ≤ A := by
    nlinarith [Real.pi_gt_d2]
  have hB : 0 < B := by
    rw [hBA]
    linarith
  have hB32 : (3 / 2 : ℝ) ≤ B := by
    rw [hBA]
    nlinarith [Real.pi_gt_three]
  have hA0 : 0 ≤ A := le_trans Real.pi_pos.le hA
  have hr0 : 0 ≤ A / B := div_nonneg hA0 hB.le
  have hr2 : A / B ≤ 2 := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    linarith
  have hz : 34 ≤ z := by
    dsimp only [z, d, e]
    exact thirtyFour_le_mul_add_thetaCuspLikelihoodGap hn hm hstable hA
  have hz14 : 14 ≤ z := by linarith
  have hpoint := thetaCuspLikelihoodEighthSourceScore_le_pow_eight hz14
  have hray :=
    thetaCuspLikelihoodEighthSourceScoreRayTransform_le_two_mul_pow_eight hr0 hr2 hz
  have hdouble :=
    thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform_le_four_mul_pow_eight hr0 hr2 hz
  have hun0 : 0 ≤ un := by
    dsimp only [un, d]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (thetaCuspLikelihoodGap_pos hn).le) hB.le
  have hum0 : 0 ≤ um := by
    dsimp only [um, e]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (thetaCuspLikelihoodGap_pos hm).le) hB.le
  have hun : un ≤ (n : ℝ) ^ (4 : ℕ) := by
    dsimp only [un, d]
    exact thetaCuspLikelihood_normalizedRayCoefficient_le_pow_four hn hB32
  have hum : um ≤ (m : ℝ) ^ (4 : ℕ) := by
    dsimp only [um, e]
    exact thetaCuspLikelihood_normalizedRayCoefficient_le_pow_four hm hB32
  have hn4 : 0 ≤ (n : ℝ) ^ (4 : ℕ) := by positivity
  have hm4 : 0 ≤ (m : ℝ) ^ (4 : ℕ) := by positivity
  have hz8 : 0 ≤ z ^ (8 : ℕ) := by positivity
  change
    (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodEighthSourceScore z +
        ((n : ℝ) ^ (4 : ℕ) * um + un * (m : ℝ) ^ (4 : ℕ)) *
            thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) z +
          un * um * thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) z ≤
      9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * z ^ (8 : ℕ)
  have hpoint' :
      (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodEighthSourceScore z ≤
        (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * z ^ (8 : ℕ) := by gcongr
  have hmixCoeff :
      (n : ℝ) ^ (4 : ℕ) * um + un * (m : ℝ) ^ (4 : ℕ) ≤
        2 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) := by nlinarith
  have hray0 : 0 ≤ thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) z := by
    unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    let s := z - 34
    have hs : 0 ≤ s := by dsimp only [s]; linarith
    rw [show z = 34 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hmix :
      ((n : ℝ) ^ (4 : ℕ) * um + un * (m : ℝ) ^ (4 : ℕ)) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) z ≤
        4 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) * z ^ (8 : ℕ) := by
    calc
      _ ≤ (2 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ))) *
          thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) z := by gcongr
      _ ≤ (2 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ))) * (2 * z ^ (8 : ℕ)) := by gcongr
      _ = 4 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) * z ^ (8 : ℕ) := by ring
  have hdouble0 :
      0 ≤ thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) z := by
    unfold thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    let s := z - 34
    have hs : 0 ≤ s := by dsimp only [s]; linarith
    rw [show z = 34 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdoubleCoeff : un * um ≤ (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) := by gcongr
  have hdouble' :
      un * um * thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) z ≤
        4 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) * z ^ (8 : ℕ) := by
    calc
      _ ≤ ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) *
          thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) z := by gcongr
      _ ≤ ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) * (4 * z ^ (8 : ℕ)) := by gcongr
      _ = 4 * ((n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ)) * z ^ (8 : ℕ) := by ring
  linarith

/-- Calibrated mass form of the uniform factor-nine pair bound. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreMass_le
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hstable : 3 ≤ n ∨ 3 ≤ m)
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomPairEighthScoreMass n m A B ≤
      9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) *
        (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m) ^ (8 : ℕ) *
        Real.exp (-(A * (thetaCuspLikelihoodGap n + thetaCuspLikelihoodGap m))) := by
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  have hcore := thetaCuspLikelihoodAtomPairEighthScoreCore_le hn hm hstable hA hBA
  have hexp : Real.exp (-(3 / 2 : ℝ) * (d + e)) * Real.exp (-(B * (d + e))) =
      Real.exp (-(A * (d + e))) := by
    rw [← Real.exp_add, hBA]
    congr 1
    ring
  unfold thetaCuspLikelihoodAtomPairEighthScoreMass
  dsimp only
  rw [hexp]
  calc
    Real.exp (-(A * (d + e))) * thetaCuspLikelihoodAtomPairEighthScoreCore n m A B ≤
        Real.exp (-(A * (d + e))) *
          (9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * (A * (d + e)) ^ (8 : ℕ)) := by
      gcongr
    _ = 9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) * (d + e) ^ (8 : ℕ) *
        Real.exp (-(A * (d + e))) := by rw [mul_pow]; ring

/-- The general pair mass specializes exactly to the previously compensated dominant pair. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq
    {A B : ℝ} (hA : (157 / 50 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomPairEighthScoreMass 2 2 A B =
      thetaCuspLikelihoodEighthDominantPairMass A := by
  unfold thetaCuspLikelihoodAtomPairEighthScoreMass
    thetaCuspLikelihoodAtomPairEighthScoreCore
    thetaCuspLikelihoodEighthDominantPairMass
    thetaCuspLikelihoodEighthDominantPairCore
  norm_num [thetaCuspLikelihoodGap]
  rw [hBA]
  have hexp : Real.exp (-(9 : ℝ)) * Real.exp (-((A - 3 / 2) * 6)) =
      Real.exp (-(6 * A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hden : A - 3 / 2 ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem thetaCusp_nat_add_three_pow_twenty_le (k : ℕ) :
    (((k + 3 : ℕ) : ℝ) ^ (20 : ℕ)) ≤ 3486784401 * (1048576 : ℝ) ^ k := by
  have hnat : k + 3 ≤ 3 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        omega
  have hcast : ((k + 3 : ℕ) : ℝ) ≤ (3 * 2 ^ k : ℕ) := by
    exact_mod_cast hnat
  calc
    (((k + 3 : ℕ) : ℝ) ^ (20 : ℕ)) ≤ (((3 * 2 ^ k : ℕ) : ℝ) ^ (20 : ℕ)) := by gcongr
    _ = 3486784401 * (1048576 : ℝ) ^ k := by
      push_cast
      rw [mul_pow]
      norm_num
      calc
        (((2 : ℝ) ^ k) ^ (20 : ℕ)) = (2 : ℝ) ^ (k * 20) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (20 * k) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ (20 : ℕ)) ^ k := by rw [pow_mul]
        _ = (1048576 : ℝ) ^ k := by norm_num

theorem thetaCusp_tail_exponent_seven_add_three_le_eighth (k : ℕ) :
    Real.exp (-Real.pi * (((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1)) ≤
      Real.exp (-8 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k := by
  have hsquare :
      (8 : ℝ) + 7 * k ≤ (((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) := by
    rcases k with _ | k
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * (((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) ≤
        -8 * Real.pi + (k : ℕ) * (-7 * Real.pi) := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ Real.exp (-8 * Real.pi + (k : ℕ) * (-7 * Real.pi)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

/-- Order-eight stable Gaussian weight has a `1/100` geometric envelope. -/
theorem thetaCuspReflectionJetTailWeight_eight_tail_le_geometric (k : ℕ) :
    thetaCuspReflectionJetTailWeight 8 (k + 1) ≤
      (1 / 4 : ℝ) * ((1 / 100 : ℝ) ^ k) := by
  let n : ℕ := k + 3
  have hpow := thetaCusp_nat_add_three_pow_twenty_le k
  have hexp := thetaCusp_tail_exponent_seven_add_three_le_eighth k
  have hbase : Real.exp (-8 * Real.pi) ≤ (1 : ℝ) / 14400000000 :=
    exp_neg_eight_pi_lt_one_div_fourteenBillionFourHundredMillion.le
  have hratio : 1048576 * Real.exp (-7 * Real.pi) ≤ (1 / 100 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_oneHundredTwentyMillion]
  have hn : (3 : ℝ) ≤ n := by
    exact_mod_cast (by dsimp only [n]; omega : 3 ≤ n)
  have hd : 0 ≤ (n : ℝ) ^ (2 : ℕ) - 1 := by nlinarith
  have hdle : ((n : ℝ) ^ (2 : ℕ) - 1) ^ (8 : ℕ) ≤ ((n : ℝ) ^ (2 : ℕ)) ^ (8 : ℕ) :=
    pow_le_pow_left₀ hd (by linarith) 8
  unfold thetaCuspReflectionJetTailWeight
  dsimp only [n]
  calc
    (n : ℝ) ^ (4 : ℕ) * ((n : ℝ) ^ (2 : ℕ) - 1) ^ (8 : ℕ) *
          Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1)) ≤
        (n : ℝ) ^ (4 : ℕ) * ((n : ℝ) ^ (2 : ℕ)) ^ (8 : ℕ) *
          Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1)) := by gcongr
    _ = (n : ℝ) ^ (20 : ℕ) * Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1)) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ (3486784401 * (1048576 : ℝ) ^ k) *
        (Real.exp (-8 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 3486784401 * Real.exp (-8 * Real.pi) *
        (1048576 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 3486784401 * ((1 : ℝ) / 14400000000) *
        ((1 / 100 : ℝ) ^ k) := by gcongr
    _ ≤ (1 / 4 : ℝ) * ((1 / 100 : ℝ) ^ k) := by
      gcongr
      norm_num

/-- Complete order-eight stable Gaussian moment is at most `25/99`. -/
theorem tsum_thetaCuspReflectionJetTailWeight_eight_tail_le :
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 8 (k + 1)) ≤
      (25 / 99 : ℝ) := by
  have hs : Summable (fun k : ℕ => thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 8)
  have hgeo : Summable (fun k : ℕ =>
      (1 / 4 : ℝ) * ((1 / 100 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 100 : ℝ)‖ < 1)).mul_left _
  calc
    (∑' k : ℕ, thetaCuspReflectionJetTailWeight 8 (k + 1)) ≤
        ∑' k : ℕ, (1 / 4 : ℝ) * ((1 / 100 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspReflectionJetTailWeight_eight_tail_le_geometric hs hgeo
    _ = (1 / 4 : ℝ) * (1 - (1 / 100 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (25 / 99 : ℝ) := by norm_num

theorem exp_neg_five_pi_lt_one_div_oneMillionTwoHundredThousand :
    Real.exp (-5 * Real.pi) < (1 : ℝ) / 1200000 := by
  rw [show -5 * Real.pi = -3 * Real.pi + (-2 * Real.pi) by ring,
    Real.exp_add]
  have h3 := thetaCusp_exp_neg_three_pi_lt
  have h2 := exp_neg_two_pi_lt_one_div_hundred
  calc
    Real.exp (-3 * Real.pi) * Real.exp (-2 * Real.pi) <
        (1 / 12000 : ℝ) * (1 / 100 : ℝ) := by gcongr
    _ = (1 : ℝ) / 1200000 := by norm_num

theorem thetaCusp_nat_add_three_pow_four_le (k : ℕ) :
    (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ)) ≤ 81 * (16 : ℝ) ^ k := by
  have hnat : k + 3 ≤ 3 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        omega
  have hcast : ((k + 3 : ℕ) : ℝ) ≤ (3 * 2 ^ k : ℕ) := by
    exact_mod_cast hnat
  calc
    (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ)) ≤ (((3 * 2 ^ k : ℕ) : ℝ) ^ (4 : ℕ)) := by gcongr
    _ = 81 * (16 : ℝ) ^ k := by
      push_cast
      rw [mul_pow]
      norm_num
      calc
        (((2 : ℝ) ^ k) ^ (4 : ℕ)) = (2 : ℝ) ^ (k * 4) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (4 * k) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ (4 : ℕ)) ^ k := by rw [pow_mul]
        _ = (16 : ℝ) ^ k := by norm_num

theorem thetaCusp_shifted_tail_exponent_seven_add_three_le (k : ℕ) :
    Real.exp (-Real.pi * ((((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) - 3)) ≤
      Real.exp (-5 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k := by
  have hsquare :
      (5 : ℝ) + 7 * k ≤ (((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) - 3 := by
    rcases k with _ | k
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * ((((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) - 3) ≤
        -5 * Real.pi + (k : ℕ) * (-7 * Real.pi) := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ Real.exp (-5 * Real.pi + (k : ℕ) * (-7 * Real.pi)) :=
      Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

/-- Gap-shifted stable activity has a `1/1000` geometric envelope. -/
theorem thetaCuspLikelihoodStableShiftedActivityTerm_le_geometric (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) ≤
      (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by
  have hpow := thetaCusp_nat_add_three_pow_four_le k
  have hexp := thetaCusp_shifted_tail_exponent_seven_add_three_le k
  have hbase : Real.exp (-5 * Real.pi) ≤ (1 : ℝ) / 1200000 :=
    exp_neg_five_pi_lt_one_div_oneMillionTwoHundredThousand.le
  have hratio : 16 * Real.exp (-7 * Real.pi) ≤ (1 / 1000 : ℝ) := by
    nlinarith [exp_neg_seven_pi_lt_one_div_oneHundredTwentyMillion]
  unfold thetaCuspLikelihoodGap
  calc
    ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
          Real.exp (-Real.pi * ((((k + 3 : ℕ) : ℝ) ^ (2 : ℕ) - 1) - 3)) ≤
        (81 * (16 : ℝ) ^ k) *
          (Real.exp (-5 * Real.pi) * (Real.exp (-7 * Real.pi)) ^ k) := by gcongr
    _ = 81 * Real.exp (-5 * Real.pi) *
        (16 * Real.exp (-7 * Real.pi)) ^ k := by ring
    _ ≤ 81 * ((1 : ℝ) / 1200000) * ((1 / 1000 : ℝ) ^ k) := by gcongr
    _ ≤ (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by
      gcongr
      norm_num

/-- Complete gap-shifted stable activity at the physical edge is at most `1/999`. -/
theorem tsum_thetaCuspLikelihoodStableShiftedActivity_pi_le :
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
      (1 / 999 : ℝ) := by
  have hgeo : Summable (fun k : ℕ =>
      (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000 : ℝ)‖ < 1)).mul_left _
  have hnonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hs := Summable.of_nonneg_of_le hnonneg
    thetaCuspLikelihoodStableShiftedActivityTerm_le_geometric hgeo
  calc
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
        ∑' k : ℕ, (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspLikelihoodStableShiftedActivityTerm_le_geometric hs hgeo
    _ = (1 / 1000 : ℝ) * (1 - (1 / 1000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (1 / 999 : ℝ) := by norm_num

/-- Order-eight Gaussian moment of the complete stable tower at scale `A`. -/
def thetaCuspLikelihoodStableEighthTail (A : ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
    Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))

/-- Stable activity after extracting the dominant exponential `exp (-3A)`. -/
def thetaCuspLikelihoodStableShiftedActivity (A : ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
    Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))

theorem thetaCuspLikelihoodStableEighthTailTerm_le_pi
    {A : ℝ} (hA : Real.pi ≤ A) (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
        Real.exp (-(A * thetaCuspLikelihoodGap (k + 3))) ≤
      thetaCuspReflectionJetTailWeight 8 (k + 1) := by
  have hgap : 0 ≤ thetaCuspLikelihoodGap (k + 3) :=
    (thetaCuspLikelihoodGap_pos (by omega)).le
  have hexponent :
      -(A * thetaCuspLikelihoodGap (k + 3)) ≤
        -Real.pi * thetaCuspLikelihoodGap (k + 3) := by
    nlinarith
  have hcoef : 0 ≤ ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hcoef
  unfold thetaCuspReflectionJetTailWeight
  simpa only [show k + 1 + 2 = k + 3 by omega, thetaCuspLikelihoodGap] using hmul

theorem summable_thetaCuspLikelihoodStableEighthTail
    {A : ℝ} (hA : Real.pi ≤ A) :
    Summable (fun k : ℕ => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
      Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) := by
  have hmajor : Summable (fun k : ℕ =>
      thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 8)
  apply Summable.of_norm_bounded hmajor
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact thetaCuspLikelihoodStableEighthTailTerm_le_pi hA k
  · positivity

/-- The stable order-eight moment keeps the uniform `25/99` edge bound at every physical scale. -/
theorem thetaCuspLikelihoodStableEighthTail_le
    {A : ℝ} (hA : Real.pi ≤ A) :
    thetaCuspLikelihoodStableEighthTail A ≤ (25 / 99 : ℝ) := by
  have hs := summable_thetaCuspLikelihoodStableEighthTail hA
  have hw : Summable (fun k : ℕ =>
      thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    (summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 8)
  unfold thetaCuspLikelihoodStableEighthTail
  exact (Summable.tsum_le_tsum
    (thetaCuspLikelihoodStableEighthTailTerm_le_pi hA) hs hw).trans
      tsum_thetaCuspReflectionJetTailWeight_eight_tail_le

theorem thetaCuspLikelihoodStableShiftedActivityTerm_le_pi
    {A : ℝ} (hA : Real.pi ≤ A) (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3))) ≤
      ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
  have hgap : 0 ≤ thetaCuspLikelihoodGap (k + 3) - 3 := by
    have hnR : (3 : ℝ) ≤ (k + 3 : ℕ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
    unfold thetaCuspLikelihoodGap
    nlinarith
  have hexponent :
      -(A * (thetaCuspLikelihoodGap (k + 3) - 3)) ≤
        -Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3) := by
    nlinarith
  gcongr

theorem summable_thetaCuspLikelihoodStableShiftedActivity
    {A : ℝ} (hA : Real.pi ≤ A) :
    Summable (fun k : ℕ => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) := by
  have hgeo : Summable (fun k : ℕ =>
      (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000 : ℝ)‖ < 1)).mul_left _
  have hpiNonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hpi := Summable.of_nonneg_of_le hpiNonneg
    thetaCuspLikelihoodStableShiftedActivityTerm_le_geometric hgeo
  apply Summable.of_norm_bounded hpi
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact thetaCuspLikelihoodStableShiftedActivityTerm_le_pi hA k
  · positivity

/-- Gap-shifted stable activity is uniformly at most `1/999`. -/
theorem thetaCuspLikelihoodStableShiftedActivity_le
    {A : ℝ} (hA : Real.pi ≤ A) :
    thetaCuspLikelihoodStableShiftedActivity A ≤ (1 / 999 : ℝ) := by
  have hs := summable_thetaCuspLikelihoodStableShiftedActivity hA
  have hgeo : Summable (fun k : ℕ =>
      (1 / 1000 : ℝ) * ((1 / 1000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 1000 : ℝ)‖ < 1)).mul_left _
  have hpiNonneg : ∀ k : ℕ, 0 ≤ ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
      Real.exp (-Real.pi * (thetaCuspLikelihoodGap (k + 3) - 3)) := by
    intro k
    positivity
  have hpi := Summable.of_nonneg_of_le hpiNonneg
    thetaCuspLikelihoodStableShiftedActivityTerm_le_geometric hgeo
  unfold thetaCuspLikelihoodStableShiftedActivity
  have hfirst := Summable.tsum_le_tsum
    (thetaCuspLikelihoodStableShiftedActivityTerm_le_pi hA) hs hpi
  exact hfirst.trans tsum_thetaCuspLikelihoodStableShiftedActivity_pi_le

/-- The one-ray transform is nonnegative on non-dominant pair support. -/
theorem thetaCuspLikelihoodEighthSourceScoreRayTransform_nonneg_of_thirtyFour_le
    {r z : ℝ} (hr0 : 0 ≤ r) (hz : 34 ≤ z) :
    0 ≤ thetaCuspLikelihoodEighthSourceScoreRayTransform r z := by
  let s := z - 34
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  rw [show z = 34 + s by dsimp only [s]; ring]
  unfold thetaCuspLikelihoodEighthSourceScoreRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  ring_nf
  positivity

/-- The two-ray transform is nonnegative on non-dominant pair support. -/
theorem thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform_nonneg_of_thirtyFour_le
    {r z : ℝ} (hr0 : 0 ≤ r) (hz : 34 ≤ z) :
    0 ≤ thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform r z := by
  let s := z - 34
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  rw [show z = 34 + s by dsimp only [s]; ring]
  unfold thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
    thetaCuspLikelihoodEighthSourceScore
    thetaCuspLikelihoodEighthSourceScoreDerivOne
    thetaCuspLikelihoodEighthSourceScoreDerivTwo
    thetaCuspLikelihoodEighthSourceScoreDerivThree
    thetaCuspLikelihoodEighthSourceScoreDerivFour
    thetaCuspLikelihoodEighthSourceScoreDerivFive
    thetaCuspLikelihoodEighthSourceScoreDerivSix
    thetaCuspLikelihoodEighthSourceScoreDerivSeven
    thetaCuspLikelihoodEighthSourceScoreDerivEight
  ring_nf
  positivity

/-- Every non-dominant atom-pair score mass is nonnegative. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hstable : 3 ≤ n ∨ 3 ≤ m)
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    0 ≤ thetaCuspLikelihoodAtomPairEighthScoreMass n m A B := by
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  let z := A * (d + e)
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hA0 : 0 ≤ A := le_trans Real.pi_pos.le hA
  have hr0 : 0 ≤ A / B := div_nonneg hA0 hB.le
  have hz : 34 ≤ z := by
    dsimp only [z, d, e]
    exact thirtyFour_le_mul_add_thetaCuspLikelihoodGap hn hm hstable hA
  have hpoint : 0 ≤ thetaCuspLikelihoodEighthSourceScore z :=
    (thetaCuspLikelihoodEighthSourceScore_pos_of_fourteen_le (by linarith)).le
  have hray : 0 ≤ thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) z :=
    thetaCuspLikelihoodEighthSourceScoreRayTransform_nonneg_of_thirtyFour_le hr0 hz
  have hdouble :
      0 ≤ thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) z :=
    thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform_nonneg_of_thirtyFour_le hr0 hz
  have hd0 : 0 ≤ d := (thetaCuspLikelihoodGap_pos hn).le
  have he0 : 0 ≤ e := (thetaCuspLikelihoodGap_pos hm).le
  unfold thetaCuspLikelihoodAtomPairEighthScoreMass
    thetaCuspLikelihoodAtomPairEighthScoreCore
  dsimp only [d, e, z]
  positivity

/-- Atom-pair score mass is symmetric in its arithmetic labels. -/
theorem thetaCuspLikelihoodAtomPairEighthScoreMass_comm
    (n m : ℕ) (A B : ℝ) :
    thetaCuspLikelihoodAtomPairEighthScoreMass n m A B =
      thetaCuspLikelihoodAtomPairEighthScoreMass m n A B := by
  unfold thetaCuspLikelihoodAtomPairEighthScoreMass
    thetaCuspLikelihoodAtomPairEighthScoreCore
  ring

/-- Adding dominant gap three costs at most thirteen copies of a stable eighth gap power. -/
theorem add_three_pow_eight_le_thirteen_mul_gap_pow_eight
    {m : ℕ} (hm : 3 ≤ m) :
    (3 + thetaCuspLikelihoodGap m) ^ (8 : ℕ) ≤
      13 * thetaCuspLikelihoodGap m ^ (8 : ℕ) := by
  let e := thetaCuspLikelihoodGap m
  have he : 8 ≤ e := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [e, thetaCuspLikelihoodGap]
    nlinarith
  have he0 : 0 ≤ e := by linarith
  have hbase : 3 + e ≤ (11 / 8 : ℝ) * e := by nlinarith
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 3 + e) hbase 8
  calc
    (3 + thetaCuspLikelihoodGap m) ^ (8 : ℕ) = (3 + e) ^ (8 : ℕ) := rfl
    _ ≤ ((11 / 8 : ℝ) * e) ^ (8 : ℕ) := hpow
    _ = (11 / 8 : ℝ) ^ (8 : ℕ) * e ^ (8 : ℕ) := by ring
    _ ≤ 13 * e ^ (8 : ℕ) := by
      gcongr
      norm_num
    _ = 13 * thetaCuspLikelihoodGap m ^ (8 : ℕ) := rfl

/-- One ordered dominant-stable pair is bounded by the stable order-eight Gaussian term. -/
theorem thetaCuspLikelihoodDominantStablePairEighthScoreMass_le
    (k : ℕ) {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B ≤
      1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
          Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) := by
  let m : ℕ := k + 3
  let e := thetaCuspLikelihoodGap m
  have hpair := thetaCuspLikelihoodAtomPairEighthScoreMass_le
    (n := 2) (m := m) (by norm_num) (by dsimp only [m]; omega)
    (Or.inr (by dsimp only [m]; omega)) hA hBA
  have hgap := add_three_pow_eight_le_thirteen_mul_gap_pow_eight
    (m := m) (by dsimp only [m]; omega)
  have hexp : Real.exp (-(A * (3 + e))) =
      Real.exp (-(3 * A)) * Real.exp (-(A * e)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hA0 : 0 ≤ A := le_trans Real.pi_pos.le hA
  have he0 : 0 ≤ e := (thetaCuspLikelihoodGap_pos (by dsimp only [m]; omega)).le
  have hm4 : 0 ≤ (m : ℝ) ^ (4 : ℕ) := by positivity
  have hscale : 0 ≤ 9 * (2 : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) := by positivity
  change thetaCuspLikelihoodAtomPairEighthScoreMass 2 m A B ≤ _
  calc
    thetaCuspLikelihoodAtomPairEighthScoreMass 2 m A B ≤
        9 * (2 : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) * (3 + e) ^ (8 : ℕ) *
          Real.exp (-(A * (3 + e))) := by
      simpa only [show thetaCuspLikelihoodGap 2 = 3 by
        norm_num [thetaCuspLikelihoodGap], e, Nat.cast_ofNat] using hpair
    _ ≤ 9 * (2 : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) * (13 * e ^ (8 : ℕ)) *
          Real.exp (-(A * (3 + e))) := by gcongr
    _ = 1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        ((m : ℝ) ^ (4 : ℕ) * e ^ (8 : ℕ) * Real.exp (-(A * e))) := by rw [hexp]; ring

/-- Complete ordered dominant-stable pair tail. -/
def thetaCuspLikelihoodDominantStablePairEighthTail (A B : ℝ) : ℝ :=
  ∑' k : ℕ, thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B

theorem summable_thetaCuspLikelihoodDominantStablePairEighthScoreMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    Summable (fun k : ℕ =>
      thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B) := by
  have hs := (summable_thetaCuspLikelihoodStableEighthTail hA).mul_left
    (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  apply Summable.of_nonneg_of_le
  · intro k
    exact thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
      (by norm_num) (by omega) (Or.inr (by omega)) hA hBA
  · intro k
    exact thetaCuspLikelihoodDominantStablePairEighthScoreMass_le k hA hBA
  · exact hs

/-- One ordered mixed tail costs at most `5200/11` dominant exponential units. -/
theorem thetaCuspLikelihoodDominantStablePairEighthTail_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantStablePairEighthTail A B ≤
      (5200 / 11 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
  have hs := summable_thetaCuspLikelihoodDominantStablePairEighthScoreMass hA hBA
  have hw := (summable_thetaCuspLikelihoodStableEighthTail hA).mul_left
    (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  have htail := thetaCuspLikelihoodStableEighthTail_le hA
  unfold thetaCuspLikelihoodDominantStablePairEighthTail
  calc
    (∑' k : ℕ, thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B) ≤
        ∑' k : ℕ, 1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspLikelihoodDominantStablePairEighthScoreMass_le k hA hBA) hs hw
    _ = (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableEighthTail A := by
      unfold thetaCuspLikelihoodStableEighthTail
      rw [tsum_mul_left]
    _ ≤ (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) * (25 / 99 : ℝ) := by
      gcongr
    _ = (5200 / 11 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by ring

/-- A stable-stable pair factors into the eighth stable moment and shifted activity. -/
theorem thetaCuspLikelihoodStableStablePairEighthScoreMass_le
    (k l : ℕ) {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomPairEighthScoreMass (k + 3) (l + 3) A B ≤
      1152 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        ((((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
              Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) *
            (((l + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
              Real.exp (-(A * (thetaCuspLikelihoodGap (l + 3) - 3)))) +
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
              Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))) *
            (((l + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (l + 3) ^ (8 : ℕ) *
              Real.exp (-(A * thetaCuspLikelihoodGap (l + 3))))) := by
  let n : ℕ := k + 3
  let m : ℕ := l + 3
  let d := thetaCuspLikelihoodGap n
  let e := thetaCuspLikelihoodGap m
  have hpair := thetaCuspLikelihoodAtomPairEighthScoreMass_le
    (n := n) (m := m) (by dsimp only [n]; omega) (by dsimp only [m]; omega)
    (Or.inl (by dsimp only [n]; omega)) hA hBA
  have hd0 : 0 ≤ d := (thetaCuspLikelihoodGap_pos (by dsimp only [n]; omega)).le
  have he0 : 0 ≤ e := (thetaCuspLikelihoodGap_pos (by dsimp only [m]; omega)).le
  have hpow := add_pow_le hd0 he0 8
  norm_num at hpow
  have hfirst :
      Real.exp (-(3 * A)) * Real.exp (-(A * d)) * Real.exp (-(A * (e - 3))) =
        Real.exp (-(A * (d + e))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsecond :
      Real.exp (-(3 * A)) * Real.exp (-(A * (d - 3))) * Real.exp (-(A * e)) =
        Real.exp (-(A * (d + e))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change thetaCuspLikelihoodAtomPairEighthScoreMass n m A B ≤ _
  calc
    thetaCuspLikelihoodAtomPairEighthScoreMass n m A B ≤
        9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) * (d + e) ^ (8 : ℕ) *
          Real.exp (-(A * (d + e))) := by
      simpa only [d, e] using hpair
    _ ≤ 9 * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * A ^ (8 : ℕ) *
          (128 * (d ^ (8 : ℕ) + e ^ (8 : ℕ))) * Real.exp (-(A * (d + e))) := by gcongr
    _ = 1152 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        (((n : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ) * Real.exp (-(A * d))) *
            ((m : ℝ) ^ (4 : ℕ) * Real.exp (-(A * (e - 3)))) +
          ((n : ℝ) ^ (4 : ℕ) * Real.exp (-(A * (d - 3)))) *
            ((m : ℝ) ^ (4 : ℕ) * e ^ (8 : ℕ) * Real.exp (-(A * e)))) := by
      linear_combination
        -(1152 * A ^ (8 : ℕ) * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ)) * hfirst -
        (1152 * A ^ (8 : ℕ) * (n : ℝ) ^ (4 : ℕ) * (m : ℝ) ^ (4 : ℕ) * e ^ (8 : ℕ)) * hsecond

/-- Complete ordered stable-stable pair tail. -/
def thetaCuspLikelihoodStableStablePairEighthTail (A B : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ,
    thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 3) (p.2 + 3) A B

theorem summable_thetaCuspLikelihoodStableStablePairEighthScoreMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    Summable (fun p : ℕ × ℕ =>
      thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 3) (p.2 + 3) A B) := by
  let f8 : ℕ → ℝ := fun k => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
    thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
      Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))
  let f0 : ℕ → ℝ := fun k => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
    Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))
  have h8 : Summable f8 := by
    simpa only [f8] using summable_thetaCuspLikelihoodStableEighthTail hA
  have h0 : Summable f0 := by
    simpa only [f0] using summable_thetaCuspLikelihoodStableShiftedActivity hA
  have hf8 : ∀ k, 0 ≤ f8 k := by intro k; dsimp only [f8]; positivity
  have hf0 : ∀ k, 0 ≤ f0 k := by intro k; dsimp only [f0]; positivity
  have hp80 : Summable (fun p : ℕ × ℕ => f8 p.1 * f0 p.2) :=
    h8.mul_of_nonneg h0 hf8 hf0
  have hp08 : Summable (fun p : ℕ × ℕ => f0 p.1 * f8 p.2) :=
    h0.mul_of_nonneg h8 hf0 hf8
  have hmajor := (hp80.add hp08).mul_left
    (1152 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  apply Summable.of_nonneg_of_le
  · intro p
    exact thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
      (by omega) (by omega) (Or.inl (by omega)) hA hBA
  · intro p
    simpa only [f8, f0] using
      thetaCuspLikelihoodStableStablePairEighthScoreMass_le p.1 p.2 hA hBA
  · exact hmajor

/-- Complete stable-stable pair tail costs less than one dominant exponential unit. -/
theorem thetaCuspLikelihoodStableStablePairEighthTail_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodStableStablePairEighthTail A B ≤
      A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
  let f8 : ℕ → ℝ := fun k => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
    thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
      Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))
  let f0 : ℕ → ℝ := fun k => ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) *
    Real.exp (-(A * (thetaCuspLikelihoodGap (k + 3) - 3)))
  have h8 : Summable f8 := by
    simpa only [f8] using summable_thetaCuspLikelihoodStableEighthTail hA
  have h0 : Summable f0 := by
    simpa only [f0] using summable_thetaCuspLikelihoodStableShiftedActivity hA
  have hf8 : ∀ k, 0 ≤ f8 k := by intro k; dsimp only [f8]; positivity
  have hf0 : ∀ k, 0 ≤ f0 k := by intro k; dsimp only [f0]; positivity
  have hp80 : Summable (fun p : ℕ × ℕ => f8 p.1 * f0 p.2) :=
    h8.mul_of_nonneg h0 hf8 hf0
  have hp08 : Summable (fun p : ℕ × ℕ => f0 p.1 * f8 p.2) :=
    h0.mul_of_nonneg h8 hf0 hf8
  have hmajor := (hp80.add hp08).mul_left
    (1152 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  have hs := summable_thetaCuspLikelihoodStableStablePairEighthScoreMass hA hBA
  have h8le := thetaCuspLikelihoodStableEighthTail_le hA
  have h0le := thetaCuspLikelihoodStableShiftedActivity_le hA
  have h8nonneg : 0 ≤ thetaCuspLikelihoodStableEighthTail A := by
    unfold thetaCuspLikelihoodStableEighthTail
    exact tsum_nonneg fun k => by positivity
  have h0nonneg : 0 ≤ thetaCuspLikelihoodStableShiftedActivity A := by
    unfold thetaCuspLikelihoodStableShiftedActivity
    exact tsum_nonneg fun k => by positivity
  unfold thetaCuspLikelihoodStableStablePairEighthTail
  calc
    (∑' p : ℕ × ℕ,
        thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 3) (p.2 + 3) A B) ≤
      ∑' p : ℕ × ℕ, 1152 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        (f8 p.1 * f0 p.2 + f0 p.1 * f8 p.2) :=
      Summable.tsum_le_tsum
        (fun p => by simpa only [f8, f0] using
          thetaCuspLikelihoodStableStablePairEighthScoreMass_le p.1 p.2 hA hBA)
        hs hmajor
    _ = 2304 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        (thetaCuspLikelihoodStableEighthTail A *
          thetaCuspLikelihoodStableShiftedActivity A) := by
      rw [tsum_mul_left, Summable.tsum_add hp80 hp08,
        ← tsum_mul_tsum_of_summable_norm h8.norm h0.norm,
        ← tsum_mul_tsum_of_summable_norm h0.norm h8.norm]
      unfold thetaCuspLikelihoodStableEighthTail
        thetaCuspLikelihoodStableShiftedActivity
      dsimp only [f8, f0]
      ring
    _ ≤ 2304 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
        ((25 / 99 : ℝ) * (1 / 999 : ℝ)) := by gcongr
    _ ≤ A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
      have hscale : 0 ≤ A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by positivity
      nlinarith [show (2304 : ℝ) * (25 / 99) * (1 / 999) ≤ 1 by norm_num]

/-- All ordered non-dominant pairs: two mixed orientations plus the stable-stable square. -/
def thetaCuspLikelihoodNonDominantPairEighthTail (A B : ℝ) : ℝ :=
  2 * thetaCuspLikelihoodDominantStablePairEighthTail A B +
    thetaCuspLikelihoodStableStablePairEighthTail A B

/-- Complete non-dominant pair sector costs at most `10411/11` dominant exponential units. -/
theorem thetaCuspLikelihoodNonDominantPairEighthTail_le
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodNonDominantPairEighthTail A B ≤
      (10411 / 11 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
  have hmixed := thetaCuspLikelihoodDominantStablePairEighthTail_le hA hBA
  have hstable := thetaCuspLikelihoodStableStablePairEighthTail_le hA hBA
  unfold thetaCuspLikelihoodNonDominantPairEighthTail
  nlinarith

/-- The dominant one-particle mass has an explicit exponential lower floor. -/
theorem seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (17496 / 5 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  have hretain :=
    one_thirtieth_mul_thetaCuspLikelihoodDominantAtomEighthMonomialMass_lt hAseam hBA
  have hmono :
      16 * (3 * A) ^ (8 : ℕ) * Real.exp (-(3 * A)) ≤
        thetaCuspLikelihoodAtomEighthMonomialMass 2 A B := by
    rw [thetaCuspLikelihoodAtomEighthMonomialMass_eq 2 (by norm_num) A hB]
    norm_num [thetaCuspLikelihoodGap, thetaCuspLikelihoodAtomWeight,
      thetaCuspLikelihoodRayWeight]
    have hexp : Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(B * 3)) =
        Real.exp (-(3 * A)) := by
      rw [← Real.exp_add, hBA]
      congr 1
      ring
    have hA0 : 0 ≤ A := le_trans Real.pi_pos.le hA
    have hr0 : 0 ≤ A / B := div_nonneg hA0 hB.le
    have hz0 : 0 ≤ 3 * A := by positivity
    have hray : 0 ≤ thetaCuspLikelihoodEighthMonomialRayTransform (A / B) (3 * A) := by
      unfold thetaCuspLikelihoodEighthMonomialRayTransform
      positivity
    have hpoint : 16 * (3 * A) ^ (8 : ℕ) * Real.exp (-(3 * A)) =
        Real.exp (-(9 / 2 : ℝ)) * 16 *
          ((A * 3) ^ (8 : ℕ) * Real.exp (-(B * 3))) := by
      linear_combination -(16 * (3 * A) ^ (8 : ℕ)) * hexp
    rw [hpoint]
    apply le_add_of_nonneg_right
    rw [show A * 3 = 3 * A by ring]
    positivity
  have hscaled :
      (1 / 30 : ℝ) * (16 * (3 * A) ^ (8 : ℕ) * Real.exp (-(3 * A))) ≤
        (1 / 30 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass 2 A B := by
    gcongr
  have hscore :
      (17496 / 5 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) <
        thetaCuspLikelihoodAtomEighthScoreMass 2 A B := by
    calc
      (17496 / 5 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) =
          (1 / 30 : ℝ) * (16 * (3 * A) ^ (8 : ℕ) * Real.exp (-(3 * A))) := by ring
      _ ≤ (1 / 30 : ℝ) * thetaCuspLikelihoodAtomEighthMonomialMass 2 A B := hscaled
      _ < thetaCuspLikelihoodAtomEighthScoreMass 2 A B := hretain
  rw [thetaCuspLikelihoodEighthDominantSingleMass_eq_atomScoreMass hAseam hBA]
  exact hscore

/-- The complete non-dominant pair sector fits strictly inside the one-third reserve. -/
theorem thetaCuspLikelihoodNonDominantPairEighthTail_lt_one_third_dominantSingleMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodNonDominantPairEighthTail A B <
      (1 / 3 : ℝ) * thetaCuspLikelihoodEighthDominantSingleMass A := by
  have htail := thetaCuspLikelihoodNonDominantPairEighthTail_le hA hBA
  have hsingle :=
    seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
      hA hBA
  have hscale : 0 < A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := Real.pi_pos.trans_le hA
    positivity
  nlinarith [show (10411 / 11 : ℝ) < (5832 / 5 : ℝ) by norm_num]

/-- Complete ordered two-particle score sector. -/
def thetaCuspLikelihoodEighthPairSectorMass (A B : ℝ) : ℝ :=
  thetaCuspLikelihoodAtomPairEighthScoreMass 2 2 A B +
    thetaCuspLikelihoodNonDominantPairEighthTail A B

/-- Full grade-two absorption: every ordered atom pair fits inside the dominant one-particle
score mass, with no discarded stable chamber. -/
theorem thetaCuspLikelihoodEighthPairSectorMass_lt_dominantSingleMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodEighthPairSectorMass A B <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hdominant :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hAseam
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hAseam hBA
  have htail :=
    thetaCuspLikelihoodNonDominantPairEighthTail_lt_one_third_dominantSingleMass hA hBA
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith

end

end RHTower
