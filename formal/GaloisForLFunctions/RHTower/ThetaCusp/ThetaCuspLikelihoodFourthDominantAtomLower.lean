import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodFourthSixthSpectralDomination

/-!
# Dominant-atom lower bound for the fourth theta likelihood jet

The square-gap-three Dirac component is a positive submeasure of the complete higher-likelihood
spectral measure.  Its exact fourth monomial, the sharp partition bound, and the `19/20` Bell
retention law produce an explicit global lower floor for the literal logarithmic fourth jet.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Dominant Dirac mass is an explicit lower bound for the complete leading fourth moment. -/
theorem dominantThetaLikelihoodAtomFourthMonomial_le_leadingMoment
    {A B : ℝ} (hB : 0 < B) (hBA : B = A - 3 / 2) :
    16 * (3 * A) ^ 4 * Real.exp (-(3 * A)) ≤
      A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 := by
  let f : ℝ → ℝ := fun t => (A * t) ^ 4 * Real.exp (-(B * t))
  let atom : Measure ℝ :=
    ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) • Measure.dirac (3 : ℝ)
  let component := thetaCuspAtomLikelihoodSpectralMeasure 2
  have hatomComponent : atom ≤ component := by
    dsimp only [atom, component, thetaCuspAtomLikelihoodSpectralMeasure]
    norm_num [thetaCuspLikelihoodGap]
    exact Measure.le_add_right (le_refl _)
  have hcomponentFull : component ≤ thetaCuspHigherLikelihoodSpectralMeasure := by
    dsimp only [component, thetaCuspHigherLikelihoodSpectralMeasure]
    exact Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) 0
  have hatomFull : atom ≤ thetaCuspHigherLikelihoodSpectralMeasure :=
    hatomComponent.trans hcomponentFull
  have hInt : Integrable f thetaCuspHigherLikelihoodSpectralMeasure := by
    have hi :=
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul
        (A ^ 4)
    convert hi using 1
    funext t
    dsimp [f]
    ring
  have hmono := integral_mono_measure hatomFull
    (Filter.Eventually.of_forall fun t => by dsimp only [f]; positivity) hInt
  have hatomEq : (∫ t : ℝ, f t ∂atom) =
      16 * (3 * A) ^ 4 * Real.exp (-(3 * A)) := by
    dsimp only [atom]
    rw [integral_smul_measure, integral_dirac]
    change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2)) * f 3 = _
    rw [ENNReal.toReal_ofReal (thetaCuspLikelihoodAtomWeight_pos (by norm_num)).le]
    dsimp only [f]
    norm_num [thetaCuspLikelihoodAtomWeight, thetaCuspLikelihoodGap]
    rw [hBA]
    rw [show Real.exp (-(9 / 2 : ℝ)) * 16 *
        ((A * 3) ^ 4 * Real.exp (-((A - 3 / 2) * 3))) =
      16 * (3 * A) ^ 4 *
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-((A - 3 / 2) * 3))) by ring]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hatomEq] at hmono
  calc
    _ ≤ ∫ t : ℝ, f t ∂thetaCuspHigherLikelihoodSpectralMeasure := hmono
    _ = A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 := by
      rw [show f = fun t => A ^ 4 * (t ^ 4 * Real.exp (-(B * t))) by
        funext t
        dsimp only [f]
        ring]
      rw [integral_const_mul, thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
      congr 2
      funext t
      ring

/-- Global explicit fourth-jet floor supplied by the dominant square-gap-three atom. -/
theorem sevenThousandEightHundred_mul_pow_four_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
    {x : ℝ} (hx : 0 ≤ x) :
    7800 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodSourceLogPartitionJetFour x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let M := thetaCuspHigherLikelihoodSpectralMoment B 4
  let m := thetaCuspLikelihoodNormalizedMoment B 4
  let S := A ^ 4 * Real.exp (-(3 * A))
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B, thetaCuspSingleAtomReflectionScale, thetaCuspLikelihoodCoordinate]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hm : 0 < m := by
    simpa only [m] using thetaCuspLikelihoodNormalizedMoment_four_pos hB
  have hM : 0 < M := by
    have hdiv : 0 < M / P := by
      simpa only [m, M, P, thetaCuspLikelihoodNormalizedMoment] using hm
    exact (div_pos_iff_of_pos_right hP).mp hdiv
  have hsmall : 399 * thetaCuspHigherLikelihoodSpectralResponse B < 1 := by
    simpa only [B] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hPeq : P = 1 + thetaCuspHigherLikelihoodSpectralResponse B := by
    dsimp only [P]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPinv : (399 / 400 : ℝ) < 1 / P := by
    apply (lt_div_iff₀ hP).2
    rw [hPeq]
    nlinarith
  have hraw := dominantThetaLikelihoodAtomFourthMonomial_le_leadingMoment hB hBA
  have hrawS : 1296 * S ≤ A ^ 4 * M := by
    calc
      1296 * S = 16 * (3 * A) ^ 4 * Real.exp (-(3 * A)) := by
        dsimp only [S]
        ring
      _ ≤ A ^ 4 * M := by simpa only [M] using hraw
  have hnormalized : (399 / 400 : ℝ) * (A ^ 4 * M) < A ^ 4 * m := by
    have hscale : 0 < A ^ 4 * M := mul_pos (pow_pos hA 4) hM
    have hmul := mul_lt_mul_of_pos_right hPinv hscale
    calc
      (399 / 400 : ℝ) * (A ^ 4 * M) < (1 / P) * (A ^ 4 * M) := hmul
      _ = A ^ 4 * (M / P) := by ring
      _ = A ^ 4 * m := by
        dsimp only [m, M, P, thetaCuspLikelihoodNormalizedMoment]
  have hord := two_fifths_le_thetaCuspLikelihoodSourceOrdinaryJetFour hx
  have hlog :=
    nineteenTwentieths_mul_ordinary_lt_thetaCuspLikelihoodSourceLogPartitionJetFour hx
  have hS : 0 < S := by dsimp only [S]; positivity
  have hord' : (32 / 5 : ℝ) * A ^ 4 * m ≤
      thetaCuspLikelihoodSourceOrdinaryJetFour x := by
    simpa only [A, B, m] using hord
  rw [show 7800 * thetaCuspSingleAtomReflectionScale 1 x ^ 4 *
      Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) = 7800 * S by
    dsimp only [S, A]
    ring]
  nlinarith

end

end RHTower
