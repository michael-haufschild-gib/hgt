import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthSpectralDecomposition
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthDominantAtomBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthStableTowerBound

open MeasureTheory Set

/-!
# Complete coefficient-faithful sixth-score bound

The first higher atom keeps its exact signed point-ray transform.  Every later atom is absorbed by
the stable Gaussian tower.  This gives a source-only uniform upper bound for the ordinary and
logarithmic sixth likelihood jets at the same aperture.
-/

namespace RHTower

noncomputable section

theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_eq_atomMass
    (A B : ℝ) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      thetaCuspLikelihoodAtomSixthScoreMass 2 A B := by
  rfl

theorem thetaCuspSingleAtomScale_likelihoodCoordinate (x : ℝ) :
    thetaCuspLikelihoodCoordinate x =
      thetaCuspSingleAtomReflectionScale 1 x - 3 / 2 := by
  unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
  norm_num
  rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring]

theorem thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      thetaCuspLikelihoodDominantAtomSixthScoreMass
          (thetaCuspSingleAtomReflectionScale 1 x)
          (thetaCuspLikelihoodCoordinate x) +
        ∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3)
          (thetaCuspSingleAtomReflectionScale 1 x)
          (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hstable := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hA hBA
  have hfull : Summable
      (fun k : ℕ => thetaCuspLikelihoodAtomSixthScoreMass (k + 2) A B) := by
    apply (summable_nat_add_iff 1).1
    simpa only [show ∀ k : ℕ, k + 1 + 2 = k + 3 by omega] using hstable
  have hdecomp := thetaCuspLikelihoodSixthScoreIntegral_eq_tsum_atom A hB
  change (∫ t : ℝ,
      thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B +
      ∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B
  calc
    _ = ∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 2) A B := by
      simpa only [thetaCuspLikelihoodAtomSixthScoreMass] using hdecomp
    _ = thetaCuspLikelihoodAtomSixthScoreMass 2 A B +
        ∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B := by
      rw [← hfull.sum_add_tsum_nat_add 1]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    _ = _ := by
      rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq_atomMass]

/-- Exact dominant atom plus a uniform stable-tower remainder. -/
theorem thetaCuspLikelihoodSixthScoreIntegral_le_completeEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) ≤
      (16 * 50000 + 18 * (25 / 41 : ℝ) * 1000000) *
          Real.exp (-(471 / 50 : ℝ)) +
        (10 / 999 : ℝ) * Real.pi ^ 6 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hdominant :=
    thetaCuspLikelihoodDominantAtomSixthScoreMass_le_seamEnvelope A hAseam hBA
  have hstable := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le hA hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  exact add_le_add hdominant hstable

/-- The normalized ordinary sixth source jet inherits the complete spectral envelope. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetSix_le_completeEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetSix x ≤
      64 * ((16 * 50000 + 18 * (25 / 41 : ℝ) * 1000000) *
          Real.exp (-(471 / 50 : ℝ)) +
        (10 / 999 : ℝ) * Real.pi ^ 6) := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let C := (16 * 50000 + 18 * (25 / 41 : ℝ) * 1000000) *
      Real.exp (-(471 / 50 : ℝ)) + (10 / 999 : ℝ) * Real.pi ^ 6
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hcoeff : 0 ≤ 64 / P := div_nonneg (by norm_num) hP.le
  have hcoeffUpper : 64 / P ≤ 64 := by
    apply (div_le_iff₀ hP).2
    nlinarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmass := thetaCuspLikelihoodSixthScoreIntegral_le_completeEnvelope hx
  rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
  change 64 / P * _ ≤ 64 * C
  calc
    64 / P * _ ≤ 64 / P * C := mul_le_mul_of_nonneg_left hmass hcoeff
    _ ≤ 64 * C := mul_le_mul_of_nonneg_right hcoeffUpper hC

/-- Uniform source-only bound for the literal logarithmic sixth likelihood jet. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_completeEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (26 / 25 : ℝ) * 64 *
        ((16 * 50000 + 18 * (25 / 41 : ℝ) * 1000000) *
            Real.exp (-(471 / 50 : ℝ)) +
          (10 / 999 : ℝ) * Real.pi ^ 6) := by
  have hordinary :=
    thetaCuspLikelihoodSourceOrdinaryJetSix_le_completeEnvelope hx
  have hscaled := mul_le_mul_of_nonneg_left hordinary
    (show 0 ≤ (26 / 25 : ℝ) by norm_num)
  exact lt_of_lt_of_le
    (thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twentySixTwentyFifths_ordinary hx)
    (by simpa only [mul_assoc] using hscaled)

end

end RHTower
