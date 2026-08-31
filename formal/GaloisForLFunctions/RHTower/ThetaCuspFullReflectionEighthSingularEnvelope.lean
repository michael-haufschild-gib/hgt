import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenCurvatureGap
import GaloisForLFunctions.RHTower.ThetaCuspAtomLikelihoodCrossDomination
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLogJets
import GaloisForLFunctions.RHTower.ThetaCuspReflectedEighthSingularEnvelope

/-!
# Physical singular envelope for theta rank-three D1

The pure polynomial identity lives in the lightweight
`ThetaCuspReflectedEighthSingularEnvelope` module.  This module adds only the physical theta
specialization and its unconditional curvature nonvanishing input.

RH chain: singular-envelope elimination -> theta ninth-jet crossing orientation -> no first D1
zero -> global rank-three TCD gate -> all-order/cofinal Hankel landing -> Weil positivity -> RH.
-/

namespace RHTower

noncomputable section

/-- Complete theta reflected curvature is uniformly nonzero on the closed positive half-line. -/
theorem thetaCuspFullReflectedLogCurvature_pos_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectedLogCurvature x := by
  have hA0 := nineteen_le_thetaCuspBornWittenLogCurvature
    (n := 1) (by norm_num) hx
  have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  unfold thetaCuspFullReflectedLogCurvature
  nlinarith

/-- At every physical singular face, the eighth logarithmic jet is eliminated exactly by the
lower rank-two and rank-three invariants. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_zero_iff_singularEnvelope
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullReflectionEighthHankelCurvature x = 0 ↔
      let A := thetaCuspFullReflectedLogCurvature x
      let B := thetaCuspFullReflectedLogFourthJet x
      let C := thetaCuspFullReflectedLogSixthJet x
      let D := thetaCuspFullReflectedLogEighthJet x
      A ^ 2 * thetaCuspRankThreeLowerGap A B * D =
        thetaCuspRankThreeSingularEighthEnvelope A
          (thetaCuspRankThreeLowerGap A B)
          (thetaCuspRankThreeSixthMargin A B C) := by
  dsimp only
  unfold thetaCuspFullReflectionEighthHankelCurvature
  exact thetaCuspReflectedEighthPolynomial_eq_zero_iff_singularEnvelope
    (thetaCuspFullReflectedLogCurvature_pos_of_nonneg hx).ne'

end

end RHTower
