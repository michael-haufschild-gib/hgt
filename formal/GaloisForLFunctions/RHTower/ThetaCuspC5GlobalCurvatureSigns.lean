import GaloisForLFunctions.RHTower.ThetaCuspLogFourthNegative
import GaloisForLFunctions.RHTower.ThetaCuspC5CompletedGateSigns

/-!
# Global curvature signs and the completed C5 velocity floor

The strict negative fourth logarithmic derivative proves `c'' > 0`
everywhere for the completed curvature `c`. Its odd first derivative
therefore increases strictly from zero. The existing chord argument
now gives the C5 velocity floor without a source-scale cutoff.
The projective inequality and compensation bound remain separate.
-/

open Set

namespace RHTower

/-- Strict convexity of the completed logarithmic curvature, including the seam. -/
theorem thetaCuspLogCurvatureJetTwo_pos_all (x : ℝ) :
    0 < thetaCuspLogCurvatureJetTwo x := by
  unfold thetaCuspLogCurvatureJetTwo
  exact neg_pos.mpr (iteratedDeriv_four_thetaCuspLogSource_neg_all x)

theorem thetaCuspLogCurvatureJet_strictMono : StrictMono thetaCuspLogCurvatureJet := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_thetaCuspLogCurvatureJet x).deriv]
  exact thetaCuspLogCurvatureJetTwo_pos_all x

theorem thetaCuspLogCurvatureJet_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspLogCurvatureJet x := by
  have hz : thetaCuspLogCurvatureJet 0 = 0 := by
    unfold thetaCuspLogCurvatureJet
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1, rfl⟩), neg_zero]
  have h := thetaCuspLogCurvatureJet_strictMono hx
  rwa [hz] at h

/-- The completed C5 velocity floor holds throughout the same-half-line chamber. -/
theorem two_mul_action_le_velocity_of_sameHalfLine {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    2 * thetaCuspReflectedLogAction u t ≤ thetaCuspReflectedActionVelocity u t := by
  apply two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
  intro x _
  exact (thetaCuspLogCurvatureJetTwo_pos_all x).le

end RHTower
