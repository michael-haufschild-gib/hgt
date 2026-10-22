import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticCurvature
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControl18Source
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem reducedKineticControl_eighteen_endpoint (h v Z : ℝ) :
    reducedKineticControl h v Z 18 =
      19*reducedKineticValue h v Z - Z*deriv (reducedKineticValue h v) Z := by
  rw [(reducedKineticValue_hasDerivAt h v Z).deriv]
  unfold reducedKineticControl kineticControl reducedKineticValue reducedKineticSlopeValue
  norm_num [Finset.sum_range_succ,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
  ring

theorem reducedKineticControl_eighteen_pos_iff (h v Z : ℝ) :
    0 < reducedKineticControl h v Z 18 ↔
      Z*deriv (reducedKineticValue h v) Z < 19*reducedKineticValue h v Z := by
  rw [reducedKineticControl_eighteen_endpoint]
  exact sub_pos

end
end HTGeometry.ThetaRatioKineticContraction
