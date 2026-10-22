import GaloisForLFunctions.RHTower.CCM.CCMThetaGroundRHCriterion
import GaloisForLFunctions.RHTower.ThetaPositiveScalingRigidity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureGroundEnergy

/-!
# Three positive energies and an unconditional range of comparison

The exact RH comparison is pole jump energy <= prime plus Gamma jump energy.
Every energy is finite and nonnegative. Existing small-aperture coercivity
transports to a uniform strict gap for every complex smooth source in one
nonempty aperture range. The unresolved task is extension to all apertures.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction +
      thetaGammaScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) -
      thetaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference,
    thetaGammaPolarScalingEnergy_eq_polar_sub_gamma]
  ring

theorem riemannHypothesis_iff_thetaThreeEnergyComparison :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      thetaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) ≤
        thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
            (ccmThetaGroundProfile u).toBoundedContinuousFunction +
          thetaGammaScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  rw [riemannHypothesis_iff_thetaGroundEnergyComparison]
  simp only [thetaGammaPolarScalingEnergy_eq_polar_sub_gamma, sub_le_iff_le_add]

theorem thetaGroundNormSq_ccmProfile_eq_physical {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    thetaGroundNormSq (ccmThetaGroundProfile u) =
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
  change _ = ‖(ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2)‖ ^ 2
  rw [norm_sq_eq_integral, thetaGroundNormSq]
  apply integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
  rw [thetaGroundNormDensity_eq, ccmThetaGroundProfile_reconstruct, hx]

/-- A whole nonempty range has a uniform positive margin, for all complex smooth test sources. -/
theorem exists_small_aperture_thetaThreeEnergy_gap :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
      ∀ (a : SuzukiPositiveAperture), a.1 < delta → ∀ u : CCMComplexSmoothInteriorSource a,
        thetaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) +
            c * thetaGroundNormSq (ccmThetaGroundProfile u) ≤
          thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
              (ccmThetaGroundProfile u).toBoundedContinuousFunction +
            thetaGammaScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  obtain ⟨delta, hd, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  let a0 : SuzukiPositiveAperture := ⟨delta / 2, half_pos hd⟩
  have hc : 0 < ccmRestrictedWeilGroundEnergy a0 := hpos a0 (half_lt_self hd)
  refine ⟨a0.1, ccmRestrictedWeilGroundEnergy a0, a0.2, hc, fun a ha u => ?_⟩
  have hmono : ccmRestrictedWeilGroundEnergy a0 ≤ ccmRestrictedWeilGroundEnergy a :=
    antitone_ccmRestrictedWeilGroundEnergy ha.le
  have hbase := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u.toCCMFormVector
  have hl := (mul_le_mul_of_nonneg_right hmono
    (sq_nonneg ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖)).trans hbase
  rw [← thetaGroundNormSq_ccmProfile_eq_physical,
    ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies] at hl
  linarith

end RHTower
