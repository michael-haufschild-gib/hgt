import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityTomography
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Reflected bi-heat multiplicity-leading jet balance

At any actual Xi divisor, both completed bi-heat channels first survive at exact Xi multiplicity.
Their top jets share same nonzero completed coefficient.  Evaluating at single fixed aperture `2`
makes their norms

`|Aρ| 2^leftOrder(ρ)` and `|Aρ| 2^rightOrder(ρ)`.

Thus equality cancels unknown multiplicity-leading coefficient and is equivalent pointwise to
`Re ρ = 1/2`.  Requiring equality at every Xi divisor is exactly RH.  This closes coefficient and
multiplicity gates for RBH receiver; remaining producer is source-first reason for balance.

`[NEW] [CLASSIFICATION] [EXACT RECEIVER] [COEFFICIENT-FREE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Common nonzero coefficient of two multiplicity-leading completed channels. -/
def reflectedBiHeatMultiplicityLeadingCoefficient (rho : XiDivisorSupport) : ℂ :=
  1 / 2 * iteratedDeriv (xiSupportMultiplicity rho) reflectedCompletedLambda (rho : ℂ)

/-- Common multiplicity-leading coefficient never vanishes on actual Xi divisor support. -/
theorem reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero (rho : XiDivisorSupport) :
    reflectedBiHeatMultiplicityLeadingCoefficient rho ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (iteratedDeriv_reflectedCompletedLambda_ne_zero_at_supportMultiplicity rho)

/-- Exact norm of left multiplicity-leading jet at fixed aperture `2`. -/
theorem norm_reflectedBiHeatLeftResponse_leadingJet_two (rho : XiDivisorSupport) :
    ‖iteratedDeriv (xiSupportMultiplicity rho)
        (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖ =
      ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
        (2 : ℝ) ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) := by
  rw [iteratedDeriv_reflectedBiHeatLeftResponse_at_supportMultiplicity (by norm_num)]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  simp [reflectedBiHeatLeftScaleOrder]

/-- Exact norm of right multiplicity-leading jet at fixed aperture `2`. -/
theorem norm_reflectedBiHeatRightResponse_leadingJet_two (rho : XiDivisorSupport) :
    ‖iteratedDeriv (xiSupportMultiplicity rho)
        (reflectedBiHeatRightResponse 2) (rho : ℂ)‖ =
      ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
        (2 : ℝ) ^ reflectedBiHeatRightScaleOrder (rho : ℂ) := by
  rw [iteratedDeriv_reflectedBiHeatRightResponse_at_supportMultiplicity (by norm_num)]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  simp [reflectedBiHeatRightScaleOrder]

/--
Pointwise coefficient-free classification: actual leading-jet norms balance at aperture `2`
exactly on self-dual wall.
-/
theorem reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff (rho : XiDivisorSupport) :
    ‖iteratedDeriv (xiSupportMultiplicity rho)
        (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖ =
      ‖iteratedDeriv (xiSupportMultiplicity rho)
        (reflectedBiHeatRightResponse 2) (rho : ℂ)‖ ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [norm_reflectedBiHeatLeftResponse_leadingJet_two,
    norm_reflectedBiHeatRightResponse_leadingJet_two]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  constructor
  · intro h
    have hpowers : (2 : ℝ) ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) =
        (2 : ℝ) ^ reflectedBiHeatRightScaleOrder (rho : ℂ) := by
      exact mul_left_cancel₀ hcoef.ne' h
    have horders : reflectedBiHeatLeftScaleOrder (rho : ℂ) =
        reflectedBiHeatRightScaleOrder (rho : ℂ) :=
      (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective hpowers
    exact (reflectedBiHeat_scaleOrders_eq_iff (rho : ℂ)).mp horders
  · intro hre
    have horders := (reflectedBiHeat_scaleOrders_eq_iff (rho : ℂ)).mpr hre
    rw [horders]

/-- Global fixed-aperture multiplicity-leading balance is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNorms_two_eq :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        ‖iteratedDeriv (xiSupportMultiplicity rho)
            (reflectedBiHeatLeftResponse 2) (rho : ℂ)‖ =
          ‖iteratedDeriv (xiSupportMultiplicity rho)
            (reflectedBiHeatRightResponse 2) (rho : ℂ)‖ := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff rho).mp (h rho)

end

end RHTower
