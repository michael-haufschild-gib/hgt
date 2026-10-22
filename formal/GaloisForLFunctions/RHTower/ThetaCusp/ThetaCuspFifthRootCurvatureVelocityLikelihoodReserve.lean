import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureStationaryLocus
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodLiftReduction

/-!
# Theta C5 center velocity: likelihood reserve

The literal modular-center fifth-root-curvature velocity is a positive source-product square
times one action three-jet polynomial.  In first-atom plus theta-likelihood coordinates, its third
likelihood jet is strictly favorable.  The theta spectral support gap pays more than six units of
the only lower likelihood curvature, so the entire third-cumulant burden is removed from the
remaining center-velocity sign problem.
-/

open Real

namespace RHTower

noncomputable section

/-- Universal action three-jet core of the literal C5 numerator velocity. -/
def thetaCuspReflectedActionFifthRootVelocityCore
    (r t q₁ q₂ q₃ : ℝ) : ℝ :=
  r * (39 * q₁ + t * (q₂ - q₁ ^ (2 : ℕ)) +
      5 * t ^ (2 : ℕ) * (q₃ - 3 * q₁ * q₂ + q₁ ^ (3 : ℕ))) -
    17 * t * q₁ ^ (2 : ℕ) - 3 * t ^ (2 : ℕ) * q₁ * (q₂ - q₁ ^ (2 : ℕ))

/-- Exact positive-factor normalization of literal source velocity. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureVelocity_eq_product_sq_mul_actionCore
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureVelocity u t =
      thetaCuspReflectedSourceProduct u t ^ (2 : ℕ) *
        thetaCuspReflectedActionFifthRootVelocityCore
          (Real.exp (thetaCuspReflectedLogAction u t) - 1) t
          (thetaCuspReflectedLogJetOne u t)
          (thetaCuspReflectedLogJetTwo u t)
          (thetaCuspReflectedLogJetThree u t) := by
  unfold thetaCuspReflectedSourceFifthRootCurvatureVelocity
  rw [thetaCuspReflectedSourceFirstDrop_eq_product_mul_exp_action_sub_one]
  unfold thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceDecayFluxThirdJet
    thetaCuspReflectedActionFifthRootVelocityCore
  ring

/-- Literal velocity positivity is exactly positivity of the action core. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureVelocity_pos_iff_actionCore
    (u t : ℝ) :
    0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity u t ↔
      0 < thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp (thetaCuspReflectedLogAction u t) - 1) t
        (thetaCuspReflectedLogJetOne u t)
        (thetaCuspReflectedLogJetTwo u t)
        (thetaCuspReflectedLogJetThree u t) := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureVelocity_eq_product_sq_mul_actionCore]
  have hP : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos hP)

/-- Center first action jet in exact first-atom plus likelihood coordinates. -/
theorem thetaCuspReflectedLogJetOne_zero_eq_likelihood
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetOne 0 t =
      -2 * (thetaCuspFirstAtomLogJetOne t +
        thetaCuspLikelihoodSourceLogPartitionJetOne t) := by
  rw [show thetaCuspReflectedLogJetOne 0 t =
      -2 * iteratedDeriv 1 thetaCuspLogSource t by
    unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
    rw [zero_add, zero_sub, iteratedDeriv_thetaCuspLogSource_neg]
    norm_num
    ring]
  rw [iteratedDeriv_one_thetaCuspLogSource_eq_full_jets ht,
    ← thetaCuspLikelihoodSourceLogPartitionJetOne_eq_higherLikelihoodLogJetOne ht]

/-- Center second action jet in exact first-atom plus likelihood coordinates. -/
theorem thetaCuspReflectedLogJetTwo_zero_eq_likelihood
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetTwo 0 t =
      2 * (thetaCuspBornWittenLogCurvature 1 t -
        thetaCuspLikelihoodSourceLogPartitionJetTwo t) := by
  rw [show thetaCuspReflectedLogJetTwo 0 t =
      -2 * iteratedDeriv 2 thetaCuspLogSource t by
    unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
    rw [zero_add, zero_sub, iteratedDeriv_thetaCuspLogSource_neg]
    norm_num
    ring]
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor ht,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo ht]
  ring

/-- Center third action jet in exact first-atom plus likelihood coordinates. -/
theorem thetaCuspReflectedLogJetThree_zero_eq_likelihood
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedLogJetThree 0 t =
      -2 * (thetaCuspFirstAtomLogJetThree t +
        thetaCuspLikelihoodSourceLogPartitionJetThree t) := by
  rw [show thetaCuspReflectedLogJetThree 0 t =
      -2 * iteratedDeriv 3 thetaCuspLogSource t by
    unfold thetaCuspReflectedLogJetThree thetaCuspLogCurvatureJet
    rw [zero_add, zero_sub, iteratedDeriv_thetaCuspLogSource_neg]
    norm_num
    ring]
  rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets ht,
    ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree ht]

/-- Modular-center velocity core with favorable third likelihood jet removed. -/
def thetaCuspCenterFifthRootVelocityLowerJetCore (t : ℝ) : ℝ :=
  thetaCuspReflectedActionFifthRootVelocityCore
    (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) t
    (thetaCuspReflectedLogJetOne 0 t)
    (thetaCuspReflectedLogJetTwo 0 t)
    (-2 * thetaCuspFirstAtomLogJetThree t)

/-- Universal six-curvature reserve carried by third likelihood jet. -/
def thetaCuspCenterFifthRootVelocityMasterReservedCore (t : ℝ) : ℝ :=
  thetaCuspCenterFifthRootVelocityLowerJetCore t +
    60 * (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) * t ^ (2 : ℕ) *
      thetaCuspLikelihoodSourceLogPartitionJetTwo t

/-- Exact third-likelihood-channel decomposition of modular-center velocity core. -/
theorem thetaCuspReflectedActionFifthRootVelocityCore_zero_eq_lowerJet_sub_thirdLikelihood
    {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) t
        (thetaCuspReflectedLogJetOne 0 t)
        (thetaCuspReflectedLogJetTwo 0 t)
        (thetaCuspReflectedLogJetThree 0 t) =
      thetaCuspCenterFifthRootVelocityLowerJetCore t -
        10 * (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) * t ^ (2 : ℕ) *
          thetaCuspLikelihoodSourceLogPartitionJetThree t := by
  rw [thetaCuspReflectedLogJetThree_zero_eq_likelihood ht]
  unfold thetaCuspCenterFifthRootVelocityLowerJetCore
    thetaCuspReflectedActionFifthRootVelocityCore
  ring

/-- Theta support gap pays more than six likelihood-curvature units inside literal center
velocity.  Thus entire third-cumulant burden is discharged unconditionally. -/
theorem thetaCuspCenterFifthRootVelocityMasterReservedCore_lt_actionCore
    {t : ℝ} (ht : 0 < t) :
    thetaCuspCenterFifthRootVelocityMasterReservedCore t <
      thetaCuspReflectedActionFifthRootVelocityCore
        (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) t
        (thetaCuspReflectedLogJetOne 0 t)
        (thetaCuspReflectedLogJetTwo 0 t)
        (thetaCuspReflectedLogJetThree 0 t) := by
  have hr : 0 < Real.exp (thetaCuspReflectedLogAction 0 t) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos ht)
  have hgap := six_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree ht.le
  have hfactor : 0 < 10 * (Real.exp (thetaCuspReflectedLogAction 0 t) - 1) * t ^ (2 : ℕ) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_left hgap hfactor
  rw [thetaCuspReflectedActionFifthRootVelocityCore_zero_eq_lowerJet_sub_thirdLikelihood ht]
  unfold thetaCuspCenterFifthRootVelocityMasterReservedCore
  nlinarith

/-- Nonnegativity of lower-jet master-reserved core forces strict literal center velocity. -/
theorem thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_of_masterReservedCore_nonneg
    {t : ℝ} (ht : 0 < t)
    (hcore : 0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore t) :
    0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t := by
  rw [thetaCuspReflectedSourceFifthRootCurvatureVelocity_pos_iff_actionCore]
  exact lt_of_le_of_lt hcore
    (thetaCuspCenterFifthRootVelocityMasterReservedCore_lt_actionCore ht)

end

end RHTower
