import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthCenterJetElimination
import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5JacobianSeamOrientation
import GaloisForLFunctions.RHTower.ThetaCuspC5RegimeOneCurvatureSigns
/-!
# Literal theta center sign for the growth logarithmic jet

Exact modular jets and the Bell transform prove
-L8(0)+(4+beta)L6(0)-4beta L4(0)>0 for the literal center beta.
This establishes the required center sign without an absorption premise.
Positive-half-line growth still requires global transport.
-/
namespace RHTower.ThetaCuspDefect
open HTGeometry
open scoped BigOperators ContDiff
noncomputable section

theorem centerSourcePositiveJet_seam (R : ℝ) (j : ℕ) (hj : j ≤ 4) :
    MvPolynomial.eval (modularThetaSourcePositiveSeamState (R^2))
      (modularThetaSourcePositiveNormalizedSourceJet (2*j)) =
        centerRawJet ((R:ℂ)^2) (2*j) := by
  rw [←modularThetaSourcePositiveChart_sourceJet,
    eval_modularThetaSourcePositiveChartPullback_seam,
    ←eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_normalizedSourceJet]
  let v := modularThetaODESeamState (R:ℂ)
  have hn (n : ℕ) : MvPolynomial.eval v (modularThetaODENormalizedSourceJet n)=
      MvPolynomial.eval v (modularThetaODESourceJet n) := by
    have he := congrArg (MvPolynomial.eval v) (modularThetaODESourceJet_eq_X_H_mul_normalized n)
    simpa [v,modularThetaODESeamState] using he.symm
  change MvPolynomial.eval v (modularThetaODENormalizedSourceJet (2*j))=_
  rw [hn,eval_modularThetaODESourceJet_eq_formalJet]
  have hm := centerMassJet_elimination (1:ℂ) (R:ℂ)
    (evalModularThetaODEFormalJet v .H) (evalModularThetaODEFormalJet v .Z)
    (evalModularThetaODEFormalJet v .R) (evalModularThetaODEFormalJet v .P)
    (by simp [v,modularThetaODESeamState]) (by simp [v,modularThetaODESeamState])
    (by simp [v,modularThetaODESeamState]) (by simp [v,modularThetaODESeamState])
    (evalModularThetaODEFormalJet_H_succ v) (evalModularThetaODEFormalJet_Z_succ v)
    (evalModularThetaODEFormalJet_R_succ v) (evalModularThetaODEFormalJet_P_succ v)
  rw [show 2*j+2=2*(j+1) by omega,hm (j+1) (by omega),hm j (by omega)]
  unfold centerRawJet
  rw [show 2*j+2=2*(j+1) by omega]
  ring

theorem ofReal_centerMassJet (X : ℝ) (j : ℕ) :
    ((centerMassJet X j:ℝ):ℂ)=centerMassJet (X:ℂ) j := by
  unfold centerMassJet
  split <;> push_cast <;> rfl

theorem ofReal_centerRawJet (X : ℝ) (j : ℕ) :
    ((centerRawJet X j:ℝ):ℂ)=centerRawJet (X:ℂ) j := by
  unfold centerRawJet
  push_cast
  rw [ofReal_centerMassJet,ofReal_centerMassJet]

theorem thetaSource_centerRawJet (j : ℕ) (hj : j ≤ 4) :
    iteratedDeriv (2*j) thetaCuspFullSource 0 =
      (thetaCuspModularODEState .H 0).re*centerRawJet (thetaCuspSelfDualModularScale^2) (2*j) := by
  have he : (fun x : ℝ => (thetaCuspFullSource x:ℂ))=
      (fun x => thetaCuspModularODEState .H x*thetaCuspModularSourcePositiveState .Q x) := by
    funext x
    exact ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ x
  have h := congrFun (iteratedDeriv_mass_mul_Q_eq_mass_mul_eval_sourcePositiveJet
    thetaCuspModularSourcePositiveState hasDerivAt_thetaCuspModularSourcePositiveState
    (thetaCuspModularODEState .H) hasDerivAt_thetaCuspModularMass_sourcePositive (2*j)) 0
  rw [←he,thetaCuspModularSourcePositiveState_zero_eq_seam,
    centerSourcePositiveJet_seam _ j hj] at h
  rw [SchwartzMap.iteratedDeriv_ofReal thetaCuspFullSource contDiff_thetaCuspFullSource] at h
  have hc : centerRawJet ((thetaCuspSelfDualModularScale:ℂ)^2) (2*j)=
      ((centerRawJet (thetaCuspSelfDualModularScale^2) (2*j):ℝ):ℂ) := by
    rw [ofReal_centerRawJet,Complex.ofReal_pow]
  rw [hc] at h
  simpa only [Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero] using
    congrArg Complex.re h


def centerGrowthRawValue {K : Type*} [Field K] (β : K) (f : ℕ → K) : K :=
  (-f 0^3*f 8+28*f 0^2*f 2*f 6+35*f 0^2*f 4^2-420*f 0*f 2^2*f 4+630*f 2^4)-
    (4+β)*(-f 0^2*f 6+15*f 0*f 2*f 4-30*f 2^3)*f 0+
    4*β*(3*f 2^2-f 0*f 4)*f 0^2

theorem centerGrowthRawValue_theta_eq_modular (β : ℝ) :
    centerGrowthRawValue β (fun n => iteratedDeriv n thetaCuspFullSource 0)=
      (thetaCuspModularODEState .H 0).re^4*
        (centerEighthNumerator (thetaCuspSelfDualModularScale^2)-
          (4+β)*centerSixthNumerator (thetaCuspSelfDualModularScale^2)*
            centerRawJet (thetaCuspSelfDualModularScale^2) 0+
          4*β*centerFourthNumerator (thetaCuspSelfDualModularScale^2)*
            centerRawJet (thetaCuspSelfDualModularScale^2) 0^2) := by
  have h0 := thetaSource_centerRawJet 0 (by omega)
  have h2 := thetaSource_centerRawJet 1 (by omega)
  have h4 := thetaSource_centerRawJet 2 (by omega)
  have h6 := thetaSource_centerRawJet 3 (by omega)
  have h8 := thetaSource_centerRawJet 4 (by omega)
  norm_num only [Nat.reduceMul] at h0 h2 h4 h6 h8
  unfold centerGrowthRawValue
  dsimp only
  rw [h0,h2,h4,h6,h8]
  unfold centerEighthNumerator centerSixthNumerator centerFourthNumerator
  ring

theorem centerGrowthRawValue_theta_eq_log (β : ℝ) :
    centerGrowthRawValue β (fun n => iteratedDeriv n thetaCuspFullSource 0)=
      thetaCuspFullSource 0^4*
        (-iteratedDeriv 8 thetaCuspLogSource 0+
          (4+β)*iteratedDeriv 6 thetaCuspLogSource 0-4*β*iteratedDeriv 4 thetaCuspLogSource 0) := by
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 by norm_num)
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 by norm_num)
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 by norm_num)
  have h7 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 7 by norm_num)
  have hexp : Real.exp (thetaCuspLogSource 0)=thetaCuspFullSource 0 := by
    rw [thetaCuspLogSource,Real.exp_log (thetaCuspFullSource_pos_all 0)]
  unfold centerGrowthRawValue
  dsimp only
  rw [iteratedDeriv_zero,iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_eight_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetSix thetaCuspLogExponentialJetEight thetaCuspLogExponentialJetZero
  rw [hexp,h1,h3,h5,h7]
  ring

theorem sourceCenter_growthLogValue_pos :
    0 < -iteratedDeriv 8 thetaCuspLogSource 0+
      (4+factorCurvature (thetaCuspLikelihoodCoordinate 0))*iteratedDeriv 6 thetaCuspLogSource 0-
      4*factorCurvature (thetaCuspLikelihoodCoordinate 0)*iteratedDeriv 4 thetaCuspLogSource 0 := by
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate 0 := by
    rw [thetaCuspLikelihoodCoordinate_zero_eq]
    linarith [Real.pi_gt_three]
  have hqu : thetaCuspLikelihoodCoordinate 0 ≤ (5/3:ℝ) := by
    rw [thetaCuspLikelihoodCoordinate_zero_eq]
    linarith [Real.pi_lt_d2]
  have hpoly := centerGrowth_modular_pos
    (le_of_lt thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one)
    (factorCurvature_ge_twoHundred hq hqu)
  have hmass := thetaCuspModularODEState_H_re_pos 0
  have hpos := mul_pos (pow_pos hmass 4) hpoly
  rw [←centerGrowthRawValue_theta_eq_modular,centerGrowthRawValue_theta_eq_log] at hpos
  exact pos_of_mul_pos_right hpos (pow_nonneg (thetaCuspFullSource_pos_all 0).le 4)

end
end RHTower.ThetaCuspDefect
