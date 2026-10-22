import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthCenterModularJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularEnergyBounds
/-! Exact modular source jets prove positivity of the eighth-order density-shape
seam numerator. This is a necessary local test for decreasing normalized
descent density; no finite-displacement monotonicity or C5 gate is asserted. -/

namespace RHTower.ThetaCuspDefect
noncomputable section
theorem centerDensityShape_shift_pos (y : ℝ) (hy : 0 ≤ y) (hyu : y ≤ 1/10) :
    0 < centerRawJet (191/10+y) 2^2*centerEighthNumerator (191/10+y)+
      15*centerRawJet (191/10+y) 2*centerFourthNumerator (191/10+y)*centerSixthNumerator (191/10+y)+
      24*centerFourthNumerator (191/10+y)^3 := by
  have hp : ∀ n : ℕ, y^(n+1) ≤ (1/10:ℝ) := by
    intro n
    induction n with
    | zero => simpa only [Nat.zero_add,pow_one] using hyu
    | succ n ih =>
      rw [pow_succ]
      have hm := mul_le_mul_of_nonneg_right ih hy
      nlinarith only [hm,hyu]
  unfold centerEighthNumerator centerSixthNumerator centerFourthNumerator centerRawJet
  simp only [centerMassJet,Nat.reduceAdd]
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.rat_rawCast_neg,Mathlib.Tactic.RingNF.int_rawCast_neg,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  linarith only [hp 0,hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,hp 8,hp 9,hp 10,hp 11]


def descentShapeRawValue (f : ℕ → ℝ) : ℝ :=
  let B := 3*f 2^2-f 0*f 4
  let C := -f 0^2*f 6+15*f 0*f 2*f 4-30*f 2^3
  let D := -f 0^3*f 8+28*f 0^2*f 2*f 6+35*f 0^2*f 4^2-
    420*f 0*f 2^2*f 4+630*f 2^4
  f 2^2*D+15*f 2*B*C+24*B^3

theorem descentShapeRawValue_theta_eq_modular :
    descentShapeRawValue (fun n => iteratedDeriv n thetaCuspFullSource 0)=
      (thetaCuspModularODEState .H 0).re^6*
        (centerRawJet (thetaCuspSelfDualModularScale^2) 2^2*centerEighthNumerator (thetaCuspSelfDualModularScale^2)+
          15*centerRawJet (thetaCuspSelfDualModularScale^2) 2*centerFourthNumerator (thetaCuspSelfDualModularScale^2)*
            centerSixthNumerator (thetaCuspSelfDualModularScale^2)+
          24*centerFourthNumerator (thetaCuspSelfDualModularScale^2)^3) := by
  have h0 := thetaSource_centerRawJet 0 (by omega)
  have h2 := thetaSource_centerRawJet 1 (by omega)
  have h4 := thetaSource_centerRawJet 2 (by omega)
  have h6 := thetaSource_centerRawJet 3 (by omega)
  have h8 := thetaSource_centerRawJet 4 (by omega)
  norm_num only [Nat.reduceMul] at h0 h2 h4 h6 h8
  unfold descentShapeRawValue
  dsimp only
  rw [h0,h2,h4,h6,h8]
  unfold centerEighthNumerator centerSixthNumerator centerFourthNumerator
  ring

theorem descentShapeRawValue_theta_eq_log :
    descentShapeRawValue (fun n => iteratedDeriv n thetaCuspFullSource 0)=
      thetaCuspFullSource 0^6*
        ((-iteratedDeriv 2 thetaCuspLogSource 0)^2*(-iteratedDeriv 8 thetaCuspLogSource 0)-
          15*(-iteratedDeriv 2 thetaCuspLogSource 0)*(-iteratedDeriv 4 thetaCuspLogSource 0)*
            (-iteratedDeriv 6 thetaCuspLogSource 0)+24*(-iteratedDeriv 4 thetaCuspLogSource 0)^3) := by
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 by norm_num)
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 by norm_num)
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 by norm_num)
  have h7 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 7 by norm_num)
  have hexp : Real.exp (thetaCuspLogSource 0)=thetaCuspFullSource 0 := by
    rw [thetaCuspLogSource,Real.exp_log (thetaCuspFullSource_pos_all 0)]
  unfold descentShapeRawValue
  dsimp only
  rw [iteratedDeriv_zero,iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_eight_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour
    thetaCuspLogExponentialJetSix thetaCuspLogExponentialJetEight thetaCuspLogExponentialJetZero
  rw [hexp,h1,h3,h5,h7]
  ring

theorem sourceCenter_densityShape_pos :
    0 < (-iteratedDeriv 2 thetaCuspLogSource 0)^2*(-iteratedDeriv 8 thetaCuspLogSource 0)-
      15*(-iteratedDeriv 2 thetaCuspLogSource 0)*(-iteratedDeriv 4 thetaCuspLogSource 0)*
        (-iteratedDeriv 6 thetaCuspLogSource 0)+24*(-iteratedDeriv 4 thetaCuspLogSource 0)^3 := by
  have hp := centerDensityShape_shift_pos (thetaCuspSelfDualModularScale^2-191/10)
    (by linarith [thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one])
    (by linarith [thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths])
  rw [show (191/10:ℝ)+(thetaCuspSelfDualModularScale^2-191/10)=thetaCuspSelfDualModularScale^2 by ring] at hp
  have hm := mul_pos (pow_pos (thetaCuspModularODEState_H_re_pos 0) 6) hp
  rw [←descentShapeRawValue_theta_eq_modular,descentShapeRawValue_theta_eq_log] at hm
  exact pos_of_mul_pos_right hm (pow_nonneg (thetaCuspFullSource_pos_all 0).le 6)


end
end RHTower.ThetaCuspDefect
