import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectPrimitiveTransport
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthCenterModularJets
/-! Source orientation for the proposed denominator-clock C5 germ.
The full theta source satisfies a strict curvature-jet invariant. The
algebraic candidate for the first comparison-compensation coefficient is
exactly this invariant divided by a positive factor. Identifying that
candidate with the analytic germ and proving the global comparison sign
remain separate obligations; neither is asserted here. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "B" => thetaCuspLogCurvatureJetTwo
local notation "q" => thetaCuspLikelihoodCoordinate

private theorem center_projective_raw_reserve {X : ℝ} (hX : 191/10 ≤ X) :
    0 < centerRawJet X 0*centerRawJet X 4-3*(centerRawJet X 2)^2-
      9*centerRawJet X 0*centerRawJet X 2 := by
  have hy : 0 ≤ X-191/10 := sub_nonneg.mpr hX
  rw [show X=(191/10:ℝ)+(X-191/10) by ring]
  generalize X-191/10=y at *
  unfold centerRawJet
  simp only [centerMassJet,Nat.reduceAdd]
  ring_nf
  positivity

private theorem center_projective_upper : B 0 < 9*c 0 := by
  have hX := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hp := center_projective_raw_reserve hX.le
  have hH := thetaCuspModularODEState_H_re_pos 0
  have hraw := mul_pos (sq_pos_of_pos hH) hp
  have h0 := thetaSource_centerRawJet 0 (by omega)
  have h2 := thetaSource_centerRawJet 1 (by omega)
  have h4 := thetaSource_centerRawJet 2 (by omega)
  norm_num only [Nat.reduceMul,iteratedDeriv_zero] at h0 h2 h4
  have hf : 0 < thetaCuspFullSource 0*iteratedDeriv 4 thetaCuspFullSource 0-
      3*(iteratedDeriv 2 thetaCuspFullSource 0)^2-
      9*thetaCuspFullSource 0*iteratedDeriv 2 thetaCuspFullSource 0 := by
    rw [h0,h2,h4]
    nlinarith only [hraw]
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 from ⟨0,rfl⟩)
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩)
  rw [iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
    iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet] at hf
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour thetaCuspLogExponentialJetZero at hf
  rw [h1,h3,thetaCuspLogSource,Real.exp_log (thetaCuspFullSource_pos_all 0)] at hf
  have hs : 0 < (thetaCuspFullSource 0)^2*(9*c 0-B 0) := by
    unfold thetaCuspLogCurvature thetaCuspLogCurvatureJetTwo
    nlinarith only [hf]
  exact sub_pos.mp (pos_of_mul_pos_right hs (sq_nonneg _))

/-- The full source curvature has a global projective second-jet ceiling. -/
theorem source_projective_upper {x : ℝ} (hx : 0 ≤ x) : B x < 9*c x := by
  have hc0 := thetaCuspLogCurvature_pos 0
  have hcx := thetaCuspLogCurvature_pos x
  have hratio := projectiveRatio_strictAntiOn.antitoneOn (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hx hx
  have h0 : thetaCuspCompletedCurvatureProjectiveRatio 0 < 9 :=
    (div_lt_iff₀ hc0).mpr center_projective_upper
  exact (div_lt_iff₀ hcx).mp (hratio.trans_lt h0)

private theorem source_factor_product_upper {x : ℝ} (hx : 0 ≤ x) :
    -factorLogSlope (q x)*(4+12/q x) < 162 := by
  have hqa := sourceCoordinate_actual_lower hx
  have hpi := Real.pi_gt_d2
  have hq : (8/5:ℝ) ≤ q x := by linarith
  have hq0 : 0 < q x := by linarith
  have hq3 : 0 < q x+3 := by linarith
  have heq : -factorLogSlope (q x)*(4+12/q x)=16+120/q x+180/(q x)^2 := by
    unfold factorLogSlope
    field_simp [hq0.ne',hq3.ne']
    ring
  rw [heq]
  have hp : 0 < (162-(16+120/q x+180/(q x)^2))*(q x)^2 := by
    have hy : 0 ≤ q x-8/5 := sub_nonneg.mpr hq
    have he : (162-(16+120/q x+180/(q x)^2))*(q x)^2=
        146*(q x-8/5)^2+(1736/5)*(q x-8/5)+44/25 := by
      field_simp [hq0.ne']
      ring
    rw [he]
    positivity
  have h := (mul_pos_iff_of_pos_right (sq_pos_of_pos hq0)).mp hp
  linarith

/-- Fourth-curvature control retaining the coupled curvature defect. -/
theorem source_fourth_curvature_affine_upper {x : ℝ} (hx : 0 ≤ x) :
    -iteratedDeriv 6 thetaCuspLogSource x < 166*B x-648*c x := by
  have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hZ := defectSturmFlux_pos hx
  unfold defectSturmFlux at hZ
  have hs := (mul_pos_iff_of_pos_left hF).mp hZ
  have hH := curvatureDefect_slope_comparison hx
  have hf := factorLogSlope_neg (thetaCuspLikelihoodCoordinate_pos hx)
  have hb := curvatureDefect_pos hx
  have h1 := mul_lt_mul_of_neg_left hH hf
  have h2 := mul_lt_mul_of_pos_right (source_factor_product_upper hx) hb
  dsimp only [sourceDefectJetSlope,sourceDefectJet,curvatureDefect,thetaCuspLogCurvatureJetTwo] at hs hH h1 h2 ⊢
  nlinarith only [hs,h1,h2]

/-- One-sided fourth-curvature control for the finite quadrature remainder. -/
theorem source_fourth_curvature_upper {x : ℝ} (hx : 0 ≤ x) :
    -iteratedDeriv 6 thetaCuspLogSource x < 846*c x := by
  have h := source_fourth_curvature_affine_upper hx
  have hB := source_projective_upper hx
  linarith

/-- The full source has the orientation required by the clock-model fourth coefficient. -/
def clockModelSourceOrientation (x : ℝ) : ℝ :=
  1311*(c x)^4-1017*(c x)^2*B x-
    122*c x*(-iteratedDeriv 6 thetaCuspLogSource x)+176*(B x)^2

theorem clockModelSourceOrientation_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < clockModelSourceOrientation x := by
  have hc := sourceCurvature_gt_eighteen hx
  have hc0 := thetaCuspLogCurvature_pos x
  have hB := mul_lt_mul_of_pos_left (source_projective_upper hx)
    (show 0 < 1017*(c x)^2 by positivity)
  have hC := mul_lt_mul_of_pos_left (source_fourth_curvature_upper hx)
    (show 0 < 122*c x by positivity)
  have hp : 0 < 1311*(c x)^2-9153*c x-103212 := by
    have hz : 0 ≤ c x-18 := by linarith
    have he : 1311*(c x)^2-9153*c x-103212=
        1311*(c x-18)^2+38043*(c x-18)+156798 := by ring
    rw [he]
    positivity
  have hprod := mul_pos (sq_pos_of_pos hc0) hp
  unfold clockModelSourceOrientation
  nlinarith only [hB,hC,hprod,sq_nonneg (B x)]

/-- Algebraic fourth coefficient proposed by the clock-model germ calculation.
Its identification with an analytic germ coefficient is a separate obligation. -/
def clockModelCandidateFourthCoefficient (x : ℝ) : ℝ :=
  let C := -iteratedDeriv 6 thetaCuspLogSource x
  let A := 6*c x/5+2*B x/(15*c x)
  let D := 81*(c x)^2/140+59*B x/140+C/(42*c x)-31*(B x)^2/(1260*(c x)^2)
  (4/3)*(c x)^2+2*B x+4*C/(45*c x)-(B x)^2/(9*(c x)^2)-20*D+10*A^2

theorem clockModelCandidateFourthCoefficient_eq (x : ℝ) :
    clockModelCandidateFourthCoefficient x=clockModelSourceOrientation x/(315*(c x)^2) := by
  have hc := (thetaCuspLogCurvature_pos x).ne'
  unfold clockModelCandidateFourthCoefficient clockModelSourceOrientation
  field_simp [hc]
  ring

theorem clockModelCandidateFourthCoefficient_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < clockModelCandidateFourthCoefficient x := by
  rw [clockModelCandidateFourthCoefficient_eq]
  exact div_pos (clockModelSourceOrientation_pos hx)
    (mul_pos (by norm_num) (sq_pos_of_pos (thetaCuspLogCurvature_pos x)))

end
end RHTower.ThetaCuspDefect
