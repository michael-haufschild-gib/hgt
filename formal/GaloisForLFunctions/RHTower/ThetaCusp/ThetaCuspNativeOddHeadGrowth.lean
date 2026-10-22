import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5ClockSourceOrientation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurCompensation

/-!
The complete normalized odd head grows strictly on the nonnegative source ray.
A positive decomposition of its derivative uses the actual curvature defect
and seventh-order source comparison. Its product with the source log-slope
has strictly negative derivative, fixing the center orientation of the full
source quadratic. The upper-center determinant sign remains open.
-/

namespace RHTower.ThetaCuspHeadGrowth
open ThetaCuspDefect
noncomputable section

private theorem factorLogSlope_lt_neg_four {q : ℝ} (hq : 0 < q) :
    factorLogSlope q < -4 := by
  have hq3 : 0 < q+3 := by linarith
  have he : factorLogSlope q = -4-15/q-3/(q+3) := by
    unfold factorLogSlope
    field_simp [hq.ne',hq3.ne']
    ring
  rw [he]
  have h1 : 0 < 15/q := by positivity
  have h2 : 0 < 3/(q+3) := by positivity
  linarith

private theorem factorCurvature_lt {x : ℝ} (hx : 0 ≤ x) :
    factorCurvature (thetaCuspLikelihoodCoordinate x) < 18*thetaCuspLogCurvature x := by
  have hr := sourceSeamReserve_pos hx
  have hf := factorLogSlope_lt_neg_four (thetaCuspLikelihoodCoordinate_pos hx)
  linarith

def core (x : ℝ) : ℝ :=
  thetaCuspLogCurvature x*(-iteratedDeriv 6 thetaCuspLogSource x)-
    thetaCuspLogCurvatureJetTwo x^2-
    18*thetaCuspLogCurvature x^2*thetaCuspLogCurvatureJetTwo x+
    24*thetaCuspLogCurvature x^4

def coreSlope (x : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet x*(-iteratedDeriv 6 thetaCuspLogSource x)+
    thetaCuspLogCurvature x*(-iteratedDeriv 7 thetaCuspLogSource x)-
    2*thetaCuspLogCurvatureJetTwo x*thetaCuspLogCurvatureJetThree x-
    36*thetaCuspLogCurvature x*thetaCuspLogCurvatureJet x*thetaCuspLogCurvatureJetTwo x-
    18*thetaCuspLogCurvature x^2*thetaCuspLogCurvatureJetThree x+
    96*thetaCuspLogCurvature x^3*thetaCuspLogCurvatureJet x

theorem native_head_eq (x : ℝ) :
    thetaCuspNativeOddHeadDet x = 4*thetaCuspFullSource x^4*core x := by
  have heq : thetaCuspNativeOddHeadDet x =
      thetaCuspFullSourceReflectionSecondSixthCurvature x := by
    unfold thetaCuspNativeOddHeadDet
    rw [thetaCuspNativeReflectionJet_two,thetaCuspNativeReflectionJet_four,
      thetaCuspNativeReflectionJet_six]
    unfold thetaCuspSourceReflectionJetTwo thetaCuspSourceReflectionJetFour
      thetaCuspSourceReflectionJetSix thetaCuspFullSourceReflectionSecondSixthCurvature
      HilbertMetric.reflectedProductSecondJet HilbertMetric.reflectedProductFourthJet
    simp only [iteratedDeriv_zero,neg_mul_neg]
  rw [heq,thetaCuspFullSourceReflectionSecondSixthCurvature_eq_logJets]
  unfold core thetaCuspLogCurvature thetaCuspLogCurvatureJetTwo
  ring

theorem core_pos (x : ℝ) : 0 < core x := by
  have h := thetaCuspNativeOddHeadDet_pos x
  rw [native_head_eq] at h
  exact pos_of_mul_pos_right h (by positivity)

theorem hasDerivAt_core (x : ℝ) : HasDerivAt core (coreSlope x) x := by
  have hc := hasDerivAt_thetaCuspLogCurvature x
  have hB := hasDerivAt_thetaCuspLogCurvatureJetTwo x
  have hE := (hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x).neg
  have hd := (((hc.mul hE).sub (hB.pow 2)).sub
    (((hc.pow 2).const_mul 18).mul hB)).add ((hc.pow 4).const_mul 24)
  convert! hd using 1
  unfold coreSlope
  simp only [Pi.neg_apply,Pi.pow_apply]
  ring

theorem coreSlope_pos {x : ℝ} (hx : 0 < x) : 0 < coreSlope x := by
  let c := thetaCuspLogCurvature x
  let v := thetaCuspLogCurvatureJet x
  let b := curvatureDefect x
  let H := sourceDefectJet x
  let β := factorCurvature (thetaCuspLikelihoodCoordinate x)
  let R := -iteratedDeriv 7 thetaCuspLogSource x+
    4*iteratedDeriv 5 thetaCuspLogSource x+β*H
  have hc : 0 < c := thetaCuspLogCurvature_pos x
  have hc18 : 18 < c := sourceCurvature_gt_eighteen hx.le
  have hv : 0 < v := thetaCuspLogCurvatureJet_pos_of_pos hx
  have hb : 0 < b := curvatureDefect_pos hx.le
  have hb5 : 0 < 5*c-b := by
    have hu := source_projective_upper hx.le
    dsimp [b,curvatureDefect,c]
    linarith only [hu]
  have hH : 0 < H := source_defect_pos hx
  have hβ : 0 < 18*c-β := sub_pos.mpr (factorCurvature_lt hx.le)
  have hR : 0 < R := by
    have hu := sourceDefect_curvature_upper hx
    dsimp [R,β,H,sourceDefectJet]
    linarith only [hu]
  have hscale : 0 < 72*c-234 := by linarith
  have hbr : 0 < 18*c^2+4*c+2*b-c*β := by
    have he : 18*c^2+4*c+2*b-c*β=c*(18*c-β)+4*c+2*b := by ring
    rw [he]
    positivity
  have he : c*coreSlope x = v*core x+c^2*R+
      v*(b^2+18*c^2*(5*c-b)+c^3*(72*c-234))+
      c*H*(18*c^2+4*c+2*b-c*β) := by
    dsimp [c,v,b,H,β,R,core,coreSlope,curvatureDefect,sourceDefectJet,
      thetaCuspLogCurvature,thetaCuspLogCurvatureJet,
      thetaCuspLogCurvatureJetTwo,thetaCuspLogCurvatureJetThree]
    ring
  have hp : 0 < c*coreSlope x := by
    rw [he]
    have ht := core_pos x
    positivity
  exact pos_of_mul_pos_right hp hc.le

end
end RHTower.ThetaCuspHeadGrowth
namespace RHTower.ThetaCuspHeadGrowth
open Set
noncomputable section

def normalizedHead (x : ℝ) : ℝ := thetaCuspNativeOddHeadDet x/thetaCuspFullSource x^4

theorem normalizedHead_eq (x : ℝ) : normalizedHead x=4*core x := by
  unfold normalizedHead
  rw [native_head_eq]
  field_simp [(thetaCuspFullSource_pos_all x).ne']

theorem hasDerivAt_normalizedHead (x : ℝ) :
    HasDerivAt normalizedHead (4*coreSlope x) x := by
  convert! (hasDerivAt_core x).const_mul 4 using 1
  exact funext normalizedHead_eq

theorem normalizedHead_pos (x : ℝ) : 0 < normalizedHead x := by
  rw [normalizedHead_eq]
  exact mul_pos (by norm_num) (core_pos x)

theorem normalizedHead_deriv_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv normalizedHead x := by
  rw [(hasDerivAt_normalizedHead x).deriv]
  exact mul_pos (by norm_num) (coreSlope_pos hx)

theorem normalizedHead_strictMonoOn : StrictMonoOn normalizedHead (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x _
    exact (hasDerivAt_normalizedHead x).continuousAt.continuousWithinAt
  · intro x hx
    exact normalizedHead_deriv_pos (by simpa only [interior_Ici,mem_Ioi] using hx)

private theorem logSlope_neg {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspLogSource x < 0 := by
  have ha : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  have hz : deriv thetaCuspLogSource 0=0 := by
    simpa only [iteratedDeriv_one] using
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 from ⟨0,rfl⟩)
  simpa only [hz] using ha hx

/-- The coefficient of the explicit center in the source-normalized correction. -/
def centerDrive (c x : ℝ) : ℝ :=
  2*c*normalizedHead x*deriv thetaCuspLogSource x

theorem hasDerivAt_centerDrive (c x : ℝ) :
    HasDerivAt (centerDrive c)
      (2*c*(4*coreSlope x*deriv thetaCuspLogSource x+
        normalizedHead x*iteratedDeriv 2 thetaCuspLogSource x)) x := by
  have hl : HasDerivAt (deriv thetaCuspLogSource)
      (iteratedDeriv 2 thetaCuspLogSource x) x := by
    simpa only [iteratedDeriv_one] using hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x
  convert! ((hasDerivAt_normalizedHead x).mul hl).const_mul (2*c) using 1
  funext y
  unfold centerDrive
  simp only [Pi.mul_apply]
  ring

theorem centerDrive_deriv_neg {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    deriv (centerDrive c) x < 0 := by
  rw [(hasDerivAt_centerDrive c x).deriv]
  have h1 := mul_neg_of_pos_of_neg
    (mul_pos (show (0:ℝ)<4 by norm_num) (coreSlope_pos hx)) (logSlope_neg hx)
  have h2 : iteratedDeriv 2 thetaCuspLogSource x < 0 :=
    neg_pos.mp (thetaCuspLogCurvature_pos x)
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hc)
    (add_neg h1 (mul_neg_of_pos_of_neg (normalizedHead_pos x) h2))

end
end RHTower.ThetaCuspHeadGrowth
