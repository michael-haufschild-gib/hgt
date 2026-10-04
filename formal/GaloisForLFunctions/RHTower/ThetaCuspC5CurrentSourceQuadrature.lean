import GaloisForLFunctions.RHTower.ThetaCuspC5EnrichedClockCurrent
/-! Exact Peano decomposition of the complete enriched current. The discarded
first-atom source gap is restored as a single positive-kernel integral.
The sign of the complete coupled expression remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section

def actionPowerPeanoRemainderKernel (m Z a g b q C : ℝ) : ℝ :=
  actionPowerCurrentKernel m Z a g b 0 0 C-
    (9+12*Z+m*g)/125*(64*(g-1)-22*(a-1)+57*b)+
    ((9+12*Z+m*g)*(5*C-9)/25+2*(2*a+b))*q

theorem actionPowerCurrentKernel_peano_identity (m Z a g b q ep C : ℝ) :
    actionPowerCurrentKernel m Z a g b q ep C=
      actionPowerPeanoRemainderKernel m Z a g b q C+
        (9+12*Z+m*g)/125*(64*(g-1)-22*(a-1)+57*b-55*q-25*ep) := by
  unfold actionPowerPeanoRemainderKernel
  have hh:=actionPowerCurrentKernel_source_difference m Z a g b q 0 ep 0 C
  linear_combination hh

local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "g" => curvatureShapeGamma
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "ep" => curvatureShapeEpsilon
local notation "C" => intrinsicClockLogElasticity
local notation "w" => quadratureCurvatureThird
local notation "coord" => thetaCuspLikelihoodCoordinate
local notation "factor" => fun x => sourceDefectFactor (coord x)

def enrichedCurrentPeanoWeight (u t : ℝ) : ℝ :=
  ((9+12*Z u t+16*g u t)+(Q u t)^2/15*(9+12*Z u t+36*g u t))/125

def enrichedCurrentPeanoRemainder (u t : ℝ) : ℝ :=
  actionPowerPeanoRemainderKernel 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (C u t)+
    (Q u t)^2/15*
      actionPowerPeanoRemainderKernel 36 (Z u t) (a u t) (g u t) (b u t) (q u t) (C u t)

def currentSourceQuadrature (u t : ℝ) : ℝ :=
  (∫ s in 0..t, coupledShapeKernel t s*w u s)+25*t^4*w u t

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)

theorem enrichedCurrentPeanoWeight_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < enrichedCurrentPeanoWeight u t := by
  have hZ : 0 < Z u t := mul_pos ht (E_pos u ht)
  have hg : 0 < g u t := div_pos hZ (thetaCuspReflectedLogAction_pos (u:=u) ht)
  unfold enrichedCurrentPeanoWeight
  positivity

/-- All fourth-source dependence becomes a single coupled quadrature. -/
theorem enrichedClockCurrent_peano_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    E u t*enrichedClockCurrent u t=
      E u t*enrichedCurrentPeanoRemainder u t+enrichedCurrentPeanoWeight u t*
        (64*(Z u t-Q u t)^2/(t*Q u t)-currentSourceQuadrature u t) := by
  have h16:=actionPowerCurrentKernel_peano_identity 16 (Z u t) (a u t) (g u t)
    (b u t) (q u t) (ep u t) (C u t)
  have h36:=actionPowerCurrentKernel_peano_identity 36 (Z u t) (a u t) (g u t)
    (b u t) (q u t) (ep u t) (C u t)
  have hp : enrichedClockCurrent u t=enrichedCurrentPeanoRemainder u t+
      enrichedCurrentPeanoWeight u t*(coupledShapeBlock u t-25*ep u t) := by
    unfold enrichedClockCurrent enrichedCurrentPeanoRemainder enrichedCurrentPeanoWeight
    have hs : coupledShapeBlock u t=64*(g u t-1)-22*(a u t-1)+57*b u t-55*q u t := rfl
    rw [hs]
    linear_combination h16+(Q u t)^2/15*h36
  rw [hp]
  have hi:=coupledShapeBlock_variance_identity u ht
  change E u t*coupledShapeBlock u t+(∫ s in 0..t, coupledShapeKernel t s*w u s)=
    64*(Z u t-Q u t)^2/(t*Q u t) at hi
  have heps : E u t*ep u t=t^4*w u t := by
    unfold curvatureShapeEpsilon
    field_simp [(E_pos u ht).ne']
  unfold currentSourceQuadrature
  linear_combination enrichedCurrentPeanoWeight u t*hi-25*enrichedCurrentPeanoWeight u t*heps

/-- Positive source density left out by the first-atom substitution. -/
def sourceModelGapDensity (x : ℝ) : ℝ :=
  sourceDefectJetSlope x-factorLogSlope (coord x)*factor x

theorem sourceModelGapDensity_pos {x : ℝ} (hx : 0 ≤ x) : 0 < sourceModelGapDensity x :=
  sub_pos.mpr (sourceDefectJetSlope_gt_factorJet hx)

theorem sourceModelGapDensity_eq_flux {x : ℝ} (hx : 0 ≤ x) :
    sourceModelGapDensity x=defectSturmFlux x/factor x+
      (-factorLogSlope (coord x))*(factor x-sourceDefectJet x) := by
  unfold sourceModelGapDensity defectSturmFlux
  field_simp [(sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)).ne']
  ring

def reflectedSourceModelGap (u t : ℝ) : ℝ :=
  ((sourceDefectJet (u+t)-factor (u+t))-(sourceDefectJet (u-t)-factor (u-t)))/2

def reflectedSourceModelGapDensity (u t : ℝ) : ℝ :=
  (sourceModelGapDensity (u+t)+sourceModelGapDensity (u-t))/2

private theorem gapPrimitive_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun s=>sourceDefectJet s-factor s) (sourceModelGapDensity x) x := by
  convert! (hasDerivAt_sourceDefectJet x).sub (hasDerivAt_sourceDefectFactor_coordinate hx) using 1
  unfold sourceModelGapDensity
  ring

theorem hasDerivAt_reflectedSourceModelGap {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    HasDerivAt (reflectedSourceModelGap u) (reflectedSourceModelGapDensity u t) t := by
  have hp:=(gapPrimitive_deriv (show 0≤u+t by linarith)).comp t ((hasDerivAt_id t).const_add u)
  have hm:=(gapPrimitive_deriv (sub_nonneg.mpr htu)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  dsimp only [reflectedSourceModelGapDensity]
  ring

private theorem gapDensity_continuousOn {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (reflectedSourceModelGapDensity u) (Icc 0 t) := by
  have hc {x : ℝ} (hx : 0 ≤ x) : ContinuousAt sourceModelGapDensity x :=
    (hasDerivAt_sourceDefectJetSlope x).continuousAt.sub
      ((hasDerivAt_factorLogSlope_coordinate hx).continuousAt.mul
        (hasDerivAt_sourceDefectFactor_coordinate hx).continuousAt)
  intro s hs
  exact (((hc (show 0≤u+s by linarith [hs.1])).comp
    (continuous_const.add continuous_id).continuousAt).add
    ((hc (show 0≤u-s by linarith [hs.2])).comp
      (continuous_const.sub continuous_id).continuousAt)).div_const 2 |>.continuousWithinAt

theorem reflectedSourceModelGapDensity_pos {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    0 < reflectedSourceModelGapDensity u t := by
  unfold reflectedSourceModelGapDensity
  exact div_pos (add_pos (sourceModelGapDensity_pos (show 0≤u+t by linarith))
    (sourceModelGapDensity_pos (sub_nonneg.mpr htu))) (by norm_num)

/-- The source-model error at each reflected endpoint is itself an integral. -/
theorem reflectedSourceModelGap_integral {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    reflectedSourceModelGap u t=∫ s in 0..t, reflectedSourceModelGapDensity u s := by
  have hi : IntervalIntegrable (reflectedSourceModelGapDensity u) volume 0 t :=
    (gapDensity_continuousOn ht htu).intervalIntegrable_of_Icc ht
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs=>hasDerivAt_reflectedSourceModelGap ((uIcc_of_le ht ▸ hs).1)
      (((uIcc_of_le ht ▸ hs).2).trans htu)) hi]
  simp only [reflectedSourceModelGap,add_zero,sub_zero,sub_self,zero_div,sub_zero]

/-- Backward primitive of the Peano weight including its endpoint mass. -/
def currentSourceGapKernel (t s : ℝ) : ℝ :=
  25*t^4+(85/3)*t^2*(t^2-s^2)-(7/4)*(t^4-s^4)+16/(15*t)*(t^5-s^5)

theorem currentSourceGapKernel_pos {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 < currentSourceGapKernel t s := by
  have hdiff : 0 ≤ t-s := sub_nonneg.mpr hst
  have hid : currentSourceGapKernel t s=25*t^4+
      ((t-s)*(t+s))*((149/6)*t^2+(7/4)*(t-s)*(t+s))+
      16/(15*t)*(t-s)*(t^4+t^3*s+t^2*s^2+t*s^3+s^4) := by
    unfold currentSourceGapKernel
    ring
  rw [hid]
  positivity

private theorem currentSourceGapKernel_deriv (t s : ℝ) :
    HasDerivAt (currentSourceGapKernel t) (-coupledShapeKernel t s) s := by
  have hh:=hasDerivAt_id s
  convert! (((hasDerivAt_const s (25*t^4)).add
    (((hh.pow 2).const_sub (t^2)).const_mul ((85/3)*t^2))).sub
      (((hh.pow 4).const_sub (t^4)).const_mul (7/4))).add
        (((hh.pow 5).const_sub (t^5)).const_mul (16/(15*t))) using 1
  dsimp only [id_eq,Pi.pow_apply]
  unfold coupledShapeKernel
  ring

private theorem kernel_continuous (t : ℝ) : Continuous (coupledShapeKernel t) := by
  unfold coupledShapeKernel
  fun_prop

/-- Endpoint loss and integrated loss are one positive source integral. -/
theorem currentSourceGapKernel_integral_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (∫ s in 0..t, coupledShapeKernel t s*reflectedSourceModelGap u s)+
      25*t^4*reflectedSourceModelGap u t=
        ∫ s in 0..t, currentSourceGapKernel t s*reflectedSourceModelGapDensity u s := by
  have hL : Continuous (currentSourceGapKernel t) :=
    continuous_iff_continuousAt.mpr (fun s=>(currentSourceGapKernel_deriv t s).continuousAt)
  have hG : ContinuousOn (reflectedSourceModelGap u) (Icc 0 t) := by
    intro s hs
    exact (hasDerivAt_reflectedSourceModelGap hs.1 (hs.2.trans htu)).continuousAt.continuousWithinAt
  have hI : IntervalIntegrable (fun s=>currentSourceGapKernel t s*reflectedSourceModelGapDensity u s) volume 0 t :=
    (hL.continuousOn.mul (gapDensity_continuousOn ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hJ : IntervalIntegrable (fun s=>coupledShapeKernel t s*reflectedSourceModelGap u s) volume 0 t :=
    ((kernel_continuous t).continuousOn.mul hG).intervalIntegrable_of_Icc ht.le
  have hd (s : ℝ) (hs : s ∈ uIcc 0 t) :
      HasDerivAt (fun r=>currentSourceGapKernel t r*reflectedSourceModelGap u r)
        (currentSourceGapKernel t s*reflectedSourceModelGapDensity u s-
          coupledShapeKernel t s*reflectedSourceModelGap u s) s := by
    have hs':s ∈ Icc 0 t:=uIcc_of_le ht.le ▸ hs
    convert! (currentSourceGapKernel_deriv t s).mul
      (hasDerivAt_reflectedSourceModelGap hs'.1 (hs'.2.trans htu)) using 1
    ring
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hI.sub hJ)
  rw [intervalIntegral.integral_sub hI hJ] at hi
  have hzero : reflectedSourceModelGap u 0=0 := by simp [reflectedSourceModelGap]
  have hend : currentSourceGapKernel t t=25*t^4 := by simp [currentSourceGapKernel]
  rw [hzero,hend,mul_zero,sub_zero] at hi
  linarith only [hi]

/-- The retained correction is strictly positive on the whole physical chamber. -/
theorem currentSourceGapKernel_integral_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < ∫ s in 0..t, currentSourceGapKernel t s*reflectedSourceModelGapDensity u s := by
  have hL : Continuous (currentSourceGapKernel t) :=
    continuous_iff_continuousAt.mpr (fun s=>(currentSourceGapKernel_deriv t s).continuousAt)
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 t) :
      0 < currentSourceGapKernel t s*reflectedSourceModelGapDensity u s :=
    mul_pos (currentSourceGapKernel_pos ht hs.1 hs.2)
      (reflectedSourceModelGapDensity_pos hs.1 (hs.2.trans htu))
  have hi:=intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (show ContinuousOn (fun _ : ℝ=> (0:ℝ)) (Icc 0 t) from continuousOn_const)
    (hL.continuousOn.mul (gapDensity_continuousOn ht.le htu))
    (fun s hs=>(hpoint s ⟨hs.1.le,hs.2⟩).le)
    ⟨0,⟨le_rfl,ht.le⟩,hpoint 0 ⟨le_rfl,ht.le⟩⟩
  simpa only [intervalIntegral.integral_zero,Pi.mul_apply] using hi

/-- The actual model comparison with both source endpoints visible. -/
def modelQuadratureSource (u t : ℝ) : ℝ :=
  4*shapeCurvatureSlope u t+(factor (u-t)-factor (u+t))/2

theorem quadratureCurvatureThird_add_modelGap (u t : ℝ) :
    w u t+reflectedSourceModelGap u t=modelQuadratureSource u t := by
  unfold quadratureCurvatureThird reflectedSourceModelGap modelQuadratureSource
    sourceDefectJet shapeCurvatureSlope thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
  ring

def currentModelSourceQuadrature (u t : ℝ) : ℝ :=
  (∫ s in 0..t, coupledShapeKernel t s*modelQuadratureSource u s)+25*t^4*modelQuadratureSource u t

private theorem w_continuous (u : ℝ) : Continuous (w u) := by
  have hc : Continuous thetaCuspLogCurvatureJetThree :=
    continuous_iff_continuousAt.mpr (fun s=>(hasDerivAt_thetaCuspLogCurvatureJetThree s).continuousAt)
  exact ((hc.comp (continuous_const.add continuous_id)).sub
    (hc.comp (continuous_const.sub continuous_id))).div_const 2

/-- Exact source correction for the whole quadrature, with no independent jet substitution. -/
theorem currentSourceQuadrature_add_modelGap {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentSourceQuadrature u t+
        (∫ s in 0..t, currentSourceGapKernel t s*reflectedSourceModelGapDensity u s)=
      currentModelSourceQuadrature u t := by
  rw [←currentSourceGapKernel_integral_identity ht htu]
  have hG : ContinuousOn (reflectedSourceModelGap u) (Icc 0 t) := by
    intro s hs
    exact (hasDerivAt_reflectedSourceModelGap hs.1 (hs.2.trans htu)).continuousAt.continuousWithinAt
  have hI : IntervalIntegrable (fun s=>coupledShapeKernel t s*w u s) volume 0 t :=
    ((kernel_continuous t).mul (w_continuous u)).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s=>coupledShapeKernel t s*reflectedSourceModelGap u s) volume 0 t :=
    ((kernel_continuous t).continuousOn.mul hG).intervalIntegrable_of_Icc ht.le
  have hi : (∫ s in 0..t, coupledShapeKernel t s*modelQuadratureSource u s)=
      (∫ s in 0..t, coupledShapeKernel t s*w u s)+
        (∫ s in 0..t, coupledShapeKernel t s*reflectedSourceModelGap u s) := by
    rw [←intervalIntegral.integral_add hI hJ]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [←quadratureCurvatureThird_add_modelGap]
    ring
  unfold currentSourceQuadrature currentModelSourceQuadrature
  rw [hi,←quadratureCurvatureThird_add_modelGap u t]
  ring

/-- Complete current: actual clock, nonlinear remainder, variance, model source,
and the strictly positive Sturm-source correction, in one identity. -/
theorem enrichedClockCurrent_model_peano_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    E u t*enrichedClockCurrent u t=
      E u t*enrichedCurrentPeanoRemainder u t+enrichedCurrentPeanoWeight u t*
        (64*(Z u t-Q u t)^2/(t*Q u t)-currentModelSourceQuadrature u t+
          (∫ s in 0..t, currentSourceGapKernel t s*reflectedSourceModelGapDensity u s)) := by
  rw [enrichedClockCurrent_peano_identity u ht]
  have hh:=currentSourceQuadrature_add_modelGap ht htu
  linear_combination -enrichedCurrentPeanoWeight u t*hh

end
end RHTower.ThetaCuspDefect
