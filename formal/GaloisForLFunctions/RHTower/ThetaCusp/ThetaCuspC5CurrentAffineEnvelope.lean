import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CurrentMomentTransfer
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5InverseForceQuadrature
import Mathlib.Topology.Order.IntermediateValue
/-! Actual affine fourth-source transport in the complete enriched current.
The positive backward kernel retains the full source slack and an exact
interior even-curvature integral. The actual affine and explicit model
source envelopes have a unique crossing, giving a canonical pointwise
minimum and an exact positive tail correction. The full current sign
on the remaining inner chamber and arbitrary-degree positivity stay open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "w" => quadratureCurvatureThird
local notation "v" => supersolutionCurvatureFourth
local notation "a" => curvatureShapeAlpha
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "W" => enrichedCurrentPeanoWeight
local notation "Delta" => enrichedPeanoDeltaCoefficient
local notation "eta" => currentMomentTransfer
local notation "L" => currentMomentGapKernel
local notation "K" => currentMomentKernel
private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem p_deriv (u s : ℝ) : HasDerivAt (p u) (r u s) s := by
  have hp:=(hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm:=(hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem r_deriv (u s : ℝ) : HasDerivAt (r u) (w u s) s := by
  have hp:=(hasDerivAt_thetaCuspLogCurvatureJetTwo (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm:=(hasDerivAt_thetaCuspLogCurvatureJetTwo (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.add hm).div_const 2 using 1
  unfold quadratureCurvatureThird
  ring
private theorem w_continuous (u : ℝ) : Continuous (w u) := by
  have hc : Continuous thetaCuspLogCurvatureJetThree :=
    continuous_iff_continuousAt.mpr (fun s=>(hasDerivAt_thetaCuspLogCurvatureJetThree s).continuousAt)
  exact ((hc.comp (continuous_const.add continuous_id)).sub
    (hc.comp (continuous_const.sub continuous_id))).div_const 2

private theorem baseGap_deriv (t s : ℝ) :
    HasDerivAt (currentSourceGapKernel t) (-coupledShapeKernel t s) s := by
  have hh:=hasDerivAt_id s
  convert! (((hasDerivAt_const s (25*t^4)).add
    (((hh.pow 2).const_sub (t^2)).const_mul ((85/3)*t^2))).sub
      (((hh.pow 4).const_sub (t^4)).const_mul (7/4))).add
        (((hh.pow 5).const_sub (t^5)).const_mul (16/(15*t))) using 1
  dsimp only [id_eq,Pi.pow_apply]
  unfold coupledShapeKernel
  ring
private theorem momentGap_deriv (u t s : ℝ) :
    HasDerivAt (currentMomentGapKernel u t) (-currentMomentKernel u t s) s := by
  convert! ((baseGap_deriv t s).const_mul (W u t)).sub
    (((((hasDerivAt_id s).pow 2).const_sub (t^2)).const_mul (eta u t*t^2)).div_const 2) using 1
  dsimp only [id_eq,Pi.pow_apply]
  unfold currentMomentKernel
  ring
private theorem kernel_continuous (u t : ℝ) : Continuous (currentMomentKernel u t) := by
  unfold currentMomentKernel coupledShapeKernel
  fun_prop
private theorem actualQuadrature_eq (u t : ℝ) :
    currentMomentActualQuadrature u t=W u t*currentSourceQuadrature u t-
      eta u t*t^2*(∫ s in 0..t, s*w u s) := by
  have hK : Continuous (coupledShapeKernel t) := by unfold coupledShapeKernel; fun_prop
  have hI : IntervalIntegrable (fun s=>W u t*(coupledShapeKernel t s*w u s)) volume 0 t :=
    ((hK.mul (w_continuous u)).const_mul (W u t)).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s=>(eta u t*t^2)*(s*w u s)) volume 0 t :=
    ((continuous_id.mul (w_continuous u)).const_mul (eta u t*t^2)).intervalIntegrable 0 t
  have hid : (fun s=>currentMomentKernel u t s*w u s)=
      (fun s=>W u t*(coupledShapeKernel t s*w u s)-(eta u t*t^2)*(s*w u s)) := by
    funext s
    unfold currentMomentKernel
    ring
  unfold currentMomentActualQuadrature currentSourceQuadrature
  rw [hid,intervalIntegral.integral_sub hI hJ,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

private theorem e_continuous (u : ℝ) : Continuous (e u) :=
  continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_completedCurvatureEven u s).continuousAt)
private theorem r_continuous (u : ℝ) : Continuous (r u) :=
  continuous_iff_continuousAt.mpr (fun s => (r_deriv u s).continuousAt)
private theorem v_continuous (u : ℝ) : Continuous (v u) := by
  have h6 := (HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 6).continuous
  unfold supersolutionCurvatureFourth thetaCuspLogCurvatureJetFour
  fun_prop
private theorem L_continuous (u t : ℝ) : Continuous (L u t) :=
  continuous_iff_continuousAt.mpr (fun s => (momentGap_deriv u t s).continuousAt)
private theorem L_endpoint (u t : ℝ) : L u t t=25*W u t*t^4 := by
  unfold currentMomentGapKernel momentTransferGapKernel currentSourceGapKernel
  ring
private theorem L_nonneg (u : ℝ) {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc 0 t) : 0 ≤ L u t s :=
  momentTransferGapKernel_nonneg (enrichedCurrentPeanoWeight_pos u ht) ht hs.1 hs.2
    (currentMomentTransfer_admitted u t)
private theorem L_pos (u : ℝ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) : 0 < L u t s :=
  momentTransferGapKernel_pos (enrichedCurrentPeanoWeight_pos u ht) ht hs hst
    (currentMomentTransfer_admitted u t)

/-- The transferred quadrature is a positive-kernel functional of the literal fourth source. -/
theorem currentMomentActualQuadrature_fourth_integral (u t : ℝ) :
    currentMomentActualQuadrature u t=∫ s in 0..t, L u t s*v u s := by
  have hI : IntervalIntegrable (fun s => L u t s*v u s) volume 0 t :=
    ((L_continuous u t).mul (v_continuous u)).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s => K u t s*w u s) volume 0 t :=
    ((kernel_continuous u t).mul (w_continuous u)).intervalIntegrable 0 t
  have hd (s : ℝ) : HasDerivAt (fun s => L u t s*w u s)
      (L u t s*v u s-K u t s*w u s) s := by
    convert! (momentGap_deriv u t s).mul (hasDerivAt_quadratureCurvatureThird u s) using 1
    ring
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hI.sub hJ)
  rw [intervalIntegral.integral_sub hI hJ,L_endpoint] at hh
  have hzero : w u 0=0 := by simp [quadratureCurvatureThird]
  rw [hzero,mul_zero,sub_zero] at hh
  unfold currentMomentActualQuadrature
  linarith only [hh]

/-- Positive literal source defect in the affine fourth-curvature inequality. -/
def currentAffineSourceSlack (u s : ℝ) : ℝ := 166*r u s-648*e u s-v u s

theorem currentAffineSourceSlack_pos {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    0 < currentAffineSourceSlack u s :=
  sub_pos.mpr (supersolutionCurvatureFourth_affine_upper hs hsu)
private theorem slack_continuous (u : ℝ) : Continuous (currentAffineSourceSlack u) :=
  (((r_continuous u).const_mul 166).sub ((e_continuous u).const_mul 648)).sub (v_continuous u)

def currentMomentAffineQuadrature (u t : ℝ) : ℝ :=
  ∫ s in 0..t, L u t s*(166*r u s-648*e u s)

/-- The full affine-source comparison retains its exact positive slack. -/
theorem currentMomentAffineQuadrature_gap (u t : ℝ) :
    currentMomentAffineQuadrature u t-currentMomentActualQuadrature u t=
      ∫ s in 0..t, L u t s*currentAffineSourceSlack u s := by
  have hI : IntervalIntegrable (fun s => L u t s*(166*r u s-648*e u s)) volume 0 t :=
    ((L_continuous u t).mul (((r_continuous u).const_mul 166).sub
      ((e_continuous u).const_mul 648))).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s => L u t s*v u s) volume 0 t :=
    ((L_continuous u t).mul (v_continuous u)).intervalIntegrable 0 t
  rw [currentMomentActualQuadrature_fourth_integral,currentMomentAffineQuadrature,
    ←intervalIntegral.integral_sub hI hJ]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [currentAffineSourceSlack]
  ring

theorem currentMomentAffineGap_integral_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < ∫ s in 0..t, L u t s*currentAffineSourceSlack u s := by
  have hnonneg (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤ L u t s*currentAffineSourceSlack u s :=
    mul_nonneg (L_nonneg u ht hs) (currentAffineSourceSlack_pos hs.1 (hs.2.trans htu)).le
  have hpoint : 0 < L u t (t/2)*currentAffineSourceSlack u (t/2) :=
    mul_pos (L_pos u ht (by linarith) (by linarith))
      (currentAffineSourceSlack_pos (by linarith) (by linarith))
  have hi:=intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (show ContinuousOn (fun _ : ℝ => (0:ℝ)) (Icc 0 t) from continuousOn_const)
    (((L_continuous u t).mul (slack_continuous u)).continuousOn)
    (fun s hs => hnonneg s ⟨hs.1.le,hs.2⟩) ⟨t/2,⟨by linarith,by linarith⟩,hpoint⟩
  simpa only [intervalIntegral.integral_zero,Pi.mul_apply] using hi

/-- Full lower remainder using the actual affine fourth-source inequality. -/
def currentMomentAffineRemainder (u t : ℝ) : ℝ :=
  E u t*enrichedCurrentLowerJetRemainder u t+E u t*eta u t*b u t+
    E u t*(Delta u t-eta u t)*(b u t)^2/a u t+
      W u t*(64*(curvatureShapeAction u t-thetaCuspReflectedLogAction u t)^2/
        (t*thetaCuspReflectedLogAction u t))-currentMomentAffineQuadrature u t

/-- Complete-current decomposition with actual affine slack and Schur reserve. -/
theorem enrichedClockCurrent_affine_moment_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    E u t*enrichedClockCurrent u t=currentMomentAffineRemainder u t+
      E u t*(Delta u t-eta u t)*(q u t-(b u t)^2/a u t)+
        (∫ s in 0..t, L u t s*currentAffineSourceSlack u s) := by
  have hP:=enrichedClockCurrent_peano_identity u ht
  rw [enrichedCurrentPeanoRemainder_delta_identity] at hP
  have hA:=actualQuadrature_eq u t
  have hQ:=curvatureShapeDelta_sub_beta_moment u ht
  have hG:=currentMomentAffineQuadrature_gap u t
  unfold currentMomentAffineRemainder
  linear_combination hP+hA+eta u t*hQ+hG

theorem currentMomentAffineRemainder_lt_complete {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentAffineRemainder u t < E u t*enrichedClockCurrent u t := by
  have hsource:=currentMomentAffineGap_integral_pos ht htu
  have hSchur:=sub_pos.mpr (curvatureShapeDelta_gt_schur ht htu)
  have hcoef:=sub_nonneg.mpr (currentMomentTransfer_le_delta u t)
  have hE:=E_pos u ht
  have hnonneg : 0 ≤ E u t*(Delta u t-eta u t)*(q u t-(b u t)^2/a u t) := by positivity
  rw [enrichedClockCurrent_affine_moment_identity u ht]
  linarith only [hsource,hnonneg]

/-- The derivative of the signed moment kernel, kept literal in the even-source integral. -/
def currentMomentKernelJet (u t s : ℝ) : ℝ :=
  W u t*((170/3)*t^2-21*s^2+64*s^3/(3*t))-eta u t*t^2
private theorem K_deriv (u t s : ℝ) : HasDerivAt (K u t) (currentMomentKernelJet u t s) s := by
  have hh:=hasDerivAt_id s
  have hp:=((hh.const_mul ((170/3)*t^2)).sub ((hh.pow 3).const_mul 7)).add
    ((hh.pow 4).const_mul (16/(3*t)))
  unfold currentMomentKernel coupledShapeKernel
  convert! (hp.const_mul (W u t)).sub (hh.const_mul (eta u t*t^2)) using 1
  · funext zv
    dsimp only [id_eq,Pi.pow_apply,Pi.add_apply,Pi.sub_apply]
    ring
  · dsimp only [id_eq,Pi.pow_apply]
    unfold currentMomentKernelJet
    ring
private theorem K_endpoint (u : ℝ) {t : ℝ} (ht : t ≠ 0) : K u t t=(55*W u t-eta u t)*t^3 := by
  unfold currentMomentKernel coupledShapeKernel
  field_simp [ht]
  ring

/-- Literal even-curvature kernel; its sign is not assumed. -/
def currentMomentEvenSourceKernel (u t s : ℝ) : ℝ :=
  648*L u t s+166*currentMomentKernelJet u t s

def currentMomentEvenQuadrature (u t : ℝ) : ℝ :=
  166*(25*W u t*t^4*p u t+(55*W u t-eta u t)*t^3*e u t)-
    ∫ s in 0..t, currentMomentEvenSourceKernel u t s*e u s

/-- All interior derivative terms are removed together, preserving the full even-source integral. -/
theorem currentMomentAffineQuadrature_even_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    currentMomentAffineQuadrature u t=currentMomentEvenQuadrature u t := by
  have hK : Continuous (currentMomentKernelJet u t) := by unfold currentMomentKernelJet; fun_prop
  have hI : IntervalIntegrable (fun s => L u t s*(166*r u s-648*e u s)) volume 0 t :=
    ((L_continuous u t).mul (((r_continuous u).const_mul 166).sub
      ((e_continuous u).const_mul 648))).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s => currentMomentEvenSourceKernel u t s*e u s) volume 0 t :=
    ((((L_continuous u t).const_mul 648).add (hK.const_mul 166)).mul
      (e_continuous u)).intervalIntegrable 0 t
  have hd (s : ℝ) : HasDerivAt (fun s => 166*(L u t s*p u s+K u t s*e u s))
      (L u t s*(166*r u s-648*e u s)+currentMomentEvenSourceKernel u t s*e u s) s := by
    convert! (((momentGap_deriv u t s).mul (p_deriv u s)).add
      ((K_deriv u t s).mul (hasDerivAt_completedCurvatureEven u s))).const_mul 166 using 1
    dsimp only [shapeCurvatureSlope]
    unfold currentMomentEvenSourceKernel
    ring
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hI.add hJ)
  rw [intervalIntegral.integral_add hI hJ,L_endpoint,K_endpoint u ht.ne'] at hh
  have hzero : p u 0=0 := by simp [shapeCurvatureSlope]
  have hKzero : K u t 0=0 := by simp [currentMomentKernel,coupledShapeKernel]
  rw [hzero,hKzero,mul_zero,zero_mul,zero_add,mul_zero,sub_zero] at hh
  unfold currentMomentAffineQuadrature currentMomentEvenQuadrature
  linarith only [hh]

local notation "c" => thetaCuspLogCurvature
local notation "c2" => thetaCuspLogCurvatureJetTwo
local notation "coord" => thetaCuspLikelihoodCoordinate
local notation "S" => thetaCuspSingleAtomReflectionScale 1
local notation "G" => sourceDefectPrimitive
local notation "beta" => normalizedCurvatureDefect
local notation "F" => fun x => sourceDefectFactor (coord x)

/-- Normalized difference of the model and actual-affine fourth-source envelopes. -/
def fourthSourceEnvelopeDifference (x : ℝ) : ℝ :=
  16+120/coord x+180/(coord x)^2-162*beta x
local notation "chi" => fourthSourceEnvelopeDifference

def fourthSourceAffineEnvelope (x : ℝ) : ℝ := 166*c2 x-648*c x
def fourthSourceModelEnvelope (x : ℝ) : ℝ := 4*c2 x-factorLogSlope (coord x)*F x

/-- Exact source identity determining which admissible envelope is smaller. -/
theorem fourthSourceEnvelopeDifference_identity {x : ℝ} (hx : 0 ≤ x) :
    fourthSourceModelEnvelope x-fourthSourceAffineEnvelope x=G x*chi x := by
  have hq:=(thetaCuspLikelihoodCoordinate_pos hx).ne'
  have hq3 : coord x+3 ≠ 0 := by have := thetaCuspLikelihoodCoordinate_pos hx; positivity
  have hG:=(sourceDefectPrimitive_pos hx).ne'
  unfold fourthSourceModelEnvelope fourthSourceAffineEnvelope fourthSourceEnvelopeDifference
    normalizedCurvatureDefect curvatureDefect
  dsimp only
  rw [show sourceDefectFactor (coord x)=G x*(4+12/coord x) from (sourceDefectPrimitive_mul_rate hx).symm]
  unfold factorLogSlope
  field_simp [hq,hq3,hG]
  ring

private theorem chi_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt chi
      (-240*S x/(coord x)^2-720*S x/(coord x)^3-
        162*(F x*sourcePrimitiveReserve x/(G x)^2)) x := by
  have hq:=thetaCuspLikelihoodCoordinate_pos hx
  have hd:=hasDerivAt_thetaCuspLikelihoodCoordinate x
  convert! ((((hasDerivAt_const x (16:ℝ)).add
    ((hasDerivAt_const x (120:ℝ)).div hd hq.ne')).add
      ((hasDerivAt_const x (180:ℝ)).div (hd.pow 2) (pow_ne_zero 2 hq.ne'))).sub
        ((hasDerivAt_normalizedCurvatureDefect hx).const_mul 162)) using 1
  dsimp only [Pi.pow_apply]
  field_simp [hq.ne']
  ring

/-- The actual source envelopes have at most one crossing. -/
theorem fourthSourceEnvelopeDifference_strictAntiOn : StrictAntiOn chi (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (chi_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(chi_deriv hx0).deriv]
    have hq:=thetaCuspLikelihoodCoordinate_pos hx0
    have hS : 0 < S x := by rw [thetaCuspC5FarTail_scale_eq_coordinate_add]; positivity
    have hF:=sourceDefectFactor_pos hq
    have hR:=sourcePrimitiveReserve_pos hx0
    have hG:=sourceDefectPrimitive_pos hx0
    have h1 : 0 < 240*S x/(coord x)^2 := by positivity
    have h2 : 0 < 720*S x/(coord x)^3 := by positivity
    have h3 : 0 < 162*(F x*sourcePrimitiveReserve x/(G x)^2) := by positivity
    simp only [neg_mul,neg_div]
    linarith only [h1,h2,h3]

/-- At infinity the model source is strictly below the affine envelope. -/
theorem fourthSourceEnvelopeDifference_tendsto : Tendsto chi atTop (nhds (-146)) := by
  have h1:=thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 1 (by norm_num)
  have h2:=thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have hh:=(((h1.const_mul 120).const_add 16).add (h2.const_mul 180)).sub
    (normalizedCurvatureDefect_tendsto_one.const_mul 162)
  convert! hh using 1
  · funext x
    unfold fourthSourceEnvelopeDifference
    simp only [pow_one]
    ring
  · norm_num

private theorem centerCurvature_lt_twenty : c 0 < 20 := by
  have hXlo:=thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hXhi:=thetaCuspSelfDualModularScale_sq_lt_twenty
  let X:=thetaCuspSelfDualModularScale^2
  have hxlo : 19 < X := by dsimp only [X]; linarith only [hXlo]
  have hxhi : X < 20 := hXhi
  have hp : 0 < centerRawJet X 2+20*centerRawJet X 0 := by
    have hid : centerRawJet X 2+20*centerRawJet X 0=
        ((20-X)*(X+20)+70*(X-19)+90)/128 := by
      unfold centerRawJet
      simp only [centerMassJet,Nat.reduceAdd]
      ring
    rw [hid]
    have hleft:=sub_pos.mpr hxhi
    have hright:=sub_pos.mpr hxlo
    have hX : 0 < X+20 := by linarith only [hxlo]
    positivity
  have hH:=thetaCuspModularODEState_H_re_pos 0
  have hmul:=mul_pos hH hp
  have h0:=thetaSource_centerRawJet 0 (by omega)
  have h2:=thetaSource_centerRawJet 1 (by omega)
  norm_num only [Nat.reduceMul,iteratedDeriv_zero] at h0 h2
  have hf : 0 < iteratedDeriv 2 thetaCuspFullSource 0+20*thetaCuspFullSource 0 := by
    rw [h0,h2]
    change 0 < (thetaCuspModularODEState .H 0).re*centerRawJet X 2+
      20*((thetaCuspModularODEState .H 0).re*centerRawJet X 0)
    nlinarith only [hmul]
  have h1:=iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 1 by norm_num)
  rw [iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet] at hf
  unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetZero at hf
  rw [h1,thetaCuspLogSource,Real.exp_log (thetaCuspFullSource_pos_all 0)] at hf
  have hpos:=thetaCuspFullSource_pos_all 0
  unfold thetaCuspLogCurvature
  nlinarith only [hf,hpos]

/-- The affine source is strictly below the model envelope at the physical center. -/
theorem fourthSourceEnvelopeDifference_zero_pos : 0 < chi 0 := by
  have hq:=thetaCuspLikelihoodCoordinate_pos (x:=0) le_rfl
  have hq2 : coord 0 < 2 := by
    have hpi:=Real.pi_lt_d2
    norm_num only [thetaCuspLikelihoodCoordinate,Real.exp_zero,one_pow,mul_one]
    linarith only [hpi]
  have hq2sq : (coord 0)^2 < 4 := by nlinarith only [mul_pos hq (sub_pos.mpr hq2),hq2]
  have hq3 : (coord 0)^3 < 8 := by
    have hh:=mul_lt_mul_of_pos_left hq2sq hq
    nlinarith only [hh,hq2]
  have hq4 : (coord 0)^4 < 16 := by
    have hh:=mul_lt_mul_of_pos_left hq2sq (sq_pos_of_pos hq)
    nlinarith only [hh,hq2sq]
  have hG : 160 < G 0 := by
    have hid : G 0=216/(coord 0)^2+648/(coord 0)^3+486/(coord 0)^4 := by
      unfold sourceDefectPrimitive
      field_simp [hq.ne']
      ring
    have hA : 54 < 216/(coord 0)^2 := (lt_div_iff₀ (sq_pos_of_pos hq)).mpr (by linarith only [hq2sq])
    have hB : 81 < 648/(coord 0)^3 := (lt_div_iff₀ (pow_pos hq 3)).mpr (by linarith only [hq3])
    have hC : 30 < 486/(coord 0)^4 := (lt_div_iff₀ (pow_pos hq 4)).mpr (by linarith only [hq4])
    rw [hid]
    linarith only [hA,hB,hC]
  have hB : curvatureDefect 0 < 100 := by
    have hh:=source_projective_upper (x:=0) le_rfl
    have hc:=centerCurvature_lt_twenty
    unfold curvatureDefect
    linarith only [hh,hc]
  have hbeta : beta 0 < 5/8 := by
    unfold normalizedCurvatureDefect
    apply (div_lt_iff₀ (sourceDefectPrimitive_pos (x:=0) le_rfl)).mpr
    linarith only [hB,hG]
  have hA : 60 < 120/coord 0 := (lt_div_iff₀ hq).mpr (by linarith only [hq2])
  have hC : 45 < 180/(coord 0)^2 := (lt_div_iff₀ (sq_pos_of_pos hq)).mpr (by linarith only [hq2sq])
  unfold fourthSourceEnvelopeDifference
  linarith only [hA,hC,hbeta]

/-- A unique, source-defined crossing separates the two admissible envelopes. -/
theorem fourthSourceEnvelope_unique_crossing :
    ∃ z : ℝ, 0 < z ∧ chi z=0 ∧
      (∀ x : ℝ, 0 ≤ x → (chi x=0 ↔ x=z)) ∧
      (∀ x : ℝ, 0 ≤ x → (0 < chi x ↔ x < z) ∧ (chi x < 0 ↔ z < x)) := by
  have htail : ∀ᶠ x in atTop, chi x < 0 :=
    fourthSourceEnvelopeDifference_tendsto.eventually (Iio_mem_nhds (by norm_num : (-146:ℝ) < 0))
  obtain ⟨T,hT,hneg⟩ := (htail.and (eventually_ge_atTop (0:ℝ))).exists
  have hT0 : 0 ≤ T := hneg
  have hneg' : chi T < 0 := hT
  have hc : ContinuousOn chi (Icc 0 T) := by
    intro x hx
    exact (chi_deriv hx.1).continuousAt.continuousWithinAt
  obtain ⟨z,hz,hzero⟩:=intermediate_value_Icc' hT0 hc
    (show (0:ℝ) ∈ Icc (chi T) (chi 0) from ⟨hneg'.le,fourthSourceEnvelopeDifference_zero_pos.le⟩)
  have hz0 : 0 < z := by
    have hne : z ≠ 0 := by intro hh; subst z; linarith only [hzero,fourthSourceEnvelopeDifference_zero_pos]
    exact lt_of_le_of_ne hz.1 (Ne.symm hne)
  have hanti:=fourthSourceEnvelopeDifference_strictAntiOn
  refine ⟨z,hz0,hzero,?_,?_⟩
  · intro x hx
    constructor
    · intro hh
      rcases lt_trichotomy x z with hlt | heq | hgt
      · have hh':=hanti hx hz0.le hlt
        linarith only [hh',hh,hzero]
      · exact heq
      · have hh':=hanti hz0.le hx hgt
        linarith only [hh',hh,hzero]
    · rintro rfl
      exact hzero
  · intro x hx
    constructor
    · constructor
      · intro hp
        by_contra hn
        have hh:=hanti.antitoneOn hz0.le hx (le_of_not_gt hn)
        linarith only [hh,hzero,hp]
      · intro hlt
        have hh:=hanti hx hz0.le hlt
        linarith only [hh,hzero]
    · constructor
      · intro hn
        by_contra hp
        have hh:=hanti.antitoneOn hx hz0.le (le_of_not_gt hp)
        linarith only [hh,hzero,hn]
      · intro hlt
        have hh:=hanti hz0.le hx hlt
        linarith only [hh,hzero]

/-- The pointwise best of the two proved actual fourth-source upper envelopes. -/
def fourthSourceCombinedEnvelope (x : ℝ) : ℝ :=
  min (fourthSourceAffineEnvelope x) (fourthSourceModelEnvelope x)

theorem fourthSourceCombinedEnvelope_gt_actual {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogCurvatureJetFour x < fourthSourceCombinedEnvelope x := by
  have ha:=source_fourth_curvature_affine_upper hx
  change thetaCuspLogCurvatureJetFour x < fourthSourceAffineEnvelope x at ha
  exact lt_min ha (sourceCurvatureFourth_lt_modelJet hx)

theorem fourthSourceEnvelope_order {x : ℝ} (hx : 0 ≤ x) :
    (fourthSourceAffineEnvelope x < fourthSourceModelEnvelope x ↔ 0 < chi x) ∧
      (fourthSourceModelEnvelope x < fourthSourceAffineEnvelope x ↔ chi x < 0) := by
  have hg:=sourceDefectPrimitive_pos hx
  constructor
  · rw [←sub_pos,fourthSourceEnvelopeDifference_identity hx]
    exact mul_pos_iff_of_pos_left hg
  · rw [←sub_neg,fourthSourceEnvelopeDifference_identity hx]
    constructor
    · intro hneg
      by_contra hn
      have hnon:=mul_nonneg hg.le (le_of_not_gt hn)
      exact (not_lt_of_ge hnon) hneg
    · intro hneg
      exact mul_neg_of_pos_of_neg hg hneg

/-- The best envelope changes formula once, at an actual source-defined crossing. -/
theorem fourthSourceCombinedEnvelope_one_crossing :
    ∃ z : ℝ, 0 < z ∧
      (∀ x : ℝ, 0 ≤ x →
        (fourthSourceAffineEnvelope x < fourthSourceModelEnvelope x ↔ x < z) ∧
        (fourthSourceModelEnvelope x < fourthSourceAffineEnvelope x ↔ z < x)) ∧
      (∀ x : ℝ, 0 ≤ x → fourthSourceCombinedEnvelope x=
        if x ≤ z then fourthSourceAffineEnvelope x else fourthSourceModelEnvelope x) := by
  obtain ⟨z,hz,hzero,_,hsign⟩:=fourthSourceEnvelope_unique_crossing
  refine ⟨z,hz,?_,?_⟩
  · intro x hx
    exact ⟨(fourthSourceEnvelope_order hx).1.trans (hsign x hx).1,
      (fourthSourceEnvelope_order hx).2.trans (hsign x hx).2⟩
  · intro x hx
    unfold fourthSourceCombinedEnvelope
    split_ifs with hle
    · apply min_eq_left
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact ((fourthSourceEnvelope_order hx).1.mpr ((hsign x hx).1.mpr hlt)).le
      · subst x
        have hi:=fourthSourceEnvelopeDifference_identity hz.le
        rw [hzero,mul_zero] at hi
        linarith only [hi]
    · exact min_eq_right (((fourthSourceEnvelope_order hx).2.mpr
        ((hsign x hx).2.mpr (lt_of_not_ge hle))).le)


/-- The sharper envelope restores exactly the positive tail correction to the affine source. -/
theorem fourthSourceCombinedEnvelope_affine_correction {x : ℝ} (hx : 0 ≤ x) :
    fourthSourceCombinedEnvelope x=fourthSourceAffineEnvelope x-
      G x*max 0 (-chi x) := by
  have hi:=fourthSourceEnvelopeDifference_identity hx
  have hG:=sourceDefectPrimitive_pos hx
  unfold fourthSourceCombinedEnvelope
  by_cases hc : 0 ≤ chi x
  · have horder : fourthSourceAffineEnvelope x ≤ fourthSourceModelEnvelope x := by
      have hp:=mul_nonneg hG.le hc
      linarith only [hi,hp]
    rw [min_eq_left horder,max_eq_left (neg_nonpos.mpr hc),mul_zero,sub_zero]
  · have hchi : chi x < 0 := lt_of_not_ge hc
    have horder:=((fourthSourceEnvelope_order hx).2.mpr hchi).le
    rw [min_eq_right horder,max_eq_right (neg_nonneg.mpr hchi.le)]
    linarith only [hi]

end
end RHTower.ThetaCuspDefect
