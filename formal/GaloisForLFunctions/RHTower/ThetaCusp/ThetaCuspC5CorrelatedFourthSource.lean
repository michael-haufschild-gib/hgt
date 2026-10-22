import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CurrentAffineEnvelope
/-! Fourth-source transport preserving the actual coordinate rate times the
actual curvature defect. Its exact positive slack improves both earlier
source envelopes and passes through the complete current quadrature.
The sign of the resulting inner-current remainder remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "c2" => thetaCuspLogCurvatureJetTwo
local notation "coord" => thetaCuspLikelihoodCoordinate
local notation "B" => curvatureDefect
local notation "G" => sourceDefectPrimitive
local notation "F" => fun x => sourceDefectFactor (coord x)
local notation "f" => fun x => factorLogSlope (coord x)

/-- Literal source-coordinate transport rate, before replacing it by a constant. -/
def sourceFourthTransportRate (x : ℝ) : ℝ := 16+120/coord x+180/(coord x)^2
local notation "h" => sourceFourthTransportRate

theorem sourceFourthTransportRate_factor {x : ℝ} (hx : 0 ≤ x) :
    h x= -f x*(4+12/coord x) := by
  have hq:=(thetaCuspLikelihoodCoordinate_pos hx).ne'
  have hq3 : coord x+3 ≠ 0 := by have := thetaCuspLikelihoodCoordinate_pos hx; positivity
  unfold sourceFourthTransportRate factorLogSlope
  dsimp only
  field_simp [hq,hq3]
  ring

theorem sourceFourthTransportRate_pos {x : ℝ} (hx : 0 ≤ x) : 0 < h x := by
  have hq:=thetaCuspLikelihoodCoordinate_pos hx
  unfold sourceFourthTransportRate
  positivity

theorem sourceFourthTransportRate_lt_ceiling {x : ℝ} (hx : 0 ≤ x) : h x < 162 := by
  have hqa:=sourceCoordinate_actual_lower hx
  have hpi:=Real.pi_gt_d2
  have hq : (8/5:ℝ) ≤ coord x := by linarith only [hqa,hpi]
  have hq0:=thetaCuspLikelihoodCoordinate_pos hx
  have hid : (162-h x)*(coord x)^2=
      146*(coord x-8/5)^2+(1736/5)*(coord x-8/5)+44/25 := by
    unfold sourceFourthTransportRate
    field_simp [hq0.ne']
    ring
  have hp : 0 < (162-h x)*(coord x)^2 := by
    rw [hid]
    have hh:=sub_nonneg.mpr hq
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_right (sq_pos_of_pos hq0)).mp hp)

private theorem rate_times_primitive {x : ℝ} (hx : 0 ≤ x) : h x*G x= -f x*F x := by
  rw [sourceFourthTransportRate_factor hx,←sourceDefectPrimitive_mul_rate hx]
  ring

/-- Fourth-source envelope retaining the correlation of local rate and actual defect. -/
def sourceCorrelatedFourthEnvelope (x : ℝ) : ℝ := 4*c2 x+h x*B x

/-- Two literal positive reserves are retained in the exact source slack. -/
theorem sourceCorrelatedFourthEnvelope_slack {x : ℝ} (hx : 0 ≤ x) :
    sourceCorrelatedFourthEnvelope x-thetaCuspLogCurvatureJetFour x=
      defectSturmFlux x/F x+h x*sourcePrimitiveReserve x := by
  have hF:=sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hcoef:=rate_times_primitive hx
  calc
    sourceCorrelatedFourthEnvelope x-thetaCuspLogCurvatureJetFour x=
        sourceDefectJetSlope x+h x*B x := by
      unfold sourceCorrelatedFourthEnvelope thetaCuspLogCurvatureJetFour
        sourceDefectJetSlope thetaCuspLogCurvatureJetTwo
      ring
    _=defectSturmFlux x/F x+h x*sourcePrimitiveReserve x := by
      unfold defectSturmFlux sourcePrimitiveReserve normalizedSourceDefect
      dsimp only
      field_simp [hF.ne']
      linear_combination sourceDefectJet x*hcoef

theorem sourceCorrelatedFourthEnvelope_gt_actual {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogCurvatureJetFour x < sourceCorrelatedFourthEnvelope x := by
  apply sub_pos.mp
  rw [sourceCorrelatedFourthEnvelope_slack hx]
  exact add_pos (div_pos (defectSturmFlux_pos hx)
    (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)))
    (mul_pos (sourceFourthTransportRate_pos hx) (sourcePrimitiveReserve_pos hx))

theorem sourceCorrelatedFourthEnvelope_lt_affine {x : ℝ} (hx : 0 ≤ x) :
    sourceCorrelatedFourthEnvelope x < fourthSourceAffineEnvelope x := by
  have hp:=mul_pos (sub_pos.mpr (sourceFourthTransportRate_lt_ceiling hx)) (curvatureDefect_pos hx)
  unfold curvatureDefect at hp
  unfold sourceCorrelatedFourthEnvelope fourthSourceAffineEnvelope curvatureDefect
  nlinarith only [hp]

theorem sourceCorrelatedFourthEnvelope_lt_model {x : ℝ} (hx : 0 ≤ x) :
    sourceCorrelatedFourthEnvelope x < fourthSourceModelEnvelope x := by
  have hp:=mul_pos (sourceFourthTransportRate_pos hx)
    (sub_pos.mpr (curvatureDefect_lt_sourcePrimitive hx))
  have hcoef:=rate_times_primitive hx
  unfold sourceCorrelatedFourthEnvelope fourthSourceModelEnvelope
  dsimp only at hcoef ⊢
  nlinarith only [hp,hcoef]

/-- Source correlation improves even the pointwise best of the previous envelopes. -/
theorem sourceCorrelatedFourthEnvelope_lt_combined {x : ℝ} (hx : 0 ≤ x) :
    sourceCorrelatedFourthEnvelope x < fourthSourceCombinedEnvelope x :=
  lt_min (sourceCorrelatedFourthEnvelope_lt_affine hx) (sourceCorrelatedFourthEnvelope_lt_model hx)

open MeasureTheory
open scoped ContDiff
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "r" => shapeCurvatureSecond
local notation "v" => supersolutionCurvatureFourth
local notation "L" => currentMomentGapKernel

private theorem rate_continuousAt {x : ℝ} (hx : 0 ≤ x) : ContinuousAt h x := by
  have hq:=thetaCuspLikelihoodCoordinate_pos hx
  have hc:=(hasDerivAt_thetaCuspLikelihoodCoordinate x).continuousAt
  exact (continuousAt_const.add (continuousAt_const.div hc hq.ne')).add
    (continuousAt_const.div (hc.pow 2) (pow_ne_zero 2 hq.ne'))
private theorem correlated_continuousAt {x : ℝ} (hx : 0 ≤ x) :
    ContinuousAt sourceCorrelatedFourthEnvelope x :=
  ((hasDerivAt_thetaCuspLogCurvatureJetTwo x).continuousAt.const_mul 4).add
    ((rate_continuousAt hx).mul (hasDerivAt_curvatureDefect x).continuousAt)
private theorem affine_continuousAt (x : ℝ) : ContinuousAt fourthSourceAffineEnvelope x :=
  ((hasDerivAt_thetaCuspLogCurvatureJetTwo x).continuousAt.const_mul 166).sub
    ((hasDerivAt_thetaCuspLogCurvature x).continuousAt.const_mul 648)
private theorem reflection_continuousOn {j : ℝ → ℝ} (hf : ∀ x, 0 ≤ x → ContinuousAt j x)
    {u t : ℝ} (_ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (fun s => (j (u+s)+j (u-s))/2) (Icc 0 t) := by
  intro s hs
  exact (((hf (u+s) (by linarith [hs.1])).comp
    (continuous_const.add continuous_id).continuousAt).add
    ((hf (u-s) (by linarith [hs.2])).comp
      (continuous_const.sub continuous_id).continuousAt)).div_const 2 |>.continuousWithinAt
private theorem v_continuous (u : ℝ) : Continuous (v u) := by
  have hh:=(HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 6).continuous
  unfold supersolutionCurvatureFourth thetaCuspLogCurvatureJetFour
  fun_prop
private theorem L_continuous (u t : ℝ) : Continuous (L u t) := by
  unfold currentMomentGapKernel momentTransferGapKernel currentSourceGapKernel
  fun_prop

/-- The same source-coordinate correlation is retained at both reflected endpoints. -/
def reflectedCorrelatedFourthEnvelope (u s : ℝ) : ℝ :=
  (sourceCorrelatedFourthEnvelope (u+s)+sourceCorrelatedFourthEnvelope (u-s))/2

def currentCorrelatedSourceGain (u s : ℝ) : ℝ :=
  (fourthSourceAffineEnvelope (u+s)+fourthSourceAffineEnvelope (u-s))/2-
    reflectedCorrelatedFourthEnvelope u s

def currentCorrelatedSourceGap (u s : ℝ) : ℝ := reflectedCorrelatedFourthEnvelope u s-v u s

private theorem gain_continuousOn {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (currentCorrelatedSourceGain u) (Icc 0 t) :=
  (reflection_continuousOn (fun x _ => affine_continuousAt x) ht htu).sub
    (reflection_continuousOn (fun _ hx => correlated_continuousAt hx) ht htu)
private theorem gap_continuousOn {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (currentCorrelatedSourceGap u) (Icc 0 t) :=
  (reflection_continuousOn (fun _ hx => correlated_continuousAt hx) ht htu).sub
    (v_continuous u).continuousOn

theorem currentCorrelatedSourceGain_pos {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    0 < currentCorrelatedSourceGain u s := by
  have hp:=sourceCorrelatedFourthEnvelope_lt_affine (x:=u+s) (by linarith)
  have hm:=sourceCorrelatedFourthEnvelope_lt_affine (sub_nonneg.mpr hsu)
  unfold currentCorrelatedSourceGain reflectedCorrelatedFourthEnvelope
  linarith only [hp,hm]

theorem currentCorrelatedSourceGap_pos {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    0 < currentCorrelatedSourceGap u s := by
  have hp:=sourceCorrelatedFourthEnvelope_gt_actual (x:=u+s) (by linarith)
  have hm:=sourceCorrelatedFourthEnvelope_gt_actual (sub_nonneg.mpr hsu)
  unfold currentCorrelatedSourceGap reflectedCorrelatedFourthEnvelope supersolutionCurvatureFourth
  linarith only [hp,hm]

private theorem source_integral_pos {u t : ℝ} (ht : 0 < t) {j : ℝ → ℝ}
    (hc : ContinuousOn j (Icc 0 t)) (hp : ∀ s ∈ Icc 0 t, 0 < j s) :
    0 < ∫ s in 0..t, L u t s*j s := by
  have hW:=enrichedCurrentPeanoWeight_pos u ht
  have heta:=currentMomentTransfer_admitted u t
  have hnonneg (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤ L u t s*j s :=
    mul_nonneg (momentTransferGapKernel_nonneg hW ht hs.1 hs.2 heta) (hp s hs).le
  have hpoint : 0 < L u t (t/2)*j (t/2) :=
    mul_pos (momentTransferGapKernel_pos hW ht (by linarith) (by linarith) heta)
      (hp (t/2) ⟨by linarith,by linarith⟩)
  have hh:=intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (show ContinuousOn (fun _ : ℝ => (0:ℝ)) (Icc 0 t) from continuousOn_const)
    ((L_continuous u t).continuousOn.mul hc)
    (fun s hs => hnonneg s ⟨hs.1.le,hs.2⟩) ⟨t/2,⟨by linarith,by linarith⟩,hpoint⟩
  simpa only [intervalIntegral.integral_zero,Pi.mul_apply] using hh

/-- The full first-order current receives the retained positive correlation gain. -/
def currentCorrelatedSourceRemainder (u t : ℝ) : ℝ :=
  currentMomentAffineRemainder u t+∫ s in 0..t, L u t s*currentCorrelatedSourceGain u s

theorem currentMomentAffineRemainder_lt_correlated {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentAffineRemainder u t < currentCorrelatedSourceRemainder u t := by
  have hh:=source_integral_pos (u:=u) ht (gain_continuousOn ht.le htu)
    (fun s hs => currentCorrelatedSourceGain_pos hs.1 (hs.2.trans htu))
  unfold currentCorrelatedSourceRemainder
  linarith only [hh]

/-- Exact current with its actual source correlation and both remaining positive reserves. -/
theorem enrichedClockCurrent_correlated_source_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    E u t*enrichedClockCurrent u t=currentCorrelatedSourceRemainder u t+
      E u t*(enrichedPeanoDeltaCoefficient u t-currentMomentTransfer u t)*
        (curvatureShapeDelta u t-(curvatureShapeBeta u t)^2/curvatureShapeAlpha u t)+
      (∫ s in 0..t, L u t s*currentCorrelatedSourceGap u s) := by
  have hI : IntervalIntegrable (fun s => L u t s*currentCorrelatedSourceGain u s) volume 0 t :=
    ((L_continuous u t).continuousOn.mul (gain_continuousOn ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hJ : IntervalIntegrable (fun s => L u t s*currentCorrelatedSourceGap u s) volume 0 t :=
    ((L_continuous u t).continuousOn.mul (gap_continuousOn ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hid : (fun s => L u t s*currentAffineSourceSlack u s)=
      (fun s => L u t s*currentCorrelatedSourceGain u s+L u t s*currentCorrelatedSourceGap u s) := by
    funext s
    unfold currentAffineSourceSlack currentCorrelatedSourceGain currentCorrelatedSourceGap
      fourthSourceAffineEnvelope shapeCurvatureSecond completedCurvatureEven
    ring
  rw [enrichedClockCurrent_affine_moment_identity u ht,hid,intervalIntegral.integral_add hI hJ]
  unfold currentCorrelatedSourceRemainder
  ring

theorem currentCorrelatedSourceRemainder_lt_complete {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentCorrelatedSourceRemainder u t < E u t*enrichedClockCurrent u t := by
  have hgap:=source_integral_pos (u:=u) ht (gap_continuousOn ht.le htu)
    (fun s hs => currentCorrelatedSourceGap_pos hs.1 (hs.2.trans htu))
  have hE : 0 < E u t := by
    rw [completedDecayEvenPrimitive_eq]
    exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
  have hcoef:=sub_nonneg.mpr (currentMomentTransfer_le_delta u t)
  have hSchur:=sub_pos.mpr (curvatureShapeDelta_gt_schur ht htu)
  have hnonneg : 0 ≤ E u t*(enrichedPeanoDeltaCoefficient u t-currentMomentTransfer u t)*
      (curvatureShapeDelta u t-(curvatureShapeBeta u t)^2/curvatureShapeAlpha u t) := by positivity
  rw [enrichedClockCurrent_correlated_source_identity ht htu]
  linarith only [hgap,hnonneg]

end
end RHTower.ThetaCuspDefect
