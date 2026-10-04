import GaloisForLFunctions.RHTower.ThetaCuspC5CurrentSchurCoupling
/-! Admissible transfer of a signed source moment in the complete enriched current.
The transfer keeps a nonnegative Schur term and a strictly positive source-gap
integral. Its first-source model remainder strictly improves the untransferred
Schur/model comparison. Positivity of that remainder remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section

/-- Backward source-gap kernel after transferring a second-source moment. -/
def momentTransferGapKernel (W eta t s : ℝ) : ℝ :=
  W*currentSourceGapKernel t s-eta*t^2*(t^2-s^2)/2

/-- Exact boundary decomposition, including the endpoint reserve. -/
theorem momentTransferGapKernel_boundary (W eta : ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    momentTransferGapKernel W eta t s=
      W*(s^2*(1459*t^2+41*s^2)/60+16*s^4*(t-s)/(15*t))+
        ((1053/10)*W-eta)*t^2*(t^2-s^2)/2 := by
  unfold momentTransferGapKernel currentSourceGapKernel
  field_simp [ht]
  ring

private theorem square_gap {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : 0 ≤ t^2-s^2 := by
  have hh:=mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ t+s by linarith only [hs,hst])
  nlinarith only [hh]

theorem momentTransferGapKernel_nonneg {W eta t s : ℝ} (hW : 0 < W) (ht : 0 < t)
    (hs : 0 ≤ s) (hst : s ≤ t) (hbudget : eta ≤ (1053/10)*W) :
    0 ≤ momentTransferGapKernel W eta t s := by
  rw [momentTransferGapKernel_boundary W eta ht.ne']
  have hts:=sub_nonneg.mpr hst
  have hgap:=square_gap hs hst
  have hB:=sub_nonneg.mpr hbudget
  positivity

theorem momentTransferGapKernel_pos {W eta t s : ℝ} (hW : 0 < W) (ht : 0 < t)
    (hs : 0 < s) (hst : s ≤ t) (hbudget : eta ≤ (1053/10)*W) :
    0 < momentTransferGapKernel W eta t s := by
  rw [momentTransferGapKernel_boundary W eta ht.ne']
  have hts:=sub_nonneg.mpr hst
  have hgap:=square_gap hs.le hst
  have hB:=sub_nonneg.mpr hbudget
  positivity

/-- Necessary and sufficient transfer admission, not an independent clock assumption. -/
theorem momentTransferGapKernel_nonneg_iff {W eta t : ℝ} (hW : 0 < W) (ht : 0 < t) :
    (∀ s∈Icc 0 t, 0 ≤ momentTransferGapKernel W eta t s) ↔ eta ≤ (1053/10)*W := by
  constructor
  · intro hh
    have hz:=hh 0 ⟨le_rfl,ht.le⟩
    rw [momentTransferGapKernel_boundary W eta ht.ne' 0] at hz
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_pow (by decide : (4:ℕ) ≠ 0),
      mul_zero,zero_mul,zero_div,zero_add,add_zero,sub_zero] at hz
    have hid : ((1053/10)*W-eta)*t^2*t^2/2=((1053/10)*W-eta)*(t^4/2) := by ring
    rw [hid] at hz
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (by positivity : 0 < t^4/2)).mp hz)
  · intro hh s hs
    exact momentTransferGapKernel_nonneg hW ht hs.1 hs.2 hh

local notation "E" => completedDecayEvenPrimitive
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "w" => quadratureCurvatureThird
local notation "a" => curvatureShapeAlpha
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "W" => enrichedCurrentPeanoWeight
local notation "Delta" => enrichedPeanoDeltaCoefficient
local notation "G" => reflectedSourceModelGap
local notation "rho" => reflectedSourceModelGapDensity

/-- Actual largest transfer preserving both source-gap and Schur contributions. -/
def currentMomentTransfer (u t : ℝ) : ℝ := min (Delta u t) ((1053/10)*W u t)
local notation "eta" => currentMomentTransfer

theorem currentMomentTransfer_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 0 < eta u t := by
  have hW:=enrichedCurrentPeanoWeight_pos u ht
  exact lt_min (enrichedPeanoDeltaCoefficient_pos ht htu) (by positivity)

theorem currentMomentTransfer_le_delta (u t : ℝ) : eta u t ≤ Delta u t := min_le_left _ _
theorem currentMomentTransfer_admitted (u t : ℝ) : eta u t ≤ (1053/10)*W u t := min_le_right _ _

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

/-- The second source and slope are linked by the same signed third-source moment. -/
theorem curvatureShapeDelta_sub_beta_moment (u : ℝ) {t : ℝ} (ht : 0 < t) :
    E u t*(q u t-b u t)=t^2*(∫ s in 0..t, s*w u s) := by
  have hd (s : ℝ) : HasDerivAt (fun zv=>zv*r u zv-p u zv) (s*w u s) s := by
    convert! ((hasDerivAt_id s).mul (r_deriv u s)).sub (p_deriv u s) using 1
    dsimp only [id_eq]
    ring
  have hc : Continuous (fun s=>s*w u s) := continuous_id.mul (w_continuous u)
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s) (hc.intervalIntegrable 0 t)
  simp only [zero_mul,shapeCurvatureSlope,add_zero,sub_zero,sub_self,zero_div] at hi
  rw [hi]
  unfold curvatureShapeDelta curvatureShapeBeta shapeCurvatureSlope
  field_simp [(E_pos u ht).ne']

/-- The signed kernel used for the actual model quadrature after transfer. -/
def currentMomentKernel (u t s : ℝ) : ℝ := W u t*coupledShapeKernel t s-eta u t*t^2*s

def currentMomentGapKernel (u t s : ℝ) : ℝ := momentTransferGapKernel (W u t) (eta u t) t s

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
private theorem gap_continuous {u t : ℝ} (_ht : 0 ≤ t) (htu : t ≤ u) : ContinuousOn (G u) (Icc 0 t) := by
  intro s hs
  exact (hasDerivAt_reflectedSourceModelGap hs.1 (hs.2.trans htu)).continuousAt.continuousWithinAt
private theorem density_continuous {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (rho u) (Icc 0 t) := by
  have hc {x : ℝ} (hx : 0 ≤ x) : ContinuousAt sourceModelGapDensity x :=
    (hasDerivAt_sourceDefectJetSlope x).continuousAt.sub
      ((hasDerivAt_factorLogSlope_coordinate hx).continuousAt.mul
        (hasDerivAt_sourceDefectFactor_coordinate hx).continuousAt)
  intro s hs
  exact (((hc (show 0 ≤ u+s by linarith [hs.1])).comp
    (continuous_const.add continuous_id).continuousAt).add
    ((hc (show 0 ≤ u-s by linarith [hs.2])).comp
      (continuous_const.sub continuous_id).continuousAt)).div_const 2 |>.continuousWithinAt

/-- The source-gap integral remains strictly positive at the admitted transfer. -/
theorem currentMomentGapKernel_integral_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < ∫ s in 0..t, currentMomentGapKernel u t s*rho u s := by
  have hL : Continuous (currentMomentGapKernel u t) :=
    continuous_iff_continuousAt.mpr (fun s=>(momentGap_deriv u t s).continuousAt)
  have hW:=enrichedCurrentPeanoWeight_pos u ht
  have hB:=currentMomentTransfer_admitted u t
  have hnonneg (s : ℝ) (hs : s∈Icc 0 t) : 0 ≤ currentMomentGapKernel u t s*rho u s :=
    mul_nonneg (momentTransferGapKernel_nonneg hW ht hs.1 hs.2 hB)
      (reflectedSourceModelGapDensity_pos hs.1 (hs.2.trans htu)).le
  have hpoint : 0 < currentMomentGapKernel u t (t/2)*rho u (t/2) :=
    mul_pos (momentTransferGapKernel_pos hW ht (by linarith) (by linarith) hB)
      (reflectedSourceModelGapDensity_pos (by linarith) (by linarith))
  have hi:=intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (show ContinuousOn (fun _ : ℝ=>(0:ℝ)) (Icc 0 t) from continuousOn_const)
    (hL.continuousOn.mul (density_continuous ht.le htu))
    (fun s hs=>hnonneg s ⟨hs.1.le,hs.2⟩)
    ⟨t/2,⟨by linarith,by linarith⟩,hpoint⟩
  simpa only [intervalIntegral.integral_zero,Pi.mul_apply] using hi

private theorem gap_integral_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (∫ s in 0..t, currentMomentKernel u t s*G u s)+25*W u t*t^4*G u t=
      ∫ s in 0..t, currentMomentGapKernel u t s*rho u s := by
  have hL : Continuous (currentMomentGapKernel u t) :=
    continuous_iff_continuousAt.mpr (fun s=>(momentGap_deriv u t s).continuousAt)
  have hI : IntervalIntegrable (fun s=>currentMomentGapKernel u t s*rho u s) volume 0 t :=
    (hL.continuousOn.mul (density_continuous ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hJ : IntervalIntegrable (fun s=>currentMomentKernel u t s*G u s) volume 0 t :=
    ((kernel_continuous u t).continuousOn.mul (gap_continuous ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hd (s : ℝ) (hs : s∈uIcc 0 t) :
      HasDerivAt (fun zv=>currentMomentGapKernel u t zv*G u zv)
        (currentMomentGapKernel u t s*rho u s-currentMomentKernel u t s*G u s) s := by
    have hs' : s∈Icc 0 t := uIcc_of_le ht.le ▸ hs
    convert! (momentGap_deriv u t s).mul
      (hasDerivAt_reflectedSourceModelGap hs'.1 (hs'.2.trans htu)) using 1
    ring
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hI.sub hJ)
  rw [intervalIntegral.integral_sub hI hJ] at hi
  have hzero : G u 0=0 := by simp [reflectedSourceModelGap]
  have hend : currentMomentGapKernel u t t=25*W u t*t^4 := by
    unfold currentMomentGapKernel momentTransferGapKernel currentSourceGapKernel
    ring
  rw [hzero,hend,mul_zero,sub_zero] at hi
  linarith only [hi]

def currentMomentActualQuadrature (u t : ℝ) : ℝ :=
  (∫ s in 0..t, currentMomentKernel u t s*w u s)+25*W u t*t^4*w u t

def currentMomentModelQuadrature (u t : ℝ) : ℝ :=
  (∫ s in 0..t, currentMomentKernel u t s*modelQuadratureSource u s)+
    25*W u t*t^4*modelQuadratureSource u t

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

private theorem modelQuadrature_eq {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentActualQuadrature u t+
      (∫ s in 0..t, currentMomentGapKernel u t s*rho u s)=currentMomentModelQuadrature u t := by
  have hI : IntervalIntegrable (fun s=>currentMomentKernel u t s*w u s) volume 0 t :=
    ((kernel_continuous u t).mul (w_continuous u)).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s=>currentMomentKernel u t s*G u s) volume 0 t :=
    ((kernel_continuous u t).continuousOn.mul (gap_continuous ht.le htu)).intervalIntegrable_of_Icc ht.le
  have hid : (fun s=>currentMomentKernel u t s*modelQuadratureSource u s)=
      (fun s=>currentMomentKernel u t s*w u s+currentMomentKernel u t s*G u s) := by
    funext s
    rw [←quadratureCurvatureThird_add_modelGap]
    ring
  rw [←gap_integral_identity ht htu]
  unfold currentMomentActualQuadrature currentMomentModelQuadrature
  rw [hid,intervalIntegral.integral_add hI hJ,←quadratureCurvatureThird_add_modelGap u t]
  ring

/-- First-source remainder; the actual second and third derivatives have been eliminated. -/
def currentMomentModelRemainder (u t : ℝ) : ℝ :=
  E u t*enrichedCurrentLowerJetRemainder u t+E u t*eta u t*b u t+
    E u t*(Delta u t-eta u t)*(b u t)^2/a u t+
      W u t*(64*(curvatureShapeAction u t-thetaCuspReflectedLogAction u t)^2/
        (t*thetaCuspReflectedLogAction u t))-currentMomentModelQuadrature u t

/-- Exact complete current with both retained positive source contributions. -/
theorem enrichedClockCurrent_moment_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    E u t*enrichedClockCurrent u t=currentMomentModelRemainder u t+
      E u t*(Delta u t-eta u t)*(q u t-(b u t)^2/a u t)+
        (∫ s in 0..t, currentMomentGapKernel u t s*rho u s) := by
  have hP:=enrichedClockCurrent_peano_identity u ht
  rw [enrichedCurrentPeanoRemainder_delta_identity] at hP
  have hA:=actualQuadrature_eq u t
  have hQ:=curvatureShapeDelta_sub_beta_moment u ht
  have hM:=modelQuadrature_eq ht htu
  unfold currentMomentModelRemainder
  linear_combination hP+hA+eta u t*hQ-hM

/-- No source-sign premise remains in this complete-current lower comparison. -/
theorem currentMomentModelRemainder_lt_complete {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentModelRemainder u t < E u t*enrichedClockCurrent u t := by
  have hsource:=currentMomentGapKernel_integral_pos ht htu
  have hSchur:=sub_pos.mpr (curvatureShapeDelta_gt_schur ht htu)
  have hcoef:=sub_nonneg.mpr (currentMomentTransfer_le_delta u t)
  have hE:=E_pos u ht
  have hnonneg : 0 ≤ E u t*(Delta u t-eta u t)*(q u t-(b u t)^2/a u t) := by positivity
  rw [enrichedClockCurrent_moment_identity ht htu]
  linarith only [hsource,hnonneg]


private theorem model_continuous {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    ContinuousOn (modelQuadratureSource u) (Icc 0 t) := by
  have hid : modelQuadratureSource u=(fun s=>w u s+G u s) := by
    funext s
    exact (quadratureCurvatureThird_add_modelGap u s).symm
  rw [hid]
  exact (w_continuous u).continuousOn.add (gap_continuous ht htu)

private theorem modelQuadrature_transfer {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentModelQuadrature u t=W u t*currentModelSourceQuadrature u t-
      eta u t*t^2*(∫ s in 0..t, s*modelQuadratureSource u s) := by
  have hK : Continuous (coupledShapeKernel t) := by unfold coupledShapeKernel; fun_prop
  have hM:=model_continuous ht.le htu
  have hI : IntervalIntegrable (fun s=>W u t*(coupledShapeKernel t s*modelQuadratureSource u s)) volume 0 t :=
    (continuousOn_const.mul (hK.continuousOn.mul hM)).intervalIntegrable_of_Icc ht.le
  have hJ : IntervalIntegrable (fun s=>(eta u t*t^2)*(s*modelQuadratureSource u s)) volume 0 t :=
    (continuousOn_const.mul (continuous_id.continuousOn.mul hM)).intervalIntegrable_of_Icc ht.le
  have hid : (fun s=>currentMomentKernel u t s*modelQuadratureSource u s)=
      (fun s=>W u t*(coupledShapeKernel t s*modelQuadratureSource u s)-
        (eta u t*t^2)*(s*modelQuadratureSource u s)) := by
    funext s
    unfold currentMomentKernel
    ring
  unfold currentMomentModelQuadrature currentModelSourceQuadrature
  rw [hid,intervalIntegral.integral_sub hI hJ,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

private theorem modelMoment_split {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (∫ s in 0..t, s*modelQuadratureSource u s)=
      (∫ s in 0..t, s*w u s)+(∫ s in 0..t, s*G u s) := by
  have hI : IntervalIntegrable (fun s=>s*w u s) volume 0 t :=
    (continuous_id.mul (w_continuous u)).intervalIntegrable 0 t
  have hJ : IntervalIntegrable (fun s=>s*G u s) volume 0 t :=
    (continuous_id.continuousOn.mul (gap_continuous ht.le htu)).intervalIntegrable_of_Icc ht.le
  rw [←intervalIntegral.integral_add hI hJ]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [←quadratureCurvatureThird_add_modelGap]
  ring

/-- The same model quadrature with the untransferred Schur substitution. -/
def currentSchurModelRemainder (u t : ℝ) : ℝ :=
  E u t*enrichedCurrentLowerJetRemainder u t+E u t*Delta u t*(b u t)^2/a u t+
    W u t*(64*(curvatureShapeAction u t-thetaCuspReflectedLogAction u t)^2/
      (t*thetaCuspReflectedLogAction u t))-W u t*currentModelSourceQuadrature u t

/-- The retained improvement is an actual Schur gap and a source-gap moment. -/
theorem currentMomentModelRemainder_improvement {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentMomentModelRemainder u t-currentSchurModelRemainder u t=
      eta u t*(E u t*(q u t-(b u t)^2/a u t)+t^2*(∫ s in 0..t, s*G u s)) := by
  have hM:=modelQuadrature_transfer ht htu
  have hQ:=curvatureShapeDelta_sub_beta_moment u ht
  have hS:=modelMoment_split ht htu
  unfold currentMomentModelRemainder currentSchurModelRemainder
  linear_combination -hM-eta u t*hQ+eta u t*t^2*hS

/-- Strict improvement throughout the physical chamber, without a source-sign premise. -/
theorem currentSchurModelRemainder_lt_moment {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    currentSchurModelRemainder u t < currentMomentModelRemainder u t := by
  have hI : 0 ≤ ∫ s in 0..t, s*G u s := by
    apply intervalIntegral.integral_nonneg ht.le
    intro s hs
    have hG : 0 ≤ G u s := by
      rw [reflectedSourceModelGap_integral hs.1 (hs.2.trans htu)]
      apply intervalIntegral.integral_nonneg hs.1
      intro x hx
      exact (reflectedSourceModelGapDensity_pos hx.1 (hx.2.trans (hs.2.trans htu))).le
    exact mul_nonneg hs.1 hG
  have hE:=E_pos u ht
  have hSchur:=sub_pos.mpr (curvatureShapeDelta_gt_schur ht htu)
  have hEta:=currentMomentTransfer_pos ht htu
  apply sub_pos.mp
  rw [currentMomentModelRemainder_improvement ht htu]
  positivity

end
end RHTower.ThetaCuspDefect
