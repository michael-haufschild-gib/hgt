import GaloisForLFunctions.RHTower.ThetaFinitePairRegularizedBulk
import GaloisForLFunctions.RHTower.ThetaFinitePairBoundaryPackets

/-! The finite prefix of the actual signed current has a node limit obtained
from its compact bulk primitive and retained endpoint flux. No dominated
convergence assertion for the singular current quotient is used. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "s" => ThetaSturmCrossing.secant
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem cont_v : Continuous v := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJet t).continuousAt
private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

def diagonalFlux (x t : ℝ) : ℝ :=
  diagonalWeight x t*diagonalSpeed x t*momentExtension x t
def centerBaseFlux (t : ℝ) : ℝ := diagonalWeight 0 t*(t*c t-p t)/2
def centerFluxVariation (t : ℝ) : ℝ := diagonalWeight 0 t*
  (centerMomentVariation t/2-p t*(t*c t-p t)-c 0*(t*c t-p t)/(2*p t))

private theorem diagonalWeight_hasDerivAt_time (x t : ℝ) :
    HasDerivAt (diagonalWeight x) (-2*p (t+x)*diagonalWeight x t) t := by
  have hk := (actualSource_hasDerivAt (t+x)).comp t ((hasDerivAt_id t).add_const x)
  convert! (hk.pow 2).div_const (k x^2) using 1
  dsimp only [Pi.pow_apply,Function.comp_apply,id_eq]
  simp only [diagonalWeight,mul_one]
  ring

private theorem diagonalSpeed_hasDerivAt_time {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    HasDerivAt (diagonalSpeed x) (diagonalSpeedTimeJet x t) t := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp t ((hasDerivAt_id t).add_const x)
  convert! ((hasDerivAt_const t (p x)).div (hp.const_mul 2)
    (mul_ne_zero (by norm_num) (ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx)).ne')).neg.const_add (1/2) using 1
  dsimp only [Function.comp_apply,id_eq]
  simp only [diagonalSpeedTimeJet,mul_one,zero_mul,zero_sub,neg_div,neg_neg]
  ring

private theorem momentExtension_hasDerivAt_time {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (momentExtension x)
      ((x+2*t)*s x t*normalizedPacket x t+
        (ThetaSturmCrossing.secantJet x t+(p t+p (t+x))*s x t)*transportPrimitive x t) t := by
  rw [show momentExtension x=matchedPacket x from funext (momentExtension_eq hx.ne')]
  convert! matchedPacket_hasDerivAt hx t using 1
  simp only [matchedPacket,ThetaSturmCrossing.forcing,ThetaSturmCrossing.intercept,ThetaSturmCrossing.secant]
  field_simp [hx.ne']
  ring

/-- The flux derivative retains the complete canonical current, including its speed jet. -/
theorem diagonalFlux_hasDerivAt_time {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    HasDerivAt (diagonalFlux x)
      (regularizedBulk x t-diagonalWeight x t*finiteCanonicalCurrent x x t) t := by
  have h := ((diagonalWeight_hasDerivAt_time x t).mul
    (diagonalSpeed_hasDerivAt_time hx ht)).mul (momentExtension_hasDerivAt_time hx t)
  convert! h using 1
  dsimp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Function.comp_apply]
  rw [finiteCanonicalCurrent_diagonal hx ht]
  unfold regularizedBulk diagonalPacketCoefficient diagonalPrimitiveCoefficient
  rw [primitiveExtension_eq hx.ne',momentExtension_eq hx.ne',
    smoothSecant_eq hx.ne',smoothSecantTimeJet_eq hx.ne']
  unfold matchedPacket
  have hs : 2*p (t+x)*diagonalSpeed x t=p (t+x)-p x := by
    unfold diagonalSpeed
    field_simp [(ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx)).ne']
  linear_combination diagonalWeight x t*(normalizedPacket x t+s x t*transportPrimitive x t)*hs

private theorem current_continuousOn {x : ℝ} (hx : 0 < x) :
    ContinuousOn (fun t => finiteCanonicalCurrent x x t) (Ici 0) := by
  intro t ht
  have hp : p (t+x)+p (t+x) ≠ 0 :=
    (add_pos (ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx))
      (ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx))).ne'
  have ha := (normalizedPacket_hasDerivAt hx t).continuousAt
  have hb := (transportPrimitive_hasDerivAt hx t).continuousAt
  have hpt : ContinuousAt (fun u => p (u+x)) t :=
    (cont_p.comp (continuous_id.add continuous_const)).continuousAt
  have hct : ContinuousAt (fun u => c (u+x)) t :=
    (cont_c.comp (continuous_id.add continuous_const)).continuousAt
  have hpp := cont_p.continuousAt (x := t)
  have hcc := cont_c.continuousAt (x := t)
  apply ContinuousAt.continuousWithinAt
  unfold finiteCanonicalCurrent matchedCurrentCoefficient primitiveCurrentCoefficient
    finiteCanonicalSpeed finiteCanonicalSpeedJet ThetaSturmCrossing.secant ThetaSturmCrossing.secantJet
  fun_prop (disch := positivity)

theorem integral_diagonalCurrent_eq {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, diagonalWeight x t*finiteCanonicalCurrent x x t)=
      (∫ t in (0:ℝ)..T, regularizedBulk x t)-diagonalFlux x T := by
  have hG : IntervalIntegrable (regularizedBulk x) volume 0 T :=
    (regularizedBulk_continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hI : IntervalIntegrable (fun t => diagonalWeight x t*finiteCanonicalCurrent x x t) volume 0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact ((diagonalWeight_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.mul
      ((current_continuousOn hx).mono (fun _ ht => ht.1)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := T) (f := diagonalFlux x)
    (fun t ht => diagonalFlux_hasDerivAt_time hx
      ((show t ∈ Icc 0 T by simpa only [uIcc_of_le hT] using ht).1))
    (hG.sub hI)
  have hz : diagonalFlux x 0=0 := by
    unfold diagonalFlux diagonalSpeed
    simp only [zero_add]
    field_simp [(ThetaSturmCrossing.slope_pos hx).ne']
    ring
  rw [intervalIntegral.integral_sub hG hI,hz,sub_zero] at he
  linarith only [he]

theorem centerBaseFlux_hasDerivAt (t : ℝ) :
    HasDerivAt centerBaseFlux (regularizedBulk 0 t) t := by
  have hj := ((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogCurvature t)).sub
    (hasDerivAt_thetaCuspLogDecaySlope t)
  convert! ((diagonalWeight_hasDerivAt_time 0 t).mul hj).div_const 2 using 1
  dsimp only [Pi.mul_apply,Pi.sub_apply]
  simp only [regularizedBulk_zero,add_zero,id_eq,one_mul]
  ring

theorem integral_regularizedBulk_zero (T : ℝ) :
    (∫ t in (0:ℝ)..T, regularizedBulk 0 t)=centerBaseFlux T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := T)
    (fun t _ => centerBaseFlux_hasDerivAt t)
    ((regularizedBulk_continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 T)
  simpa only [centerBaseFlux,p_zero,zero_mul,sub_zero,mul_zero,zero_div] using h

private theorem diagonalSpeed_hasDerivAt_node_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalSpeed x t) (-c 0/(2*p t)) 0 := by
  have hp : HasDerivAt (fun x => p (t+x)) (c t) 0 := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope (t+0)).comp 0
      ((hasDerivAt_id (0:ℝ)).const_add t) using 1
    simp only [add_zero,mul_one]
  have h := ((hasDerivAt_thetaCuspLogDecaySlope 0).div (hp.const_mul 2)
    (show 2*p (t+0) ≠ 0 by simpa only [add_zero] using
      (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (ThetaSturmCrossing.slope_pos ht).ne'))).neg.const_add (1/2)
  convert! h using 1
  simp only [p_zero,add_zero,zero_mul,sub_zero]
  field_simp [(ThetaSturmCrossing.slope_pos ht).ne']

theorem diagonalFlux_zero (t : ℝ) : diagonalFlux 0 t=centerBaseFlux t := by
  simp only [diagonalFlux,diagonalSpeed,p_zero,zero_div,sub_zero,momentExtension_zero,centerBaseFlux]
  ring

theorem diagonalFlux_hasDerivAt_node_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalFlux x t) (centerFluxVariation t) 0 := by
  convert! ((diagonalWeight_hasDerivAt 0 t).mul (diagonalSpeed_hasDerivAt_node_zero ht)).mul
    (momentExtension_hasDerivAt 0 t) using 1
  dsimp only [Pi.mul_apply]
  simp only [diagonalSpeed,p_zero,zero_div,sub_zero,add_zero,mul_zero,
    momentExtension_zero,momentExtensionJet_zero,centerFluxVariation]
  ring

/-- The actual current prefix has an exact boundary-sensitive node limit. -/
theorem integral_diagonalCurrent_ratio_limit {T : ℝ} (hT : 0 < T) :
    Tendsto (fun x => (∫ t in (0:ℝ)..T,
      diagonalWeight x t*finiteCanonicalCurrent x x t)/x) (𝓝[>] 0)
      (𝓝 ((∫ t in (0:ℝ)..T, centerBulkVariation t)-centerFluxVariation T)) := by
  have h := (integral_regularizedBulk_hasDerivAt_zero T).sub
    (diagonalFlux_hasDerivAt_node_zero hT)
  have hl := h.tendsto_slope_zero_right
  simp only [Pi.sub_apply,zero_add,integral_regularizedBulk_zero,diagonalFlux_zero,sub_self,
    sub_zero,smul_eq_mul,inv_mul_eq_div] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [integral_diagonalCurrent_eq hx hT.le]

/-- The limiting endpoint flux retains exactly half the positive boundary mass. -/
theorem centerFluxVariation_boundary_limit :
    Tendsto centerFluxVariation (𝓝[>] 0) (𝓝 (centerBoundaryMass/2)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hp : Tendsto p (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa only [p_zero] using (cont_p.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (c 0)) := (cont_c.tendsto 0).mono_left nhdsWithin_le_nhds
  have hv : Tendsto v (𝓝[>] 0) (𝓝 (v 0)) := (cont_v.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb : Tendsto centerPrimitiveVariation (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa only [centerPrimitiveVariation_zero] using
      (centerPrimitiveVariation_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hW : Tendsto (diagonalWeight 0) (𝓝[>] 0) (𝓝 (1:ℝ)) := by
    have hwc : Continuous (diagonalWeight 0) := diagonalWeight_continuous.comp
      (show Continuous (fun t : ℝ => ((0:ℝ),t)) from continuous_const.prodMk continuous_id)
    have hh : Tendsto (diagonalWeight 0) (𝓝[>] 0) (𝓝 (diagonalWeight 0 0)) :=
      (hwc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [diagonalWeight,add_zero,div_self (pow_ne_zero 2
      (thetaCuspFullSource_pos_all 0).ne')] using hh
  have hC : Tendsto centerMomentVariation (𝓝[>] 0) (𝓝 centerBoundaryMass) := by
    have hα : Tendsto (fun _ : ℝ => I/J) (𝓝[>] 0) (𝓝 (I/J)) := tendsto_const_nhds
    have hh := (((hα.sub ((hc.add (hp.pow 2)).div_const 2)).add
      ((ht.mul hv).div_const 2)).add (hc.mul hb))
    convert! hh using 1
    simp only [centerBoundaryMass,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,
      zero_mul,zero_div,mul_zero]
  have hlin : Tendsto (fun t => p t/t) (𝓝[>] 0) (𝓝 (c 0)) := by
    simpa only [zero_add,p_zero,sub_zero,smul_eq_mul,inv_mul_eq_div] using
      (hasDerivAt_thetaCuspLogDecaySlope 0).tendsto_slope_zero_right
  have hj : Tendsto (fun t => (t*c t-p t)/p t) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    have hh := (hc.div hlin (thetaCuspLogCurvature_pos 0).ne').sub_const 1
    simp only [div_self (thetaCuspLogCurvature_pos 0).ne',sub_self] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht'
    have ht0 : 0 < t := ht'
    dsimp only [Pi.div_apply]
    field_simp [ht0.ne',(ThetaSturmCrossing.slope_pos ht0).ne']
  have hh := hW.mul (((hC.div_const 2).sub (hp.mul ((ht.mul hc).sub hp))).sub
    (hj.const_mul (c 0/2)))
  convert! hh using 1
  · funext t
    unfold centerFluxVariation
    ring
  · ring

private theorem centerBulkVariation_continuous : Continuous centerBulkVariation := by
  have hc := regularizedBulkJet_continuous.comp
    (show Continuous (fun t : ℝ => ((0:ℝ),t)) from continuous_const.prodMk continuous_id)
  convert! hc using 1
  funext t
  exact (regularizedBulkJet_zero t).symm

theorem centerPrefixVariation_boundary_limit :
    Tendsto (fun T => (∫ t in (0:ℝ)..T, centerBulkVariation t)-centerFluxVariation T)
      (𝓝[>] 0) (𝓝 (-centerBoundaryMass/2)) := by
  have hc : Continuous (fun T : ℝ => ∫ t in (0:ℝ)..T, centerBulkVariation t) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun _ t : ℝ => centerBulkVariation t) (μ := volume)
      (centerBulkVariation_continuous.comp continuous_snd) continuous_id
  have hh := ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).sub centerFluxVariation_boundary_limit
  simpa only [intervalIntegral.integral_same,zero_sub,neg_div] using hh

/-- Actual negative boundary mass dominates every sufficiently short fixed prefix
once the diagonal nodes are sufficiently close to the center. -/
theorem eventually_negative_diagonalCurrent_prefix :
    ∀ᶠ T in 𝓝[>] (0:ℝ), ∀ᶠ x in 𝓝[>] (0:ℝ),
      (∫ t in (0:ℝ)..T, diagonalWeight x t*finiteCanonicalCurrent x x t) < 0 := by
  have hneg : -centerBoundaryMass/2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos centerBoundaryMass_pos) (by norm_num)
  have h := (tendsto_order.1 centerPrefixVariation_boundary_limit).2 0 hneg
  filter_upwards [h,self_mem_nhdsWithin] with T hT ht
  have hxneg := (tendsto_order.1 (integral_diagonalCurrent_ratio_limit ht)).2 0 hT
  filter_upwards [hxneg,self_mem_nhdsWithin] with x hx hx0
  simpa only [zero_mul] using (div_lt_iff₀ hx0).mp hx

end RHTower.ThetaFiniteTransport
