import GaloisForLFunctions.RHTower.ThetaFinitePairCenterMoment
import GaloisForLFunctions.RHTower.ThetaTailJointCenterJets
import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterLimits

/-! The center profile exposed by the finite-pair current has a positive germ.
This leaf proves the literal profile and its source-time limit. Identification
with the finite-pair parameter derivative is a separate obligation. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem v_zero : v 0=0 := by
  simp only [thetaCuspLogCurvatureJet,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩,neg_zero]

private theorem center_ne : J ≠ 0 := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact (ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0).ne'

/-- The first node variation of the actual normalized primitive, in kernel jets. -/
def centerPrimitiveVariation (t : ℝ) : ℝ :=
  t*p t-(I/J)*H t t/(k t)^2-ThetaJoint.secondLeft t t/(2*(k t)^2)

theorem centerPrimitiveVariation_continuous : Continuous centerPrimitiveVariation := by
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
  have hk := thetaCuspSchwartzReal.continuous
  have hH := ThetaJoint.source_kernel_continuous.comp
    (show Continuous (fun t : ℝ => (t,t)) from continuous_id.prodMk continuous_id)
  have h2 := ThetaJoint.secondLeft_continuous.comp
    (show Continuous (fun t : ℝ => (t,t)) from continuous_id.prodMk continuous_id)
  exact ((continuous_id.mul hp).sub
    ((continuous_const.mul hH).div (hk.pow 2) (fun t => pow_ne_zero 2
      (thetaCuspFullSource_pos_all t).ne'))).sub
    (h2.div (continuous_const.mul (hk.pow 2)) (fun t => mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (thetaCuspFullSource_pos_all t).ne')))

theorem centerPrimitiveVariation_zero : centerPrimitiveVariation 0=0 := by
  unfold centerPrimitiveVariation
  rw [ThetaJoint.secondLeft_origin]
  field_simp [center_ne,(thetaCuspFullSource_pos_all 0).ne']
  ring

/-- Exact profile produced by the diagonal finite-node first variation. -/
def centerCurrentProfile (t : ℝ) : ℝ :=
  p t*c t*(t*p t/2+1/2-centerPrimitiveVariation t)-t*c t*(I/J)+t*c₂ t/12+
    c 0*(p t*c t+t*p t*v t-t*c t^2)/(2*p t^2)

private theorem second_quotient_limit {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g d 0) (hz : g 0=0) :
    Tendsto (fun z => (f z-f 0)/z^2) (𝓝[>] 0) (𝓝 (d/2)) := by
  have hq : Tendsto (fun z => g z/z) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add,hz,sub_zero,smul_eq_mul,inv_mul_eq_div] using
      hg.tendsto_slope_zero_right
  have hq' : Tendsto (fun z => g z/(2*z)) (𝓝[>] 0) (𝓝 (d/2)) := by
    convert! hq.div_const 2 using 1
    funext z; ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall fun z => (hf z).sub_const (f 0))
    (Eventually.of_forall fun z => by
      convert! (hasDerivAt_id z).pow 2 using 1; simp only [id_eq]; ring)
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with z hz'
    exact mul_ne_zero (by norm_num) (ne_of_gt hz')
  · simpa only [sub_self] using ((hf 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).sub_const (f 0)
  · simpa using (tendsto_id : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds |>.pow 2

private theorem p_linear_limit : Tendsto (fun t => p t/t) (𝓝[>] 0) (𝓝 (c 0)) := by
  simpa only [zero_add,p_zero,sub_zero,smul_eq_mul,inv_mul_eq_div] using
    (hasDerivAt_thetaCuspLogDecaySlope 0).tendsto_slope_zero_right

private theorem v_linear_limit : Tendsto (fun t => v t/t) (𝓝[>] 0) (𝓝 (c₂ 0)) := by
  simpa only [zero_add,v_zero,sub_zero,smul_eq_mul,inv_mul_eq_div] using
    (hasDerivAt_thetaCuspLogCurvatureJet 0).tendsto_slope_zero_right

private theorem p_cubic_limit :
    Tendsto (fun t => (p t-c 0*t)/t^3) (𝓝[>] 0) (𝓝 (c₂ 0/6)) := by
  apply ThetaConfluent.third_quotient_limit
    (g := fun t => c t-c 0) (h := v)
  · intro t
    convert! (hasDerivAt_thetaCuspLogDecaySlope t).sub
      ((hasDerivAt_id t).const_mul (c 0)) using 1
    simp only [mul_one]
  · intro t; exact (hasDerivAt_thetaCuspLogCurvature t).sub_const (c 0)
  · exact hasDerivAt_thetaCuspLogCurvatureJet 0
  · simp only [p_zero,mul_zero,sub_zero]
  · exact sub_self _
  · exact v_zero

private theorem c_quadratic_limit :
    Tendsto (fun t => (c t-c 0)/t^2) (𝓝[>] 0) (𝓝 (c₂ 0/2)) :=
  second_quotient_limit hasDerivAt_thetaCuspLogCurvature
    (hasDerivAt_thetaCuspLogCurvatureJet 0) v_zero

private theorem elasticity_quotient_limit :
    Tendsto (fun t => (p t*c t+t*p t*v t-t*c t^2)/(t*p t^2))
      (𝓝[>] 0) (𝓝 (2*c₂ 0/(3*c 0))) := by
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (c 0)) :=
    (hasDerivAt_thetaCuspLogCurvature 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := ((hc.mul (p_cubic_limit.sub c_quadratic_limit)).add
    (p_linear_limit.mul v_linear_limit)).div (p_linear_limit.pow 2)
      (pow_ne_zero 2 (thetaCuspLogCurvature_pos 0).ne')
  have hv : (c 0*(c₂ 0/6-c₂ 0/2)+c 0*c₂ 0)/(c 0)^2=2*c₂ 0/(3*c 0) := by
    field_simp [(thetaCuspLogCurvature_pos 0).ne']
    ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  simp only [Pi.div_apply]
  field_simp [ht0.ne',(ThetaSturmCrossing.slope_pos ht0).ne']
  ring

/-- The complete center profile has a strictly positive, source-determined linear coefficient. -/
theorem centerCurrentProfile_ratio_limit :
    Tendsto (fun t => centerCurrentProfile t/t) (𝓝[>] 0)
      (𝓝 (c 0^2/2-c 0*(I/J)+5*c₂ 0/12)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hp : Tendsto p (𝓝[>] 0) (𝓝 (p 0)) :=
    (hasDerivAt_thetaCuspLogDecaySlope 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [p_zero] at hp
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (c 0)) :=
    (hasDerivAt_thetaCuspLogCurvature 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ha : Tendsto c₂ (𝓝[>] 0) (𝓝 (c₂ 0)) :=
    (hasDerivAt_thetaCuspLogCurvatureJetTwo 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto centerPrimitiveVariation (𝓝[>] 0) (𝓝 (centerPrimitiveVariation 0)) :=
    centerPrimitiveVariation_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [centerPrimitiveVariation_zero] at hb
  have h := ((((p_linear_limit.mul hc).mul
    ((((ht.mul hp).div_const 2).add_const (1/2)).sub hb)).sub
      (hc.const_mul (I/J))).add (ha.div_const 12)).add
      (elasticity_quotient_limit.const_mul (c 0/2))
  have he : c 0*c 0*(0*0/2+1/2-0)-(I/J)*c 0+c₂ 0/12+
      (c 0/2)*(2*c₂ 0/(3*c 0))=c 0^2/2-c 0*(I/J)+5*c₂ 0/12 := by
    field_simp [(thetaCuspLogCurvature_pos 0).ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht'
  have ht0 : 0 < t := ht'
  unfold centerCurrentProfile
  field_simp [ht0.ne',(ThetaSturmCrossing.slope_pos ht0).ne']

theorem centerCurrentProfile_eventually_pos :
    ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < centerCurrentProfile t := by
  have h := centerCurrentProfile_ratio_limit.eventually
    (lt_mem_nhds center_current_variation_coefficient_pos)
  filter_upwards [h,self_mem_nhdsWithin] with t ht ht0
  exact (div_pos_iff_of_pos_right ht0).mp ht

end RHTower.ThetaFiniteTransport
