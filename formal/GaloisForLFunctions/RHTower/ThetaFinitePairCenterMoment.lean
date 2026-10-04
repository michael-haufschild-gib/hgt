import GaloisForLFunctions.RHTower.ThetaFinitePairPacketTail
import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterGram

/-! Projective curvature descent controls the actual center derivative mass.
The exact moment comparison determines the sign of the center variation of
the finite-pair current; every integral retains the complete theta source. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

def centerProjectiveRate : ℝ := c₂ 0/c 0

theorem centerProjectiveRate_pos : 0 < centerProjectiveRate :=
  div_pos (thetaCuspLogCurvatureJetTwo_pos_all 0) (thetaCuspLogCurvature_pos 0)

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem v_zero : v 0=0 := by
  simp only [thetaCuspLogCurvatureJet,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩,neg_zero]

private theorem v_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ v t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h,v_zero]
  · exact (thetaCuspLogCurvatureJet_pos_of_pos h).le

private theorem nonneg_from_derivative {f g : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (g t) t) (h0 : f 0=0)
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro u _; exact (hd u).continuousAt.continuousWithinAt
    · intro u _; exact (hd u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hd u).deriv]
      exact hg u (interior_subset hu)
  simpa only [h0] using hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht

private theorem acceleration_le {t : ℝ} (ht : 0 ≤ t) :
    c₂ t ≤ centerProjectiveRate*c t := by
  have h := ThetaCuspDefect.projectiveRatio_strictAntiOn.antitoneOn
    (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  change c₂ t/c t ≤ centerProjectiveRate at h
  exact (div_le_iff₀ (thetaCuspLogCurvature_pos t)).mp h

/-- The center projective rate bounds the actual velocity relative to slope. -/
theorem velocity_le_centerRate_slope {t : ℝ} (ht : 0 ≤ t) :
    v t ≤ centerProjectiveRate*p t := by
  have hd (u : ℝ) : HasDerivAt (fun r => centerProjectiveRate*p r-v r)
      (centerProjectiveRate*c u-c₂ u) u := by
    exact ((hasDerivAt_thetaCuspLogDecaySlope u).const_mul _).sub
      (hasDerivAt_thetaCuspLogCurvatureJet u)
  have h := nonneg_from_derivative hd
    (by simp only [p_zero,v_zero,mul_zero,sub_zero])
    (fun u hu => sub_nonneg.mpr (acceleration_le hu)) ht
  linarith only [h]

private theorem tangent_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t*c t-p t := by
  have hd (u : ℝ) : HasDerivAt (fun r => r*c r-p r) (u*v u) u := by
    convert! ((hasDerivAt_id u).mul (hasDerivAt_thetaCuspLogCurvature u)).sub
      (hasDerivAt_thetaCuspLogDecaySlope u) using 1
    simp only [id_eq]
    ring
  exact nonneg_from_derivative hd (by simp only [zero_mul,p_zero,sub_zero])
    (fun u hu => mul_nonneg hu (v_nonneg hu)) ht

private def slopeComparisonJet (t : ℝ) : ℝ :=
  centerProjectiveRate*(2*t*p t+t^2*c t)/6-c t+c 0

private theorem slopeComparisonJet_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ slopeComparisonJet t := by
  have hd (u : ℝ) : HasDerivAt slopeComparisonJet
      (centerProjectiveRate*(2*p u+4*u*c u+u^2*v u)/6-v u) u := by
    convert! ((((((hasDerivAt_id u).const_mul 2).mul
      (hasDerivAt_thetaCuspLogDecaySlope u)).add
      (((hasDerivAt_id u).pow 2).mul (hasDerivAt_thetaCuspLogCurvature u))).const_mul
      centerProjectiveRate).div_const 6).sub
      (hasDerivAt_thetaCuspLogCurvature u) |>.add_const (c 0) using 1
    simp only [Pi.pow_apply,id_eq]
    ring
  apply nonneg_from_derivative hd ?_ ?_ ht
  · simp only [slopeComparisonJet,zero_mul,zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero,add_zero,zero_div,zero_sub,neg_add_cancel]
  · intro u hu
    have h1 := mul_nonneg centerProjectiveRate_pos.le (tangent_nonneg hu)
    have h2 := mul_nonneg centerProjectiveRate_pos.le (mul_nonneg (sq_nonneg u) (v_nonneg hu))
    have h3 := velocity_le_centerRate_slope hu
    nlinarith only [h1,h2,h3]

/-- Exact cubic source comparison forced by projective descent. -/
theorem slope_center_cubic {t : ℝ} (ht : 0 ≤ t) :
    p t-c 0*t ≤ centerProjectiveRate*t^2*p t/6 := by
  have hd (u : ℝ) : HasDerivAt
      (fun r => centerProjectiveRate*r^2*p r/6-p r+c 0*r)
      (slopeComparisonJet u) u := by
    convert! (((((hasDerivAt_id u).pow 2).const_mul centerProjectiveRate).mul
      (hasDerivAt_thetaCuspLogDecaySlope u)).div_const 6).sub
      (hasDerivAt_thetaCuspLogDecaySlope u) |>.add ((hasDerivAt_id u).const_mul (c 0)) using 1
    simp only [slopeComparisonJet,Pi.pow_apply,id_eq]
    ring
  have h := nonneg_from_derivative hd
    (by simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_div,p_zero,sub_zero,add_zero])
    (fun _ hu => slopeComparisonJet_nonneg hu) ht
  linarith only [h]

/-- The full tangent reserve obeys the matching projective comparison. -/
theorem tangent_center_cubic {t : ℝ} (ht : 0 ≤ t) :
    t*c t-p t ≤ centerProjectiveRate*t^2*p t/3 := by
  have hd (u : ℝ) : HasDerivAt
      (fun r => centerProjectiveRate*r^2*p r/3-(r*c r-p r))
      (u*(centerProjectiveRate*(2*p u+u*c u)/3-v u)) u := by
    convert! (((((hasDerivAt_id u).pow 2).const_mul centerProjectiveRate).mul
      (hasDerivAt_thetaCuspLogDecaySlope u)).div_const 3).sub
      (((hasDerivAt_id u).mul (hasDerivAt_thetaCuspLogCurvature u)).sub
      (hasDerivAt_thetaCuspLogDecaySlope u)) using 1
    simp only [Pi.pow_apply,id_eq]
    ring
  have h := nonneg_from_derivative hd
    (by simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_mul,zero_div,p_zero,sub_zero])
    (fun u hu => mul_nonneg hu (by
      have h1 := mul_nonneg centerProjectiveRate_pos.le (tangent_nonneg hu)
      have h2 := velocity_le_centerRate_slope hu
      nlinarith only [h1,h2])) ht
  linarith only [h]

private def weighted (n : ℕ) (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t^n) f

private theorem weighted_apply (n : ℕ) (f : SchwartzMap ℝ ℝ) (t : ℝ) :
    weighted n f t=t^n*f t := by
  have hg : (fun t : ℝ => t^n).HasTemperateGrowth := by fun_prop
  simp only [weighted,SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]

private theorem weighted_product_integrable (n : ℕ) (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => t^n*f t*g t) := by
  have hi : Integrable (fun t : ℝ => weighted n f t*g t) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (weighted n f) g).integrable
  simpa only [weighted_apply] using hi

private theorem source_deriv_eq (t : ℝ) : deriv k t=-p t*k t :=
  (actualSource_hasDerivAt t).deriv

private theorem firstMoment_integrable : Integrable (fun t : ℝ => t*k t^2) := by
  simpa only [pow_one,pow_two,thetaCuspSchwartzReal_apply,mul_assoc] using
    weighted_product_integrable 1 thetaCuspSchwartzReal thetaCuspSchwartzReal

private theorem slopeMoment_integrable (n : ℕ) :
    Integrable (fun t : ℝ => t^n*p t*k t^2) := by
  have hi := (weighted_product_integrable n thetaCuspSchwartzReal
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)).neg
  convert! hi using 1
  funext t
  change t^n*p t*k t^2 = -(t^n*k t*deriv k t)
  rw [source_deriv_eq]
  ring

private theorem firstMoment_eq : (∫ t in Ioi 0, t*k t^2)=J/2 := by
  have h := thetaTailFirstMomentKernel_commonShift_eq_tail 0 0 0
  simp only [thetaTailCommonTranslationIntegrand,zero_add,add_zero] at h
  have he : (fun t : ℝ => (2*t)*k t*k t) = fun t => 2*(t*k t^2) := by
    funext t; ring
  rw [he,integral_const_mul] at h
  linarith only [h]

private theorem slopeMoment_zero_eq : (∫ t in Ioi 0, p t*k t^2)=k 0^2/2 := by
  have he : (fun t => p t*k t^2) = fun t => -(k t*deriv k t) := by
    funext t; rw [source_deriv_eq]; ring
  rw [he,integral_neg,ThetaGeometricBoundaryAudit.source_times_derivative_tail]
  ring

/-- The quadratic slope moment is exactly the first source mass. -/
theorem slopeMoment_two_eq : (∫ t in Ioi 0, t^2*p t*k t^2)=J/2 := by
  have hd (t : ℝ) : HasDerivAt (fun u => u^2*k u^2)
      (2*(t*k t^2)-2*(t^2*p t*k t^2)) t := by
    convert! ((hasDerivAt_id t).pow 2).mul ((actualSource_hasDerivAt t).pow 2) using 1
    simp only [Pi.pow_apply,id_eq]
    ring
  have hi := (firstMoment_integrable.const_mul 2).sub ((slopeMoment_integrable 2).const_mul 2)
  have hl : Tendsto (fun t : ℝ => t^2*k t^2) atTop (𝓝 0) := by
    have h := ((weighted 2 thetaCuspSchwartzReal).tendsto_cocompact.mono_left
      atTop_le_cocompact).mul
      (thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact)
    convert! h using 1
    · funext t; simp only [weighted_apply,thetaCuspSchwartzReal_apply]; ring
    · simp only [mul_zero]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn hl
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,sub_zero] at h
  rw [integral_sub (firstMoment_integrable.const_mul 2).integrableOn
    ((slopeMoment_integrable 2).const_mul 2).integrableOn,
    integral_const_mul,integral_const_mul,firstMoment_eq] at h
  linarith only [h]

theorem center_source_mass_upper :
    k 0^2 ≤ (c 0+centerProjectiveRate/6)*J := by
  have hpoint : ∀ t ∈ Ioi (0:ℝ), p t*k t^2 ≤
      c 0*(t*k t^2)+(centerProjectiveRate/6)*(t^2*p t*k t^2) := by
    intro t ht
    have h := mul_le_mul_of_nonneg_right (slope_center_cubic ht.le) (sq_nonneg (k t))
    nlinarith only [h]
  have hi0 : Integrable (fun t => p t*k t^2) := by
    simpa only [pow_zero,one_mul] using slopeMoment_integrable 0
  have hi1 := (firstMoment_integrable.const_mul (c 0)).add
    ((slopeMoment_integrable 2).const_mul (centerProjectiveRate/6))
  have h := integral_mono_ae hi0.integrableOn hi1.integrableOn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hpoint t ht)
  simp only [Pi.add_apply] at h
  rw [integral_add (firstMoment_integrable.const_mul (c 0)).integrableOn
      ((slopeMoment_integrable 2).const_mul (centerProjectiveRate/6)).integrableOn,
    integral_const_mul,integral_const_mul,firstMoment_eq,slopeMoment_two_eq,
    slopeMoment_zero_eq] at h
  nlinarith only [h]

theorem center_entry_upper : 2*I-k 0^2 ≤ centerProjectiveRate*J/6 := by
  have hpoint : ∀ t ∈ Ioi (0:ℝ), ThetaConfluent.sourceCurrent t ≤
      (centerProjectiveRate/3)*(t^2*p t*k t^2) := by
    intro t ht
    rw [ThetaConfluent.sourceCurrent_eq]
    have h := mul_le_mul_of_nonneg_right (tangent_center_cubic ht.le) (sq_nonneg (k t))
    dsimp only [thetaCuspLogCurvature] at h
    nlinarith only [h]
  have h := integral_mono_ae ThetaConfluent.sourceCurrent_integrable.integrableOn
    ((slopeMoment_integrable 2).const_mul (centerProjectiveRate/3)).integrableOn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hpoint t ht)
  rw [integral_const_mul,slopeMoment_two_eq,← ThetaConfluent.centerEntry_eq_integral] at h
  dsimp only [ThetaConfluent.centerEntry] at h
  nlinarith only [h]

/-- Global derivative mass controlled by the center's projective curvature data. -/
theorem center_derivative_mass_upper :
    I ≤ (c 0/2+centerProjectiveRate/6)*J := by
  have h1 := center_source_mass_upper
  have h2 := center_entry_upper
  nlinarith only [h1,h2]

/-- The exact center coefficient in the finite-pair current variation is positive. -/
theorem center_current_variation_coefficient_pos :
    0 < c 0^2/2-c 0*(I/J)+5*c₂ 0/12 := by
  have hJ : 0 < J := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0
  have hm := (div_le_iff₀ hJ).mpr center_derivative_mass_upper
  have h := mul_le_mul_of_nonneg_left hm (thetaCuspLogCurvature_pos 0).le
  have he : c 0*(c 0/2+centerProjectiveRate/6)=c 0^2/2+c₂ 0/6 := by
    unfold centerProjectiveRate
    field_simp [(thetaCuspLogCurvature_pos 0).ne']
  rw [he] at h
  have ha := thetaCuspLogCurvatureJetTwo_pos_all 0
  linarith only [h,ha]

end RHTower.ThetaFiniteTransport
