import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGreenEndpointTrace

/-! Actual bounds on the original Green response and retained lift. -/
open Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- A compact-radius profile has its exact original exponential bound on the full negative ray. -/
theorem laplaceProfile_norm_le_exp (w : ℂ) (F : ℝ → ℂ) (hF : ContinuousOn F (Icc 0 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 →
      ‖Complex.exp (w*(t:ℂ))*F (radialUnit t)‖ ≤ C*Real.exp (w.re*t) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  refine ⟨max C 0,le_max_right _ _,fun t ht => ?_⟩
  have hb := (hC _ ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩).trans (le_max_left C 0)
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

/-- The retained physical amplitude has an exponential bound for every compact-radius multiplier. -/
theorem sourceAmplitude_profile_norm_le_exp (s w a T : ℂ) (P : ℝ → ℂ)
    (hP : ContinuousOn P (Icc 0 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 →
      ‖sourceAmplitude s w a T t*P (radialUnit t)‖ ≤ C*Real.exp (w.re*t) := by
  have hpow : ContinuousOn (fun u : ℝ => power (2*s) (1+u)) (Icc 0 1) := by
    intro u hu
    exact (((power_derivatives (2*s) (by linarith [hu.1] : 0 < 1+u)).1.continuousAt).comp_of_eq
      (continuous_const.add continuous_id).continuousAt rfl).continuousWithinAt
  have h := laplaceProfile_norm_le_exp w (fun u => power (2*s) (1+u)*a^(2 : ℕ)*T*P u)
    (((hpow.mul continuousOn_const).mul continuousOn_const).mul hP)
  simpa only [sourceAmplitude,mul_assoc] using h

/-- The literal full-square lift has a uniform bound in the causal chamber. -/
theorem radialLift_bounded (s w a T : ℂ) (hw : 0 < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖radialLift s w a T t‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := sourceAmplitude_profile_norm_le_exp s w a T
    (fun u : ℝ => (-s*(s-1)/4)*(u:ℂ)^(3 : ℕ)) (by fun_prop)
  refine ⟨C,hC,fun t ht => ?_⟩
  have he : Real.exp (w.re*t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw.le ht.le)
  have ht' := hb t ht
  have hid : sourceAmplitude s w a T t*((-s*(s-1)/4)*(radialUnit t:ℂ)^(3 : ℕ)) = radialLift s w a T t := by
    unfold radialLift
    ring
  rw [hid] at ht'
  exact ht'.trans (mul_le_of_le_one_right hC he)

/-- Both proved endpoint limits give a genuine global bound for the original Green integral. -/
theorem tortoiseGreen_bounded {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖tortoiseGreen w chi s a J K T t‖ ≤ C := by
  have hc : ContinuousOn (response w chi s a J K T) (Ioo 0 1) :=
    fun z hz => (response_derivatives h s a J K T hz).1.continuousAt.continuousWithinAt
  have he := continuousOn_Icc_extendFrom_Ioo hc (response_horizon h s a J K T) (response_boundary h s a J K T)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn he
  refine ⟨max C 0,le_max_right _ _,fun t ht => ?_⟩
  have hz := horizonCoordinate_interior t ht
  have hb := (hC _ ⟨hz.1.le,hz.2.le⟩).trans (le_max_left C 0)
  rw [extendFrom_extends hc _ hz] at hb
  exact hb

/-- The actual Green correction is uniformly bounded in its original coordinate. -/
theorem principalDifference_bounded (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t < 0 → ‖principalDifference q branch w a T i t‖ ≤ C := by
  obtain ⟨C,hC,hg⟩ := tortoiseGreen_bounded (hw i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) T
  obtain ⟨D,hD,hl⟩ := radialLift_bounded (physicalRate q branch) w a T (principalChamber_re_pos hw)
  refine ⟨C+D*‖principalAmplitude q i‖,add_nonneg hC (mul_nonneg hD (norm_nonneg _)),fun t ht => ?_⟩
  calc
    ‖principalDifference q branch w a T i t‖ ≤
      ‖tortoiseGreen w (principalFrequency q i) (physicalRate q branch) a
        (principalAmplitude q i) (principalGradient q branch i) T t‖+
          ‖radialLift (physicalRate q branch) w a T t*principalAmplitude q i‖ := norm_sub_le _ _
    _ ≤ C+D*‖principalAmplitude q i‖ := by
      rw [norm_mul]
      exact add_le_add (hg t ht) (mul_le_mul_of_nonneg_right (hl t ht) (norm_nonneg _))

end
end RHTower.D4BMJointSource
