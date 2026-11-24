import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.VisibilityThreshold.Overlap

/-! # Fixed-time slope and joint time-temperature profile of the optimal overlap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology

/-- Lower endpoint of all normalized opposite-time overlaps on finite exact factors. -/
def finiteOverlapFloor (β t : ℝ) : ℝ := sInf (finiteFactorOverlaps β t)

theorem finiteOverlapFloor_above {β : ℝ} (hβ : 1/2 < β) (t : ℝ) :
    finiteOverlapFloor β t = partitionVisibility (thermalPoint (β+β) (t+t)) := by
  rw [finiteOverlapFloor,finiteFactorOverlaps_eq]
  apply (global_visibility_above_one (s := thermalPoint (β+β) (t+t)) (by rw [thermalPoint_re]; linarith)).csInf_eq
  exact ⟨_,∅,visibility_mem ∅ (box_exact ∅ 1) (box_supported ∅ 1) _⟩

/-- The residue at one, read with real parameter h on an arbitrary nonzero complex ray. -/
private theorem zeta_radial_residue (v : ℂ) (hv : v ≠ 0) :
    Tendsto (fun h : ℝ => (h:ℂ)*riemannZeta (1+(h:ℂ)*v)) (𝓝[>] 0) (𝓝 v⁻¹) := by
  have hc := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hp : Tendsto (fun h : ℝ => 1+(h:ℂ)*v) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa only [Complex.ofReal_zero,zero_mul,add_zero] using (tendsto_const_nhds (x := (1:ℂ))).add (hc.mul_const v)
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      intro he
      change 1+(h:ℂ)*v = 1 at he
      exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') hv) (add_eq_left.mp he)
  have hl := (riemannZeta_residue_one.comp hp).div_const v
  rw [one_div] at hl
  apply hl.congr
  intro h
  change ((1+(h:ℂ)*v-1)*riemannZeta (1+(h:ℂ)*v))/v = _
  rw [add_sub_cancel_left,mul_right_comm, mul_div_cancel_right₀ _ hv]

private theorem real_argument (h : ℝ) :
    (((1/2+h)+(1/2+h):ℝ):ℂ) = 1+(h:ℂ)*2 := by push_cast; ring

private theorem moving_argument (h u : ℝ) :
    thermalPoint ((1/2+h)+(1/2+h)) (u*h+u*h) = 1+(h:ℂ)*(2*(1+(u:ℂ)*Complex.I)) := by
  unfold thermalPoint
  push_cast
  ring

/-- At fixed nonzero time the opening slope recovers the zeta modulus on the line Re(s)=1. -/
theorem finiteOverlapFloor_fixed_time_slope {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun h : ℝ => finiteOverlapFloor (1/2+h) t / (2*h)) (𝓝[>] 0)
      (𝓝 ‖riemannZeta (thermalPoint 1 (t+t))‖) := by
  have hc : Continuous (fun h : ℝ => thermalPoint ((1/2+h)+(1/2+h)) (t+t)) := by
    unfold thermalPoint
    fun_prop
  have harg : Tendsto (fun h : ℝ => thermalPoint ((1/2+h)+(1/2+h)) (t+t)) (𝓝[>] 0)
      (𝓝 (thermalPoint 1 (t+t))) := by
    simpa only [add_zero,add_halves] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hne : thermalPoint 1 (t+t) ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    rw [thermalPoint_im,Complex.one_im] at hh
    exact ht (by linarith)
  have hnum := (differentiableAt_riemannZeta hne).continuousAt.tendsto.comp harg
  have hden := (tendsto_const_nhds (x := (2:ℂ))).mul (zeta_radial_residue 2 two_ne_zero)
  rw [mul_inv_cancel₀ two_ne_zero] at hden
  have hl := (hnum.div hden one_ne_zero).norm
  rw [div_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [finiteOverlapFloor_above (lt_add_of_pos_right _ hh),partitionVisibility,thermalPoint_re,real_argument]
  change ‖riemannZeta _ / (2*((h:ℂ)*riemannZeta _))‖ = _
  rw [norm_div,norm_mul,norm_mul,Complex.norm_of_nonneg hh.le,show ‖(2:ℂ)‖ = 2 by norm_num]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- When time and excess damping vanish in a fixed ratio, all finite-factor optimization has a universal profile. -/
theorem finiteOverlapFloor_joint_limit (u : ℝ) :
    Tendsto (fun h : ℝ => finiteOverlapFloor (1/2+h) (u*h)) (𝓝[>] 0) (𝓝 (1/Real.sqrt (1+u^2))) := by
  let v : ℂ := 2*(1+(u:ℂ)*Complex.I)
  have hn : 1+(u:ℂ)*Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
  have hv : v ≠ 0 := mul_ne_zero two_ne_zero hn
  have hl := ((zeta_radial_residue v hv).div (zeta_radial_residue 2 two_ne_zero) (inv_ne_zero two_ne_zero)).norm
  have hval : ‖v⁻¹/(2:ℂ)⁻¹‖ = 1/Real.sqrt (1+u^2) := by
    have hrat : v⁻¹/(2:ℂ)⁻¹ = (1+(u:ℂ)*Complex.I)⁻¹ := by
      change ((2:ℂ)*(1+(u:ℂ)*Complex.I))⁻¹/2⁻¹ = _
      rw [div_inv_eq_mul,mul_inv_rev,mul_assoc,inv_mul_cancel₀ two_ne_zero,mul_one]
    rw [hrat,norm_inv,one_div,Complex.norm_def]
    simp [Complex.normSq_apply,pow_two]
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [finiteOverlapFloor_above (lt_add_of_pos_right _ hh),partitionVisibility,thermalPoint_re,moving_argument,real_argument]
  change ‖((h:ℂ)*riemannZeta (1+(h:ℂ)*v))/((h:ℂ)*riemannZeta (1+(h:ℂ)*2))‖ = _
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hh.ne'),norm_div]

#print axioms finiteOverlapFloor_above
#print axioms finiteOverlapFloor_fixed_time_slope
#print axioms finiteOverlapFloor_joint_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
