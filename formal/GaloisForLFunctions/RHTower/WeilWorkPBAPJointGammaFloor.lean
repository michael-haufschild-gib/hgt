import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedGamma

/-!
# A modulation-uniform Gamma floor for arbitrary complex profiles

The exact paired mass pays the logarithmic width term. The L1 Fourier bound
is used only against the integrable logarithmic singularity on the unit
interval. No correlation sign or modulation-height premise is needed.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A fixed, integrable majorant for the negative logarithmic singularity. -/
def jointLogDeficit (v : ℝ) : ℝ := (Ioc (-1:ℝ) 1).indicator (fun x => |Real.log x|) v

theorem jointLogDeficit_nonneg (v : ℝ) : 0 ≤ jointLogDeficit v := by
  unfold jointLogDeficit
  by_cases hv : v ∈ Ioc (-1:ℝ) 1
  · rw [indicator_of_mem hv]; exact abs_nonneg _
  · rw [indicator_of_notMem hv]

theorem jointLogDeficit_integrable : Integrable jointLogDeficit := by
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).1.abs

private theorem neg_deficit_le_log (v : ℝ) : -jointLogDeficit v ≤ Real.log v := by
  unfold jointLogDeficit
  by_cases hv : v ∈ Ioc (-1:ℝ) 1
  · rw [indicator_of_mem hv]; exact neg_abs_le _
  · rw [indicator_of_notMem hv, neg_zero]
    have ha : 1 ≤ |v| := by
      change ¬ (-1 < v ∧ v ≤ 1) at hv
      by_cases h : -1 < v
      · have hh := lt_of_not_ge (fun hh => hv ⟨h,hh⟩)
        linarith [le_abs_self v]
      · have hh := le_of_not_gt h
        linarith [neg_le_abs v]
    rw [← Real.log_abs]
    exact Real.log_nonneg ha

/-- The only exceptional point is the null singleton at frequency zero. -/
theorem joint_gamma_width_lower {W ξ : ℝ} (hW : 0 < W) (hξ : ξ ≠ 0) :
    -Real.log W-(10+Real.log 4)-jointLogDeficit (W*ξ) ≤ EF.gammaBracket ξ := by
  have hh := joint_gamma_lower_log ξ
  have hl := Real.log_le_log (abs_pos.mpr hξ)
    (show |ξ| ≤ 2+|ξ| by linarith)
  rw [Real.log_abs] at hl
  have hd := neg_deficit_le_log (W*ξ)
  rw [Real.log_mul hW.ne' hξ] at hd
  linarith

private theorem base_fourier_bound (f : JointSmoothTest) (v : ℝ) :
    ‖paperFT f.1.1 (v:ℂ)‖ ≤ ∫ u : ℝ, ‖f.1.1 u‖ := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  have h := norm_paperFT_le
    (f.2.continuous.integrable_of_hasCompactSupport f.1.2.2) ha (v:ℂ)
  simpa only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] using h

/-- A uniform density bound from the actual source's L1 norm. -/
theorem jointPairDensity_le_l1 (f : JointSmoothTest) (L T ξ : ℝ) :
    jointPairDensity f L T ξ ≤ 4*(∫ u : ℝ, ‖f.1.1 u‖)^2 := by
  have hA : 0 ≤ ∫ u : ℝ, ‖f.1.1 u‖ := integral_nonneg fun u => norm_nonneg _
  have hp := (sq_le_sq₀ (norm_nonneg _) hA).mpr (base_fourier_bound f (ξ+T))
  have hm := (sq_le_sq₀ (norm_nonneg _) hA).mpr (base_fourier_bound f (ξ-T))
  have hh := joint_pair_real_density_le f L T ξ
  change _ ≤ _ at hh
  dsimp only [jointPairDensity]
  linarith

private theorem gamma_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2*EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.1.2.1 f.1.2.2 f.1.2.1 f.1.2.2
  refine h.re.congr (Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1.1 f.1.1) (ξ:ℂ)*(EF.gammaBracket ξ:ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem pair_gamma_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (fun ξ => jointPairDensity f L T ξ*EF.gammaBracket ξ) := by
  have h := (gamma_integrable (clusterDifferenceTest (cosineProfileTest f T) L)).add
    (gamma_integrable (clusterDifferenceTest (sineProfileTest f T) L))
  exact h.congr (Eventually.of_forall fun ξ => by
    change ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2*
      EF.gammaBracket ξ +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2*
      EF.gammaBracket ξ = jointPairDensity f L T ξ*EF.gammaBracket ξ
    dsimp only [jointPairDensity]
    ring)

/-- Exact paired mass retains coefficient two at every modulation height. -/
theorem joint_pair_gamma_width_floor (f : JointSmoothTest) {L X W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 X) (hXL : X < L) (hL : 0 ≤ L)
    (hW : 0 < W) (T : ℝ) :
    2*testMass f.1.1*(-Real.log W-(10+Real.log 4))-
      (1/(2*Real.pi))*(4*(∫ u : ℝ, ‖f.1.1 u‖)^2*
        (W⁻¹*∫ v : ℝ, jointLogDeficit v)) ≤
      testGamma (clusterDifference (cosineProfile f.1.1 T) L)+
        testGamma (clusterDifference (sineProfile f.1.1 T) L) := by
  let q := jointPairDensity f L T
  let A := 4*(∫ u : ℝ, ‖f.1.1 u‖)^2
  let b := -Real.log W-(10+Real.log 4)
  have hq : Integrable q := jointPairDensity_integrable f L T
  have hh : Integrable (fun ξ => jointLogDeficit (W*ξ)) :=
    (integrable_comp_mul_left_iff jointLogDeficit hW.ne').mpr jointLogDeficit_integrable
  have hpoint : ∀ᵐ ξ : ℝ, q ξ*b-A*jointLogDeficit (W*ξ) ≤ q ξ*EF.gammaBracket ξ := by
    filter_upwards [volume.ae_ne (0:ℝ)] with ξ hξ
    have hqn : 0 ≤ q ξ := by dsimp [q, jointPairDensity]; positivity
    have hd := jointLogDeficit_nonneg (W*ξ)
    have hqa : q ξ ≤ A := jointPairDensity_le_l1 f L T ξ
    have h1 := mul_le_mul_of_nonneg_left (joint_gamma_width_lower hW hξ) hqn
    have h2 := mul_le_mul_of_nonneg_right hqa hd
    dsimp only [b]
    nlinarith only [h1, h2]
  have hi := integral_mono_ae ((hq.mul_const b).sub (hh.const_mul A))
    (pair_gamma_integrable f L T) hpoint
  change (∫ ξ : ℝ, q ξ*b-A*jointLogDeficit (W*ξ)) ≤ _ at hi
  rw [integral_sub (hq.mul_const b) (hh.const_mul A), integral_mul_const,
    integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hW),
    smul_eq_mul] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))
  have hm := jointPairDensity_mass f hf hXL hL T
  rw [joint_pair_gamma_eq_integral]
  calc
    _ = (1/(2*Real.pi))*((∫ ξ, q ξ)*b-A*(W⁻¹*∫ v, jointLogDeficit v)) := by
      dsimp only [q, A, b]
      linear_combination -(-Real.log W-(10+Real.log 4))*hm
    _ ≤ _ := hi'

/-- A fixed finite source cost; no sign or nonzero integral is assumed. -/
def jointGammaFloorCost (f : JointSmoothTest) : ℝ :=
  2*testMass f.1.1*(10+Real.log 4)+
    (2/Real.pi)*(∫ u : ℝ, ‖f.1.1 u‖)^2*(∫ v : ℝ, jointLogDeficit v)

/-- The literal dilated family has an O(width) Gamma remainder, uniformly in L and T. -/
theorem joint_dilated_gamma_floor (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {W L : ℝ} (hW : 0 < W) (hWL : W < L) (T : ℝ) :
    -2*W*testMass f.1.1*Real.log W-W*jointGammaFloorCost f ≤
      testGamma (clusterDifference (cosineProfile (jointDilatedProfile f.1.1 W) T) L)+
        testGamma (clusterDifference (sineProfile (jointDilatedProfile f.1.1 W) T) L) := by
  have h := joint_pair_gamma_width_floor (jointDilatedTest f W hW)
    (jointDilatedProfile_support hf hW) hWL (by linarith) hW T
  have hi : (∫ u : ℝ, ‖jointDilatedProfile f.1.1 W u‖)=W*(∫ u : ℝ, ‖f.1.1 u‖) := by
    change (∫ u : ℝ, (fun v => ‖f.1.1 v‖) (W⁻¹*u)) = _
    rw [Measure.integral_comp_inv_mul_left (fun v => ‖f.1.1 v‖) W,
      abs_of_pos hW, smul_eq_mul]
  dsimp only [jointDilatedTest] at h
  rw [jointDilatedProfile_mass f.1.1 hW, hi] at h
  convert h using 1
  unfold jointGammaFloorCost
  field_simp [hW.ne']
  ring

end RHTower.WeilWorkPBAP
