import GaloisForLFunctions.RHTower.WeilWorkPBAPJointGammaFloor

/-!
# Source-uniform narrow-window Fourier and Gamma budgets

Every constant depends only on the support width and actual L2 mass.
The log-deficit integral remains symbolic. No derivative norm, nonzero
source integral, correlation sign or modulation bound is assumed.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Cauchy--Schwarz with the actual interval length, not its symmetric hull. -/
theorem joint_l1_sq_le_width_mass (f : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) :
    (∫ u : ℝ, ‖f.1.1 u‖)^2 ≤ W*testMass f.1.1 := by
  have hz (u : ℝ) (hu : u ∉ Icc 0 W) : f.1.1 u = 0 := by
    by_contra hn
    exact hu (hf (subset_tsupport _ hn))
  have hi1 : Integrable (fun u : ℝ => ‖f.1.1 u‖) :=
    (f.2.continuous.integrable_of_hasCompactSupport f.1.2.2).norm
  have hc2 : HasCompactSupport (fun u : ℝ => ‖f.1.1 u‖^(2:ℕ)) := by
    apply f.1.2.2.mono
    intro u hu
    change ‖f.1.1 u‖^(2:ℕ) ≠ 0 at hu
    change f.1.1 u ≠ 0
    intro h
    exact hu (by simp only [h, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)])
  have hi2 : Integrable (fun u : ℝ => ‖f.1.1 u‖^(2:ℕ)) :=
    (f.2.continuous.norm.pow 2).integrable_of_hasCompactSupport hc2
  have hrestrict (g : ℝ → ℝ) (hg : ∀ u, u ∉ Icc 0 W → g u = 0) :
      (∫ u, g u) = ∫ u in Icc 0 W, g u := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1; funext u
    by_cases hu : u ∈ Icc 0 W
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, hg u hu]
  unfold testMass
  rw [hrestrict _ (fun u hu => by simp [hz u hu]),
    hrestrict _ (fun u hu => by simp [hz u hu])]
  generalize hP : (∫ u in Icc 0 W, ‖f.1.1 u‖) = P
  generalize hQ : (∫ u in Icc 0 W, ‖f.1.1 u‖^2) = Q
  let m : ℝ := P/W
  have hzero : 0 ≤ ∫ u in Icc 0 W, (‖f.1.1 u‖-m)^2 :=
    setIntegral_nonneg measurableSet_Icc (fun _ _ => sq_nonneg _)
  have he : (∫ u in Icc 0 W, (‖f.1.1 u‖-m)^2) = Q-2*m*P+m^2*W := by
    simp_rw [show ∀ u : ℝ, (‖f.1.1 u‖-m)^2 =
      ‖f.1.1 u‖^2-2*m*‖f.1.1 u‖+m^2 from fun _ => by ring]
    have hiw : IntegrableOn (fun u : ℝ => 2*m*‖f.1.1 u‖) (Icc 0 W) :=
      (hi1.const_mul (2*m)).integrableOn
    have his : IntegrableOn (fun u : ℝ => ‖f.1.1 u‖^2-2*m*‖f.1.1 u‖) (Icc 0 W) :=
      hi2.integrableOn.sub hiw
    have hic : IntegrableOn (fun _u : ℝ => m^2) (Icc 0 W) :=
      integrableOn_const (by simp) (by simp)
    rw [integral_add his hic,
      integral_sub hi2.integrableOn hiw,
      integral_const_mul, setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, sub_zero, smul_eq_mul,
      ENNReal.toReal_ofReal hW.le]
    rw [hP, hQ]
    ring
  rw [he] at hzero
  have hm : m*W=P := by dsimp only [m]; exact div_mul_cancel₀ _ hW.ne'
  have hid : Q-2*m*P+m^2*W = Q-m*P := by rw [← hm]; ring
  rw [hid] at hzero
  change P^2 ≤ W*Q
  calc
    P^2 = (m*W)*P := by rw [hm]; ring
    _ = W*(m*P) := by ring
    _ ≤ W*Q := mul_le_mul_of_nonneg_left (sub_nonneg.mp hzero) hW.le

/-- Arbitrarily oscillatory source profiles satisfy the same pointwise budget. -/
theorem joint_fourier_sq_le_width_mass (f : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (ξ : ℝ) :
    ‖paperFT f.1.1 (ξ:ℂ)‖^2 ≤ W*testMass f.1.1 := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  have hb := norm_paperFT_le
    (f.2.continuous.integrable_of_hasCompactSupport f.1.2.2) ha (ξ:ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at hb
  exact ((sq_le_sq₀ (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)).mpr hb).trans
    (joint_l1_sq_le_width_mass f hW hf)

theorem joint_source_fourier_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2) := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  exact integrable_normSq_paperFT f.1.2.1 (tsupport_subset_of_vanish
    (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h)))

theorem joint_source_gamma_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2*EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.1.2.1 f.1.2.2 f.1.2.1 f.1.2.2
  refine h.re.congr (Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1.1 f.1.1) (ξ:ℂ)*(EF.gammaBracket ξ:ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The logarithmic deficit has an integrable majorant with no source derivative cost. -/
theorem joint_source_log_deficit_integrable (f : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2*jointLogDeficit (W*ξ)) := by
  have hh : Integrable (fun ξ => jointLogDeficit (W*ξ)) :=
    (integrable_comp_mul_left_iff jointLogDeficit hW.ne').mpr jointLogDeficit_integrable
  apply (hh.const_mul (W*testMass f.1.1)).mono'
    ((joint_source_fourier_integrable f).aestronglyMeasurable.mul hh.aestronglyMeasurable)
  exact Eventually.of_forall fun ξ => by
    change ‖‖paperFT f.1.1 (ξ:ℂ)‖^2*jointLogDeficit (W*ξ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (jointLogDeficit_nonneg _))]
    exact mul_le_mul_of_nonneg_right (joint_fourier_sq_le_width_mass f hW hf ξ)
      (jointLogDeficit_nonneg _)

/-- Integrating the singularity costs a universal constant times physical mass. -/
theorem joint_source_log_deficit_le (f : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) :
    (∫ ξ : ℝ, ‖paperFT f.1.1 (ξ:ℂ)‖^2*jointLogDeficit (W*ξ)) ≤
      testMass f.1.1*(∫ v : ℝ, jointLogDeficit v) := by
  have hh : Integrable (fun ξ => jointLogDeficit (W*ξ)) :=
    (integrable_comp_mul_left_iff jointLogDeficit hW.ne').mpr jointLogDeficit_integrable
  have hi := integral_mono (joint_source_log_deficit_integrable f hW hf)
    (hh.const_mul (W*testMass f.1.1)) (fun ξ =>
      mul_le_mul_of_nonneg_right (joint_fourier_sq_le_width_mass f hW hf ξ)
        (jointLogDeficit_nonneg _))
  rw [integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr hW), smul_eq_mul] at hi
  calc
    _ ≤ W*testMass f.1.1*(W⁻¹*∫ v : ℝ, jointLogDeficit v) := hi
    _ = _ := by field_simp

/-- The Gamma floor is uniform over all smooth profiles with this support width. -/
theorem joint_source_gamma_width_floor (f : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) :
    testMass f.1.1*(-Real.log W-(10+Real.log 4)-
      (1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v)) ≤ testGamma f.1.1 := by
  let q := fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2
  let b := -Real.log W-(10+Real.log 4)
  have hq := joint_source_fourier_integrable f
  have hh := joint_source_log_deficit_integrable f hW hf
  have hi := integral_mono_ae ((hq.mul_const b).sub hh)
    (joint_source_gamma_integrable f) (show ∀ᵐ ξ : ℝ,
      q ξ*b-q ξ*jointLogDeficit (W*ξ) ≤ q ξ*EF.gammaBracket ξ from by
      filter_upwards [volume.ae_ne (0:ℝ)] with ξ hξ
      have h := mul_le_mul_of_nonneg_left (joint_gamma_width_lower hW hξ) (sq_nonneg
        ‖paperFT f.1.1 (ξ:ℂ)‖)
      dsimp only [q, b]
      nlinarith only [h])
  change (∫ ξ : ℝ, q ξ*b-q ξ*jointLogDeficit (W*ξ)) ≤ _ at hi
  rw [integral_sub (hq.mul_const b) hh, integral_mul_const] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))
  have hm := LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.1.2.1 f.1.2.2
  have hd := mul_le_mul_of_nonneg_left (joint_source_log_deficit_le f hW hf)
    (by positivity : 0 ≤ 1/(2*Real.pi))
  change (1/(2*Real.pi))*(∫ ξ, q ξ) = testMass f.1.1 at hm
  change _ ≤ (1/(2*Real.pi))*∫ ξ, q ξ*EF.gammaBracket ξ
  change testMass f.1.1*(b-(1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v)) ≤ _
  calc
    _ = testMass f.1.1*b-(1/(2*Real.pi))*(testMass f.1.1*∫ v, jointLogDeficit v) := by ring
    _ ≤ testMass f.1.1*b-(1/(2*Real.pi))*(∫ ξ, q ξ*jointLogDeficit (W*ξ)) :=
      sub_le_sub_left hd _
    _ = (1/(2*Real.pi))*((∫ ξ, q ξ)*b-∫ ξ, q ξ*jointLogDeficit (W*ξ)) := by
      linear_combination -b*hm
    _ ≤ _ := hi'

/-- Two independent complex sources share one mass-normalized Gamma floor. -/
theorem joint_two_source_gamma_width_floor (f g : JointSmoothTest) {W : ℝ} (hW : 0 < W)
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hg : tsupport g.1.1 ⊆ Icc 0 W) :
    (testMass f.1.1+testMass g.1.1)*(-Real.log W-(10+Real.log 4)-
      (1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v)) ≤
      testGamma f.1.1+testGamma g.1.1 := by
  simpa only [add_mul] using add_le_add (joint_source_gamma_width_floor f hW hf)
    (joint_source_gamma_width_floor g hW hg)

end RHTower.WeilWorkPBAP
