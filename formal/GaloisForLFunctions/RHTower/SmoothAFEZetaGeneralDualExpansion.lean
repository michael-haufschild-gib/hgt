import GaloisForLFunctions.RHTower.SmoothAFEZetaDualExpansion
import GaloisForLFunctions.RHTower.ZetaChiVerticalGrowth
import GaloisForLFunctions.RHTower.GaussianShiftedMoment
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralEdge

/-!
# Exact reflected Dirichlet expansion at a general point

The fixed left edge `Re w = -1` is absolutely expandable whenever
`0 < Re s < 1`.  This includes every Levinson abscissa.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter

theorem zetaChi_ne_zero_of_mem_openStrip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : zetaChi s ≠ 0 := by
  intro hs
  have h := zetaChi_mul_one_sub_of_mem_strip h0 h1
  rw [hs, zero_mul] at h
  exact zero_ne_one h

theorem smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one_of_re_lt_one
    {s : ℂ} {x t : ℝ} (hsre : s.re < 1) :
    smoothAFEZetaMellinIntegrand s x ((-1 : ℂ) + (t : ℂ) * I) =
      ∑' n : ℕ, smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (t : ℂ) * I) := by
  apply smoothAFEZetaMellinIntegrand_eq_reflected_tsum
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
    Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  linarith

theorem norm_zetaChi_add_left_one_le
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖zetaChi (s + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
        C * (1 + |s.im| + |v|) ^ 2 := by
  have hσ0 : s.re - 1 ≠ 0 := by linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_zetaChi_vertical hσ0
    (by linarith : -1 ≤ s.re - 1) (by linarith : s.re - 1 ≤ 1 / 2)
  refine ⟨C, hC0, fun v => ?_⟩
  have heq :
      s + ((-1 : ℂ) + (v : ℂ) * I) =
        ((s.re - 1 : ℝ) : ℂ) + ((s.im + v : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [heq]
  have hbase : 1 + |s.im + v| ≤ 1 + |s.im| + |v| := by
    linarith [abs_add_le s.im v]
  have hsq : (1 + |s.im + v|) ^ 2 ≤ (1 + |s.im| + |v|) ^ 2 := by
    nlinarith [abs_nonneg (s.im + v), abs_nonneg s.im, abs_nonneg v]
  calc
    ‖zetaChi (((s.re - 1 : ℝ) : ℂ) + ((s.im + v : ℝ) : ℂ) * I)‖
        ≤ C * (1 + |s.im + v|) ^ 2 := hC (s.im + v)
    _ ≤ C * (1 + |s.im| + |v|) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq hC0

theorem norm_smoothAFEZetaReflectedTerm_general_left_one_le
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    {C : ℝ} (hC : ∀ v : ℝ,
      ‖zetaChi (s + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
        C * (1 + |s.im| + |v|) ^ 2)
    (n : ℕ) (v : ℝ) :
    ‖smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
      (((1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C) *
        ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2)))) := by
  have hn : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have hkernel :=
    norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -1) (by norm_num) v
  have hkernel' :
      ‖smoothAFEGaussianKernel ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
        Real.exp 1 * Real.exp (-(v ^ 2)) := by
    convert hkernel using 1 <;> norm_num
  rw [smoothAFEZetaReflectedTerm_eq_cpow, norm_mul, norm_mul, norm_mul,
    show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hexponent :
      (s + ((-1 : ℂ) + (v : ℂ) * I) - 1).re = s.re - 2 := by simp; ring
  have hwre : (((-1 : ℂ) + (v : ℂ) * I).re) = -1 := by simp
  rw [hexponent, show s.re - 2 = -(2 - s.re) by ring,
    Real.rpow_neg hn.le, hwre, Real.rpow_neg_one]
  have hCnonneg : 0 ≤ C * (1 + |s.im| + |v|) ^ 2 :=
    le_trans (norm_nonneg _) (hC v)
  calc
    ‖zetaChi (s + (-1 + ↑v * I))‖ *
          ((n + 1 : ℝ) ^ (2 - s.re))⁻¹ * x⁻¹ *
          ‖smoothAFEGaussianKernel (-1 + ↑v * I)‖
        ≤ (C * (1 + |s.im| + |v|) ^ 2) *
            ((n + 1 : ℝ) ^ (2 - s.re))⁻¹ * x⁻¹ *
            (Real.exp 1 * Real.exp (-(v ^ 2))) := by
          gcongr
          exact hC v
    _ = (((1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C) *
        ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2)))) := by ring

theorem smoothAFEZetaReflectedTerm_general_left_one_integrable
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (n : ℕ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_zetaChi_add_left_one_le h0 h1
  let D : ℝ :=
    (1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (1 + |s.im|) 2).const_mul D)
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
    let w : ℝ → ℂ := fun v => (-1 : ℂ) + (v : ℂ) * I
    have hw : Continuous w := by
      dsimp only [w]
      fun_prop
    have hchi : Continuous (fun v : ℝ => zetaChi (s + w v)) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        dsimp only [w]
        simp only [Complex.sub_re, Complex.one_re, Complex.add_re,
          Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        linarith
    have hpowN : Continuous (fun v : ℝ =>
        (n + 1 : ℂ) ^ (s + w v - 1)) :=
      (continuous_const_cpow (n + 1 : ℂ)).comp (by fun_prop)
    have hpowX : Continuous (fun v : ℝ => (x : ℂ) ^ (w v)) :=
      (continuous_const_cpow (x : ℂ)).comp hw
    have hwne : ∀ v : ℝ, w v ≠ 0 := by
      intro v hzero
      have hre := congrArg Complex.re hzero
      dsimp only [w] at hre
      simp at hre
    have hkernel : Continuous (fun v : ℝ =>
        smoothAFEGaussianKernel (w v)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hw.pow 2)).div hw hwne
    rw [show (fun v : ℝ =>
        smoothAFEZetaReflectedTerm s x n (w v)) =
      fun v => zetaChi (s + w v) *
        (n + 1 : ℂ) ^ (s + w v - 1) *
        (x : ℂ) ^ (w v) * smoothAFEGaussianKernel (w v) by
          funext v
          exact smoothAFEZetaReflectedTerm_eq_cpow s x n (w v)]
    exact (((hchi.mul hpowN).mul hpowX).mul hkernel).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [D, add_assoc] using
        norm_smoothAFEZetaReflectedTerm_general_left_one_le hx hC n v

theorem summable_integral_norm_smoothAFEZetaReflectedTerm_general_left_one
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Summable (fun n : ℕ => ∫ v : ℝ,
      ‖smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I)‖) := by
  obtain ⟨C, hC0, hC⟩ := norm_zetaChi_add_left_one_le h0 h1
  let D : ℝ := x⁻¹ * Real.exp 1 * C *
      ∫ v : ℝ, (1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))
  have hbase := summable_smoothAFEZetaMajorant
    (p := 2 - s.re) (by linarith)
  have hmajor : Summable (fun n : ℕ =>
      (1 / (n + 1 : ℝ) ^ (2 - s.re)) * D) := hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaReflectedTerm_general_left_one_integrable hx h0 h1 n
  have hgauss := integrable_shifted_pow_mul_exp_neg_sq (1 + |s.im|) 2
  have hdom : Integrable (fun v : ℝ =>
      (((1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C) *
        ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))))) := by
    simpa only [add_assoc] using hgauss.const_mul
      ((1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C)
  calc
    ∫ v : ℝ, ‖smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ,
          (((1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C) *
          ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2)))) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun v =>
          norm_smoothAFEZetaReflectedTerm_general_left_one_le hx hC n v
    _ = (1 / (n + 1 : ℝ) ^ (2 - s.re)) * D := by
      rw [integral_const_mul]
      dsimp only [D]
      ring

theorem integral_smoothAFEZetaMellinIntegrand_general_left_one_eq_tsum
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
        ((-1 : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
  calc
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand s x
        ((-1 : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, ∑' n : ℕ,
        smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v =>
          smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one_of_re_lt_one h1
    _ = ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
      symm
      apply integral_tsum_of_summable_integral_norm
      · exact fun n => smoothAFEZetaReflectedTerm_general_left_one_integrable hx h0 h1 n
      · exact summable_integral_norm_smoothAFEZetaReflectedTerm_general_left_one hx h0 h1

/-- Exact general-point dual cutoff retaining the shifted `χ` ratio. -/
def smoothAFEZetaDualCutoffGeneral (s : ℂ) (y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEDualRatioIntegrand s y
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem integral_smoothAFEZetaReflectedTerm_general_left_one_eq
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (n : ℕ) :
    (∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I)) =
      (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
        ∫ v : ℝ, smoothAFEDualRatioIntegrand s
          (1 / ((n + 1 : ℝ) * x))
          ((-1 : ℂ) + (v : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change smoothAFEZetaReflectedTerm s x n
        ((-1 : ℂ) + (v : ℂ) * I) =
      (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
        smoothAFEDualRatioIntegrand s
          (1 / ((n + 1 : ℝ) * x))
          ((-1 : ℂ) + (v : ℂ) * I)
    rw [smoothAFEZetaReflectedTerm_eq_dualRatioTerm n
        (zetaChi_ne_zero_of_mem_openStrip h0 h1),
      smoothAFEDualRatioTerm_eq_integrand hx]

/-- The normalized reflected edge is an exact dual Dirichlet series at every
point of the open critical strip. -/
theorem smoothAFEZetaDualMellinGeneral_eq_tsum
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    smoothAFEZetaDualMellinGeneral s x =
      ∑' n : ℕ,
        (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
          smoothAFEZetaDualCutoffGeneral s
            (1 / ((n + 1 : ℝ) * x)) := by
  unfold smoothAFEZetaDualMellinGeneral
  rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
  rw [integral_smoothAFEZetaMellinIntegrand_general_left_one_eq_tsum hx h0 h1]
  rw [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx h0 h1]
  unfold smoothAFEZetaDualCutoffGeneral
  rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
  rw [Complex.real_smul]
  ring

/-- Exact unconditional two-Dirichlet-series Gaussian smooth AFE throughout
the open critical strip, including every Levinson abscissa. -/
theorem riemannZeta_eq_two_tsum_smoothAFE_general
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 1)
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-s) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) -
      (∑' n : ℕ,
        (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
          smoothAFEZetaDualCutoffGeneral s
            (1 / ((n + 1 : ℝ) * x))) -
      smoothAFEZetaShiftedPoleResidue s x := by
  rw [← smoothAFEZetaDualMellinGeneral_eq_tsum hx h0 h1]
  exact riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general
    hx hs h0 (by linarith)

end RHTower
