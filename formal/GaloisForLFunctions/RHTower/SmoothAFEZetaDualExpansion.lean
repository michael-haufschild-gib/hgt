import GaloisForLFunctions.RHTower.SmoothAFEZetaExact

/-!
# Exact reflected Dirichlet expansion of the Gaussian smooth AFE

On the left line `w=-1+iv`, the reflected Dirichlet series has exponent
`-3/2`, while the exact functional-equation factor grows only linearly in
`|τ+v|`.  Gaussian decay therefore justifies integrating the series term by
term.  The resulting coefficients are expressed through an exact
height-dependent dual cutoff retaining the shifted `χ` ratio.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter

theorem integrable_one_add_abs_mul_exp_neg_sq :
    Integrable (fun v : ℝ => (1 + |v|) * Real.exp (-(v ^ 2))) := by
  have h0 : Integrable (fun v : ℝ => Real.exp (-1 * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have h1raw : Integrable (fun v : ℝ => v * Real.exp (-1 * v ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  have h1 : Integrable (fun v : ℝ => |v| * Real.exp (-1 * v ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h1raw.norm
  have hsum := h0.add h1
  apply hsum.congr
  exact Filter.Eventually.of_forall fun v => by
    simp only [Pi.add_apply]
    rw [show -(v ^ 2) = -1 * v ^ 2 by ring]
    ring

theorem norm_zetaChi_linePt_add_left_one_le
    (τ v : ℝ) :
    ‖zetaChi
        (linePt τ + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤
      (1 + |τ|) * (1 + |v|) := by
  rw [linePt_add_left_one_eq_smoothAFEZetaLeftLinePt,
    norm_zetaChi_smoothAFEZetaLeftLinePt]
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hnorm :
      ‖smoothAFEZetaLeftLinePt (τ + v)‖ ≤
        1 + |τ + v| := by
    rw [smoothAFEZetaLeftLinePt]
    calc
      ‖(((-1 / 2 : ℝ) : ℂ) + ((τ + v : ℝ) : ℂ) * I)‖ ≤
          ‖(((-1 / 2 : ℝ) : ℂ))‖ +
            ‖((τ + v : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |τ + v| := by
        simp only [norm_mul, norm_I, Complex.norm_real,
          Real.norm_eq_abs, mul_one]
        norm_num
      _ ≤ 1 + |τ + v| := by linarith
  have habs : |τ + v| ≤ |τ| + |v| := abs_add_le τ v
  calc
    ‖smoothAFEZetaLeftLinePt (τ + v)‖ / (2 * Real.pi) ≤
        ‖smoothAFEZetaLeftLinePt (τ + v)‖ := by
          exact div_le_self (norm_nonneg _) hpi
    _ ≤ 1 + |τ + v| := hnorm
    _ ≤ 1 + |τ| + |v| := by linarith
    _ ≤ (1 + |τ|) * (1 + |v|) := by
      nlinarith [abs_nonneg τ, abs_nonneg v]

theorem norm_smoothAFEZetaReflectedTerm_left_one_le
    {x : ℝ} (hx : 0 < x) (τ : ℝ) (n : ℕ) (v : ℝ) :
    ‖smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
      (((1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x⁻¹ *
          Real.exp 1 * (1 + |τ|)) *
        ((1 + |v|) * Real.exp (-(v ^ 2)))) := by
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
      (linePt τ + ((-1 : ℂ) + (v : ℂ) * I) - 1).re =
        -(3 / 2 : ℝ) := by
    rw [Complex.sub_re, Complex.add_re, linePt_re]
    norm_num
  have hwre :
      (((-1 : ℂ) + (v : ℂ) * I).re) = -1 := by simp
  rw [hexponent, Real.rpow_neg hn.le, hwre, Real.rpow_neg_one]
  calc
    ‖zetaChi (linePt τ + (-1 + ↑v * I))‖ *
          ((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ * x⁻¹ *
          ‖smoothAFEGaussianKernel (-1 + ↑v * I)‖
        ≤ ((1 + |τ|) * (1 + |v|)) *
            ((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹ * x⁻¹ *
            (Real.exp 1 * Real.exp (-(v ^ 2))) := by
          gcongr
          exact norm_zetaChi_linePt_add_left_one_le τ v
    _ = (((1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x⁻¹ *
          Real.exp 1 * (1 + |τ|)) *
        ((1 + |v|) * Real.exp (-(v ^ 2)))) := by ring

theorem smoothAFEZetaReflectedTerm_left_one_integrable
    {x : ℝ} (hx : 0 < x) (τ : ℝ) (n : ℕ) :
    Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I)) := by
  let D : ℝ :=
    (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x⁻¹ *
      Real.exp 1 * (1 + |τ|)
  apply Integrable.mono'
    (integrable_one_add_abs_mul_exp_neg_sq.const_mul D)
  · haveI : NeZero (x : ℂ) :=
      ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    letI : NeZero (n + 1 : ℂ) := ⟨hn⟩
    let w : ℝ → ℂ := fun v => (-1 : ℂ) + (v : ℂ) * I
    have hw : Continuous w := by
      dsimp only [w]
      fun_prop
    have hchi : Continuous (fun v : ℝ => zetaChi (linePt τ + w v)) := by
      rw [continuous_iff_continuousAt]
      intro v
      apply (zetaChi_analyticAt ?_).continuousAt.comp
      · fun_prop
      · apply Complex.Gammaℝ_ne_zero_of_re_pos
        dsimp only [w]
        rw [Complex.sub_re, Complex.one_re, Complex.add_re, linePt_re]
        norm_num
    have hpowN : Continuous (fun v : ℝ =>
        (n + 1 : ℂ) ^ (linePt τ + w v - 1)) :=
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
        smoothAFEZetaReflectedTerm (linePt τ) x n (w v)) =
      fun v => zetaChi (linePt τ + w v) *
        (n + 1 : ℂ) ^ (linePt τ + w v - 1) *
        (x : ℂ) ^ (w v) * smoothAFEGaussianKernel (w v) by
          funext v
          exact smoothAFEZetaReflectedTerm_eq_cpow
            (linePt τ) x n (w v)]
    exact (((hchi.mul hpowN).mul hpowX).mul hkernel).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa only [D] using
        norm_smoothAFEZetaReflectedTerm_left_one_le hx τ n v

theorem summable_integral_norm_smoothAFEZetaReflectedTerm_left_one
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ,
      ‖smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I)‖) := by
  let D : ℝ :=
    x⁻¹ * Real.exp 1 * (1 + |τ|) *
      ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  have hbase := summable_smoothAFEZetaMajorant
    (p := (3 / 2 : ℝ)) (by norm_num)
  have hmajor : Summable (fun n : ℕ =>
      (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * D) :=
    hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hmajor
  have hterm := smoothAFEZetaReflectedTerm_left_one_integrable hx τ n
  have hgauss := integrable_one_add_abs_mul_exp_neg_sq
  have hdom : Integrable (fun v : ℝ =>
      (((1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x⁻¹ *
          Real.exp 1 * (1 + |τ|)) *
        ((1 + |v|) * Real.exp (-(v ^ 2))))) := by
    exact hgauss.const_mul _
  calc
    ∫ v : ℝ, ‖smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ,
          (((1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * x⁻¹ *
            Real.exp 1 * (1 + |τ|)) *
          ((1 + |v|) * Real.exp (-(v ^ 2)))) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun v =>
          norm_smoothAFEZetaReflectedTerm_left_one_le hx τ n v
    _ = (1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) * D := by
      rw [integral_const_mul]
      dsimp only [D]
      ring

theorem integral_smoothAFEZetaMellinIntegrand_left_one_eq_tsum
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand (linePt τ) x
        ((-1 : ℂ) + (v : ℂ) * I)) =
      ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm (linePt τ) x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
  calc
    (∫ v : ℝ, smoothAFEZetaMellinIntegrand (linePt τ) x
        ((-1 : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, ∑' n : ℕ,
        smoothAFEZetaReflectedTerm (linePt τ) x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v =>
          smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one
            (s := linePt τ) (x := x) (t := v) (linePt_re τ)
    _ = ∑' n : ℕ, ∫ v : ℝ,
        smoothAFEZetaReflectedTerm (linePt τ) x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
      symm
      apply integral_tsum_of_summable_integral_norm
      · exact fun n => smoothAFEZetaReflectedTerm_left_one_integrable hx τ n
      · exact summable_integral_norm_smoothAFEZetaReflectedTerm_left_one hx τ

/-- Exact height-dependent dual cutoff.  It retains the shifted quotient
`χ(1/2+iτ+w) / χ(1/2+iτ)` rather than replacing it by a Stirling
approximation. -/
def smoothAFEZetaDualCutoff (τ y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEDualRatioIntegrand (linePt τ) y
      (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

theorem integral_smoothAFEZetaReflectedTerm_left_one_eq
    {x : ℝ} (hx : 0 < x) (τ : ℝ) (n : ℕ) :
    (∫ v : ℝ, smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I)) =
      (zetaChi (linePt τ) *
        (n + 1 : ℂ) ^ (linePt τ - 1)) *
        ∫ v : ℝ, smoothAFEDualRatioIntegrand (linePt τ)
          (1 / ((n + 1 : ℝ) * x))
          ((-1 : ℂ) + (v : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change smoothAFEZetaReflectedTerm (linePt τ) x n
        ((-1 : ℂ) + (v : ℂ) * I) =
      (zetaChi (linePt τ) *
        (n + 1 : ℂ) ^ (linePt τ - 1)) *
        smoothAFEDualRatioIntegrand (linePt τ)
          (1 / ((n + 1 : ℝ) * x))
          ((-1 : ℂ) + (v : ℂ) * I)
    rw [smoothAFEZetaReflectedTerm_eq_dualRatioTerm_line,
      smoothAFEDualRatioTerm_eq_integrand hx]

/-- The normalized reflected edge is an exact dual Dirichlet series. -/
theorem smoothAFEZetaDualMellinAt_eq_tsum
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    smoothAFEZetaDualMellinAt τ x =
      ∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualCutoff τ
            (1 / ((n + 1 : ℝ) * x)) := by
  unfold smoothAFEZetaDualMellinAt
  rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
  rw [integral_smoothAFEZetaMellinIntegrand_left_one_eq_tsum hx τ]
  rw [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [integral_smoothAFEZetaReflectedTerm_left_one_eq hx]
  unfold smoothAFEZetaDualCutoff
  rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
  rw [Complex.real_smul]
  ring

/-- Exact unconditional two-Dirichlet-series Gaussian smooth AFE on the
critical line. -/
theorem riemannZeta_line_eq_two_tsum_smoothAFE
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    riemannZeta (linePt τ) =
      (∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt τ) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) -
      (∑' n : ℕ,
        (zetaChi (linePt τ) *
          (n + 1 : ℂ) ^ (linePt τ - 1)) *
          smoothAFEZetaDualCutoff τ
            (1 / ((n + 1 : ℝ) * x))) -
      smoothAFEZetaShiftedPoleResidue (linePt τ) x := by
  rw [← smoothAFEZetaDualMellinAt_eq_tsum hx τ]
  exact riemannZeta_line_eq_tsum_smoothAFECutoff_sub_dual_sub_residue hx τ

end RHTower
