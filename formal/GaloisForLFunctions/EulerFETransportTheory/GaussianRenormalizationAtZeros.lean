import GaloisForLFunctions.RHTower.GaussianGapSignPhaseTransition
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!+# Gaussian renormalization at an actual zero

The nonresonant Gamma field is absolutely summable at every positive damping.
After its subtraction, the full prime discrepancy retains the resonant
incomplete Mellin integral with its exact divisor multiplicity. Reciprocal
square summability controls the entire complementary divisor.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Copies of all zeros except the complete multiplicity fibre at `ρ`. -/
abbrev NonresonantZero (ρ : XiDivisorSupport) := {q : XiZeroCopy // q.1 ≠ ρ}

/-- The paired incomplete-Mellin germ, before separating its Gamma mode. -/
def complexGaussianGerm (s : ℂ) (y : ℝ) (q : XiZeroCopy) : ℂ :=
  (Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s)

/-- The paired finite part away from the resonant fibre. -/
def complexGaussianFinitePart (s : ℂ) (q : XiZeroCopy) : ℂ :=
  (1 / 2 - s) / ((xiZero q - 1 / 2) * (xiZero q - s))

/-- The Gamma-subtracted nonresonant germ. -/
def nonresonantGaussianRemainder (ρ : XiDivisorSupport) (y : ℝ)
    (q : NonresonantZero ρ) : ℂ :=
  complexGaussianGerm ρ y q - gaussianMBKernel y (xiZero q - ρ)

private theorem nonresonant_sub_ne_zero (ρ : XiDivisorSupport) (q : NonresonantZero ρ) :
    xiZero q - (ρ : ℂ) ≠ 0 := by
  intro h
  exact q.property (Subtype.ext (sub_eq_zero.mp h))

/-- Reciprocal squares remain summable after any complex translation, including
at a divisor point where the algebraic inverse is zero on its finite fibre. -/
theorem summable_norm_inv_xiZero_sub_sq (s : ℂ) :
    Summable (fun q : XiZeroCopy => ‖(xiZero q - s)⁻¹‖ ^ 2) := by
  have h := XiWeilSquareSummable_cauchy ((s - 1 / 2) * -I)
  unfold XiWeilSquareSummable xiWeilCauchyTest at h
  refine h.congr fun q => ?_
  have he : xiSpectralPoint q - (s - 1 / 2) * -I = (xiZero q - s) * -I := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
    change ((q.1 : ℂ) - 1 / 2) * -I - (s - 1 / 2) * -I = ((q.1 : ℂ) - s) * -I
    ring
  simp only [he, mul_inv, norm_mul, norm_inv, norm_neg, norm_I, inv_one, mul_one]

private theorem summable_reciprocal_product (s t : ℂ) :
    Summable (fun q : XiZeroCopy => ‖(xiZero q - s)⁻¹‖ * ‖(xiZero q - t)⁻¹‖) := by
  have h := summable_norm_mul_of_sq (summable_norm_inv_xiZero_sub_sq s)
    (summable_norm_inv_xiZero_sub_sq t)
  simpa only [norm_mul] using h

private def germErrorWeight (ρ : XiDivisorSupport) (q : XiZeroCopy) : ℝ :=
  ‖(xiZero q - (ρ : ℂ))⁻¹‖ * ‖(xiZero q - (ρ : ℂ) + 2)⁻¹‖

private theorem summable_germErrorWeight (ρ : XiDivisorSupport) :
    Summable (germErrorWeight ρ) := by
  convert summable_reciprocal_product (ρ : ℂ) ((ρ : ℂ) - 2) using 1
  funext q
  rw [germErrorWeight]
  congr 3
  ring

theorem summable_norm_complexGaussianFinitePart (s : ℂ) :
    Summable (fun q : XiZeroCopy => ‖complexGaussianFinitePart s q‖) := by
  refine ((summable_reciprocal_product (1 / 2) s).mul_left ‖1 / 2 - s‖).congr fun q => ?_
  simp only [complexGaussianFinitePart, norm_div, norm_mul, norm_inv,
    div_eq_mul_inv, mul_inv]
  ring

/-- The nonresonant error has a summable reciprocal-product majorant. -/
theorem norm_nonresonantGaussianRemainder_sub_le (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) (q : NonresonantZero ρ) :
    ‖nonresonantGaussianRemainder ρ y q -
        (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q‖ ≤
      (2 * y + 2 * y ^ 2) * germErrorWeight ρ q := by
  have hρ := xi_divisor_support_re_mem_open_unit ρ
  have hq := xiZeroCopy_re_pos (q : XiZeroCopy)
  change 0 < (xiZero (q : XiZeroCopy)).re at hq
  have ha := nonresonant_sub_ne_zero ρ q
  have hk := XiAtlasFinitePart.xiZero_sub_half_ne_zero (q : XiZeroCopy)
  have hb : -2 < (xiZero q - (ρ : ℂ)).re := by simp; linarith [hρ.2]
  have h := norm_zeroGerm_sub_gamma_le hy hb ha
  have he : nonresonantGaussianRemainder ρ y q -
      (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q =
      (Real.exp (-y) : ℂ) / (xiZero q - (ρ : ℂ)) +
        gaussianIncompleteMellin y (xiZero q - (ρ : ℂ)) -
        gaussianMBKernel y (xiZero q - (ρ : ℂ)) := by
    unfold nonresonantGaussianRemainder complexGaussianGerm complexGaussianFinitePart
    have hc : 1 / 2 - (ρ : ℂ) = (xiZero q - ρ) - (xiZero q - 1 / 2) := by ring
    rw [hc]
    generalize xiZero q - 1 / 2 = κ at hk ⊢
    generalize xiZero q - (ρ : ℂ) = a at ha ⊢
    field_simp
    ring
  rw [he, gaussianMBKernel]
  simpa only [germErrorWeight, norm_inv, div_eq_mul_inv, mul_inv, mul_assoc] using h

private theorem norm_nonresonantGaussianRemainder_le (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (q : NonresonantZero ρ) :
    ‖nonresonantGaussianRemainder ρ y q‖ ≤
      ‖complexGaussianFinitePart ρ q‖ + 4 * germErrorWeight ρ q := by
  have hb := norm_nonresonantGaussianRemainder_sub_le ρ hy q
  have he : ‖(Real.exp (-y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have ht := norm_add_le (nonresonantGaussianRemainder ρ y q -
    (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q)
    ((Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q)
  rw [sub_add_cancel, norm_mul] at ht
  have hw : 0 ≤ germErrorWeight ρ q := by unfold germErrorWeight; positivity
  have hcoef : 2 * y + 2 * y ^ 2 ≤ 4 := by nlinarith
  have heC := mul_le_mul_of_nonneg_right he (norm_nonneg (complexGaussianFinitePart ρ q))
  have heW := mul_le_mul_of_nonneg_right hcoef hw
  nlinarith

/-- The complete nonresonant remainder converges at an actual zero. -/
theorem tendsto_nonresonantGaussianRemainder_tsum (ρ : XiDivisorSupport) :
    Tendsto (fun y : ℝ => ∑' q : NonresonantZero ρ, nonresonantGaussianRemainder ρ y q)
      (𝓝[>] 0) (𝓝 (∑' q : NonresonantZero ρ, complexGaussianFinitePart ρ q)) := by
  have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpoint : ∀ q : NonresonantZero ρ,
      Tendsto (fun y : ℝ => nonresonantGaussianRemainder ρ y q) (𝓝[>] 0)
        (𝓝 (complexGaussianFinitePart ρ q)) := by
    intro q
    have hd : Tendsto (fun y : ℝ => nonresonantGaussianRemainder ρ y q -
        (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hb : Tendsto (fun y : ℝ => (2 * y + 2 * y ^ 2) * germErrorWeight ρ q)
          (𝓝[>] 0) (𝓝 0) := by
        simpa using ((hy0.const_mul 2).add ((hy0.pow 2).const_mul 2)).mul_const
          (germErrorWeight ρ q)
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (by filter_upwards [self_mem_nhdsWithin] with y hy
            exact norm_nonresonantGaussianRemainder_sub_le ρ hy q) hb
    have hr : Tendsto (fun y : ℝ => (Real.exp (-y) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have he : Tendsto (fun y : ℝ => Real.exp (-y)) (𝓝[>] 0) (𝓝 1) := by
        simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
          (Real.continuous_exp.tendsto (-0)).comp hy0.neg
      simpa only [Function.comp_def, Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto 1).comp he
    simpa only [zero_add, one_mul, sub_add_cancel] using
      hd.add (hr.mul_const (complexGaussianFinitePart ρ q))
  refine tendsto_tsum_of_dominated_convergence
    (((summable_norm_complexGaussianFinitePart ρ).add
      ((summable_germErrorWeight ρ).mul_left 4)).subtype _) hpoint ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy q
  exact norm_nonresonantGaussianRemainder_le ρ hy.1 hy.2.le q

/-- Two incomplete-Mellin recursions give absolute admission of every
nonresonant germ, with no restriction on the height or multiplicity of `ρ`. -/
theorem summable_norm_nonresonantGaussianGerm (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : NonresonantZero ρ => ‖complexGaussianGerm ρ y q‖) := by
  let M : ℝ := y ^ (-(4 + 1 : ℝ) / 2) * (1 / 2) * Real.Gamma ((4 + 1 : ℝ) / 2)
  let e : ℂ := (Real.exp (-y) : ℂ)
  let H : NonresonantZero ρ → ℂ := fun q =>
    -2 * (y : ℂ) * e + 4 * (y : ℂ) ^ 2 *
      gaussianIncompleteMellin y (xiZero q - ρ + 2 + 2)
  have hH : ∀ q, ‖H q‖ ≤ ‖-2 * (y : ℂ) * e‖ + ‖4 * (y : ℂ) ^ 2‖ * M := by
    intro q
    have hq := xiZeroCopy_re_lt_one (q : XiZeroCopy)
    change (xiZero (q : XiZeroCopy)).re < 1 at hq
    have hρ := (xi_divisor_support_re_mem_open_unit ρ).1
    have hE := norm_gaussianIncompleteMellin_le hy (r := 4) (by norm_num)
      (b := xiZero q - ρ + 2 + 2) (by simp; linarith)
    exact (norm_add_le _ _).trans (add_le_add_left
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)) _)
  have htail : Summable (fun q : NonresonantZero ρ =>
      ‖(xiZero q - (ρ : ℂ))⁻¹ * (xiZero q - (ρ : ℂ) + 2)⁻¹ * H q‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (((summable_germErrorWeight ρ).subtype _).mul_right
        (‖-2 * (y : ℂ) * e‖ + ‖4 * (y : ℂ) ^ 2‖ * M))
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hH q) (by positivity)
  have hhead := ((summable_norm_complexGaussianFinitePart ρ).subtype
    (fun q : XiZeroCopy => q.1 ≠ ρ)).mul_left ‖e‖
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hhead.add htail)
  have ha := nonresonant_sub_ne_zero ρ q
  have hk := XiAtlasFinitePart.xiZero_sub_half_ne_zero (q : XiZeroCopy)
  have ha2 : xiZero q - (ρ : ℂ) + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    have hq := xiZeroCopy_re_pos (q : XiZeroCopy)
    change 0 < (xiZero (q : XiZeroCopy)).re at hq
    have hρ := (xi_divisor_support_re_mem_open_unit ρ).2
    simp at hh
    linarith
  have hid : complexGaussianGerm ρ y q = e * complexGaussianFinitePart ρ q +
      (xiZero q - (ρ : ℂ))⁻¹ * (xiZero q - (ρ : ℂ) + 2)⁻¹ * H q := by
    unfold complexGaussianGerm complexGaussianFinitePart H
    rw [gaussianIncompleteMellin_recursion hy ha,
      gaussianIncompleteMellin_recursion hy ha2]
    change e / (xiZero q - 1 / 2) + _ = _
    rw [show 1 / 2 - (ρ : ℂ) = (xiZero q - ρ) - (xiZero q - 1 / 2) by ring]
    generalize xiZero q - 1 / 2 = κ at hk ⊢
    generalize xiZero q - (ρ : ℂ) = a at ha ha2 ⊢
    change e / κ + (-e / a + _) = _
    field_simp
    ring
  rw [hid]
  simpa only [norm_mul] using norm_add_le (e * complexGaussianFinitePart ρ q)
    ((xiZero q - (ρ : ℂ))⁻¹ * (xiZero q - (ρ : ℂ) + 2)⁻¹ * H q)

theorem summable_norm_nonresonantGaussianRemainder (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : NonresonantZero ρ => ‖nonresonantGaussianRemainder ρ y q‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    ((((summable_germErrorWeight ρ).mul_left (2 * y + 2 * y ^ 2)).add
      ((summable_norm_complexGaussianFinitePart ρ).mul_left ‖(Real.exp (-y) : ℂ)‖)).subtype _)
  calc
    _ ≤ ‖nonresonantGaussianRemainder ρ y q -
        (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q‖ +
        ‖(Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q‖ := norm_le_insert' _ _
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add_right (norm_nonresonantGaussianRemainder_sub_le ρ hy q) _

/-- The full nonresonant Gamma field is absolutely convergent at each positive
damping, even when the observation point is an actual zero. -/
theorem summable_norm_nonresonantGaussianModes (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : NonresonantZero ρ => ‖gaussianMBKernel y (xiZero q - ρ)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    ((summable_norm_nonresonantGaussianGerm ρ hy).add
      (summable_norm_nonresonantGaussianRemainder ρ hy))
  have h := norm_sub_le (complexGaussianGerm ρ y q) (nonresonantGaussianRemainder ρ y q)
  simpa only [nonresonantGaussianRemainder, sub_sub_cancel] using h

end GaloisForLFunctions.EulerFETransportTheory
