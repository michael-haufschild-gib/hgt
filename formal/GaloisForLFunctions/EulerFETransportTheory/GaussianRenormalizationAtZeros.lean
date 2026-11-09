import GaloisForLFunctions.RHTower.GaussianGapSignPhaseTransition
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelExponentialTail

/-!
# Gaussian renormalization at an actual zero

The nonresonant Gamma field is absolutely summable at every positive damping.
After its subtraction, the full prime discrepancy retains the resonant
incomplete Mellin integral with its exact divisor multiplicity. Reciprocal
square summability controls the entire complementary divisor.
-/

open Complex Filter Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Copies of all zeros except the complete multiplicity fibre at `ρ`. -/
abbrev NonresonantZero (ρ : XiDivisorSupport) := {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ}

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
  exact q.property (mem_xiZeroCopyFiber.mpr (Subtype.ext (sub_eq_zero.mp h)))

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
  simp only [complexGaussianFinitePart, norm_mul, norm_inv,
    div_eq_mul_inv, mul_inv]

/-- The nonresonant error has a summable reciprocal-product majorant. -/
private theorem norm_nonresonantGaussianRemainder_sub_le (ρ : XiDivisorSupport)
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
    calc
      ‖H q‖ ≤ ‖-2 * (y : ℂ) * e‖ +
          ‖4 * (y : ℂ) ^ 2 * gaussianIncompleteMellin y (xiZero q - ρ + 2 + 2)‖ :=
        norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul (4 * (y : ℂ) ^ 2)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
  have htail : Summable (fun q : NonresonantZero ρ =>
      ‖(xiZero q - (ρ : ℂ))⁻¹ * (xiZero q - (ρ : ℂ) + 2)⁻¹ * H q‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (((summable_germErrorWeight ρ).subtype _).mul_right
        (‖-2 * (y : ℂ) * e‖ + ‖4 * (y : ℂ) ^ 2‖ * M))
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hH q) (by positivity)
  have hhead : Summable (fun q : NonresonantZero ρ =>
      ‖e‖ * ‖complexGaussianFinitePart ρ q‖) :=
    ((summable_norm_complexGaussianFinitePart ρ).subtype _).mul_left ‖e‖
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
  change ‖complexGaussianGerm ρ y q‖ ≤ ‖e‖ * ‖complexGaussianFinitePart ρ q‖ + _
  rw [hid, ← norm_mul e]
  exact norm_add_le _ _

theorem summable_norm_nonresonantGaussianRemainder (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : NonresonantZero ρ => ‖nonresonantGaussianRemainder ρ y q‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    ((((summable_germErrorWeight ρ).mul_left (2 * y + 2 * y ^ 2)).add
      ((summable_norm_complexGaussianFinitePart ρ).mul_left ‖(Real.exp (-y) : ℂ)‖)).subtype _)
  calc
    _ ≤ ‖nonresonantGaussianRemainder ρ y q -
        (Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q‖ +
        ‖(Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q‖ := by
          simpa only [add_comm] using norm_le_insert' (nonresonantGaussianRemainder ρ y q)
            ((Real.exp (-y) : ℂ) * complexGaussianFinitePart ρ q)
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add (norm_nonresonantGaussianRemainder_sub_le ρ hy q) le_rfl

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

/-- All nonresonant Gamma modes, retaining the full divisor with multiplicity. -/
def nonresonantGaussianModes (ρ : XiDivisorSupport) (y : ℝ) : ℂ :=
  ∑' q : NonresonantZero ρ, gaussianMBKernel y (xiZero q - ρ)

theorem summable_complexGaussianGerm_at_zero (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) : Summable (complexGaussianGerm ρ y) := by
  exact (xiZeroCopyFiber ρ).summable_compl_iff.mp
    (summable_norm_nonresonantGaussianGerm ρ hy).of_norm

/-- Splitting the complete explicit formula at the resonant multiplicity fibre. -/
theorem gaussianPrimeGap_add_nonresonantModes (ρ : XiDivisorSupport)
    {y : ℝ} (hy : 0 < y) :
    gaussianPrimeContinuumGap ρ y + nonresonantGaussianModes ρ y +
        ((xiZeroCopyFiber ρ).card : ℂ) * gaussianIncompleteMellin y 0 =
      gaussianArchimedeanMB y 2 ρ -
        ((xiZeroCopyFiber ρ).card : ℂ) * ((Real.exp (-y) : ℂ) / ((ρ : ℂ) - 1 / 2)) -
        ∑' q : NonresonantZero ρ, nonresonantGaussianRemainder ρ y q := by
  classical
  have hsplit := (summable_complexGaussianGerm_at_zero ρ hy).sum_add_tsum_subtype_compl
    (xiZeroCopyFiber ρ)
  have hf : ∑ q ∈ xiZeroCopyFiber ρ, complexGaussianGerm ρ y q =
      ((xiZeroCopyFiber ρ).card : ℂ) *
        ((Real.exp (-y) : ℂ) / ((ρ : ℂ) - 1 / 2) + gaussianIncompleteMellin y 0) := by
    calc
      _ = ∑ _q ∈ xiZeroCopyFiber ρ,
          ((Real.exp (-y) : ℂ) / ((ρ : ℂ) - 1 / 2) + gaussianIncompleteMellin y 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqρ : xiZero q = (ρ : ℂ) := congrArg Subtype.val (mem_xiZeroCopyFiber.mp hq)
        simp only [complexGaussianGerm, hqρ, sub_self]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hf] at hsplit
  have hR := ((summable_norm_nonresonantGaussianGerm ρ hy).of_norm).tsum_sub
    (summable_norm_nonresonantGaussianModes ρ hy).of_norm
  change (∑' q : NonresonantZero ρ, nonresonantGaussianRemainder ρ y q) = _ at hR
  have hρ := (xi_divisor_support_re_mem_open_unit ρ).1
  have hex := gaussianPrimeCurrent_sub_continuum_eq hy (c := 2) two_pos
    (s := (ρ : ℂ)) (by linarith)
  change gaussianPrimeContinuumGap ρ y = gaussianArchimedeanMB y 2 ρ -
    ∑' q, complexGaussianGerm ρ y q at hex
  rw [hex, ← hsplit, hR, nonresonantGaussianModes]
  ring

/-- Removing the entire nonresonant field and the resonant incomplete integral
leaves a convergent paired finite part at every actual zero. -/
theorem tendsto_gaussianPrimeGap_resonantFinitePart (ρ : XiDivisorSupport) :
    Tendsto (fun y : ℝ => gaussianPrimeContinuumGap ρ y + nonresonantGaussianModes ρ y +
        ((xiZeroCopyFiber ρ).card : ℂ) * gaussianIncompleteMellin y 0) (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent ρ -
        ((xiZeroCopyFiber ρ).card : ℂ) / ((ρ : ℂ) - 1 / 2) -
        ∑' q : NonresonantZero ρ, complexGaussianFinitePart ρ q)) := by
  have hA := tendsto_gaussianArchimedeanCurrent_sub_MB (c := 2) two_pos
    (s := (ρ : ℂ)) (xi_divisor_support_re_mem_open_unit ρ).1
  have hM := (tendsto_const_nhds (x := gaussianArchimedeanCurrent ρ)).sub hA
  simp only [sub_zero, sub_sub_cancel] at hM
  have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun y : ℝ => Real.exp (-y)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      (Real.continuous_exp.tendsto (-0)).comp hy0.neg
  have hE := ((Complex.continuous_ofReal.tendsto 1).comp he).div_const ((ρ : ℂ) - 1 / 2)
  have h := (hM.sub (hE.const_mul ((xiZeroCopyFiber ρ).card : ℂ))).sub
    (tendsto_nonresonantGaussianRemainder_tsum ρ)
  simp only [Complex.ofReal_one, mul_one_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (gaussianPrimeGap_add_nonresonantModes ρ hy).symm

/-- At resonance, the incomplete Mellin integral is half the exponential integral. -/
theorem gaussianIncompleteMellin_zero_eq {y : ℝ} (hy : 0 < y) :
    gaussianIncompleteMellin y 0 =
      ((∫ v in Set.Ioi y, Real.exp (-v) / v : ℝ) : ℂ) / 2 := by
  have h : upperIncGamma 0 y = ((∫ v in Set.Ioi y, Real.exp (-v) / v : ℝ) : ℂ) := by
    rw [upperIncGamma, ← integral_complex_ofReal]
    congr 1
    funext v
    simp only [zero_sub, Complex.cpow_neg_one, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv]
  rw [gaussianIncompleteMellin_eq_upperIncGamma hy 0]
  simp only [zero_div, neg_zero, Complex.cpow_zero, mul_one, h]
  ring

/-- The exact logarithmic finite part of the resonant incomplete integral. -/
theorem tendsto_gaussianIncompleteMellin_zero_add_log :
    Tendsto (fun y : ℝ => gaussianIncompleteMellin y 0 + (Real.log y : ℂ) / 2)
      (𝓝[>] 0) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) / 2)) := by
  have h := ((Complex.continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp
    tendsto_integral_exp_neg_div_id_add_log_nhdsGT_zero).div_const (2 : ℂ)
  simp only [Complex.ofReal_neg, Function.comp_def] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [gaussianIncompleteMellin_zero_eq hy, Complex.ofReal_add]
  ring

/-- The logarithmic coefficient of the full prime discrepancy is exactly minus
the divisor multiplicity in the variable `log(1/y)`. -/
theorem tendsto_gaussianPrimeGap_logarithmicFinitePart (ρ : XiDivisorSupport) :
    Tendsto (fun y : ℝ => gaussianPrimeContinuumGap ρ y + nonresonantGaussianModes ρ y -
        ((xiZeroCopyFiber ρ).card : ℂ) * (Real.log y : ℂ) / 2) (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent ρ -
        ((xiZeroCopyFiber ρ).card : ℂ) / ((ρ : ℂ) - 1 / 2) -
        ∑' q : NonresonantZero ρ, complexGaussianFinitePart ρ q +
        ((xiZeroCopyFiber ρ).card : ℂ) * (Real.eulerMascheroniConstant : ℂ) / 2)) := by
  have h := (tendsto_gaussianPrimeGap_resonantFinitePart ρ).sub
    (tendsto_gaussianIncompleteMellin_zero_add_log.const_mul
      ((xiZeroCopyFiber ρ).card : ℂ))
  convert h using 1
  · funext y
    ring
  · congr 1
    ring

/-- Two positive damping scales recover the exact multiplicity at every actual
zero. The complete nonresonant Gamma field is retained on both scales. -/
theorem two_gaussian_scales_read_zero_multiplicity (ρ : XiDivisorSupport)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => gaussianPrimeContinuumGap ρ y - gaussianPrimeContinuumGap ρ (c * y) +
        nonresonantGaussianModes ρ y - nonresonantGaussianModes ρ (c * y))
      (𝓝[>] 0) (𝓝 (-(((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℂ) *
        (Real.log c : ℂ) / 2)) := by
  rw [← card_xiZeroCopyFiber ρ]
  have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hc0 : Tendsto (fun y : ℝ => c * y) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using hy0.const_mul c, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_pos hc hy
  have h := tendsto_gaussianPrimeGap_logarithmicFinitePart ρ
  have hd := (h.sub (h.comp hc0)).sub_const
    (((xiZeroCopyFiber ρ).card : ℂ) * (Real.log c : ℂ) / 2)
  simp only [sub_self, zero_sub] at hd
  rw [show -(((xiZeroCopyFiber ρ).card : ℂ) * (Real.log c : ℂ) / 2) =
    -((xiZeroCopyFiber ρ).card : ℂ) * (Real.log c : ℂ) / 2 by ring] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  dsimp only [Function.comp_def]
  rw [Real.log_mul hc.ne' (ne_of_gt hy), Complex.ofReal_add]
  ring

#print axioms summable_norm_nonresonantGaussianModes
#print axioms tendsto_gaussianPrimeGap_resonantFinitePart
#print axioms tendsto_gaussianPrimeGap_logarithmicFinitePart
#print axioms two_gaussian_scales_read_zero_multiplicity

end GaloisForLFunctions.EulerFETransportTheory
