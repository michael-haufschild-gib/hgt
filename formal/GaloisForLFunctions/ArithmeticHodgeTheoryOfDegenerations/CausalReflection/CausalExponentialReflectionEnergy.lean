import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CausalExponentialZeroReflection
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# The exact energy defect of a weighted exponential reflection

The exponential resolvent acts on every actual L² profile through its
literal convolution. A real exponential weight shifts the resolvent pole;
the reflected norm loses exactly the positive resolvent energy.
-/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

private theorem measurable_causalKernel (b : ℝ) : Measurable (causalFourierExponential b) := by
  unfold causalFourierExponential
  exact (by fun_prop : Continuous (fun y : ℝ => (Real.pi : ℂ) *
    Complex.exp (-((Real.pi * b : ℝ) : ℂ) * y))).measurable.indicator measurableSet_Ioi

/-- The Schur operator agrees with the literal convolution on any L² representative. -/
theorem causalExponential_op_coeFn {b : ℝ} (hb : 0 < b)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (((convolutionKernel (causalFourierExponential b)
      (measurable_causalKernel b)
      (causalFourierExponential_integrable hb)).op (hf.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ)
      =ᵐ[volume] (causalFourierExponential b ⋆[ContinuousLinearMap.mul ℂ ℂ] f) := by
  let k := convolutionKernel (causalFourierExponential b)
    (measurable_causalKernel b) (causalFourierExponential_integrable hb)
  filter_upwards [k.op_coeFn (hf.toLp f)] with y hy
  rw [hy, causalExponentialConvolution_eq_reversed]
  unfold SchurKernel.apply
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with u hu
  change causalFourierExponential b (y - u) * (hf.toLp f : ℝ → ℂ) u =
    causalFourierExponential b (y - u) * f u
  rw [hu]

/-- The actual exponential convolution preserves square integrability. -/
theorem memLp_causalExponentialConvolution {b : ℝ} (hb : 0 < b)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (causalFourierExponential b ⋆[ContinuousLinearMap.mul ℂ ℂ] f) 2 volume :=
  (memLp_congr_ae (causalExponential_op_coeFn hb hf)).mp (Lp.memLp _)

private theorem reflection_symbol_energy (a x ξ : ℝ) (w : ℂ) :
    ‖(((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ) * w‖ ^ 2 =
      ‖-((((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ) * w) + (2 * a : ℂ) * w‖ ^ 2 +
        (4 * a * x) * ‖w‖ ^ 2 := by
  have he : -((((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ) * w) + (2 * a : ℂ) * w =
      (((a - x : ℝ) : ℂ) - 2 * Complex.I * ξ) * w := by push_cast; ring
  rw [he, norm_mul, norm_mul, mul_pow, mul_pow]
  have hplus : ‖((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ‖ ^ 2 = (a + x) ^ 2 + 4 * ξ ^ 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hminus : ‖((a - x : ℝ) : ℂ) - 2 * Complex.I * ξ‖ ^ 2 = (a - x) ^ 2 + 4 * ξ ^ 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hplus, hminus]
  ring

/-- The resolvent's pointwise Fourier energy defect. -/
theorem causalExponential_reflection_symbol_defect {a x : ℝ} (hb : 0 < a + x)
    (ξ : ℝ) (z : ℂ) :
    ‖z‖ ^ 2 =
      ‖-z + (2 * a : ℂ) * ((((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ)⁻¹ * z)‖ ^ 2 +
      (4 * a * x) * ‖(((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ)⁻¹ * z‖ ^ 2 := by
  let d : ℂ := ((a + x : ℝ) : ℂ) + 2 * Complex.I * ξ
  have hd : d ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    have hr : d.re = a + x := by simp [d]
    rw [hr, Complex.zero_re] at hh
    exact hb.ne' hh
  have hz : d * (d⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hh := reflection_symbol_energy a x ξ (d⁻¹ * z)
  change ‖d * (d⁻¹ * z)‖ ^ 2 = ‖-(d * (d⁻¹ * z)) + (2 * a : ℂ) * (d⁻¹ * z)‖ ^ 2 +
    (4 * a * x) * ‖d⁻¹ * z‖ ^ 2 at hh
  rwa [hz] at hh

/-- The literal exponential Schur operator has the resolvent Fourier symbol. -/
theorem causalExponential_op_fourier {b : ℝ} (hb : 0 < b) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ((fourierL2 ℝ ((convolutionKernel (causalFourierExponential b)
      (measurable_causalKernel b)
      (causalFourierExponential_integrable hb)).op f) : Lp ℂ 2 volume) : ℝ → ℂ)
      =ᵐ[volume] fun ξ => ((b : ℂ) + 2 * Complex.I * ξ)⁻¹ *
        ((fourierL2 ℝ f : Lp ℂ 2 volume) : ℝ → ℂ) ξ := by
  rw [convolutionKernel_op_eq_fourierMulCLM, fourierMulCLM_apply, fourierL2_fourierL2inv]
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (continuous_fourier_of_integrable' (causalFourierExponential_integrable hb)).measurable
    (integral_nonneg fun y => norm_nonneg (causalFourierExponential b y))
    (norm_fourier_apply_le_integral_norm (causalFourierExponential b)) (fourierL2 ℝ f)] with ξ hξ
  rw [hξ, fourier_causalFourierExponential hb]

/-- Exact L² energy loss under an exponential reflection with shifted rate. -/
theorem causalExponential_reflection_energy {a x : ℝ} (hb : 0 < a + x)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    let k := convolutionKernel (causalFourierExponential (a + x))
      (measurable_causalKernel (a + x)) (causalFourierExponential_integrable hb)
    ‖f‖ ^ 2 = ‖-f + (2 * a : ℂ) • k.op f‖ ^ 2 + (4 * a * x) * ‖k.op f‖ ^ 2 := by
  intro k
  let g := k.op f
  let h : Lp ℂ 2 (volume : Measure ℝ) := -f + (2 * a : ℂ) • g
  have hg := causalExponential_op_fourier hb f
  have hhclass : fourierL2 ℝ h = -(fourierL2 ℝ f) + (2 * a : ℂ) • fourierL2 ℝ g := by
    change fourierL2 ℝ (-f + (2 * a : ℂ) • g) = _
    simp only [map_add, map_neg, map_smul]
  have hh : ((fourierL2 ℝ h : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -((fourierL2 ℝ f : Lp ℂ 2 volume) : ℝ → ℂ) ξ +
        (2 * a : ℂ) * ((fourierL2 ℝ g : Lp ℂ 2 volume) : ℝ → ℂ) ξ := by
    rw [hhclass]
    filter_upwards [Lp.coeFn_add (-(fourierL2 ℝ f)) ((2 * a : ℂ) • fourierL2 ℝ g),
      Lp.coeFn_neg (fourierL2 ℝ f), Lp.coeFn_smul (2 * a : ℂ) (fourierL2 ℝ g)] with ξ h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    rfl
  have hgint : Integrable (fun ξ => ‖((fourierL2 ℝ g : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hhint : Integrable (fun ξ => ‖((fourierL2 ℝ h : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hnorm (v : Lp ℂ 2 (volume : Measure ℝ)) :
      ‖v‖ ^ 2 = ∫ ξ, ‖((fourierL2 ℝ v : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 := by
    rw [← GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
    change ‖v‖ ^ 2 = ‖(𝓕 v : Lp ℂ 2 volume)‖ ^ 2
    rw [Lp.norm_fourier_eq]
  change ‖f‖ ^ 2 = ‖h‖ ^ 2 + (4 * a * x) * ‖g‖ ^ 2
  calc
    _ = ∫ ξ, ‖((fourierL2 ℝ f : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 := hnorm f
    _ = ∫ ξ, (‖((fourierL2 ℝ h : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 +
        (4 * a * x) * ‖((fourierL2 ℝ g : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2) := by
      refine integral_congr_ae ?_
      filter_upwards [hh, hg] with ξ h1 h2
      change ((fourierL2 ℝ g : Lp ℂ 2 volume) : ℝ → ℂ) ξ = _ at h2
      change ‖((fourierL2 ℝ f : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 =
        ‖((fourierL2 ℝ h : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2 +
        (4 * a * x) * ‖((fourierL2 ℝ g : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2
      rw [h1, h2]
      exact causalExponential_reflection_symbol_defect hb ξ _
    _ = _ := by
      rw [integral_add hhint (hgint.const_mul (4 * a * x)), integral_const_mul,
        ← hnorm h, ← hnorm g]

/-- The same energy defect for literal convolution integrals and arbitrary
square-integrable measurable representatives. -/
theorem integral_causalExponential_reflection_energy {a x : ℝ} (hb : 0 < a + x)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    let g := causalFourierExponential (a + x) ⋆[ContinuousLinearMap.mul ℂ ℂ] f
    (∫ u, ‖f u‖ ^ 2) = (∫ u, ‖-f u + (2 * a : ℂ) * g u‖ ^ 2) +
      (4 * a * x) * ∫ u, ‖g u‖ ^ 2 := by
  intro g
  let v := hf.toLp f
  let k := convolutionKernel (causalFourierExponential (a + x))
    (measurable_causalKernel (a + x)) (causalFourierExponential_integrable hb)
  let w := k.op v
  let h : Lp ℂ 2 (volume : Measure ℝ) := -v + (2 * a : ℂ) • w
  have hw : (w : ℝ → ℂ) =ᵐ[volume] g := causalExponential_op_coeFn hb hf
  have hh : (h : ℝ → ℂ) =ᵐ[volume] fun u => -f u + (2 * a : ℂ) * g u := by
    filter_upwards [Lp.coeFn_add (-v) ((2 * a : ℂ) • w), Lp.coeFn_neg v,
      Lp.coeFn_smul (2 * a : ℂ) w, hf.coeFn_toLp, hw] with u h1 h2 h3 h4 h5
    change ((-v + (2 * a : ℂ) • w : Lp ℂ 2 volume) : ℝ → ℂ) u = _
    rw [h1, Pi.add_apply, h2, h3]
    change -(v : ℝ → ℂ) u + (2 * a : ℂ) * (w : ℝ → ℂ) u = _
    rw [h4, h5]
  have hn (v' : Lp ℂ 2 (volume : Measure ℝ)) (f' : ℝ → ℂ)
      (heq : (v' : ℝ → ℂ) =ᵐ[volume] f') : ‖v'‖ ^ 2 = ∫ u, ‖f' u‖ ^ 2 := by
    rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
    exact integral_congr_ae (heq.fun_comp fun z => ‖z‖ ^ 2)
  have he := causalExponential_reflection_energy hb v
  change ‖v‖ ^ 2 = ‖h‖ ^ 2 + (4 * a * x) * ‖w‖ ^ 2 at he
  rwa [hn v f hf.coeFn_toLp, hn h _ hh, hn w g hw] at he

/-- The actual Blaschke reflection preserves the Fourier modulus at every real frequency. -/
theorem norm_fourier_causalBlaschkeStep {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    ‖𝓕 (causalBlaschkeStep a f) ξ‖ = ‖𝓕 f ξ‖ := by
  rw [fourier_causalBlaschkeStep ha hf ξ, norm_mul, norm_div]
  have hd : (a : ℂ) + 2 * Complex.I * ξ ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    exact ha.ne' hh
  have hs : ‖(a : ℂ) - 2 * Complex.I * ξ‖ ^ 2 =
      ‖(a : ℂ) + 2 * Complex.I * ξ‖ ^ 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  have hn : ‖(a : ℂ) - 2 * Complex.I * ξ‖ = ‖(a : ℂ) + 2 * Complex.I * ξ‖ := by
    nlinarith only [hs, norm_nonneg ((a : ℂ) - 2 * Complex.I * ξ),
      norm_nonneg ((a : ℂ) + 2 * Complex.I * ξ)]
  rw [hn, div_self (norm_ne_zero_iff.mpr hd), one_mul]

end GaloisForLFunctions.HTGeometry
