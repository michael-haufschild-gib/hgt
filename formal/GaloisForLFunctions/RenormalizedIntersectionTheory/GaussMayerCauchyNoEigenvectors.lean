import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchySpectrum
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# Absence of point spectrum for actual Cauchy averaging

The Gamma multiplier is holomorphic on its Mellin strip. Its nonconstant
real-frequency trace has countable level sets, so no nonzero logarithmic
`L²` field can be an eigenvector, even where the operator amplifies norms.
-/

open Complex Set Filter MeasureTheory FourierTransform
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open GaloisForLFunctions.HTGeometry
open MayerCauchyL2 MayerCauchyMellinSymbol MayerCauchySpectrum
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyNoEigenvectors

private def symbolStrip (w : ℂ) : Set ℂ := {u | -1 < u.re ∧ u.re < w.re+1}

private theorem symbolStrip_open (w : ℂ) : IsOpen (symbolStrip w) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem symbolStrip_preconnected (w : ℂ) : IsPreconnected (symbolStrip w) := by
  have hc : Convex ℝ (symbolStrip w) :=
    (convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt (w.re+1))
  exact hc.isPreconnected

private theorem gamma_differentiable {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro n he
  have hr := congrArg Complex.re he
  simp only [Complex.neg_re,Complex.natCast_re] at hr
  linarith only [hs,hr,Nat.cast_nonneg (α := ℝ) n]

private theorem symbol_analytic (w eigenvalue : ℂ) :
    AnalyticOnNhd ℂ (fun u => symbol w u-eigenvalue) (symbolStrip w) := by
  apply DifferentiableOn.analyticOnNhd _ (symbolStrip_open w)
  intro u hu
  change -1 < u.re ∧ u.re < w.re+1 at hu
  apply DifferentiableAt.differentiableWithinAt
  have hA : 0 < ((u+1)/2).re := by
    simp only [Complex.div_ofNat_re,Complex.add_re,Complex.one_re]
    linarith only [hu.1]
  have hB : 0 < ((w+1-u)/2).re := by
    simp only [Complex.div_ofNat_re,Complex.sub_re,Complex.add_re,Complex.one_re]
    linarith only [hu.2]
  have ha := (gamma_differentiable hA).comp u (show DifferentiableAt ℂ (fun z : ℂ => (z+1)/2) u from by fun_prop)
  have hb := (gamma_differentiable hB).comp u (show DifferentiableAt ℂ (fun z : ℂ => (w+1-z)/2) u from by fun_prop)
  simpa only [symbol,Function.comp_def] using!
    ((ha.mul hb).div_const ((Real.pi : ℂ)^(1/2 : ℂ)*Gamma ((w+1)/2))).sub_const eigenvalue

private theorem frequency_mem_strip {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I ∈ symbolStrip w := by
  have hr : (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I).re=w.re/2 := by simp
  change -1 < (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I).re ∧
    (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I).re < w.re+1
  rw [hr]
  constructor <;> linarith only [hw]

private theorem frequency_injective (w : ℂ) :
    Function.Injective (fun ξ : ℝ => w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I) := by
  intro x y he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im,Complex.mul_I_im,Complex.ofReal_re] at hi
  have hm : (2*Real.pi)*x=(2*Real.pi)*y := by linarith only [hi]
  exact mul_left_cancel₀ (by positivity : (2 : ℝ)*Real.pi ≠ 0) hm

private theorem exists_symbol_ne {w : ℂ} (hw : 0 < w.re) (eigenvalue : ℂ) :
    ∃ ξ : ℝ, 𝓕 (logKernel w) ξ ≠ eigenvalue := by
  by_contra h
  push Not at h
  have ht : Tendsto (𝓕 (logKernel w)) atTop (𝓝 0) :=
    (Real.zero_at_infty_fourier _).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  have hc : Tendsto (fun _ : ℝ => eigenvalue) atTop (𝓝 0) := ht.congr h
  have heigenvalue : eigenvalue=0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact fourier_logKernel_ne_zero hw 0 ((h 0).trans heigenvalue)

/-- Every complex value has only countably many real Fourier frequencies. -/
theorem frequency_level_countable {w : ℂ} (hw : 0 < w.re) (eigenvalue : ℂ) :
    {ξ : ℝ | 𝓕 (logKernel w) ξ=eigenvalue}.Countable := by
  obtain ⟨ξ,hξ⟩ := exists_symbol_ne hw eigenvalue
  have hne : symbol w (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I)-eigenvalue ≠ 0 := by
    rw [← fourier_logKernel_symbol hw]
    exact sub_ne_zero.mpr hξ
  have hz := Bottcher.analyticOnNhd_zeros_countable (symbol_analytic w eigenvalue)
    (symbolStrip_preconnected w) (frequency_mem_strip hw ξ) hne
  apply (hz.preimage (frequency_injective w)).mono
  intro x hx
  exact ⟨frequency_mem_strip hw x,sub_eq_zero.mpr ((fourier_logKernel_symbol hw x).symm.trans hx)⟩

/-- No complex multiplier value occupies a set of positive real frequency measure. -/
theorem frequency_level_ae_ne {w : ℂ} (hw : 0 < w.re) (eigenvalue : ℂ) :
    ∀ᵐ ξ : ℝ ∂volume, 𝓕 (logKernel w) ξ ≠ eigenvalue := by
  simpa only [ae_iff,not_not] using
    ((frequency_level_countable hw eigenvalue).measure_zero (μ := (volume : Measure ℝ)))

/-- The actual Cauchy operator has no nonzero logarithmic `L²` eigenvector at any eigenvalue. -/
theorem eigenvector_eq_zero {w : ℂ} (hw : 0 < w.re) (eigenvalue : ℂ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : operator hw f=eigenvalue • f) : f=0 := by
  let hφ := (continuous_fourier_of_integrable' (logKernel_integrable hw)).measurable
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ
    (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw)
  have ht : fourierL2 ℝ (operator hw f)=M (fourierL2 ℝ f) := by
    rw [operator_eq_multiplier,fourierMulCLM_apply,fourierL2_fourierL2inv]
  have he : M (fourierL2 ℝ f)=eigenvalue • fourierL2 ℝ f := by
    rw [← ht,hf,map_smul]
  have hF : fourierL2 ℝ f=0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ
      (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw) (fourierL2 ℝ f),
      Lp.coeFn_smul eigenvalue (fourierL2 ℝ f),Lp.coeFn_zero ℂ 2 (volume : Measure ℝ),
      frequency_level_ae_ne hw eigenvalue] with ξ hM hs hzero hne
    have hpoint := congrArg (fun v : Lp ℂ 2 (volume : Measure ℝ) => v ξ) he
    change (M (fourierL2 ℝ f)) ξ=(eigenvalue • fourierL2 ℝ f) ξ at hpoint
    rw [hM,hs,Pi.smul_apply,smul_eq_mul] at hpoint
    have hmul : (𝓕 (logKernel w) ξ-eigenvalue)*(fourierL2 ℝ f) ξ=0 := by linear_combination hpoint
    have hz : (fourierL2 ℝ f) ξ=0 := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
    exact hz.trans hzero.symm
  have hi := congrArg (fourierL2inv ℝ) hF
  simpa only [fourierL2inv_fourierL2,map_zero] using hi

#print axioms frequency_level_countable
#print axioms frequency_level_ae_ne
#print axioms eigenvector_eq_zero

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyNoEigenvectors
