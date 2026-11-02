import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyFrequencyMaximum
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCore
import Mathlib.Analysis.MellinInversion

/-!
# The actual Cauchy averaging operator on logarithmic L²

Logarithmic height conjugates the actual multiplicative Cauchy integral to
an integrable convolution kernel. Its Fourier symbol is the certified
Gamma quotient, so the operator is injective and its norm is bounded by
the central multiplier. For the canonical scattering-subtracted field,
the change of variables identifies both weighted energies and gives the
same explicit bound on the actual Cauchy image.
-/

open Complex Set MeasureTheory Filter FourierTransform
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerCauchyFrequencyMaximum
open GaloisForLFunctions.HTGeometry
open scoped Topology Convolution
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyL2

/-- The actual Cauchy kernel in balanced logarithmic height coordinates. -/
def logKernel (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(w/2)*(x : ℂ))*cauchyKernel w (Real.exp (-x))

private theorem exp_neg_deriv :
    ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem exp_neg_image : Real.exp ∘ Neg.neg '' (univ : Set ℝ)=Ioi 0 := by
  rw [Set.image_comp,Set.image_univ_of_surjective neg_surjective,Set.image_univ,Real.range_exp]

private theorem exp_neg_inj : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem log_change_factor (x : ℝ) (s v : ℂ) :
    Real.exp (-x) • ((Real.exp (-x) : ℂ)^(s-1) • v)=Complex.exp (-s*(x : ℂ))*v := by
  have hA : (Real.exp (-x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hp : (Real.exp (-x) : ℂ)*(Real.exp (-x) : ℂ)^(s-1)=Complex.exp (-s*(x : ℂ)) := by
    calc
      _ = (Real.exp (-x) : ℂ)^(1 : ℂ)*(Real.exp (-x) : ℂ)^(s-1) := by rw [Complex.cpow_one]
      _ = (Real.exp (-x) : ℂ)^s := by
        rw [← Complex.cpow_add _ _ hA]
        congr 1
        ring
      _ = _ := by
        rw [Complex.cpow_def_of_ne_zero hA,← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
        congr 1
        push_cast
        ring
  change (Real.exp (-x) : ℂ)*((Real.exp (-x) : ℂ)^(s-1)*v)=_
  rw [← mul_assoc,hp]

private theorem mellin_log_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s=∫ x : ℝ,Complex.exp (-s*(x : ℂ))*f (Real.exp (-x)) := by
  rw [mellin,← exp_neg_image,integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_inj]
  simp only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),
    Measure.restrict_univ,log_change_factor]

/-- Absolute central Mellin convergence gives an integrable actual logarithmic kernel. -/
theorem logKernel_integrable {w : ℂ} (hw : 0 < w.re) : Integrable (logKernel w) := by
  have h : MellinConvergent (cauchyKernel w) (w/2) := by
    simpa only [ofReal_zero,zero_mul,add_zero] using (frequency_hasMellin hw 0).1
  rw [MellinConvergent,← exp_neg_image,integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_inj] at h
  simpa only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),
    integrableOn_univ,log_change_factor,logKernel] using! h

/-- Fourier frequency retains the full complex central Mellin parameter. -/
theorem fourier_logKernel (w : ℂ) (ξ : ℝ) :
    𝓕 (logKernel w) ξ=mellin (cauchyKernel w) (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I) := by
  rw [mellin_log_integral,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [logKernel,smul_eq_mul]
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The logarithmic kernel is measurable for every parameter. -/
theorem logKernel_measurable (w : ℂ) : Measurable (logKernel w) := by
  unfold logKernel cauchyKernel cauchyWeight
  fun_prop

/-- The actual Cauchy integral extends to a bounded operator on logarithmic `L²`. -/
def operator {w : ℂ} (hw : 0 < w.re) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (convolutionKernel (logKernel w) (logKernel_measurable w) (logKernel_integrable hw)).op

/-- The operator acts by the actual convolution integral on every `L²` class. -/
theorem operator_ae_integral {w : ℂ} (hw : 0 < w.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (operator hw f : ℝ → ℂ)=ᵐ[volume] fun y => ∫ z : ℝ,logKernel w (y-z)*f z := by
  have h := (convolutionKernel (logKernel w) (logKernel_measurable w) (logKernel_integrable hw)).op_coeFn f
  filter_upwards [h] with y hy
  exact hy

/-- The actual Fourier multiplier is the exact Gamma quotient. -/
theorem fourier_logKernel_symbol {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    𝓕 (logKernel w) ξ=symbol w (w/2+((2*Real.pi*ξ : ℝ) : ℂ)*I) := by
  rw [fourier_logKernel,(frequency_hasMellin hw (2*Real.pi*ξ)).2]

/-- The actual logarithmic multiplier is nowhere zero. -/
theorem fourier_logKernel_ne_zero {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    𝓕 (logKernel w) ξ ≠ 0 := by
  rw [fourier_logKernel_symbol hw]
  apply symbol_ne_zero hw <;> simp <;> linarith only [hw]

/-- Central frequency bounds every value of the actual Fourier multiplier. -/
theorem fourier_logKernel_norm_le {w : ℂ} (hw : 0 < w.re) (ξ : ℝ) :
    ‖𝓕 (logKernel w) ξ‖ ≤ ‖symbol w (w/2)‖ := by
  rw [fourier_logKernel_symbol hw]
  exact norm_symbol_frequency_le hw (2*Real.pi*ξ)

/-- Plancherel identifies the actual integral operator with its central-weight multiplier. -/
theorem operator_eq_multiplier {w : ℂ} (hw : 0 < w.re) :
    operator hw=fourierMulCLM (continuous_fourier_of_integrable' (logKernel_integrable hw)).measurable
      (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw) := by
  rw [operator,convolutionKernel_op_eq_fourierMulCLM]
  exact fourierMulCLM_congr_ae _ _ _ _ _ _ (Eventually.of_forall (fun _ => rfl))

/-- The exact central multiplier bounds the actual operator norm. -/
theorem operator_norm_le {w : ℂ} (hw : 0 < w.re) : ‖operator hw‖ ≤ ‖symbol w (w/2)‖ := by
  rw [operator_eq_multiplier]
  exact norm_fourierMulCLM_le _ _ _

/-- The sharp Gamma envelope also bounds the actual integral operator strictly. -/
theorem operator_norm_lt {w : ℂ} (hw : 0 < w.re) : ‖operator hw‖ < (2 : ℝ)^((1-w.re)/2) := by
  have h := MayerCauchySchur.norm_mellin_half_lt hw
  have he := (frequency_hasMellin hw 0).2
  simp only [ofReal_zero,zero_mul,add_zero] at he
  rw [he] at h
  exact (operator_norm_le hw).trans_lt h

/-- The actual integral operator is strictly contractive at spectral abscissa at least one. -/
theorem operator_contractive {w : ℂ} (hw : 1 ≤ w.re) :
    ‖operator (zero_lt_one.trans_le hw)‖ < 1 := by
  have h := MayerCauchySchur.central_contractive hw
  have he := (frequency_hasMellin (zero_lt_one.trans_le hw) 0).2
  simp only [ofReal_zero,zero_mul,add_zero] at he
  rw [he] at h
  exact (operator_norm_le (zero_lt_one.trans_le hw)).trans_lt h

/-- No nonzero square-integrable field is lost by the actual Cauchy averaging operator. -/
theorem operator_injective {w : ℂ} (hw : 0 < w.re) : Function.Injective (operator hw) := by
  intro f g hfg
  let hφ := (continuous_fourier_of_integrable' (logKernel_integrable hw)).measurable
  let M := lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ
    (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw)
  have hf (v : Lp ℂ 2 (volume : Measure ℝ)) : fourierL2 ℝ (operator hw v)=M (fourierL2 ℝ v) := by
    rw [operator_eq_multiplier,fourierMulCLM_apply,fourierL2_fourierL2inv]
  have he : M (fourierL2 ℝ f)=M (fourierL2 ℝ g) := by rw [← hf,← hf,hfg]
  have hfour : fourierL2 ℝ f=fourierL2 ℝ g := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ
      (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw) (fourierL2 ℝ f),
      lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hφ
      (norm_nonneg (symbol w (w/2))) (fourier_logKernel_norm_le hw) (fourierL2 ℝ g)] with ξ hfξ hgξ
    have hi := congrArg (fun v : Lp ℂ 2 (volume : Measure ℝ) => v ξ) he
    change (M (fourierL2 ℝ f)) ξ= (M (fourierL2 ℝ g)) ξ at hi
    rw [hfξ,hgξ] at hi
    exact mul_left_cancel₀ (fourier_logKernel_ne_zero hw ξ) hi
  have ht := congrArg (fourierL2inv ℝ) hfour
  simpa only [fourierL2inv_fourierL2] using ht

#print axioms logKernel_integrable
#print axioms fourier_logKernel
#print axioms operator_ae_integral
#print axioms fourier_logKernel_symbol
#print axioms fourier_logKernel_ne_zero
#print axioms fourier_logKernel_norm_le
#print axioms operator_eq_multiplier
#print axioms operator_norm_le
#print axioms operator_norm_lt
#print axioms operator_contractive
#print axioms operator_injective

/-- A height field expressed in the central logarithmic coordinate. -/
def logField (w : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(w/2)*(x : ℂ))*f (Real.exp (-x))

private theorem norm_logField (w : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    ‖logField w f x‖=(Real.exp (-x))^(w.re/2)*‖f (Real.exp (-x))‖ := by
  rw [logField,norm_mul,Complex.norm_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 1
  congr 1
  simp
  ring

private theorem norm_logField_sq (w : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    ‖logField w f x‖^2=Real.exp (-x)*
      ((Real.exp (-x))^(w.re-1)*‖f (Real.exp (-x))‖^2) := by
  have ha : 0 < Real.exp (-x) := Real.exp_pos _
  have hp : ((Real.exp (-x))^(w.re/2))^2=(Real.exp (-x))^w.re := by
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have hq : Real.exp (-x)*(Real.exp (-x))^(w.re-1)=(Real.exp (-x))^w.re := by
    calc
      _ = (Real.exp (-x))^(1 : ℝ)*(Real.exp (-x))^(w.re-1) := by rw [Real.rpow_one]
      _ = (Real.exp (-x))^(1+(w.re-1)) := (Real.rpow_add ha _ _).symm
      _ = _ := by congr 1; ring
  rw [norm_logField,mul_pow,hp,← mul_assoc,hq]

/-- Logarithmic square energy equals the actual central-weight height energy. -/
theorem logField_energy_integral (w : ℂ) (f : ℝ → ℂ) :
    (∫ x : ℝ,‖logField w f x‖^2)=∫ a in Ioi (0 : ℝ),a^(w.re-1)*‖f a‖^2 := by
  rw [← exp_neg_image,integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_inj]
  simp only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),smul_eq_mul,
    Measure.restrict_univ,← norm_logField_sq]

/-- The logarithmic profile has integrable square norm exactly when its weighted height field does. -/
theorem logField_energy_integrable_iff (w : ℂ) (f : ℝ → ℂ) :
    Integrable (fun x : ℝ => ‖logField w f x‖^2) ↔
      IntegrableOn (fun a : ℝ => a^(w.re-1)*‖f a‖^2) (Ioi 0) := by
  rw [← exp_neg_image,integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ exp_neg_deriv exp_neg_inj]
  simp only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),smul_eq_mul,
    integrableOn_univ,← norm_logField_sq]

private theorem log_product (w : ℂ) (f : ℝ → ℂ) (y x : ℝ) :
    logKernel w x*logField w f (y-x)=Complex.exp (-(w/2)*(y : ℂ))*
      (cauchyKernel w (Real.exp (-x))*f (Real.exp (-y)/Real.exp (-x))) := by
  have he : Real.exp (-(y-x))=Real.exp (-y)/Real.exp (-x) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hp : Complex.exp (-(w/2)*(x : ℂ))*Complex.exp (-(w/2)*((y-x : ℝ) : ℂ))=
      Complex.exp (-(w/2)*(y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [logKernel,logField,he]
  calc
    _ = (Complex.exp (-(w/2)*(x : ℂ))*Complex.exp (-(w/2)*((y-x : ℝ) : ℂ)))*
        (cauchyKernel w (Real.exp (-x))*f (Real.exp (-y)/Real.exp (-x))) := by ring
    _ = _ := by rw [hp]

private theorem cauchy_log_integral (w : ℂ) (f : ℝ → ℂ) (y : ℝ) :
    _root_.RHTower.positiveMellinConvolution (cauchyKernel w) f (Real.exp (-y))=
      ∫ x : ℝ,cauchyKernel w (Real.exp (-x))*f (Real.exp (-y)/Real.exp (-x)) := by
  rw [_root_.RHTower.positiveMellinConvolution,← exp_neg_image,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ exp_neg_deriv exp_neg_inj]
  simp only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : (Real.exp (-x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  change (Real.exp (-x) : ℂ)*
    (cauchyKernel w (Real.exp (-x))*f (Real.exp (-y)/Real.exp (-x))/(Real.exp (-x) : ℂ))=_
  field_simp

/-- The logarithmic convolution is the literal Cauchy transform of the original height field. -/
theorem convolution_logField (w : ℂ) (f : ℝ → ℂ) (y : ℝ) :
    (∫ z : ℝ,logKernel w (y-z)*logField w f z)=
      logField w (_root_.RHTower.positiveMellinConvolution (cauchyKernel w) f) y := by
  calc
    _ = ∫ x : ℝ,logKernel w x*logField w f (y-x) := by
      have h := integral_sub_left_eq_self
        (fun z : ℝ => logKernel w (y-z)*logField w f z) volume y
      simpa only [sub_sub_self] using h.symm
    _ = Complex.exp (-(w/2)*(y : ℂ))*
        ∫ x : ℝ,cauchyKernel w (Real.exp (-x))*f (Real.exp (-y)/Real.exp (-x)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun x => log_product w f y x))
    _ = _ := by rw [← cauchy_log_integral]; rfl

/-- The actual scattering-subtracted canonical field belongs to logarithmic `L²`. -/
theorem core_log_memLp {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2) (him : 0 < w.im) :
    MemLp (logField w (MayerScatteringCore.fieldCore w)) 2 (volume : Measure ℝ) := by
  have h0 : w ≠ 0 := by rintro rfl; norm_num at hw
  have h2 : w ≠ 2 := by rintro rfl; norm_num at him
  have hE := MayerEpsteinHeightMeasurability.measurable_epsteinField h0 h2
  have hF : Measurable (MayerScatteringCore.fieldCore w) := by
    unfold MayerScatteringCore.fieldCore MayerScatteringCore.scatteringPowers
    fun_prop
  have hm : Measurable (logField w (MayerScatteringCore.fieldCore w)) := by
    unfold logField
    fun_prop
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    ((logField_energy_integrable_iff w _).mpr (MayerScatteringCore.weighted_energy_integrable hw hw2 him))

/-- On the canonical core the bounded operator agrees almost everywhere with its actual Cauchy image. -/
theorem operator_core_ae {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2) (him : 0 < w.im) :
    (operator hw ((core_log_memLp hw hw2 him).toLp
      (logField w (MayerScatteringCore.fieldCore w))) : ℝ → ℂ)=ᵐ[volume]
      logField w (_root_.RHTower.positiveMellinConvolution (cauchyKernel w)
        (MayerScatteringCore.fieldCore w)) := by
  have hcoe := (core_log_memLp hw hw2 him).coeFn_toLp
  filter_upwards [operator_ae_integral hw ((core_log_memLp hw hw2 him).toLp
    (logField w (MayerScatteringCore.fieldCore w)))] with y hy
  rw [hy,← convolution_logField]
  apply integral_congr_ae
  filter_upwards [hcoe] with z hz
  rw [hz]

#print axioms logField_energy_integral
#print axioms logField_energy_integrable_iff
#print axioms convolution_logField
#print axioms core_log_memLp
#print axioms operator_core_ae

/-- The actual Cauchy image of the canonical core has finite central-weight square energy. -/
theorem cauchy_core_energy_integrable {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2)
    (him : 0 < w.im) :
    IntegrableOn (fun a : ℝ => a^(w.re-1)*
      ‖_root_.RHTower.positiveMellinConvolution (cauchyKernel w)
        (MayerScatteringCore.fieldCore w) a‖^2) (Ioi 0) := by
  have hm := (memLp_congr_ae (operator_core_ae hw hw2 him)).mp
    (Lp.memLp (operator hw ((core_log_memLp hw hw2 him).toLp
      (logField w (MayerScatteringCore.fieldCore w)))))
  exact (logField_energy_integrable_iff w _).mp
    ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)

private theorem lp_norm_sq (v : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖v‖^2=∫ x : ℝ,‖v x‖^2 := by
  rw [Lp.norm_def,toReal_eLpNorm (Lp.aestronglyMeasurable v),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable v)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- The central Gamma multiplier bounds the actual corrected-period energy. -/
theorem cauchy_core_energy_le {w : ℂ} (hw : 0 < w.re) (hw2 : w.re < 2) (him : 0 < w.im) :
    (∫ a in Ioi (0 : ℝ),a^(w.re-1)*
      ‖_root_.RHTower.positiveMellinConvolution (cauchyKernel w)
        (MayerScatteringCore.fieldCore w) a‖^2) ≤
      ‖symbol w (w/2)‖^2*∫ a in Ioi (0 : ℝ),a^(w.re-1)*‖MayerScatteringCore.fieldCore w a‖^2 := by
  let v := (core_log_memLp hw hw2 him).toLp (logField w (MayerScatteringCore.fieldCore w))
  have hin : ‖v‖^2=∫ a in Ioi (0 : ℝ),a^(w.re-1)*‖MayerScatteringCore.fieldCore w a‖^2 := by
    rw [lp_norm_sq,← logField_energy_integral]
    apply integral_congr_ae
    filter_upwards [(core_log_memLp hw hw2 him).coeFn_toLp] with x hx
    rw [show v x=logField w (MayerScatteringCore.fieldCore w) x from hx]
  have hout : ‖operator hw v‖^2=∫ a in Ioi (0 : ℝ),a^(w.re-1)*
      ‖_root_.RHTower.positiveMellinConvolution (cauchyKernel w)
        (MayerScatteringCore.fieldCore w) a‖^2 := by
    rw [lp_norm_sq,← logField_energy_integral]
    apply integral_congr_ae
    filter_upwards [operator_core_ae hw hw2 him] with x hx
    rw [show (operator hw v) x=logField w
      (_root_.RHTower.positiveMellinConvolution (cauchyKernel w) (MayerScatteringCore.fieldCore w)) x from hx]
  have h := ContinuousLinearMap.le_of_opNorm_le (operator hw) (operator_norm_le hw) v
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow,hout,hin] at hs
  exact hs

#print axioms cauchy_core_energy_integrable
#print axioms cauchy_core_energy_le

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyL2
