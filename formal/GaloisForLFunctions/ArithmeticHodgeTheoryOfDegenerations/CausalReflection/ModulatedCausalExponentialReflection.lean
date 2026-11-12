import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.NegativeHalfLineLaplaceContinuity
import GaloisForLFunctions.RHTower.SoninPacketFourierModulation

/-!
# Modulation of actual causal exponential reflections

Unit-modulus modulation conjugates a real-rate causal resolvent into a
complex-rate resolvent. The identities hold for literal representatives;
L¹ and L² admissions follow from exact pointwise norm preservation.
-/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Multiplication of a literal profile by a real-frequency character. -/
def causalModulation (b : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * b * u : ℝ) : ℂ) * Complex.I) * f u

/-- The complex-rate causal kernel, with decay rate a and frequency b. -/
def modulatedCausalExponential (a b : ℝ) : ℝ → ℂ :=
  causalModulation (-b) (causalFourierExponential a)

def modulatedCausalConvolution (a b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  modulatedCausalExponential a b ⋆[ContinuousLinearMap.mul ℂ ℂ] f

/-- Reflection changes the phase and keeps the real decay coefficient. -/
def modulatedCausalReflection (a b : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  -f u + (2 * a : ℂ) * modulatedCausalConvolution a b f u

theorem norm_causalModulation (b : ℝ) (f : ℝ → ℂ) (u : ℝ) :
    ‖causalModulation b f u‖ = ‖f u‖ := by
  simp only [causalModulation, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, Real.exp_zero, one_mul]

theorem causalModulation_zero (f : ℝ → ℂ) : causalModulation 0 f = f := by
  funext u
  simp only [causalModulation, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]

theorem causalModulation_add (b c : ℝ) (f : ℝ → ℂ) :
    causalModulation b (causalModulation c f) = causalModulation (b + c) f := by
  funext u
  unfold causalModulation
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem measurable_causalModulation (b : ℝ) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (causalModulation b f) := by
  exact (by fun_prop : Continuous (fun u : ℝ =>
    Complex.exp (((2 * Real.pi * b * u : ℝ) : ℂ) * Complex.I))).measurable.mul hf

theorem measurable_modulatedCausalExponential (a b : ℝ) :
    Measurable (modulatedCausalExponential a b) := by
  apply measurable_causalModulation
  unfold causalFourierExponential
  exact (by fun_prop : Continuous (fun u : ℝ => (Real.pi : ℂ) *
    Complex.exp (-((Real.pi * a : ℝ) : ℂ) * u))).measurable.indicator measurableSet_Ioi

/-- The literal resolvent is measurable without choosing an almost-everywhere representative. -/
theorem measurable_modulatedCausalConvolution (a b : ℝ) {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (modulatedCausalConvolution a b f) := by
  have hm : StronglyMeasurable (modulatedCausalConvolution a b f) := by
    apply StronglyMeasurable.integral_prod_right
    exact (((measurable_modulatedCausalExponential a b).comp measurable_snd).mul
      (hf.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact hm.measurable

theorem measurable_modulatedCausalReflection (a b : ℝ) {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (modulatedCausalReflection a b f) :=
  hf.neg.add (measurable_const.mul (measurable_modulatedCausalConvolution a b hf))

theorem aestronglyMeasurable_causalModulation (b : ℝ) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (causalModulation b f) := by
  have hc : Continuous (fun u : ℝ =>
      Complex.exp (((2 * Real.pi * b * u : ℝ) : ℂ) * Complex.I)) := by fun_prop
  exact hc.aestronglyMeasurable.mul hf

theorem integrable_causalModulation (b : ℝ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (causalModulation b f) := by
  apply hf.norm.mono' (aestronglyMeasurable_causalModulation b hf.aestronglyMeasurable)
  exact Eventually.of_forall fun u => (norm_causalModulation b f u).le

theorem memLp_two_causalModulation (b : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (causalModulation b f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_causalModulation b hf.aestronglyMeasurable)).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply hi.congr
  exact Eventually.of_forall fun u =>
    (congrArg (fun r : ℝ => r ^ 2) (norm_causalModulation b f u)).symm

/-- Modulation distributes across literal convolution without regularity premises. -/
theorem causalModulation_convolution (b : ℝ) (k f : ℝ → ℂ) :
    causalModulation b (k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      causalModulation b k ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f := by
  funext y
  rw [causalModulation, convolution_def, convolution_def, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  change Complex.exp (((2 * Real.pi * b * y : ℝ) : ℂ) * Complex.I) * (k t * f (y - t)) =
    causalModulation b k t * causalModulation b f (y - t)
  unfold causalModulation
  have he : Complex.exp (((2 * Real.pi * b * y : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * b * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * b * (y - t) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The complex-rate resolvent is a modulation conjugate of the real one. -/
theorem modulatedCausalConvolution_eq_conjugate (a b : ℝ) (f : ℝ → ℂ) :
    modulatedCausalConvolution a b f =
      causalModulation (-b)
        (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) := by
  rw [causalModulation_convolution, causalModulation_add, neg_add_cancel, causalModulation_zero]
  rfl

/-- Reflection has the same modulation conjugacy as its resolvent. -/
theorem modulatedCausalReflection_eq_conjugate (a b : ℝ) (f : ℝ → ℂ) :
    modulatedCausalReflection a b f =
      causalModulation (-b) (causalBlaschkeStep a (causalModulation b f)) := by
  have hc := congrFun (modulatedCausalConvolution_eq_conjugate a b f)
  have hi := congrFun (causalModulation_add (-b) b f)
  rw [neg_add_cancel, causalModulation_zero] at hi
  funext u
  rw [modulatedCausalReflection, hc u]
  change -f u + (2 * a : ℂ) * causalModulation (-b)
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) u = _
  rw [← hi u]
  unfold causalModulation causalBlaschkeStep
  ring

/-- Real exponential weights commute with unit-modulus modulation. -/
theorem causalLaplaceWeighted_causalModulation (x b : ℝ) (f : ℝ → ℂ) :
    causalLaplaceWeighted x (causalModulation b f) =
      causalModulation b (causalLaplaceWeighted x f) := by
  funext u
  unfold causalLaplaceWeighted causalModulation
  ring

theorem fourier_causalModulation (b : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (causalModulation b f) ξ = 𝓕 f (ξ - b) :=
  fourier_exp_mul f b ξ

/-- The complex-rate resolvent and reflection preserve actual L¹ admission. -/
theorem integrable_modulatedCausalConvolution {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) : Integrable (modulatedCausalConvolution a b f) := by
  rw [modulatedCausalConvolution_eq_conjugate]
  apply integrable_causalModulation
  exact (causalFourierExponential_integrable ha).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_causalModulation b hf)

end GaloisForLFunctions.HTGeometry
