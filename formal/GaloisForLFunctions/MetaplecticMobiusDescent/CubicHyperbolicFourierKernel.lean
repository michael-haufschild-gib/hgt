/-
The cubic hyperbolic Fourier kernel adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicTraceFourierPeriodization
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# The hyperbolic kernel and its exact zero Fourier mode

Polar integration and the substitution `t=r²` show that `(1+|z|²)⁻ˢ`
is integrable for `Re s>1`, with integral `π/(s−1)`. Its trace-normalized
Fourier transform agrees with the Euclidean transform at frequency
`2 conjugate(ξ)`, fixing the normalization for the nonzero modes.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * tracePhase (-freq*z)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1<s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z*tracePhase (-freq*z)) :=
  trace_mul_integrable _ (hyperbolicKernel_integrable s hs) freq

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    using integral_hyperbolicKernel s hs

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * tracePhase (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma sourceFourierKernel_eq_fourier (s freq : ℂ) :
    sourceFourierKernel s freq = 𝓕 (hyperbolicKernel s) (2*starRingEnd ℂ freq) :=
  traceIntegral_eq_fourier (hyperbolicKernel s) freq


#print axioms hyperbolicKernel_integrable
#print axioms integral_hyperbolicKernel
#print axioms sourceFourierKernel_eq_fourier
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
