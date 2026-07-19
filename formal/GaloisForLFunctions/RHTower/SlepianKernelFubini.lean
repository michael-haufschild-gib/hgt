import GaloisForLFunctions.RHTower.SlepianKernelFourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The composed band transform collapses to the Slepian kernel

Applying the band-limited Fourier cutoff twice produces a double integral over the aperture.
Swapping the order of integration frees the inner variable, and the resulting inner integral is
exactly the band integral of a Fourier character — the Slepian sinc profile.  So

```text
∫∫ e^{−2πixy} e^{−2πiyt} g(t) dt dy = ∫ K̃(x+t)·g(t) dt,
```

with `K̃ = sincSmooth (2πa)`.  The argument that appears is `x + t`, **not** `x − t`: composing a
cutoff with *itself* rather than with its adjoint reflects one variable.  On functions even in
`t` the two agree after `t ↦ −t`, which is the reason the constrained prolate problem is posed on
the even carrier — off it, the Slepian kernel is not the kernel of this operator.

Fubini applies because the integrand is dominated by `‖g‖` uniformly in the free variable, and
the aperture has finite measure.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

theorem norm_fourierChar (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem continuous_fourierChar_mul (y : ℝ) :
    Continuous fun t : ℝ => Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) := by
  fun_prop

/-- A character times an integrable function is integrable on the aperture. -/
theorem integrableOn_fourierChar_mul {a : ℝ} {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume) (y : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t)
      (Set.Icc (-a) a) volume := by
  refine Integrable.mono' hg.norm
    (((continuous_fourierChar_mul y).aestronglyMeasurable).mul hg.1) ?_
  filter_upwards with t
  rw [norm_mul, norm_fourierChar, one_mul]

/-- **The composed band-Fourier double integral is the Slepian kernel integral.** -/
theorem double_integral_fourierChar_eq_sinc (a x : ℝ) (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume) :
    (∫ y in Set.Icc (-a) a, Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I)
        * ∫ t in Set.Icc (-a) a, Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t)
      = ∫ t in Set.Icc (-a) a, ((sincSmooth (2 * π * a) (x + t) : ℝ) : ℂ) * g t := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (-a) a) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by simp⟩
  set F : ℝ → ℝ → ℂ := fun y t =>
    Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I)
      * (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t) with hF
  -- the double integral in curried form
  have hcurry : (∫ y in Set.Icc (-a) a, Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I)
      * ∫ t in Set.Icc (-a) a, Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t)
      = ∫ y, (∫ t, F y t ∂μ) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [hF]
    exact (integral_const_mul _ _).symm
  -- integrability of the uncurried integrand
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) := by
    have h1 : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((-(2 * π * x * p.1) : ℝ) * Complex.I)
          * Complex.exp ((-(2 * π * p.1 * p.2) : ℝ) * Complex.I) := by fun_prop
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (μ.prod μ) :=
      (hg.1 : AEStronglyMeasurable g μ).comp_snd
    refine (h1.aestronglyMeasurable.mul h2).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show Complex.exp ((-(2 * π * x * p.1) : ℝ) * Complex.I)
        * Complex.exp ((-(2 * π * p.1 * p.2) : ℝ) * Complex.I) * g p.2
      = Complex.exp ((-(2 * π * x * p.1) : ℝ) * Complex.I)
        * (Complex.exp ((-(2 * π * p.1 * p.2) : ℝ) * Complex.I) * g p.2)
    exact mul_assoc _ _ _
  have hnormF : ∀ y t, ‖F y t‖ = ‖g t‖ := by
    intro y t
    rw [hF]
    simp only [norm_mul, norm_fourierChar, one_mul]
  have hslice : ∀ᵐ y ∂μ, Integrable (fun t => Function.uncurry F (y, t)) μ := by
    filter_upwards with y
    have h := (integrableOn_fourierChar_mul hg y).const_mul
      (Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I))
    exact h
  have hnormint : Integrable (fun y => ∫ t, ‖Function.uncurry F (y, t)‖ ∂μ) μ := by
    have hconst : (fun y : ℝ => ∫ t, ‖Function.uncurry F (y, t)‖ ∂μ)
        = fun _ : ℝ => ∫ t, ‖g t‖ ∂μ := by
      funext y
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => hnormF y t)
    rw [hconst]
    exact integrable_const _
  have hint : Integrable (Function.uncurry F) (μ.prod μ) :=
    (integrable_prod_iff hmeas).mpr ⟨hslice, hnormint⟩
  rw [hcurry, integral_integral_swap hint]
  -- the inner integral is the sinc profile
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  have hinner : (∫ y, F y t ∂μ)
      = ((sincSmooth (2 * π * a) (x + t) : ℝ) : ℂ) * g t := by
    have hrw : ∀ y : ℝ, F y t
        = Complex.exp ((-(2 * π * y * (x + t)) : ℝ) * Complex.I) * g t := by
      intro y
      show Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I)
          * (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t) = _
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hstep : (∫ y, F y t ∂μ)
        = ∫ y in Set.Icc (-a) a,
            Complex.exp ((-(2 * π * y * (x + t)) : ℝ) * Complex.I) * g t := by
      rw [hμ]
      exact integral_congr_ae (Filter.Eventually.of_forall hrw)
    rw [hstep, integral_mul_const, setIntegral_Icc_fourierChar a (x + t) ha]
  exact hinner

/-! ## The even carrier: `x + t` becomes `x − t` -/

/-- A set integral over a symmetric aperture is reflection invariant. -/
theorem setIntegral_Icc_comp_neg (a : ℝ) (h : ℝ → ℂ) :
    ∫ t in Set.Icc (-a) a, h (-t) = ∫ t in Set.Icc (-a) a, h t := by
  have hsym : ∀ t : ℝ, t ∈ Set.Icc (-a) a ↔ -t ∈ Set.Icc (-a) a := by
    intro t
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  calc
    (∫ t, (Set.Icc (-a) a).indicator (fun u => h (-u)) t) =
        ∫ t, (Set.Icc (-a) a).indicator h (-t) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      change (Set.Icc (-a) a).indicator (fun u => h (-u)) t =
        (Set.Icc (-a) a).indicator h (-t)
      by_cases ht : t ∈ Set.Icc (-a) a
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hsym t).mp ht)]
      · rw [Set.indicator_of_notMem ht,
          Set.indicator_of_notMem (fun hc => ht ((hsym t).mpr hc))]
    _ = ∫ t, (Set.Icc (-a) a).indicator h t :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding _

/-- **On the even carrier the composed band transform has the Slepian kernel.**  The composition
produces the argument `x + t`; reflecting the integration variable, which is free on an even
function, turns it into `x − t`.  This is the identification that lets the prolate ODE apparatus
speak about the concentration operator of the constrained transfer. -/
theorem double_integral_fourierChar_eq_sincKernel (a x : ℝ) (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume)
    (hgeven : ∀ᵐ t ∂(volume : Measure ℝ), g (-t) = g t) :
    (∫ y in Set.Icc (-a) a, Complex.exp ((-(2 * π * x * y) : ℝ) * Complex.I)
        * ∫ t in Set.Icc (-a) a, Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I) * g t)
      = ∫ t in Set.Icc (-a) a, ((sincKernelSmooth (2 * π * a) x t : ℝ) : ℂ) * g t := by
  rw [double_integral_fourierChar_eq_sinc a x ha hg,
    ← setIntegral_Icc_comp_neg a (fun t : ℝ => ((sincSmooth (2 * π * a) (x + t) : ℝ) : ℂ) * g t)]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [hgeven] with t ht
  intro _
  rw [ht, sincKernelSmooth]
  congr 2

end RHTower

end
