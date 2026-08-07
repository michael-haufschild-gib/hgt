import GaloisForLFunctions.RHTower.SlepianKernelFubini
import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaled finite-Fourier composition

The unit-aperture prolate rescaling changes Fourier frequency from `1` to a positive parameter
`κ`.  Composing two such transforms produces `sincSmooth (2π) (κ(x+t))`; on even inputs,
reflection changes `x+t` to `x-t`.  Multiplication by `κ` then gives the Slepian kernel at
bandwidth `2πκ`.  The factor `κ` is essential: it is the Jacobian supplied by the two aperture
rescalings in the physical finite-Fourier eigen-equation.
-/

open MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-- A scaled Fourier character times an integrable function remains integrable on the aperture. -/
theorem integrableOn_scaledFourierChar_mul {a κ : ℝ} {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume) (y : ℝ) :
    IntegrableOn
      (fun t : ℝ => Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t)
      (Set.Icc (-a) a) volume := by
  refine Integrable.mono' hg.norm
    (((by fun_prop : Continuous fun t : ℝ =>
      Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I)).aestronglyMeasurable).mul hg.1) ?_
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  exact le_rfl

/-- Composing finite Fourier transforms with frequency multiplier `κ` collapses to a scaled sinc
kernel. -/
theorem double_integral_scaledFourierChar_eq_sinc
    (a κ x : ℝ) (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume) :
    (∫ y in Set.Icc (-a) a,
        Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I) *
          ∫ t in Set.Icc (-a) a,
            Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t) =
      ∫ t in Set.Icc (-a) a,
        ((sincSmooth (2 * π * a) (κ * (x + t)) : ℝ) : ℂ) * g t := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (-a) a) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]
    exact ⟨by simp⟩
  set F : ℝ → ℝ → ℂ := fun y t =>
    Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I) *
      (Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t) with hF
  have hcurry :
      (∫ y in Set.Icc (-a) a,
          Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I) *
            ∫ t in Set.Icc (-a) a,
              Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t) =
        ∫ y, (∫ t, F y t ∂μ) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [hF]
    exact (integral_const_mul _ _).symm
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) := by
    have h1 : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((-(2 * π * κ * x * p.1) : ℝ) * Complex.I) *
          Complex.exp ((-(2 * π * κ * p.1 * p.2) : ℝ) * Complex.I) := by
      fun_prop
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (μ.prod μ) :=
      (hg.1 : AEStronglyMeasurable g μ).comp_snd
    refine (h1.aestronglyMeasurable.mul h2).congr
      (Filter.Eventually.of_forall fun p => ?_)
    show Complex.exp ((-(2 * π * κ * x * p.1) : ℝ) * Complex.I) *
          Complex.exp ((-(2 * π * κ * p.1 * p.2) : ℝ) * Complex.I) * g p.2 =
      Complex.exp ((-(2 * π * κ * x * p.1) : ℝ) * Complex.I) *
        (Complex.exp ((-(2 * π * κ * p.1 * p.2) : ℝ) * Complex.I) * g p.2)
    exact mul_assoc _ _ _
  have hnormF : ∀ y t, ‖F y t‖ = ‖g t‖ := by
    intro y t
    rw [hF]
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      Real.exp_zero, one_mul]
  have hslice : ∀ᵐ y ∂μ, Integrable (fun t => Function.uncurry F (y, t)) μ := by
    filter_upwards with y
    have h := (integrableOn_scaledFourierChar_mul (κ := κ) hg y).const_mul
      (Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I))
    exact h
  have hnormint : Integrable (fun y => ∫ t, ‖Function.uncurry F (y, t)‖ ∂μ) μ := by
    have hconst : (fun y : ℝ => ∫ t, ‖Function.uncurry F (y, t)‖ ∂μ) =
        fun _ : ℝ => ∫ t, ‖g t‖ ∂μ := by
      funext y
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => hnormF y t)
    rw [hconst]
    exact integrable_const _
  have hint : Integrable (Function.uncurry F) (μ.prod μ) :=
    (integrable_prod_iff hmeas).mpr ⟨hslice, hnormint⟩
  rw [hcurry, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  have hinner : (∫ y, F y t ∂μ) =
      ((sincSmooth (2 * π * a) (κ * (x + t)) : ℝ) : ℂ) * g t := by
    have hrw : ∀ y : ℝ, F y t =
        Complex.exp ((-(2 * π * y * (κ * (x + t))) : ℝ) * Complex.I) * g t := by
      intro y
      show Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I) *
          (Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t) = _
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hstep : (∫ y, F y t ∂μ) =
        ∫ y in Set.Icc (-a) a,
          Complex.exp ((-(2 * π * y * (κ * (x + t))) : ℝ) * Complex.I) * g t := by
      rw [hμ]
      exact integral_congr_ae (Filter.Eventually.of_forall hrw)
    rw [hstep, integral_mul_const,
      setIntegral_Icc_fourierChar a (κ * (x + t)) ha]
  exact hinner

/-- On even inputs, scaled finite-Fourier composition has the reflected Slepian difference
argument. -/
theorem double_integral_scaledFourierChar_eq_sincKernel
    (a κ x : ℝ) (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Icc (-a) a) volume)
    (hgeven : ∀ᵐ t ∂(volume : Measure ℝ), g (-t) = g t) :
    (∫ y in Set.Icc (-a) a,
        Complex.exp ((-(2 * π * κ * x * y) : ℝ) * Complex.I) *
          ∫ t in Set.Icc (-a) a,
            Complex.exp ((-(2 * π * κ * y * t) : ℝ) * Complex.I) * g t) =
      ∫ t in Set.Icc (-a) a,
        ((sincSmooth (2 * π * a) (κ * (x - t)) : ℝ) : ℂ) * g t := by
  rw [double_integral_scaledFourierChar_eq_sinc a κ x ha hg,
    ← setIntegral_Icc_comp_neg a
      (fun t : ℝ => ((sincSmooth (2 * π * a) (κ * (x + t)) : ℝ) : ℂ) * g t)]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [hgeven] with t ht
  intro _
  rw [ht]
  congr 3

/-- Scaling the argument and bandwidth of the entire sinc profile gives the exact Jacobian
factor. -/
theorem mul_sincSmooth_scaled (c κ u : ℝ) (hκ : 0 < κ) :
    κ * sincSmooth c (κ * u) = sincSmooth (c * κ) u := by
  by_cases hu : u = 0
  · subst hu
    rw [mul_zero, sincSmooth_zero, sincSmooth_zero]
    ring
  · have hκu : κ * u ≠ 0 := mul_ne_zero hκ.ne' hu
    rw [sincSmooth_eq_off hκu, sincSmooth_eq_off hu, sincScalar, sincScalar]
    field_simp

/-- At unit aperture, multiplication by the frequency factor converts the scaled-composition
kernel exactly to the Slepian kernel of bandwidth `2πκ`. -/
theorem scaled_sincIntegral_eq_bandIntegral
    (κ x : ℝ) (hκ : 0 < κ) (g : ℝ → ℂ) :
    (κ : ℂ) *
        ∫ t in Set.Icc (-1 : ℝ) 1,
          ((sincSmooth (2 * π) (κ * (x - t)) : ℝ) : ℂ) * g t =
      ∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * π * κ) x t : ℝ) : ℂ) * g t := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_mul,
    mul_sincSmooth_scaled (2 * π) κ (x - t) hκ]
  simp only [sincKernelSmooth]

/-! ## Concrete signed prolate modes -/

/-- The unit-scaled canonical representative of every live signed prolate mode is an exact
Slepian concentration eigenfunction, with eigenvalue equal to the square of its signed
finite-Fourier eigenvalue. -/
theorem evenProlateSignedPointwiseSource_bandTransform_eigen
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * Real.pi * a ^ 2) x t : ℝ) : ℂ) *
          evenProlateSignedPointwiseSource a n hvalue (a * t)) =
      (evenProlateSignedValue a n : ℂ) ^ 2 *
        evenProlateSignedPointwiseSource a n hvalue (a * x) := by
  let g : ℝ → ℂ := fun t => evenProlateSignedPointwiseSource a n hvalue (a * t)
  let χ : ℂ := (evenProlateSignedValue a n : ℂ)
  let κ : ℝ := a ^ 2
  have hκ : 0 < κ := by
    dsimp only [κ]
    positivity
  have hg : Integrable g := by
    dsimp only [g]
    exact (integrable_evenProlateSignedPointwiseSource a ha.le n hvalue).comp_mul_left' ha.ne'
  have hgeven : Function.Even g := by
    intro t
    dsimp only [g]
    rw [show a * -t = -(a * t) by ring]
    exact even_evenProlateSignedPointwiseSource a n hvalue (a * t)
  have heig : ∀ {y : ℝ}, y ∈ Set.Ioo (-1 : ℝ) 1 →
      (a : ℂ) *
          ∫ t in Set.Icc (-1 : ℝ) 1,
            Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * g t =
        χ * g y := by
    intro y hy
    have h := evenProlateSignedPointwiseSource_unitScale_eigen ha n hvalue hy
    simp only [Circle.smul_def, Real.fourierChar_apply, Complex.real_smul, smul_eq_mul] at h
    change (a : ℂ) *
        ∫ t in Set.Icc (-1 : ℝ) 1,
          Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) *
            evenProlateSignedPointwiseSource a n hvalue (a * t) =
      χ * evenProlateSignedPointwiseSource a n hvalue (a * y)
    calc
      (a : ℂ) *
          ∫ t in Set.Icc (-1 : ℝ) 1,
            Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) *
              evenProlateSignedPointwiseSource a n hvalue (a * t) =
        (a : ℂ) *
          ∫ t in Set.Icc (-1 : ℝ) 1,
            Complex.exp ((2 * Real.pi * -((a * t) * (a * y)) : ℝ) * Complex.I) *
              evenProlateSignedPointwiseSource a n hvalue (a * t) := by
                congr 1
                refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
                congr 2
                push_cast
                dsimp only [κ]
                rw [Complex.ofReal_pow]
                ring
      _ = χ * evenProlateSignedPointwiseSource a n hvalue (a * y) := by
            simpa only [χ] using h
  let innerF : ℝ → ℂ := fun y =>
    ∫ t in Set.Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * g t
  let outerF : ℝ → ℂ := fun y =>
    Complex.exp ((-(2 * Real.pi * κ * x * y) : ℝ) * Complex.I)
  have hscaledDouble :
      (a : ℂ) * (∫ y in Set.Icc (-1 : ℝ) 1, outerF y * innerF y) =
        χ * ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * g y := by
    rw [← integral_const_mul]
    calc
      (∫ y in Set.Icc (-1 : ℝ) 1, (a : ℂ) * (outerF y * innerF y)) =
          ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * ((a : ℂ) * innerF y) := by
            refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
            ring
      _ = ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * (χ * g y) := by
            refine setIntegral_congr_ae measurableSet_Icc ?_
            filter_upwards [Ioo_ae_eq_Icc] with y hy
            intro hycc
            rw [heig (hy.mpr hycc)]
      _ = χ * ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * g y := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
            ring
  have hdouble := double_integral_scaledFourierChar_eq_sincKernel
    1 κ x (by norm_num) hg.integrableOn (Filter.Eventually.of_forall hgeven)
  change (∫ y in Set.Icc (-1 : ℝ) 1, outerF y * innerF y) =
      ∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincSmooth (2 * Real.pi * 1) (κ * (x - t)) : ℝ) : ℂ) * g t at hdouble
  norm_num at hdouble
  have hband := scaled_sincIntegral_eq_bandIntegral κ x hκ g
  change (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincKernelSmooth (2 * Real.pi * κ) x t : ℝ) : ℂ) * g t) = χ ^ 2 * g x
  rw [← hband, ← hdouble]
  calc
    (κ : ℂ) * (∫ y in Set.Icc (-1 : ℝ) 1, outerF y * innerF y) =
        (a : ℂ) * ((a : ℂ) * ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * innerF y) := by
          dsimp only [κ]
          push_cast
          ring
    _ = (a : ℂ) * (χ * ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * g y) := by
          rw [hscaledDouble]
    _ = χ * ((a : ℂ) * ∫ y in Set.Icc (-1 : ℝ) 1, outerF y * g y) := by
          ring
    _ = χ * (χ * g x) := by
          rw [heig hx]
    _ = χ ^ 2 * g x := by
          ring

end RHTower
