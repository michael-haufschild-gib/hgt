import GaloisForLFunctions.RHTower.SlepianKernelFubini
import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative
import GaloisForLFunctions.RHTower.ProlateJointEigenExistence
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

/-- A normalized canonical signed-mode source cannot vanish throughout the open physical
aperture. -/
theorem exists_evenProlateSignedPointwiseSource_ne_zero_interior
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ x ∈ Set.Ioo (-a) a, evenProlateSignedPointwiseSource a n hvalue x ≠ 0 := by
  by_contra hnone
  have hzero : ∀ x ∈ Set.Ioo (-a) a,
      evenProlateSignedPointwiseSource a n hvalue x = 0 := by
    intro x hx
    by_contra hxne
    exact hnone ⟨x, hx, hxne⟩
  have hae : evenProlateSignedPointwiseSource a n hvalue =ᵐ[volume] 0 := by
    filter_upwards [Ioo_ae_eq_Icc] with x hx
    by_cases hxcc : x ∈ Set.Icc (-a) a
    · exact hzero x (hx.mpr hxcc)
    · exact timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
        a ha.le (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
        (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hxcc
  have hnorm := integral_norm_sq_evenProlateSignedPointwiseSource_eq_one
    a ha.le n hvalue
  have haeNorm :
      (fun x : ℝ => ‖evenProlateSignedPointwiseSource a n hvalue x‖ ^ 2) =ᵐ[volume]
        fun _ : ℝ => 0 := by
    filter_upwards [hae] with x hx
    rw [hx]
    simp
  have hzeroIntegral :
      (∫ x : ℝ, ‖evenProlateSignedPointwiseSource a n hvalue x‖ ^ 2) = 0 := by
    rw [integral_congr_ae haeNorm]
    simp
  linarith

/-- After unit rescaling, a normalized canonical signed-mode source is nonzero at an interior
point. -/
theorem exists_rescaled_evenProlateSignedPointwiseSource_ne_zero
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
      evenProlateSignedPointwiseSource a n hvalue (a * x) ≠ 0 := by
  obtain ⟨y, hy, hyne⟩ :=
    exists_evenProlateSignedPointwiseSource_ne_zero_interior ha n hvalue
  refine ⟨y / a, ?_, ?_⟩
  · constructor
    · exact (lt_div_iff₀ ha).mpr (by linarith [hy.1])
    · exact (div_lt_iff₀ ha).mpr (by simpa using hy.2)
  · rwa [mul_div_cancel₀ y ha.ne']

/-- Global smooth unit-band extension of the canonical signed-mode source.  On the open unit
band it is the source itself after physical rescaling. -/
def evenProlateSignedUnitExtension
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) : ℂ :=
  (evenProlateSignedValue a n : ℂ)⁻¹ *
    evenProlateSignedFourierRepresentative a n hvalue (a * x)

theorem continuous_evenProlateSignedUnitExtension
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    Continuous (evenProlateSignedUnitExtension a n hvalue) := by
  exact continuous_const.mul
    ((evenProlateSignedFourierRepresentative a n hvalue).continuous.comp (by fun_prop))

theorem even_evenProlateSignedUnitExtension
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    Function.Even (evenProlateSignedUnitExtension a n hvalue) := by
  intro x
  rw [evenProlateSignedUnitExtension, evenProlateSignedUnitExtension,
    show a * -x = -(a * x) by ring,
    even_evenProlateSignedFourierRepresentative a n hvalue (a * x)]

theorem evenProlateSignedUnitExtension_eq_source
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    evenProlateSignedUnitExtension a n hvalue x =
      evenProlateSignedPointwiseSource a n hvalue (a * x) := by
  have hax : a * x ∈ Set.Ioo (-a) a := by
    constructor <;> nlinarith [hx.1, hx.2]
  have hsource := evenProlateSignedPointwiseSource_eq_inv_mul_fourier_interior
    ha.le n hvalue hax
  rw [fourier_evenProlateSignedPointwiseSource_eq_representative
    a ha.le n hvalue (a * x)] at hsource
  exact hsource.symm

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

/-- The global smooth unit-band extension obeys the same Slepian concentration equation on the
open band. -/
theorem evenProlateSignedUnitExtension_bandIntegral_eigen
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * Real.pi * a ^ 2) x t : ℝ) : ℂ) *
          evenProlateSignedUnitExtension a n hvalue t) =
      (evenProlateSignedValue a n : ℂ) ^ 2 *
        evenProlateSignedUnitExtension a n hvalue x := by
  calc
    (∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * Real.pi * a ^ 2) x t : ℝ) : ℂ) *
          evenProlateSignedUnitExtension a n hvalue t) =
      ∫ t in Set.Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * Real.pi * a ^ 2) x t : ℝ) : ℂ) *
          evenProlateSignedPointwiseSource a n hvalue (a * t) := by
        refine setIntegral_congr_ae measurableSet_Icc ?_
        filter_upwards [Ioo_ae_eq_Icc] with t ht
        intro htcc
        rw [evenProlateSignedUnitExtension_eq_source ha n hvalue (ht.mpr htcc)]
    _ = (evenProlateSignedValue a n : ℂ) ^ 2 *
          evenProlateSignedPointwiseSource a n hvalue (a * x) :=
      evenProlateSignedPointwiseSource_bandTransform_eigen ha n hvalue hx
    _ = (evenProlateSignedValue a n : ℂ) ^ 2 *
          evenProlateSignedUnitExtension a n hvalue x := by
      rw [evenProlateSignedUnitExtension_eq_source ha n hvalue hx]

/-- Real part of the smooth extension is an exact real Slepian eigenfunction on the open band. -/
theorem bandTransform_evenProlateSignedUnitExtension_re
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    bandTransform (2 * Real.pi * a ^ 2)
        (fun t => (evenProlateSignedUnitExtension a n hvalue t).re) x =
      evenProlateSignedValue a n ^ 2 *
        (evenProlateSignedUnitExtension a n hvalue x).re := by
  let q := evenProlateSignedUnitExtension a n hvalue
  let c := 2 * Real.pi * a ^ 2
  have hq : Continuous q := continuous_evenProlateSignedUnitExtension a n hvalue
  have hint : IntegrableOn
      (fun t : ℝ => ((sincKernelSmooth c x t : ℝ) : ℂ) * q t)
      (Set.Icc (-1 : ℝ) 1) volume := by
    exact ((Complex.continuous_ofReal.comp
      ((contDiff_sincSmooth c).continuous.comp (by fun_prop))).mul hq).integrableOn_Icc
  have hcplx := evenProlateSignedUnitExtension_bandIntegral_eigen ha n hvalue hx
  change (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincKernelSmooth c x t : ℝ) : ℂ) * q t) =
    (evenProlateSignedValue a n : ℂ) ^ 2 * q x at hcplx
  calc
    bandTransform c (fun t => (q t).re) x =
        ∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).re := by
          rw [bandTransform, intervalIntegral.integral_of_le (by norm_num),
            ← integral_Icc_eq_integral_Ioc]
    _ = (∫ t in Set.Icc (-1 : ℝ) 1,
          ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := by
          calc
            (∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).re) =
                ∫ t in Set.Icc (-1 : ℝ) 1,
                  (((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := by
                    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
                    simp
            _ = (∫ t in Set.Icc (-1 : ℝ) 1,
                  ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := integral_re hint
    _ = ((evenProlateSignedValue a n : ℂ) ^ 2 * q x).re := by
          rw [hcplx]
    _ = evenProlateSignedValue a n ^ 2 * (q x).re := by
          rw [← Complex.ofReal_pow, Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Imaginary part of the smooth extension is an exact real Slepian eigenfunction on the open
band. -/
theorem bandTransform_evenProlateSignedUnitExtension_im
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    bandTransform (2 * Real.pi * a ^ 2)
        (fun t => (evenProlateSignedUnitExtension a n hvalue t).im) x =
      evenProlateSignedValue a n ^ 2 *
        (evenProlateSignedUnitExtension a n hvalue x).im := by
  let q := evenProlateSignedUnitExtension a n hvalue
  let c := 2 * Real.pi * a ^ 2
  have hq : Continuous q := continuous_evenProlateSignedUnitExtension a n hvalue
  have hint : IntegrableOn
      (fun t : ℝ => ((sincKernelSmooth c x t : ℝ) : ℂ) * q t)
      (Set.Icc (-1 : ℝ) 1) volume := by
    exact ((Complex.continuous_ofReal.comp
      ((contDiff_sincSmooth c).continuous.comp (by fun_prop))).mul hq).integrableOn_Icc
  have hcplx := evenProlateSignedUnitExtension_bandIntegral_eigen ha n hvalue hx
  change (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincKernelSmooth c x t : ℝ) : ℂ) * q t) =
    (evenProlateSignedValue a n : ℂ) ^ 2 * q x at hcplx
  calc
    bandTransform c (fun t => (q t).im) x =
        ∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).im := by
          rw [bandTransform, intervalIntegral.integral_of_le (by norm_num),
            ← integral_Icc_eq_integral_Ioc]
    _ = (∫ t in Set.Icc (-1 : ℝ) 1,
          ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := by
          calc
            (∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).im) =
                ∫ t in Set.Icc (-1 : ℝ) 1,
                  (((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := by
                    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
                    simp
            _ = (∫ t in Set.Icc (-1 : ℝ) 1,
                  ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := integral_im hint
    _ = ((evenProlateSignedValue a n : ℂ) ^ 2 * q x).im := by
          rw [hcplx]
    _ = evenProlateSignedValue a n ^ 2 * (q x).im := by
          rw [← Complex.ofReal_pow, Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Every live signed prolate mode supplies a nonzero continuous even real eigenfunction of the
unit-band Slepian transform.  No phase convention is imposed: whichever of real or imaginary
channel is nonzero is selected. -/
theorem exists_continuous_even_real_bandEigen_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (ψ : ℝ → ℝ) (x₀ : ℝ),
      Continuous ψ ∧ Function.Even ψ ∧ x₀ ∈ Set.Ioo (-1 : ℝ) 1 ∧ ψ x₀ ≠ 0 ∧
        ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
          bandTransform (2 * Real.pi * a ^ 2) ψ x =
            evenProlateSignedValue a n ^ 2 * ψ x := by
  obtain ⟨x₀, hx₀, hx₀ne⟩ :=
    exists_rescaled_evenProlateSignedPointwiseSource_ne_zero ha n hvalue
  let q := evenProlateSignedUnitExtension a n hvalue
  have hqcont : Continuous q := continuous_evenProlateSignedUnitExtension a n hvalue
  have hqeven : Function.Even q := even_evenProlateSignedUnitExtension a n hvalue
  have hqne : q x₀ ≠ 0 := by
    change evenProlateSignedUnitExtension a n hvalue x₀ ≠ 0
    rw [evenProlateSignedUnitExtension_eq_source ha n hvalue hx₀]
    exact hx₀ne
  by_cases hre : (q x₀).re ≠ 0
  · refine ⟨fun x => (q x).re, x₀, Complex.continuous_re.comp hqcont, ?_, hx₀, hre, ?_⟩
    · intro x
      exact congrArg Complex.re (hqeven x)
    · intro x hx
      exact bandTransform_evenProlateSignedUnitExtension_re ha n hvalue hx
  · have him : (q x₀).im ≠ 0 := by
      intro him
      apply hqne
      apply Complex.ext
      · simpa using not_ne_iff.mp hre
      · simpa using him
    refine ⟨fun x => (q x).im, x₀, Complex.continuous_im.comp hqcont, ?_, hx₀, him, ?_⟩
    · intro x
      exact congrArg Complex.im (hqeven x)
    · intro x hx
      exact bandTransform_evenProlateSignedUnitExtension_im ha n hvalue hx

/-! ## Even `L²` band eigenspaces -/

/-- Extending the band class of a continuous function is exactly the inverse-eigenvalue-scaled
band transform of that function. -/
theorem eigenExtension_bandClass_eq_inv_mul_bandTransform
    (c lam : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (x : ℝ) :
    GaloisForLFunctions.RHTower.eigenExtension c lam
        (GaloisForLFunctions.RHTower.bandClass Φ hΦ) x =
      lam⁻¹ * bandTransform c Φ x := by
  rw [GaloisForLFunctions.RHTower.eigenExtension, bandTransform,
    ← GaloisForLFunctions.RHTower.integral_subtype_unit]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass Φ hΦ] with y hy
  rw [hy]

/-- A continuous pointwise band eigenfunction is recovered globally from its `L²` band class. -/
theorem eigenExtension_bandClass_eq_self_of_bandEigen
    {c lam : ℝ} (hlam : lam ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heig : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    GaloisForLFunctions.RHTower.eigenExtension c lam
        (GaloisForLFunctions.RHTower.bandClass Φ hΦ) = Φ := by
  funext x
  rw [eigenExtension_bandClass_eq_inv_mul_bandTransform c lam hΦ x, heig x]
  field_simp

/-- The Slepian band transform preserves evenness. -/
theorem even_bandTransform (c : ℝ) {Φ : ℝ → ℝ} (_hΦ : Continuous Φ)
    (hΦeven : Function.Even Φ) : Function.Even (bandTransform c Φ) := by
  intro x
  rw [bandTransform, bandTransform]
  have hneg :
      (∫ y in (-1 : ℝ)..1,
          sincKernelSmooth c (-x) (-y) * Φ (-y)) =
        ∫ y in (-1 : ℝ)..1, sincKernelSmooth c (-x) y * Φ y := by
    have h := intervalIntegral.integral_comp_neg
      (a := (-1 : ℝ)) (b := 1)
      (fun y : ℝ => sincKernelSmooth c (-x) y * Φ y)
    simpa using h
  rw [← hneg]
  apply intervalIntegral.integral_congr
  intro y _hy
  rw [hΦeven y]
  unfold sincKernelSmooth
  rw [show -x - -y = -(x - y) by ring, sincSmooth_even]

/-- The prolate Sturm--Liouville action preserves evenness. -/
theorem even_prolateSLAction (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Function.Even Φ) :
    Function.Even (prolateSLAction c Φ) := by
  intro x
  have hderiv : deriv Φ (-x) = -deriv Φ x := by
    have hfun : (fun y : ℝ => Φ (-y)) = Φ := funext hΦ
    have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    rw [deriv_comp_neg] at h
    linarith
  have hderiv2 : deriv (deriv Φ) (-x) = deriv (deriv Φ) x := by
    have hfun : (fun y : ℝ => deriv Φ (-y)) = fun y : ℝ => -deriv Φ y :=
      funext fun y => hderiv y
    have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    rw [deriv_comp_neg, deriv.neg] at h
    linarith
  unfold prolateSLAction
  rw [hΦ x, hderiv, hderiv2]
  ring

/-- Every live signed prolate mode produces a nonzero eigenvector of the established real
`L²[-1,1]` Slepian operator, at the squared signed eigenvalue. -/
theorem exists_realIntervalL2_bandEigen_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ ψ₀ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1,
      ψ₀ ≠ 0 ∧
        GaloisForLFunctions.RHTower.bandOperatorL2 (2 * Real.pi * a ^ 2) ψ₀ =
          evenProlateSignedValue a n ^ 2 • ψ₀ ∧
        Function.Even
          (GaloisForLFunctions.RHTower.eigenExtension (2 * Real.pi * a ^ 2)
            (evenProlateSignedValue a n ^ 2) ψ₀) := by
  obtain ⟨ψ, x₀, hψ, hψeven, hx₀, hψx₀, heig⟩ :=
    exists_continuous_even_real_bandEigen_of_signedMode ha n hvalue
  let c : ℝ := 2 * Real.pi * a ^ 2
  let lam : ℝ := evenProlateSignedValue a n ^ 2
  have htransform : Continuous (bandTransform c ψ) :=
    GaloisForLFunctions.RHTower.continuous_bandTransform c hψ
  have hmul : Continuous fun x => lam * ψ x := continuous_const.mul hψ
  have heigIcc : ∀ x ∈ Set.Icc (-1 : ℝ) 1, bandTransform c ψ x = lam * ψ x := by
    intro x hx
    have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    rw [hclosure] at hx
    exact (Set.EqOn.closure (fun y hy => heig y hy) htransform hmul) hx
  let ψ₀ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
    GaloisForLFunctions.RHTower.bandClass ψ hψ
  have hψ₀ne : ψ₀ ≠ 0 := by
    intro hzero
    have hclassZero :
        GaloisForLFunctions.RHTower.bandClass ψ hψ =
          GaloisForLFunctions.RHTower.bandClass (fun _ : ℝ => 0) continuous_const := by
      rw [show GaloisForLFunctions.RHTower.bandClass ψ hψ = 0 from hzero,
        GaloisForLFunctions.RHTower.bandClass_zero]
    have hpoint := GaloisForLFunctions.RHTower.eqOn_of_bandClass_eq
      hψ continuous_const hclassZero x₀ (Set.Ioo_subset_Icc_self hx₀)
    exact hψx₀ (by simpa using hpoint)
  have hclassEig :
      GaloisForLFunctions.RHTower.bandClass (bandTransform c ψ) htransform =
        GaloisForLFunctions.RHTower.bandClass (fun x => lam * ψ x) hmul := by
    apply Lp.ext
    filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass (bandTransform c ψ) htransform,
      GaloisForLFunctions.RHTower.coeFn_bandClass (fun x => lam * ψ x) hmul] with x hx₁ hx₂
    rw [hx₁, hx₂]
    exact heigIcc x x.property
  have hψ₀eig : GaloisForLFunctions.RHTower.bandOperatorL2 c ψ₀ = lam • ψ₀ := by
    rw [show ψ₀ = GaloisForLFunctions.RHTower.bandClass ψ hψ from rfl,
      GaloisForLFunctions.RHTower.bandOperatorL2_bandClass, hclassEig,
      GaloisForLFunctions.RHTower.bandClass_smul]
  have hextEven : Function.Even
      (GaloisForLFunctions.RHTower.eigenExtension c lam ψ₀) := by
    have htransformEven : Function.Even (bandTransform c ψ) :=
      even_bandTransform c hψ hψeven
    have hext : GaloisForLFunctions.RHTower.eigenExtension c lam ψ₀ =
        fun x => lam⁻¹ * bandTransform c ψ x := by
      funext x
      exact eigenExtension_bandClass_eq_inv_mul_bandTransform c lam hψ x
    rw [hext]
    intro x
    rw [htransformEven x]
  exact ⟨ψ₀, hψ₀ne, hψ₀eig, hextEven⟩

/-- Every live signed finite-Fourier mode has a nonzero smooth representative which is
simultaneously an eigenfunction of the Slepian band transform and the prolate
Sturm--Liouville action.  The band eigenvalue is the square of the signed finite-Fourier
eigenvalue, with exact rescaled bandwidth `2πa²`. -/
theorem exists_joint_prolate_band_eigen_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Φ : ℝ → ℝ) (η : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
        Φ ≠ 0 ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ 2) Φ x =
            evenProlateSignedValue a n ^ 2 * Φ x) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          prolateSLAction (2 * Real.pi * a ^ 2) Φ x = η * Φ x) := by
  obtain ⟨ψ₀, hψ₀ne, hψ₀eig, _hψ₀even⟩ :=
    exists_realIntervalL2_bandEigen_of_signedMode ha n hvalue
  exact GaloisForLFunctions.RHTower.exists_joint_prolate_band_eigen
    (by positivity) (pow_ne_zero 2 hvalue) hψ₀eig hψ₀ne

end RHTower
