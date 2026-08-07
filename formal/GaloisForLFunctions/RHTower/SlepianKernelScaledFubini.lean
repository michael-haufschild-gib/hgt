import GaloisForLFunctions.RHTower.SlepianKernelFubini
import GaloisForLFunctions.RHTower.ConstrainedProlatePointwiseRepresentative
import GaloisForLFunctions.RHTower.ProlateJointEigenExistence
import GaloisForLFunctions.RHTower.ProlateDiagonalization
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
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
  change sincKernelSmooth c (-x) (-y) * Φ (-y) = sincKernelSmooth c x y * Φ y
  rw [hΦeven y]
  unfold sincKernelSmooth
  rw [show -x - -y = -(x - y) by ring, sincSmooth_even]

/-- The prolate Sturm--Liouville action preserves evenness. -/
theorem even_prolateSLAction (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Function.Even Φ) :
    Function.Even (prolateSLAction c Φ) := by
  have hderiv : Function.Odd (deriv Φ) := by
    intro x
    have hfun : (fun y : ℝ => Φ (-y)) = Φ := funext hΦ
    have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    rw [deriv_comp_neg] at h
    linarith
  have hderiv2 : Function.Even (deriv (deriv Φ)) := by
    intro x
    have hfun : (fun y : ℝ => deriv Φ (-y)) = fun y : ℝ => -deriv Φ y :=
      funext fun y => hderiv y
    have h := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    rw [deriv_comp_neg] at h
    have hright : deriv (fun y : ℝ => -deriv Φ y) x = -deriv (deriv Φ) x := by
      change deriv (-(deriv Φ)) x = -deriv (deriv Φ) x
      rw [deriv.neg]
    rw [hright] at h
    linarith
  intro x
  unfold prolateSLAction
  rw [hΦ x, hderiv x, hderiv2 x]
  ring

/-- Linear subspace of even real-valued functions. -/
def evenFunctionSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {Φ | Function.Even Φ}
  zero_mem' := by
    intro x
    rfl
  add_mem' := by
    intro Φ Ψ hΦ hΨ x
    change Φ (-x) + Ψ (-x) = Φ x + Ψ x
    rw [hΦ x, hΨ x]
  smul_mem' := by
    intro r Φ hΦ x
    change r * Φ (-x) = r * Φ x
    rw [hΦ x]

/-- The smooth Slepian extension depends linearly on its `L²` class. -/
def eigenExtensionLinearMap (c lam : ℝ) :
    GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := GaloisForLFunctions.RHTower.eigenExtension c lam f
  map_add' f g := by
    funext x
    exact GaloisForLFunctions.RHTower.eigenExtension_add c lam f g x
  map_smul' r f := by
    funext x
    change GaloisForLFunctions.RHTower.eigenExtension c lam (r • f) x =
      r * GaloisForLFunctions.RHTower.eigenExtension c lam f x
    exact GaloisForLFunctions.RHTower.eigenExtension_smul c lam r f x

/-- Even part of one Slepian band eigenspace, kept as a direct subspace of the ambient interval
`L²` space so its inherited Hilbert structure is definitionally coherent. -/
def evenBandEigenspace (c lam : ℝ) :
    Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :=
  GaloisForLFunctions.RHTower.bandEigenspace c lam ⊓
    evenFunctionSubmodule.comap (eigenExtensionLinearMap c lam)

theorem mem_evenBandEigenspace_iff
    {c lam : ℝ}
    {f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1} :
    f ∈ evenBandEigenspace c lam ↔
      GaloisForLFunctions.RHTower.bandOperatorL2 c f = lam • f ∧
        Function.Even (GaloisForLFunctions.RHTower.eigenExtension c lam f) := by
  rw [evenBandEigenspace, Submodule.mem_inf,
    GaloisForLFunctions.RHTower.mem_bandEigenspace_iff]
  rfl

/-- The canonical representative of the prolate action's band class is the prolate action
itself.  This upgrades equality of `L²` classes to a global pointwise identity. -/
theorem eigenRep_prolateOnEigenspace
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : GaloisForLFunctions.RHTower.bandEigenspace c lam) :
    GaloisForLFunctions.RHTower.eigenRep c lam
        (GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam f) =
      prolateSLAction c (GaloisForLFunctions.RHTower.eigenRep c lam f) := by
  change GaloisForLFunctions.RHTower.eigenExtension c lam
      (GaloisForLFunctions.RHTower.bandClass
        (prolateSLAction c (GaloisForLFunctions.RHTower.eigenRep c lam f)) _) = _
  apply eigenExtension_bandClass_eq_self_of_bandEigen hlam
  intro x
  exact GaloisForLFunctions.RHTower.bandTransform_prolateSLAction
    (GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam f)
    (GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam f) x

/-- Prolate action restricted to the even part of one band eigenspace. -/
def prolateOnEvenEigenspace
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    evenBandEigenspace c lam →ₗ[ℝ] evenBandEigenspace c lam where
  toFun f :=
    let bf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨f.1, f.2.1⟩
    let pf := GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam bf
    ⟨pf.1, ⟨pf.2, by
      change Function.Even (GaloisForLFunctions.RHTower.eigenRep c lam pf)
      rw [eigenRep_prolateOnEigenspace hc hlam]
      exact even_prolateSLAction c f.2.2⟩⟩
  map_add' f g := by
    apply Subtype.ext
    change ((GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨f.1 + g.1, _⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)).1 =
      ((GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨f.1, f.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)).1 +
      ((GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨g.1, g.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)).1
    exact congrArg Subtype.val
      (map_add (GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨f.1, f.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)
        (⟨g.1, g.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam))
  map_smul' r f := by
    apply Subtype.ext
    change ((GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨r • f.1, _⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)).1 =
      r • ((GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam)
        (⟨f.1, f.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)).1
    exact congrArg Subtype.val
      (map_smul (GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam) r
        (⟨f.1, f.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam))

/-- Symmetry survives restriction to the even invariant subspace. -/
theorem isSymmetric_prolateOnEvenEigenspace
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    (prolateOnEvenEigenspace hc hlam).IsSymmetric := by
  intro f g
  exact GaloisForLFunctions.RHTower.isSymmetric_prolateOnEigenspace hc hlam
    (⟨f.1, f.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)
    (⟨g.1, g.2.1⟩ : GaloisForLFunctions.RHTower.bandEigenspace c lam)

/-- Every nonzero even Slepian band eigenvector carries a nonzero smooth even joint
band/prolate eigenfunction. -/
theorem exists_joint_even_prolate_band_eigen
    {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {ψ₀ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hψ₀ : GaloisForLFunctions.RHTower.bandOperatorL2 c ψ₀ = lam • ψ₀)
    (hψ₀ne : ψ₀ ≠ 0)
    (hψ₀even : Function.Even
      (GaloisForLFunctions.RHTower.eigenExtension c lam ψ₀)) :
    ∃ (Φ : ℝ → ℝ) (η : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
        Φ ≠ 0 ∧ Function.Even Φ ∧
        (∀ x : ℝ, bandTransform c Φ x = lam * Φ x) ∧
        (∀ x : ℝ, prolateSLAction c Φ x = η * Φ x) := by
  let ef₀ : evenBandEigenspace c lam :=
    ⟨ψ₀, GaloisForLFunctions.RHTower.mem_bandEigenspace_iff.mpr hψ₀, hψ₀even⟩
  letI : FiniteDimensional ℝ
      (GaloisForLFunctions.RHTower.bandEigenspace c lam) :=
    GaloisForLFunctions.RHTower.finiteDimensional_bandEigenspace hlam
  let inclusion : evenBandEigenspace c lam →ₗ[ℝ]
      GaloisForLFunctions.RHTower.bandEigenspace c lam :=
    { toFun := fun f => ⟨f.1, f.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : FiniteDimensional ℝ (evenBandEigenspace c lam) :=
    FiniteDimensional.of_injective inclusion (by
      intro f g hfg
      apply Subtype.ext
      exact congrArg (fun h : GaloisForLFunctions.RHTower.bandEigenspace c lam => h.1) hfg)
  have hef₀ne : ef₀ ≠ 0 := by
    intro hzero
    apply hψ₀ne
    have hval := congrArg
      (fun f : evenBandEigenspace c lam => f.1) hzero
    exact hval
  letI : Nontrivial (evenBandEigenspace c lam) := nontrivial_of_ne ef₀ 0 hef₀ne
  have hsym := isSymmetric_prolateOnEvenEigenspace hc hlam
  obtain ⟨η, hη⟩ : ∃ η : ℝ, Module.End.HasEigenvalue
      (prolateOnEvenEigenspace hc hlam) η :=
    ⟨_, hsym.hasEigenvalue_iSup_of_finiteDimensional⟩
  obtain ⟨v, hvmem, hvne⟩ := hη.exists_hasEigenvector
  have hveq : prolateOnEvenEigenspace hc hlam v = η • v :=
    Module.End.mem_eigenspace_iff.mp hvmem
  let vf : GaloisForLFunctions.RHTower.bandEigenspace c lam := ⟨v.1, v.2.1⟩
  let Φ : ℝ → ℝ := GaloisForLFunctions.RHTower.eigenRep c lam vf
  have hΦne : Φ ≠ 0 := by
    intro hzero
    have hclass := GaloisForLFunctions.RHTower.bandClass_eigenRep hlam vf
    have hclassZero : GaloisForLFunctions.RHTower.bandClass Φ
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam vf) = 0 := by
      have hstep := GaloisForLFunctions.RHTower.bandClass_congr
        (GaloisForLFunctions.RHTower.continuous_eigenRep c lam vf)
        continuous_const hzero
      rw [hstep]
      exact GaloisForLFunctions.RHTower.bandClass_zero _
    have hvzero : (v : evenBandEigenspace c lam) = 0 := by
      apply Subtype.ext
      rw [← hclass]
      exact hclassZero
    exact hvne hvzero
  have hprolate : ∀ x : ℝ, prolateSLAction c Φ x = η * Φ x := by
    have hvaleq :
        GaloisForLFunctions.RHTower.prolateOnEigenspace hc hlam vf = η • vf := by
      apply Subtype.ext
      exact congrArg (fun w : evenBandEigenspace c lam => w.1) hveq
    have hrepeq := congrArg
      (fun w : GaloisForLFunctions.RHTower.bandEigenspace c lam =>
        GaloisForLFunctions.RHTower.eigenRep c lam w) hvaleq
    rw [eigenRep_prolateOnEigenspace hc hlam] at hrepeq
    intro x
    have hx := congrFun hrepeq x
    change prolateSLAction c Φ x = η * Φ x
    have hsmul : GaloisForLFunctions.RHTower.eigenRep c lam (η • vf) x =
        η * GaloisForLFunctions.RHTower.eigenRep c lam vf x :=
      GaloisForLFunctions.RHTower.eigenExtension_smul c lam η vf x
    rw [hsmul] at hx
    exact hx
  exact ⟨Φ, η, GaloisForLFunctions.RHTower.contDiff_eigenRep hc hlam vf,
    hΦne, v.2.2,
    GaloisForLFunctions.RHTower.bandTransform_eigenRep hlam vf, hprolate⟩

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
    change lam⁻¹ * bandTransform c ψ (-x) = lam⁻¹ * bandTransform c ψ x
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

/-- Parity-preserving strengthening: every live signed mode carries a nonzero smooth **even**
joint Slepian/prolate eigenfunction, and the differential equation holds globally. -/
theorem exists_joint_even_prolate_band_eigen_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Φ : ℝ → ℝ) (η : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
        Φ ≠ 0 ∧ Function.Even Φ ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ 2) Φ x =
            evenProlateSignedValue a n ^ 2 * Φ x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ 2) Φ x = η * Φ x) := by
  obtain ⟨ψ₀, hψ₀ne, hψ₀eig, hψ₀even⟩ :=
    exists_realIntervalL2_bandEigen_of_signedMode ha n hvalue
  exact exists_joint_even_prolate_band_eigen
    (by positivity) (pow_ne_zero 2 hvalue) hψ₀eig hψ₀ne hψ₀even

/-- Unconditional fixed-index form: every signed mode eventually admits an exact nonzero smooth
even joint Slepian/prolate representative. -/
theorem eventually_exists_joint_even_prolate_band_eigen_of_signedMode (n : ℕ) :
    ∀ᶠ a : ℝ in Filter.atTop,
      ∃ (Φ : ℝ → ℝ) (η : ℝ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
          Φ ≠ 0 ∧ Function.Even Φ ∧
          (∀ x : ℝ,
            bandTransform (2 * Real.pi * a ^ 2) Φ x =
              evenProlateSignedValue a n ^ 2 * Φ x) ∧
          (∀ x : ℝ,
            prolateSLAction (2 * Real.pi * a ^ 2) Φ x = η * Φ x) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    eventually_evenProlateSignedValue_ne_zero n] with a ha hvalue
  exact exists_joint_even_prolate_band_eigen_of_signedMode ha n hvalue

/-! ## Uniqueness of the regular even prolate mode

The singular endpoints prevent a global Lipschitz estimate after solving the prolate equation for
the second derivative.  On every strictly interior compact interval, however, the equation is a
uniformly Lipschitz first-order system.  This is the exact uniqueness input needed for classical
mode identification; no boundary regularity or spectral simplicity is assumed.
-/

/-- Value/derivative state of a scalar prolate solution. -/
def prolateODEState (Phi : ℝ → ℝ) (x : ℝ) : ℝ × ℝ :=
  (Phi x, deriv Phi x)

/-- First-order vector field equivalent to the prolate equation away from `x = ±1`. -/
def prolateODEField (c chi x : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, ((chi + c ^ 2 * x ^ 2) * z.1 + 2 * x * z.2) / (1 - x ^ 2))

/-- Uniform state-space Lipschitz bound on a strict interior interval `|x| ≤ r < 1`. -/
theorem lipschitzWith_prolateODEField {c chi r x : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : |x| ≤ r) :
    LipschitzWith
      (Real.toNNReal
        (1 + (|chi| + c ^ 2 * r ^ 2 + 2 * r) / (1 - r ^ 2)))
      (prolateODEField c chi x) := by
  let N : ℝ := |chi| + c ^ 2 * r ^ 2 + 2 * r
  let M : ℝ := 1 + N / (1 - r ^ 2)
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hx_sq : x ^ 2 ≤ r ^ 2 := by
    nlinarith [sq_abs x,
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hr0 (abs_nonneg x))]
  have hxden : 0 < 1 - x ^ 2 := by nlinarith
  have hN0 : 0 ≤ N := by
    dsimp [N]
    positivity
  have hcoef : |chi + c ^ 2 * x ^ 2| + |2 * x| ≤ N := by
    have hcpart : |c ^ 2 * x ^ 2| = c ^ 2 * x ^ 2 := abs_of_nonneg (by positivity)
    have hxpart : |2 * x| = 2 * |x| := by rw [abs_mul]; norm_num
    calc
      |chi + c ^ 2 * x ^ 2| + |2 * x|
          ≤ (|chi| + |c ^ 2 * x ^ 2|) + |2 * x| := by
            gcongr
            exact abs_add_le chi (c ^ 2 * x ^ 2)
      _ = |chi| + c ^ 2 * x ^ 2 + 2 * |x| := by rw [hcpart, hxpart]
      _ ≤ N := by
        dsimp [N]
        nlinarith [sq_nonneg c]
  have hfrac0 : 0 ≤ N / (1 - r ^ 2) := div_nonneg hN0 hrden.le
  have hM0 : 0 ≤ M := by dsimp [M]; linarith
  have hM1 : 1 ≤ M := by dsimp [M]; linarith
  change LipschitzWith (Real.toNNReal M) (prolateODEField c chi x)
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.coe_toNNReal M hM0, Prod.dist_eq]
  apply max_le
  · calc
      dist z.2 w.2 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ ≤ M * dist z w := by
        exact (le_mul_of_one_le_left dist_nonneg hM1)
  · rw [Real.dist_eq]
    have hz1 : |z.1 - w.1| ≤ dist z w := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_left _ _
    have hz2 : |z.2 - w.2| ≤ dist z w := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_right _ _
    have hnum :
        |(chi + c ^ 2 * x ^ 2) * (z.1 - w.1) + 2 * x * (z.2 - w.2)|
          ≤ N * dist z w := by
      calc
        |(chi + c ^ 2 * x ^ 2) * (z.1 - w.1) + 2 * x * (z.2 - w.2)|
            ≤ |(chi + c ^ 2 * x ^ 2) * (z.1 - w.1)| +
                |2 * x * (z.2 - w.2)| :=
              abs_add_le _ _
        _ = |chi + c ^ 2 * x ^ 2| * |z.1 - w.1| +
                |2 * x| * |z.2 - w.2| := by rw [abs_mul, abs_mul]
        _ ≤ |chi + c ^ 2 * x ^ 2| * dist z w + |2 * x| * dist z w :=
              add_le_add
                (mul_le_mul_of_nonneg_left hz1 (abs_nonneg _))
                (mul_le_mul_of_nonneg_left hz2 (abs_nonneg _))
        _ = (|chi + c ^ 2 * x ^ 2| + |2 * x|) * dist z w := by ring
        _ ≤ N * dist z w := mul_le_mul_of_nonneg_right hcoef dist_nonneg
    have hdencomp :
        N * dist z w / (1 - x ^ 2) ≤ N * dist z w / (1 - r ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hN0 dist_nonneg) hrden (by nlinarith)
    have hsecond :
        dist
            (prolateODEField c chi x z).2
            (prolateODEField c chi x w).2
          ≤ (N / (1 - r ^ 2)) * dist z w := by
      rw [Real.dist_eq]
      change
        |(((chi + c ^ 2 * x ^ 2) * z.1 + 2 * x * z.2) / (1 - x ^ 2)) -
            (((chi + c ^ 2 * x ^ 2) * w.1 + 2 * x * w.2) / (1 - x ^ 2))|
          ≤ _
      rw [← sub_div, show
        (chi + c ^ 2 * x ^ 2) * z.1 + 2 * x * z.2 -
            ((chi + c ^ 2 * x ^ 2) * w.1 + 2 * x * w.2) =
          (chi + c ^ 2 * x ^ 2) * (z.1 - w.1) + 2 * x * (z.2 - w.2) by ring,
        abs_div, abs_of_pos hxden]
      calc
        |(chi + c ^ 2 * x ^ 2) * (z.1 - w.1) + 2 * x * (z.2 - w.2)| /
              (1 - x ^ 2)
            ≤ N * dist z w / (1 - x ^ 2) := div_le_div_of_nonneg_right hnum hxden.le
        _ ≤ N * dist z w / (1 - r ^ 2) := hdencomp
        _ = (N / (1 - r ^ 2)) * dist z w := by ring
    change dist (prolateODEField c chi x z).2 (prolateODEField c chi x w).2 ≤ _
    exact hsecond.trans (mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) dist_nonneg)

/-- A smooth prolate solution gives an integral curve of `prolateODEField` on `(-1,1)`. -/
theorem hasDerivAt_prolateODEState {c chi : ℝ} {Phi : ℝ → ℝ}
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi))
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (prolateODEState Phi) (prolateODEField c chi x (prolateODEState Phi x)) x := by
  have hxden : 1 - x ^ 2 ≠ 0 := by
    have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact this.ne'
  have hsecond :
      deriv (deriv Phi) x =
        ((chi + c ^ 2 * x ^ 2) * Phi x + 2 * x * deriv Phi x) / (1 - x ^ 2) := by
    apply (eq_div_iff hxden).2
    have h := heig x
    simp only [prolateSLAction] at h
    linarith
  change HasDerivAt (fun y => (Phi y, deriv Phi y))
    (prolateODEField c chi x (prolateODEState Phi x)) x
  have hstate : HasDerivAt (fun y => (Phi y, deriv Phi y))
      (deriv Phi x, deriv (deriv Phi) x) x :=
    (hPhi1 x).hasDerivAt.prodMk (hPhi2 x).hasDerivAt
  simpa [prolateODEState, prolateODEField, hsecond] using hstate

/-- Two globally smooth solutions of the same prolate equation with equal value and derivative at
zero agree throughout the regular interval `(-1,1)`. -/
theorem eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
    {c chi : ℝ} {Phi Psi : ℝ → ℝ}
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi))
    (hPsi1 : Differentiable ℝ Psi) (hPsi2 : Differentiable ℝ (deriv Psi))
    (hPhiEig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiEig : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x)
    (hvalue : Phi 0 = Psi 0) (hderiv : deriv Phi 0 = deriv Psi 0) :
    Set.EqOn Phi Psi (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  let r : ℝ := (|x| + 1) / 2
  have hxabs : |x| < 1 := (abs_lt).2 hx
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hxmem : x ∈ Set.Ioo (-r) r := by
    exact (abs_lt).1 (by dsimp [r]; linarith)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-r) r := by exact ⟨by linarith, hrpos⟩
  have hstateEq : prolateODEState Phi 0 = prolateODEState Psi 0 := by
    ext <;> simp [prolateODEState, hvalue, hderiv]
  have hstates : Set.EqOn (prolateODEState Phi) (prolateODEState Psi) (Set.Ioo (-r) r) := by
    apply ODE_solution_unique_of_mem_Ioo
      (K := Real.toNNReal
        (1 + (|chi| + c ^ 2 * r ^ 2 + 2 * r) / (1 - r ^ 2)))
      (v := prolateODEField c chi) (s := fun _ => Set.univ) (t₀ := 0)
    · intro t ht
      exact (lipschitzWith_prolateODEField hr0 hr1
        (abs_lt.mpr ht).le).lipschitzOnWith
    · exact hzero
    · intro t ht
      exact ⟨hasDerivAt_prolateODEState hPhi1 hPhi2 hPhiEig
        ⟨lt_trans (by linarith [hr1]) ht.1, lt_trans ht.2 hr1⟩, Set.mem_univ _⟩
    · intro t ht
      exact ⟨hasDerivAt_prolateODEState hPsi1 hPsi2 hPsiEig
        ⟨lt_trans (by linarith [hr1]) ht.1, lt_trans ht.2 hr1⟩, Set.mem_univ _⟩
    · exact hstateEq
  exact congrArg Prod.fst (hstates hxmem)

/-- An even function has zero derivative at the symmetry center. -/
theorem deriv_zero_of_even {Phi : ℝ → ℝ} (hPhiEven : Function.Even Phi) :
    deriv Phi 0 = 0 := by
  have hfun : (fun y : ℝ => Phi (-y)) = Phi := funext hPhiEven
  have h := congrArg (fun f : ℝ → ℝ => deriv f 0) hfun
  rw [deriv_comp_neg] at h
  have hneg : -deriv Phi 0 = deriv Phi 0 := by simpa using h
  linarith

/-- A nonzero smooth even joint band/prolate eigenfunction cannot vanish at the symmetry center.
If it did, evenness would also kill its first derivative, ODE uniqueness would kill it on the
aperture, and the nonzero band eigenvalue would then kill it globally. -/
theorem value_zero_ne_of_even_joint_prolate_band_eigen
    {c lam chi : ℝ} {Phi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPhiNe : Phi ≠ 0) (hPhiEven : Function.Even Phi) (hlam : lam ≠ 0)
    (hBand : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (hProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    Phi 0 ≠ 0 := by
  intro hPhi0
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhiDerivSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hPhiSmooth).2
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hPhiDerivSmooth).1
  have hzeroProlate : ∀ x : ℝ,
      prolateSLAction c (fun _ : ℝ => 0) x = chi * (fun _ : ℝ => 0) x := by
    intro x
    simp [prolateSLAction]
  have hzeroIoo : Set.EqOn Phi (fun _ : ℝ => 0) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hPhi1 hPhi2 (by fun_prop) (by fun_prop) hProlate hzeroProlate
      (by simpa using hPhi0) (by simp [deriv_zero_of_even hPhiEven])
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hzeroIcc : Set.EqOn Phi (fun _ : ℝ => 0) (Set.Icc (-1 : ℝ) 1) := by
    rw [hclosure]
    exact hzeroIoo.closure hPhi1.continuous continuous_const
  have hBandZero : ∀ x : ℝ, bandTransform c Phi x = 0 := by
    intro x
    unfold bandTransform
    calc
      (∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * Phi y) =
          ∫ _y in (-1 : ℝ)..1, 0 := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
            have hyzero : Phi y = 0 := by simpa using hzeroIcc hy'
            simp [hyzero]
      _ = 0 := by simp
  apply hPhiNe
  funext x
  have hxzero : lam * Phi x = 0 := by rw [← hBand x, hBandZero x]
  exact (mul_eq_zero.mp hxzero).resolve_left hlam

/-- Simplicity of a regular even prolate separation mode on the aperture.  Any two nonzero smooth
even joint band/prolate eigenfunctions with the same separation value are scalar multiples on
`[-1,1]`; their band eigenvalues may be different. -/
theorem eqOn_Icc_const_mul_of_even_joint_prolate_eigen
    {c lamPsi chi : ℝ} {Phi Psi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPsiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi)
    (hPsiNe : Psi ≠ 0)
    (hPhiEven : Function.Even Phi) (hPsiEven : Function.Even Psi)
    (hlamPsi : lamPsi ≠ 0)
    (hPsiBand : ∀ x : ℝ, bandTransform c Psi x = lamPsi * Psi x)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPsiProlate : ∀ x : ℝ, prolateSLAction c Psi x = chi * Psi x) :
    ∃ mu : ℝ, Set.EqOn Phi (fun x => mu * Psi x) (Set.Icc (-1 : ℝ) 1) := by
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPhiSmooth).2).1
  have hPsi1 : Differentiable ℝ Psi := (contDiff_infty_iff_deriv.mp hPsiSmooth).1
  have hPsi2 : Differentiable ℝ (deriv Psi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPsiSmooth).2).1
  have hPsi0 : Psi 0 ≠ 0 := value_zero_ne_of_even_joint_prolate_band_eigen
    hPsiSmooth hPsiNe hPsiEven hlamPsi hPsiBand hPsiProlate
  let mu : ℝ := Phi 0 / Psi 0
  have hscaled1 : Differentiable ℝ (fun x => mu * Psi x) := by fun_prop
  have hscaledDeriv : deriv (fun x => mu * Psi x) = fun x => mu * deriv Psi x := by
    funext x
    exact deriv_const_mul mu (hPsi1 x)
  have hscaled2 : Differentiable ℝ (deriv (fun x => mu * Psi x)) := by
    rw [hscaledDeriv]
    fun_prop
  have hscaledProlate : ∀ x : ℝ,
      prolateSLAction c (fun y => mu * Psi y) x = chi * (mu * Psi x) := by
    intro x
    rw [GaloisForLFunctions.RHTower.prolateSLAction_const_mul mu hPsi1 hPsi2 x,
      hPsiProlate x]
    ring
  have hvalue : Phi 0 = mu * Psi 0 := by
    dsimp [mu]
    field_simp
  have hderiv : deriv Phi 0 = deriv (fun x => mu * Psi x) 0 := by
    rw [hscaledDeriv]
    simp [deriv_zero_of_even hPhiEven, deriv_zero_of_even hPsiEven]
  have hEqIoo : Set.EqOn Phi (fun x => mu * Psi x) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hPhi1 hPhi2 hscaled1 hscaled2 hPhiProlate hscaledProlate hvalue hderiv
  refine ⟨mu, ?_⟩
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [hclosure]
  exact hEqIoo.closure hPhi1.continuous hscaled1.continuous

/-- A nontrivial regular even prolate solution cannot vanish at the symmetry center. -/
theorem value_zero_ne_of_even_prolate_eigen
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPhiEven : Function.Even Phi)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPhiInterior : ∃ x ∈ Set.Ioo (-1 : ℝ) 1, Phi x ≠ 0) :
    Phi 0 ≠ 0 := by
  intro hPhi0
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPhiSmooth).2).1
  have hzeroProlate : ∀ x : ℝ,
      prolateSLAction c (fun _ : ℝ => 0) x = chi * (fun _ : ℝ => 0) x := by
    intro x
    simp [prolateSLAction]
  have hzeroIoo : Set.EqOn Phi (fun _ : ℝ => 0) (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hPhi1 hPhi2 (by fun_prop) (by fun_prop) hPhiProlate hzeroProlate
      (by simpa using hPhi0) (by simp [deriv_zero_of_even hPhiEven])
  obtain ⟨x, hx, hne⟩ := hPhiInterior
  exact hne (by simpa using hzeroIoo hx)

/-- **Global aperture diagonalization.**  Every nontrivial smooth even solution of the regular
prolate equation spans an invariant line of the Slepian band transform on all of `[-1,1]`.
Unlike the quotient/Wronskian argument, this theorem needs no zero-free subinterval: equality of
the value and derivative at the center and ODE uniqueness propagate across every interior zero. -/
theorem bandTransform_eq_smul_on_Icc_of_even_prolate_eigen
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (hPhiSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hPhiEven : Function.Even Phi)
    (hPhiProlate : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x)
    (hPhiInterior : ∃ x ∈ Set.Ioo (-1 : ℝ) 1, Phi x ≠ 0) :
    ∃ mu : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, bandTransform c Phi x = mu * Phi x := by
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hPhiSmooth).1
  have hPhiDerivSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hPhiSmooth).2
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp hPhiDerivSmooth).1
  have hPhi2c : Continuous (deriv (deriv Phi)) :=
    (contDiff_infty_iff_deriv.mp hPhiDerivSmooth).2.continuous
  have hPhi0 := value_zero_ne_of_even_prolate_eigen
    hPhiSmooth hPhiEven hPhiProlate hPhiInterior
  have hBand1 : Differentiable ℝ (bandTransform c Phi) :=
    differentiable_bandTransform c hPhi1.continuous
  have hBand2 : Differentiable ℝ (deriv (bandTransform c Phi)) :=
    differentiable_deriv_bandTransform c hPhi1.continuous
  have hBandEven : Function.Even (bandTransform c Phi) :=
    even_bandTransform c hPhi1.continuous hPhiEven
  have hBandProlate : ∀ x : ℝ,
      prolateSLAction c (bandTransform c Phi) x = chi * bandTransform c Phi x :=
    fun x => slepian_commutation_eigen
      c x hPhi1 hPhi2 hPhi2c hPhiProlate
  let mu : ℝ := bandTransform c Phi 0 / Phi 0
  have hscaled1 : Differentiable ℝ (fun x => mu * Phi x) := by fun_prop
  have hscaledDeriv : deriv (fun x => mu * Phi x) = fun x => mu * deriv Phi x := by
    funext x
    exact deriv_const_mul mu (hPhi1 x)
  have hscaled2 : Differentiable ℝ (deriv (fun x => mu * Phi x)) := by
    rw [hscaledDeriv]
    fun_prop
  have hscaledProlate : ∀ x : ℝ,
      prolateSLAction c (fun y => mu * Phi y) x = chi * (mu * Phi x) := by
    intro x
    rw [GaloisForLFunctions.RHTower.prolateSLAction_const_mul mu hPhi1 hPhi2 x,
      hPhiProlate x]
    ring
  have hvalue : bandTransform c Phi 0 = mu * Phi 0 := by
    dsimp [mu]
    field_simp
  have hderiv : deriv (bandTransform c Phi) 0 = deriv (fun x => mu * Phi x) 0 := by
    rw [hscaledDeriv]
    simp [deriv_zero_of_even hBandEven, deriv_zero_of_even hPhiEven]
  have hEqIoo : Set.EqOn (bandTransform c Phi) (fun x => mu * Phi x)
      (Set.Ioo (-1 : ℝ) 1) :=
    eqOn_Ioo_of_prolateSLAction_eq_of_value_deriv_eq
      hBand1 hBand2 hscaled1 hscaled2 hBandProlate hscaledProlate hvalue hderiv
  refine ⟨mu, ?_⟩
  have hclosure : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [hclosure]
  exact hEqIoo.closure hBand1.continuous hscaled1.continuous

end RHTower
