import GaloisForLFunctions.RHTower.SlepianKernelScaledFubini

/-!
# The unit-band prolate extension is a global Slepian eigenfunction

The canonical source of a live signed prolate mode is supported in the physical aperture, and its
finite-Fourier eigen-relation is therefore available only inside that aperture.  The unit-band
*extension* — the aperture-rescaled Fourier representative divided by the eigenvalue — carries the
same relation at **every** real point: the compact-support rescaling of the Fourier integral has no
restriction on the frequency, so composing it with itself propagates the Slepian eigen-equation off
the band.

Two consequences follow.  The real and imaginary channels of the extension are exact Slepian
eigenfunctions on all of `ℝ`, and the Fourier transform of the source is the eigenvalue times the
extension of the rescaled frequency — an exact pointwise self-reciprocity, valid arbitrarily far
outside the aperture.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real FourierTransform

namespace RHTower

variable {a : ℝ} {n : ℕ}

/-- On the closed unit band the extension agrees almost everywhere with the rescaled source. -/
theorem evenProlateSignedUnitExtension_ae_eq_source
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∀ᵐ t ∂(volume.restrict (Icc (-1 : ℝ) 1)),
      evenProlateSignedUnitExtension a n hvalue t
        = evenProlateSignedPointwiseSource a n hvalue (a * t) := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Ioo_ae_eq_Icc] with t ht htcc
  exact evenProlateSignedUnitExtension_eq_source ha n hvalue (ht.mpr htcc)

/-- The canonical source vanishes off the physical aperture. -/
theorem evenProlateSignedPointwiseSource_eq_zero_of_not_mem_Icc
    (ha : 0 ≤ a) (hvalue : evenProlateSignedValue a n ≠ 0) {y : ℝ} (hy : y ∉ Icc (-a) a) :
    evenProlateSignedPointwiseSource a n hvalue y = 0 :=
  timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hy

/-- **Global unit-scale eigen-relation.**  The finite Fourier transform of the unit-band extension
reproduces the extension itself, at every real point — not only inside the aperture. -/
theorem evenProlateSignedUnitExtension_unitScale_eigen
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    a • ∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) • evenProlateSignedUnitExtension a n hvalue t =
      (evenProlateSignedValue a n : ℂ) * evenProlateSignedUnitExtension a n hvalue x := by
  have hχ : ((evenProlateSignedValue a n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvalue
  have hcongr : (∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) • evenProlateSignedUnitExtension a n hvalue t)
      = ∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) • evenProlateSignedPointwiseSource a n hvalue (a * t) := by
    refine integral_congr_ae ?_
    filter_upwards [evenProlateSignedUnitExtension_ae_eq_source ha hvalue] with t ht
    rw [ht]
  rw [hcongr,
    fourier_compactSupport_unitScale ha
      (fun y hy => evenProlateSignedPointwiseSource_eq_zero_of_not_mem_Icc ha.le hvalue hy) x,
    fourier_evenProlateSignedPointwiseSource_eq_representative a ha.le n hvalue (a * x),
    evenProlateSignedUnitExtension, ← mul_assoc, mul_inv_cancel₀ hχ, one_mul]

/-- **Global Slepian eigen-relation of the unit-band extension.** -/
theorem evenProlateSignedUnitExtension_bandIntegral_eigen_global
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    (∫ t in Icc (-1 : ℝ) 1,
        ((sincKernelSmooth (2 * Real.pi * a ^ 2) x t : ℝ) : ℂ) *
          evenProlateSignedUnitExtension a n hvalue t) =
      (evenProlateSignedValue a n : ℂ) ^ 2 * evenProlateSignedUnitExtension a n hvalue x := by
  set g : ℝ → ℂ := evenProlateSignedUnitExtension a n hvalue with hgdef
  set χ : ℂ := (evenProlateSignedValue a n : ℂ) with hχdef
  set κ : ℝ := a ^ 2 with hκdef
  have hκ : 0 < κ := by
    rw [hκdef]
    positivity
  have hgc : Continuous g := continuous_evenProlateSignedUnitExtension a n hvalue
  have hg : IntegrableOn g (Icc (-1 : ℝ) 1) volume := hgc.integrableOn_Icc
  have hgeven : Function.Even g := even_evenProlateSignedUnitExtension a n hvalue
  have heig : ∀ y : ℝ,
      (a : ℂ) * ∫ t in Icc (-1 : ℝ) 1,
          Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * g t = χ * g y := by
    intro y
    have h := evenProlateSignedUnitExtension_unitScale_eigen ha hvalue y
    simp only [Circle.smul_def, Real.fourierChar_apply, Complex.real_smul, smul_eq_mul] at h
    calc
      (a : ℂ) * ∫ t in Icc (-1 : ℝ) 1,
            Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * g t
          = (a : ℂ) * ∫ t in Icc (-1 : ℝ) 1,
              Complex.exp ((2 * Real.pi * -((a * t) * (a * y)) : ℝ) * Complex.I) * g t := by
            congr 1
            refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
            congr 2
            rw [hκdef]
            push_cast
            ring
      _ = χ * g y := by simpa only [hχdef, hgdef] using h
  set innerF : ℝ → ℂ := fun y =>
    ∫ t in Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * g t with hinnerF
  set outerF : ℝ → ℂ := fun y =>
    Complex.exp ((-(2 * Real.pi * κ * x * y) : ℝ) * Complex.I) with houterF
  have hscaledDouble :
      (a : ℂ) * (∫ y in Icc (-1 : ℝ) 1, outerF y * innerF y) =
        χ * ∫ y in Icc (-1 : ℝ) 1, outerF y * g y := by
    rw [← integral_const_mul]
    calc
      (∫ y in Icc (-1 : ℝ) 1, (a : ℂ) * (outerF y * innerF y)) =
          ∫ y in Icc (-1 : ℝ) 1, outerF y * ((a : ℂ) * innerF y) := by
            refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
            ring
      _ = ∫ y in Icc (-1 : ℝ) 1, outerF y * (χ * g y) := by
            refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
            rw [heig y]
      _ = χ * ∫ y in Icc (-1 : ℝ) 1, outerF y * g y := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
            ring
  have hdouble := double_integral_scaledFourierChar_eq_sincKernel
    1 κ x (by norm_num) hg (Filter.Eventually.of_forall hgeven)
  change (∫ y in Icc (-1 : ℝ) 1, outerF y * innerF y) =
      ∫ t in Icc (-1 : ℝ) 1,
        ((sincSmooth (2 * Real.pi * 1) (κ * (x - t)) : ℝ) : ℂ) * g t at hdouble
  norm_num at hdouble
  have hband := scaled_sincIntegral_eq_bandIntegral κ x hκ g
  change (∫ t in Icc (-1 : ℝ) 1,
      ((sincKernelSmooth (2 * Real.pi * κ) x t : ℝ) : ℂ) * g t) = χ ^ 2 * g x
  rw [← hband, ← hdouble]
  calc
    (κ : ℂ) * (∫ y in Icc (-1 : ℝ) 1, outerF y * innerF y) =
        (a : ℂ) * ((a : ℂ) * ∫ y in Icc (-1 : ℝ) 1, outerF y * innerF y) := by
          rw [hκdef]
          push_cast
          ring
    _ = (a : ℂ) * (χ * ∫ y in Icc (-1 : ℝ) 1, outerF y * g y) := by
          rw [hscaledDouble]
    _ = χ * ((a : ℂ) * ∫ y in Icc (-1 : ℝ) 1, outerF y * g y) := by
          ring
    _ = χ * (χ * g x) := by
          rw [heig x]
    _ = χ ^ 2 * g x := by
          ring

/-- The real channel of the unit-band extension is a global real Slepian eigenfunction. -/
theorem bandTransform_evenProlateSignedUnitExtension_re_global
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    bandTransform (2 * Real.pi * a ^ 2)
        (fun t => (evenProlateSignedUnitExtension a n hvalue t).re) x =
      evenProlateSignedValue a n ^ 2 *
        (evenProlateSignedUnitExtension a n hvalue x).re := by
  set q := evenProlateSignedUnitExtension a n hvalue with hq
  set c := 2 * Real.pi * a ^ 2 with hc
  have hqc : Continuous q := continuous_evenProlateSignedUnitExtension a n hvalue
  have hint : IntegrableOn
      (fun t : ℝ => ((sincKernelSmooth c x t : ℝ) : ℂ) * q t) (Icc (-1 : ℝ) 1) volume :=
    ((Complex.continuous_ofReal.comp
      ((contDiff_sincSmooth c).continuous.comp (by fun_prop))).mul hqc).integrableOn_Icc
  have hcplx := evenProlateSignedUnitExtension_bandIntegral_eigen_global ha hvalue x
  calc
    bandTransform c (fun t => (q t).re) x =
        ∫ t in Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).re := by
          rw [bandTransform, intervalIntegral.integral_of_le (by norm_num),
            ← integral_Icc_eq_integral_Ioc]
    _ = (∫ t in Icc (-1 : ℝ) 1, ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := by
          calc
            (∫ t in Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).re) =
                ∫ t in Icc (-1 : ℝ) 1,
                  (((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := by
                    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
                    simp
            _ = (∫ t in Icc (-1 : ℝ) 1,
                  ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).re := integral_re hint
    _ = ((evenProlateSignedValue a n : ℂ) ^ 2 * q x).re := by rw [hcplx]
    _ = evenProlateSignedValue a n ^ 2 * (q x).re := by
          rw [← Complex.ofReal_pow, Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The imaginary channel of the unit-band extension is a global real Slepian eigenfunction. -/
theorem bandTransform_evenProlateSignedUnitExtension_im_global
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    bandTransform (2 * Real.pi * a ^ 2)
        (fun t => (evenProlateSignedUnitExtension a n hvalue t).im) x =
      evenProlateSignedValue a n ^ 2 *
        (evenProlateSignedUnitExtension a n hvalue x).im := by
  set q := evenProlateSignedUnitExtension a n hvalue with hq
  set c := 2 * Real.pi * a ^ 2 with hc
  have hqc : Continuous q := continuous_evenProlateSignedUnitExtension a n hvalue
  have hint : IntegrableOn
      (fun t : ℝ => ((sincKernelSmooth c x t : ℝ) : ℂ) * q t) (Icc (-1 : ℝ) 1) volume :=
    ((Complex.continuous_ofReal.comp
      ((contDiff_sincSmooth c).continuous.comp (by fun_prop))).mul hqc).integrableOn_Icc
  have hcplx := evenProlateSignedUnitExtension_bandIntegral_eigen_global ha hvalue x
  calc
    bandTransform c (fun t => (q t).im) x =
        ∫ t in Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).im := by
          rw [bandTransform, intervalIntegral.integral_of_le (by norm_num),
            ← integral_Icc_eq_integral_Ioc]
    _ = (∫ t in Icc (-1 : ℝ) 1, ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := by
          calc
            (∫ t in Icc (-1 : ℝ) 1, sincKernelSmooth c x t * (q t).im) =
                ∫ t in Icc (-1 : ℝ) 1,
                  (((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := by
                    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
                    simp
            _ = (∫ t in Icc (-1 : ℝ) 1,
                  ((sincKernelSmooth c x t : ℝ) : ℂ) * q t).im := integral_im hint
    _ = ((evenProlateSignedValue a n : ℂ) ^ 2 * q x).im := by rw [hcplx]
    _ = evenProlateSignedValue a n ^ 2 * (q x).im := by
          rw [← Complex.ofReal_pow, Complex.mul_im]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **Exact pointwise self-reciprocity.**  The Fourier transform of the canonical source is the
signed eigenvalue times the unit-band extension at the rescaled frequency, at every real point. -/
theorem fourier_evenProlateSignedPointwiseSource_eq_unitExtension
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (w : ℝ) :
    𝓕 (evenProlateSignedPointwiseSource a n hvalue) w =
      (evenProlateSignedValue a n : ℂ) *
        evenProlateSignedUnitExtension a n hvalue (w / a) := by
  have hχ : ((evenProlateSignedValue a n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvalue
  rw [fourier_evenProlateSignedPointwiseSource_eq_representative a ha.le n hvalue w,
    evenProlateSignedUnitExtension, mul_div_cancel₀ w ha.ne', ← mul_assoc,
    mul_inv_cancel₀ hχ, one_mul]

/-- Real-channel form of the self-reciprocity. -/
theorem re_fourier_evenProlateSignedPointwiseSource_eq_unitExtension
    (ha : 0 < a) (hvalue : evenProlateSignedValue a n ≠ 0) (w : ℝ) :
    (𝓕 (evenProlateSignedPointwiseSource a n hvalue) w).re =
      evenProlateSignedValue a n *
        (evenProlateSignedUnitExtension a n hvalue (w / a)).re := by
  rw [fourier_evenProlateSignedPointwiseSource_eq_unitExtension ha hvalue w, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end RHTower
