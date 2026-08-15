import GaloisForLFunctions.RHTower.ProlateBandComponentEven
import GaloisForLFunctions.HTGeometry.CompactFourierIntegrableEntire

/-!
# The Slepian band operator is injective

The band operator is the composition of two finite Fourier transforms.  Its value at a point is
therefore the compact Fourier transform of the inner transform, read at a rescaled real frequency;
both transforms are entire in that frequency because their amplitudes are merely integrable.  An
element of the kernel makes the outer transform vanish almost everywhere on the aperture, the
identity theorem spreads that to the whole plane, `L¹` Fourier uniqueness kills the inner transform,
and the same two steps applied once more kill the element itself.

Consequently the eigenvalue `0` contributes nothing to the spectral decomposition of the aperture
`L²` space: every eigencomponent lives at a nonzero eigenvalue, where the smooth representative and
the prolate machinery are available.
-/

noncomputable section

open MeasureTheory Set

attribute [local instance] Measure.Subtype.measureSpace

namespace RHTower

/-- The zero-extension of an `L²` class on the unit band to the whole line. -/
def bandZeroExtend (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ → ℝ :=
  fun x => if h : x ∈ Set.Icc (-1 : ℝ) 1 then (f ⟨x, h⟩ : ℝ) else 0

theorem bandZeroExtend_coe (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
    (y : Set.Icc (-1 : ℝ) 1) : bandZeroExtend f (y : ℝ) = (f y : ℝ) := by
  unfold bandZeroExtend
  rw [dif_pos y.2]

theorem bandZeroExtend_eq_zero (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : bandZeroExtend f x = 0 := by
  unfold bandZeroExtend
  rw [dif_neg hx]

theorem integrable_bandZeroExtend (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    Integrable (bandZeroExtend f) volume := by
  have hsub : Integrable (fun y : Set.Icc (-1 : ℝ) 1 => bandZeroExtend f (y : ℝ))
      (volume : Measure (Set.Icc (-1 : ℝ) 1)) := by
    refine (GaloisForLFunctions.RHTower.integrable_of_realIntervalL2 f).congr ?_
    filter_upwards with y
    exact (bandZeroExtend_coe f y).symm
  have hon : IntegrableOn (bandZeroExtend f) (Set.Icc (-1 : ℝ) 1) volume :=
    (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Icc).mpr hsub
  have hind : Set.indicator (Set.Icc (-1 : ℝ) 1) (bandZeroExtend f) = bandZeroExtend f := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, bandZeroExtend_eq_zero f hx]
  rw [← hind]
  exact (integrable_indicator_iff measurableSet_Icc).mpr hon

/-- Complexified zero-extension. -/
def bandZeroExtendC (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ → ℂ :=
  fun x => ((bandZeroExtend f x : ℝ) : ℂ)

theorem integrable_bandZeroExtendC (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    Integrable (bandZeroExtendC f) volume := (integrable_bandZeroExtend f).ofReal

theorem bandZeroExtendC_eq_zero (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : bandZeroExtendC f x = 0 := by
  rw [bandZeroExtendC, bandZeroExtend_eq_zero f hx, Complex.ofReal_zero]

/-- The compact Fourier transform on the unit band, as a set integral. -/
theorem compactFourier_unit_eq_setIntegral (h : ℝ → ℂ) (z : ℂ) :
    GaloisForLFunctions.HTGeometry.compactFourier h (-1) 1 z
      = ∫ t in Set.Icc (-1 : ℝ) 1, h t * Complex.exp (Complex.I * (z * (t : ℂ))) := by
  rw [GaloisForLFunctions.HTGeometry.compactFourier,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The inner finite-Fourier transform of the zero-extension. -/
def bandInnerTransform (κ : ℝ) (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    ℝ → ℂ :=
  fun y => ∫ t in Set.Icc (-1 : ℝ) 1,
    Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * bandZeroExtendC f t

theorem bandInnerTransform_eq_compactFourier (κ : ℝ)
    (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) (y : ℝ) :
    bandInnerTransform κ f y
      = GaloisForLFunctions.HTGeometry.compactFourier (bandZeroExtendC f) (-1) 1
          ((-(2 * Real.pi * κ * y) : ℝ) : ℂ) := by
  rw [compactFourier_unit_eq_setIntegral, bandInnerTransform]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [show Complex.I * (((-(2 * Real.pi * κ * y) : ℝ) : ℂ) * (t : ℂ))
      = ((-(2 * Real.pi * κ * y * t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  ring

theorem continuous_bandInnerTransform (κ : ℝ)
    (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    Continuous (bandInnerTransform κ f) := by
  have hcf : Continuous (GaloisForLFunctions.HTGeometry.compactFourier
      (bandZeroExtendC f) (-1) 1) :=
    GaloisForLFunctions.HTGeometry.continuous_compactFourier_of_integrable
      ((integrable_bandZeroExtendC f).intervalIntegrable)
  have hlin : Continuous fun y : ℝ => (((-(2 * Real.pi * κ * y) : ℝ)) : ℂ) := by fun_prop
  have hcomp : Continuous fun y : ℝ =>
      GaloisForLFunctions.HTGeometry.compactFourier (bandZeroExtendC f) (-1) 1
        (((-(2 * Real.pi * κ * y) : ℝ)) : ℂ) := hcf.comp hlin
  exact hcomp.congr fun y => (bandInnerTransform_eq_compactFourier κ f y).symm

/-- The smoothing extension at unit eigenvalue is the complex set integral of the
zero-extension against the kernel. -/
theorem eigenExtension_one_eq_setIntegral {c : ℝ}
    (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) (x : ℝ) :
    ((GaloisForLFunctions.RHTower.eigenExtension c 1 f x : ℝ) : ℂ)
      = ∫ t in Set.Icc (-1 : ℝ) 1, ((sincKernelSmooth c x t : ℝ) : ℂ) * bandZeroExtendC f t := by
  have hswap : (∫ y : Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * (f y : ℝ) ∂volume)
      = ∫ y : Set.Icc (-1 : ℝ) 1,
          sincKernelSmooth c x (y : ℝ) * bandZeroExtend f (y : ℝ) ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [bandZeroExtend_coe f y]
  have hsub := GaloisForLFunctions.RHTower.integral_subtype_unit
    (fun t => sincKernelSmooth c x t * bandZeroExtend f t)
  have hIcc : (∫ t in (-1 : ℝ)..1, sincKernelSmooth c x t * bandZeroExtend f t)
      = ∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * bandZeroExtend f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hreal : GaloisForLFunctions.RHTower.eigenExtension c 1 f x
      = ∫ t in Set.Icc (-1 : ℝ) 1, sincKernelSmooth c x t * bandZeroExtend f t := by
    rw [GaloisForLFunctions.RHTower.eigenExtension, inv_one, one_mul, hswap, hsub, hIcc]
  have hcast : (∫ t in Set.Icc (-1 : ℝ) 1, ((sincKernelSmooth c x t : ℝ) : ℂ) * bandZeroExtendC f t)
      = ∫ t in Set.Icc (-1 : ℝ) 1, ((sincKernelSmooth c x t * bandZeroExtend f t : ℝ) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [bandZeroExtendC]
    push_cast
    ring
  rw [hreal, hcast, integral_complex_ofReal]

/-- **The band integral is the composition of two finite Fourier transforms.** -/
theorem eigenExtension_one_eq_compactFourier {κ : ℝ} (hκ : 0 < κ)
    (f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) (x : ℝ) :
    ((GaloisForLFunctions.RHTower.eigenExtension (2 * Real.pi * κ) 1 f x : ℝ) : ℂ)
      = (κ : ℂ) * GaloisForLFunctions.HTGeometry.compactFourier
          (bandInnerTransform κ f) (-1) 1 ((2 * Real.pi * κ * x : ℝ) : ℂ) := by
  have hg : MeasureTheory.IntegrableOn (bandZeroExtendC f) (Set.Icc (-1 : ℝ) 1) volume :=
    (integrable_bandZeroExtendC f).integrableOn
  have hdouble := double_integral_scaledFourierChar_eq_sinc 1 κ (-x) (by norm_num) hg
  have hband := scaled_sincIntegral_eq_bandIntegral κ x hκ (bandZeroExtendC f)
  -- rewrite the inner integral as the inner transform
  have hinner : (∫ y in Set.Icc (-1 : ℝ) 1,
      Complex.exp ((-(2 * Real.pi * κ * (-x) * y) : ℝ) * Complex.I) *
        ∫ t in Set.Icc (-1 : ℝ) 1,
          Complex.exp ((-(2 * Real.pi * κ * y * t) : ℝ) * Complex.I) * bandZeroExtendC f t)
      = GaloisForLFunctions.HTGeometry.compactFourier
          (bandInnerTransform κ f) (-1) 1 ((2 * Real.pi * κ * x : ℝ) : ℂ) := by
    rw [compactFourier_unit_eq_setIntegral]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [bandInnerTransform]
    rw [show Complex.I * (((2 * Real.pi * κ * x : ℝ) : ℂ) * (y : ℂ))
        = ((-(2 * Real.pi * κ * (-x) * y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    ring
  -- rewrite the reflected sinc profile
  have hrefl : (∫ t in Set.Icc (-1 : ℝ) 1,
      ((sincSmooth (2 * Real.pi * 1) (κ * (-x + t)) : ℝ) : ℂ) * bandZeroExtendC f t)
      = ∫ t in Set.Icc (-1 : ℝ) 1,
          ((sincSmooth (2 * Real.pi) (κ * (x - t)) : ℝ) : ℂ) * bandZeroExtendC f t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [mul_one, show κ * (-x + t) = -(κ * (x - t)) by ring, sincSmooth_even]
  rw [hinner] at hdouble
  rw [hrefl] at hdouble
  rw [eigenExtension_one_eq_setIntegral, ← hband, hdouble]

/-- Integrals of a real profile over the band subtype and over the interval agree, through the
zero-extension. -/
theorem integral_subtype_abs (F : ℝ → ℝ) :
    (∫ y : Set.Icc (-1 : ℝ) 1, F (y : ℝ) ∂volume) = ∫ y in Set.Icc (-1 : ℝ) 1, F y := by
  have hsub := GaloisForLFunctions.RHTower.integral_subtype_unit F
  rw [hsub, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The Slepian band operator is injective.** -/
theorem eq_zero_of_bandOperatorL2_eq_zero {c : ℝ} (hc : 0 < c)
    {f : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hf : GaloisForLFunctions.RHTower.bandOperatorL2 c f = 0) : f = 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set κ : ℝ := c / (2 * Real.pi) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hcκ : 2 * Real.pi * κ = c := by rw [hκdef]; field_simp
  set Ψ := GaloisForLFunctions.RHTower.eigenExtension c 1 f with hΨ
  have hΨc : Continuous Ψ := GaloisForLFunctions.RHTower.continuous_eigenExtension c 1 f
  -- the band value vanishes almost everywhere on the aperture
  have hae : ∀ᵐ x : Set.Icc (-1 : ℝ) 1 ∂volume, Ψ (x : ℝ) = 0 := by
    have h1 := GaloisForLFunctions.RHTower.bandOperatorL2_coeFn c f
    have h2 : ((GaloisForLFunctions.RHTower.bandOperatorL2 c f :
        GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
        Set.Icc (-1 : ℝ) 1 → ℝ) =ᵐ[volume] 0 := by
      rw [hf]
      exact Lp.coeFn_zero ℝ 2 _
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1] at hx2
    rw [hΨ, GaloisForLFunctions.RHTower.eigenExtension, inv_one, one_mul]
    simpa using hx2
  -- hence almost everywhere on the interval
  have haeIcc : Ψ =ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] 0 := by
    have hzero : (∫ x : Set.Icc (-1 : ℝ) 1, |Ψ (x : ℝ)| ∂volume) = 0 := by
      rw [MeasureTheory.integral_congr_ae (g := fun _ : Set.Icc (-1 : ℝ) 1 => (0 : ℝ))
        (by filter_upwards [hae] with x hx; rw [hx, abs_zero])]
      simp
    rw [integral_subtype_abs (fun y => |Ψ y|)] at hzero
    have hnn : ∀ y, 0 ≤ |Ψ y| := fun y => abs_nonneg _
    have hint : MeasureTheory.IntegrableOn (fun y => |Ψ y|) (Set.Icc (-1 : ℝ) 1) volume :=
      (hΨc.abs.integrableOn_Icc)
    have habs := (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn hint).mp hzero
    filter_upwards [habs] with y hy
    have : |Ψ y| = 0 := hy
    simpa using abs_eq_zero.mp this
  have haeIoo : Ψ =ᵐ[volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))] 0 := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset ?_ haeIcc
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- the outer transform is entire and vanishes on the aperture
  have hAcont : Continuous (bandInnerTransform κ f) := continuous_bandInnerTransform κ f
  set F₁ : ℂ → ℂ := fun z => GaloisForLFunctions.HTGeometry.compactFourier
    (bandInnerTransform κ f) (-1) 1 (((2 * Real.pi * κ : ℝ) : ℂ) * z) with hF₁
  have hF₁diff : Differentiable ℂ F₁ := by
    have h := GaloisForLFunctions.HTGeometry.differentiable_compactFourier_of_integrable
      (a := (-1 : ℝ)) (b := (1 : ℝ)) (hAcont.intervalIntegrable (-1) 1)
    exact h.comp (by fun_prop)
  have hkey : ∀ x : ℝ, ((Ψ x : ℝ) : ℂ)
      = (κ : ℂ) * GaloisForLFunctions.HTGeometry.compactFourier
          (bandInnerTransform κ f) (-1) 1 ((2 * Real.pi * κ * x : ℝ) : ℂ) := by
    intro x
    rw [hΨ, ← hcκ]
    exact eigenExtension_one_eq_compactFourier hκ f x
  have hF₁real : ∀ x : ℝ, (κ : ℂ) * F₁ ((x : ℝ) : ℂ) = ((Ψ x : ℝ) : ℂ) := by
    intro x
    simp only [hF₁]
    rw [hkey x,
      show (((2 * Real.pi * κ : ℝ) : ℂ) * ((x : ℝ) : ℂ)) = ((2 * Real.pi * κ * x : ℝ) : ℂ) by
        push_cast; ring]
  have hF₁ae : ∀ᵐ t ∂(volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))),
      F₁ ((t : ℝ) : ℂ) = 0 := by
    filter_upwards [haeIoo] with t ht
    have h := hF₁real t
    have hΨt : ((Ψ t : ℝ) : ℂ) = 0 := by rw [show Ψ t = 0 from ht, Complex.ofReal_zero]
    rw [hΨt] at h
    have hκne : ((κ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
    exact (mul_eq_zero.mp h).resolve_left hκne
  have hF₁zero : ∀ z : ℂ, F₁ z = 0 :=
    GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
      hF₁diff (by norm_num : (0 : ℝ) < 1) hF₁ae
  have hAfourier : ∀ w : ℂ, GaloisForLFunctions.HTGeometry.compactFourier
      (bandInnerTransform κ f) (-1) 1 w = 0 := by
    intro w
    have hz := hF₁zero (((2 * Real.pi * κ : ℝ) : ℂ)⁻¹ * w)
    simp only [hF₁] at hz
    have hne : ((2 * Real.pi * κ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hz
  -- the inner transform vanishes almost everywhere on the aperture
  set A' : ℝ → ℂ := Set.indicator (Set.Icc (-1 : ℝ) 1) (bandInnerTransform κ f) with hA'
  have hA'int : MeasureTheory.Integrable A' volume := by
    rw [hA']
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    exact hAcont.integrableOn_Icc
  have hA'supp : ∀ x : ℝ, x ∉ Set.Icc (-1 : ℝ) 1 → A' x = 0 := by
    intro x hx
    rw [hA', Set.indicator_of_notMem hx]
  have hA'fourier : ∀ z : ℂ, GaloisForLFunctions.HTGeometry.compactFourier A' (-1) 1 z = 0 := by
    intro z
    rw [show GaloisForLFunctions.HTGeometry.compactFourier A' (-1) 1 z
        = GaloisForLFunctions.HTGeometry.compactFourier (bandInnerTransform κ f) (-1) 1 z from ?_]
    · exact hAfourier z
    · rw [GaloisForLFunctions.HTGeometry.compactFourier,
        GaloisForLFunctions.HTGeometry.compactFourier]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
        rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      rw [hA', Set.indicator_of_mem htIcc]
  have hA'ae : A' =ᵐ[volume] 0 :=
    GaloisForLFunctions.HTGeometry.ae_eq_zero_of_compactFourier_vanishing (t₀ := 0)
      (by norm_num : (-1 : ℝ) ≤ 1) hA'int hA'supp (by norm_num : (0 : ℝ) < 1)
      (Filter.Eventually.of_forall fun t => hA'fourier _)
  -- transfer to the inner transform on the open aperture
  have hAae : ∀ᵐ t ∂(volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))),
      bandInnerTransform κ f t = 0 := by
    have hres : A' =ᵐ[volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))] 0 :=
      MeasureTheory.ae_restrict_of_ae hA'ae
    filter_upwards [hres, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htmem
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [htmem.1], by linarith [htmem.2]⟩
    rw [hA', Set.indicator_of_mem htIcc] at ht
    exact ht
  -- the zero-extension's own transform is entire and vanishes on the aperture
  set F₂ : ℂ → ℂ := fun z => GaloisForLFunctions.HTGeometry.compactFourier
    (bandZeroExtendC f) (-1) 1 (((-(2 * Real.pi * κ) : ℝ) : ℂ) * z) with hF₂
  have hF₂diff : Differentiable ℂ F₂ := by
    have h := GaloisForLFunctions.HTGeometry.differentiable_compactFourier_of_integrable
      (a := (-1 : ℝ)) (b := (1 : ℝ)) ((integrable_bandZeroExtendC f).intervalIntegrable)
    exact h.comp (by fun_prop)
  have hF₂ae : ∀ᵐ t ∂(volume.restrict (Set.Ioo ((0 : ℝ) - 1) ((0 : ℝ) + 1))),
      F₂ ((t : ℝ) : ℂ) = 0 := by
    filter_upwards [hAae] with t ht
    simp only [hF₂]
    rw [show (((-(2 * Real.pi * κ) : ℝ) : ℂ) * ((t : ℝ) : ℂ)) = ((-(2 * Real.pi * κ * t) : ℝ) : ℂ) by
      push_cast; ring]
    rw [← bandInnerTransform_eq_compactFourier κ f t]
    exact ht
  have hF₂zero : ∀ z : ℂ, F₂ z = 0 :=
    GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
      hF₂diff (by norm_num : (0 : ℝ) < 1) hF₂ae
  have hGfourier : ∀ w : ℂ, GaloisForLFunctions.HTGeometry.compactFourier
      (bandZeroExtendC f) (-1) 1 w = 0 := by
    intro w
    have hz := hF₂zero (((-(2 * Real.pi * κ) : ℝ) : ℂ)⁻¹ * w)
    simp only [hF₂] at hz
    have hne : ((-(2 * Real.pi * κ) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      have : (0 : ℝ) < 2 * Real.pi * κ := by positivity
      linarith
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hz
  have hGae : bandZeroExtendC f =ᵐ[volume] 0 :=
    GaloisForLFunctions.HTGeometry.ae_eq_zero_of_compactFourier_vanishing (t₀ := 0)
      (by norm_num : (-1 : ℝ) ≤ 1) (integrable_bandZeroExtendC f)
      (fun x hx => bandZeroExtendC_eq_zero f hx) (by norm_num : (0 : ℝ) < 1)
      (Filter.Eventually.of_forall fun t => hGfourier _)
  -- conclude
  have hgae : bandZeroExtend f =ᵐ[volume] 0 := by
    filter_upwards [hGae] with x hx
    have : ((bandZeroExtend f x : ℝ) : ℂ) = 0 := hx
    exact_mod_cast this
  have hzero : (∫ y : Set.Icc (-1 : ℝ) 1, |(f y : ℝ)| ∂volume) = 0 := by
    have hcongr : (∫ y : Set.Icc (-1 : ℝ) 1, |(f y : ℝ)| ∂volume)
        = ∫ y : Set.Icc (-1 : ℝ) 1, |bandZeroExtend f (y : ℝ)| ∂volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with y
      rw [bandZeroExtend_coe f y]
    rw [hcongr, integral_subtype_abs (fun y => |bandZeroExtend f y|)]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hgae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, abs_zero]
  have hint : MeasureTheory.Integrable (fun y : Set.Icc (-1 : ℝ) 1 => |(f y : ℝ)|)
      (volume : Measure (Set.Icc (-1 : ℝ) 1)) :=
    (GaloisForLFunctions.RHTower.integrable_of_realIntervalL2 f).abs
  have hfae := (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hint).mp hzero
  refine Lp.ext ?_
  filter_upwards [hfae, Lp.coeFn_zero ℝ 2 (volume : Measure (Set.Icc (-1 : ℝ) 1))] with y hy hz
  rw [hz]
  have : |(f y : ℝ)| = 0 := hy
  exact abs_eq_zero.mp this

/-- The zero eigenspace of the band operator is trivial. -/
theorem bandEigenspace_zero_eq_bot {c : ℝ} (hc : 0 < c) :
    GaloisForLFunctions.RHTower.bandEigenspace c 0 = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.mpr fun f hf => ?_
  have h := GaloisForLFunctions.RHTower.mem_bandEigenspace_iff.mp hf
  rw [zero_smul] at h
  exact eq_zero_of_bandOperatorL2_eq_zero hc h

/-- **The zero eigencomponent vanishes.** -/
theorem bandComponent_zero_eq_zero {c : ℝ} (hc : 0 < c)
    (v : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    bandComponent c v 0 = 0 := by
  have hmem := bandComponent_mem c v 0
  rw [bandEigenspace_zero_eq_bot hc, Submodule.mem_bot] at hmem
  exact hmem

end RHTower
