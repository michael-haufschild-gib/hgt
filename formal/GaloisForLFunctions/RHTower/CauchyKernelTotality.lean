import GaloisForLFunctions.RHTower.CauchyTransformHardy
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective

noncomputable section

/-!
# Totality of the Cauchy kernels

The Cauchy kernels `k_v(x) = (x - v)⁻¹` with `Im v > 0` are total in the orthogonal complement of
the Hardy space: an `L²` boundary function whose Cauchy transform vanishes on the whole open lower
half-plane already lies in `H²`.  This is the exact converse of `integral_cauchyTransform_eq_zero`.

The proof works on the Fourier side.  Above the axis the kernel is the Fourier transform of the
one-sided exponential `2πi e^{2πi v s} 1_{s>0}`, which is genuinely `L¹ ∩ L²` because `Im v > 0`
makes it decay.  The component of the given function orthogonal to `H²` carries a datum on the
positive ray, and Plancherel turns the pairing with the kernel into the half-line Laplace transform
of that datum at the point `2πi conj v`.  As `v` runs over the upper half-plane those points sweep
out the whole open right half-plane, so injectivity of the half-line Laplace transform forces the
datum to vanish.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform

namespace RHTower

/-- The one-sided exponential whose Fourier transform is the Cauchy kernel above the axis. -/
def cauchyDatumUpper (v : ℂ) : ℝ → ℂ :=
  Set.indicator (Set.Ioi (0 : ℝ))
    (fun s : ℝ => (2 * (Real.pi : ℂ) * I) *
      Complex.exp (2 * (Real.pi : ℂ) * I * v * (s : ℂ)))

/-- The decay rate of the upper datum. -/
def cauchyRateUpper (v : ℂ) : ℝ := 2 * Real.pi * v.im

theorem cauchyRateUpper_pos {v : ℂ} (hv : 0 < v.im) : 0 < cauchyRateUpper v := by
  have := Real.pi_pos
  simp only [cauchyRateUpper]
  positivity

theorem re_cauchyUpperExponent (v : ℂ) (s : ℝ) :
    (2 * (Real.pi : ℂ) * I * v * (s : ℂ)).re = -(cauchyRateUpper v * s) := by
  simp only [cauchyRateUpper]
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_cauchyDatumUpper (v : ℂ) (s : ℝ) :
    ‖cauchyDatumUpper v s‖
      = Set.indicator (Set.Ioi (0 : ℝ))
        (fun s : ℝ => 2 * Real.pi * Real.exp (-(cauchyRateUpper v * s))) s := by
  rcases lt_or_ge 0 s with h | h
  · have hmem : s ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr h
    rw [cauchyDatumUpper, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, norm_mul,
      Complex.norm_exp, re_cauchyUpperExponent]
    congr 1
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  · have hnot : s ∉ Set.Ioi (0 : ℝ) := by simpa using h
    rw [cauchyDatumUpper, Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot, norm_zero]

theorem integrable_cauchyDatumUpper {v : ℂ} (hv : 0 < v.im) :
    Integrable (cauchyDatumUpper v) volume := by
  have hb := cauchyRateUpper_pos hv
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-(cauchyRateUpper v * s)))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_Ioi (a := -(cauchyRateUpper v)) (by linarith) 0
    refine h.congr_fun ?_ measurableSet_Ioi
    intro s _
    show Real.exp (-(cauchyRateUpper v) * s) = Real.exp (-(cauchyRateUpper v * s))
    ring_nf
  have h1 : IntegrableOn (fun s : ℝ => 2 * Real.pi * Real.exp (-(cauchyRateUpper v * s)))
      (Set.Ioi (0 : ℝ)) := Integrable.const_mul h0 (2 * Real.pi)
  have hmajall : Integrable (Set.indicator (Set.Ioi (0 : ℝ))
      (fun s : ℝ => 2 * Real.pi * Real.exp (-(cauchyRateUpper v * s)))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr h1
  refine Integrable.mono' hmajall ?_ ?_
  · refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioi
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  · filter_upwards with s
    rw [norm_cauchyDatumUpper]

theorem re_cauchyUpperShift (v : ℂ) (ξ : ℝ) :
    (2 * (Real.pi : ℂ) * I * (v - (ξ : ℂ))).re = -(cauchyRateUpper v) := by
  simp only [cauchyRateUpper]
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]

/-- **The Cauchy kernel above the axis is the Fourier transform of a one-sided exponential.** -/
theorem fourierIntegral_cauchyDatumUpper {v : ℂ} (hv : 0 < v.im) (ξ : ℝ) :
    𝓕 (cauchyDatumUpper v) ξ = (((ξ : ℝ) : ℂ) - v)⁻¹ := by
  have hb := cauchyRateUpper_pos hv
  have ha : (2 * (Real.pi : ℂ) * I * (v - (ξ : ℂ))).re < 0 := by
    rw [re_cauchyUpperShift]
    linarith
  have hane : (2 * (Real.pi : ℂ) * I * (v - (ξ : ℂ))) ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hpt : ∀ s : ℝ,
      (Real.fourierChar (-(inner ℝ s ξ)) : ℂ) * cauchyDatumUpper v s
        = Set.indicator (Set.Ioi (0 : ℝ))
          (fun s : ℝ => (2 * (Real.pi : ℂ) * I) *
            Complex.exp (2 * (Real.pi : ℂ) * I * (v - (ξ : ℂ)) * (s : ℂ))) s := by
    intro s
    rcases lt_or_ge 0 s with h | h
    · have hmem : s ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr h
      rw [cauchyDatumUpper, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Real.fourierChar_apply]
      rw [show (-(inner ℝ s ξ) : ℝ) = -(s * ξ) by simp [mul_comm]]
      rw [show Complex.exp (((2 * Real.pi * -(s * ξ) : ℝ) : ℂ) * I)
            * (2 * (Real.pi : ℂ) * I * Complex.exp (2 * (Real.pi : ℂ) * I * v * (s : ℂ)))
          = (2 * (Real.pi : ℂ) * I)
            * (Complex.exp (((2 * Real.pi * -(s * ξ) : ℝ) : ℂ) * I)
              * Complex.exp (2 * (Real.pi : ℂ) * I * v * (s : ℂ))) by ring]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    · have hnot : s ∉ Set.Ioi (0 : ℝ) := by simpa using h
      rw [cauchyDatumUpper, Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot, mul_zero]
  rw [Real.fourier_eq]
  have hsmul : ∀ s : ℝ, (Real.fourierChar (-(inner ℝ s ξ))) • cauchyDatumUpper v s
      = (Real.fourierChar (-(inner ℝ s ξ)) : ℂ) * cauchyDatumUpper v s := fun s => rfl
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun s => (hsmul s).trans (hpt s)))]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi ha 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  rw [show ((ξ : ℂ) - v) = -(v - (ξ : ℂ)) by ring, one_div, one_div, inv_neg]

theorem norm_cauchyDatumUpper_le {v : ℂ} (hv : 0 < v.im) (s : ℝ) :
    ‖cauchyDatumUpper v s‖ ≤ 2 * Real.pi := by
  have hb := cauchyRateUpper_pos hv
  rcases lt_or_ge 0 s with h | h
  · have hmem : s ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr h
    rw [norm_cauchyDatumUpper, Set.indicator_of_mem hmem]
    have hexp : Real.exp (-(cauchyRateUpper v * s)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    nlinarith [Real.pi_pos, Real.exp_pos (-(cauchyRateUpper v * s))]
  · have hnot : s ∉ Set.Ioi (0 : ℝ) := by simpa using h
    rw [norm_cauchyDatumUpper, Set.indicator_of_notMem hnot]
    positivity

theorem memLp_cauchyDatumUpper {v : ℂ} (hv : 0 < v.im) :
    MemLp (cauchyDatumUpper v) 2 (volume : Measure ℝ) := by
  have hint := integrable_cauchyDatumUpper hv
  refine (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (hint.norm.const_mul (2 * Real.pi)) ?_ ?_
  · exact (hint.aestronglyMeasurable.norm.pow 2)
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right (norm_cauchyDatumUpper_le hv s) (norm_nonneg _)


theorem cauchyDatumUpper_mem_halfLineL2 {v : ℂ} (hv : 0 < v.im) :
    (memLp_cauchyDatumUpper hv).toLp _ ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  filter_upwards [(memLp_cauchyDatumUpper hv).coeFn_toLp] with x h1 hx
  rw [h1, cauchyDatumUpper, Set.indicator_of_notMem (by simp; linarith)]

/-- The Cauchy kernel above the axis is the `L²` Fourier transform of the one-sided exponential
`cauchyDatumUpper`. -/
theorem fourierTransform_cauchyDatumUpper {v : ℂ} (hv : 0 < v.im) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap
        ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : Lp ℂ 2 (volume : Measure ℝ))
      = (memLp_cauchyKernel (ne_of_gt hv)).toLp (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹) := by
  have hint : Integrable (((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : ℝ → ℂ) :=
    (integrable_cauchyDatumUpper hv).congr (memLp_cauchyDatumUpper hv).coeFn_toLp.symm
  refine MeasureTheory.Lp.ext ?_
  have hbridge := GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_ae_eq_fourierIntegral
    ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) hint
  have hclass : ∀ ξ : ℝ,
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp
        (((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : ℝ → ℂ)) : ℝ → ℂ) ξ
        = (((ξ : ℝ) : ℂ) - v)⁻¹ := by
    intro ξ
    rw [Real.Lp.fourierTransform_apply, ← fourierIntegral_cauchyDatumUpper hv ξ]
    have hae : (((memLp_one_iff_integrable.mpr hint).toLp
        (((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : ℝ → ℂ)) : ℝ → ℂ)
        =ᵐ[volume] cauchyDatumUpper v :=
      ((memLp_one_iff_integrable.mpr hint).coeFn_toLp).trans
        (memLp_cauchyDatumUpper hv).coeFn_toLp
    rw [Real.fourier_eq, Real.fourier_eq]
    exact MeasureTheory.integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  have hbridge' : (((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap
      ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : Lp ℂ 2 (volume : Measure ℝ)) :
        ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ =>
        (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hint).toLp
          (((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) : ℝ → ℂ))) ξ := hbridge
  filter_upwards [hbridge', (memLp_cauchyKernel (ne_of_gt hv)).coeFn_toLp] with ξ h1 h2
  rw [h1, hclass ξ, h2]


open GaloisForLFunctions.HTGeometry in
/-- Pairing the one-sided exponential against an `L²` function is the half-line Laplace transform
of that function. -/
theorem inner_cauchyDatumUpper {v : ℂ} (hv : 0 < v.im) (d : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) d : ℂ)
      = (-(2 * (Real.pi : ℂ) * I)) *
        laplaceRay (d : ℝ → ℂ) (2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) v) := by
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x : ℝ =>
        (inner ℂ ((((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) ((d : ℝ → ℂ) x) : ℂ))
      =ᵐ[volume] Set.indicator (Set.Ioi (0 : ℝ))
        (fun s : ℝ => (-(2 * (Real.pi : ℂ) * I)) *
          ((d : ℝ → ℂ) s * expRay (2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) v) s)) := by
    filter_upwards [(memLp_cauchyDatumUpper hv).coeFn_toLp] with x h1
    rw [RCLike.inner_apply, h1]
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx, cauchyDatumUpper, Set.indicator_of_mem hx, map_mul,
        ← Complex.exp_conj, expRay]
      have hc1 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * I) = -(2 * (Real.pi : ℂ) * I) := by
        simp [Complex.ext_iff]
      have hc2 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * I * v * (x : ℂ))
          = -(2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) v * (x : ℂ)) := by
        rw [map_mul, map_mul, hc1, Complex.conj_ofReal]
        ring
      rw [hc1, hc2]
      ring
    · rw [Set.indicator_of_notMem hx, cauchyDatumUpper, Set.indicator_of_notMem hx, map_zero,
        mul_zero]
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_indicator measurableSet_Ioi,
    MeasureTheory.integral_const_mul]
  rfl


open GaloisForLFunctions.HTGeometry in
/-- **Totality of the Cauchy kernels with one point removed.**  Vanishing of the Cauchy transform
on the lower half-plane away from a single point already forces membership in the Hardy space, since
the corresponding datum's Laplace transform then vanishes off one point of the right half-plane. -/
theorem mem_hardyL2_of_cauchyTransform_eq_zero_of_ne {F : Lp ℂ 2 (volume : Measure ℝ)} (v₀ : ℂ)
    (h : ∀ w : ℂ, w.im < 0 → w ≠ v₀ →
      (∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    F ∈ hardyL2 := by
  haveI : CompleteSpace (hardyL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
    isClosed_hardyL2.completeSpace_coe
  set P : Lp ℂ 2 (volume : Measure ℝ) := hardyL2.starProjection F with hP
  have hPmem : P ∈ hardyL2 := hardyL2.starProjection_apply_mem F
  set G : Lp ℂ 2 (volume : Measure ℝ) := F - P with hG
  have hGmem : G ∈ hardyL2ᗮ := hardyL2.sub_starProjection_mem_orthogonal F
  -- the Cauchy kernels above the axis annihilate `F`
  have hkF : ∀ (v : ℂ) (hv : 0 < v.im), v ≠ (starRingEnd ℂ) v₀ →
      (inner ℂ ((memLp_cauchyKernel (ne_of_gt hv)).toLp
        (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹)) F : ℂ) = 0 := by
    intro v hv hvne
    have hconj : ((starRingEnd ℂ) v).im < 0 := by simpa using hv
    have hconjne : (starRingEnd ℂ) v ≠ v₀ := by
      intro hc
      exact hvne (by rw [← hc, Complex.conj_conj])
    rw [MeasureTheory.L2.inner_def]
    have hrw : (∫ x : ℝ, (inner ℂ ((((memLp_cauchyKernel (ne_of_gt hv)).toLp
          (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
          ((F : ℝ → ℂ) x) : ℂ))
        = ∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - (starRingEnd ℂ) v) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [(memLp_cauchyKernel (ne_of_gt hv)).coeFn_toLp] with x h1
      rw [RCLike.inner_apply, h1]
      show (F : ℝ → ℂ) x * (starRingEnd ℂ) ((((x : ℝ) : ℂ) - v)⁻¹)
        = (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - (starRingEnd ℂ) v)
      rw [map_inv₀, map_sub, Complex.conj_ofReal, div_eq_mul_inv]
    rw [hrw]
    exact h _ hconj hconjne
  -- hence they annihilate the component of `F` orthogonal to the Hardy space
  have hkG : ∀ (v : ℂ) (hv : 0 < v.im), v ≠ (starRingEnd ℂ) v₀ →
      (inner ℂ ((memLp_cauchyKernel (ne_of_gt hv)).toLp
        (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹)) G : ℂ) = 0 := by
    intro v hv hvne
    have hkP : (inner ℂ ((memLp_cauchyKernel (ne_of_gt hv)).toLp
        (fun ξ : ℝ => (((ξ : ℝ) : ℂ) - v)⁻¹)) P : ℂ) = 0 := by
      have hkmem := cauchyKernel_mem_hardyL2_orthogonal hv
      exact inner_eq_zero_symm.mp
        (Submodule.mem_orthogonal _ _ |>.mp hkmem P hPmem)
    rw [hG, inner_sub_right, hkF v hv hvne, hkP, sub_zero]
  -- `G` has a datum on the positive ray
  rw [hardyL2_orthogonal] at hGmem
  obtain ⟨d, hd, hdG⟩ := hGmem
  -- the pairing with the kernel is the Laplace transform of that datum
  have hlap : ∀ (v : ℂ), 0 < v.im → v ≠ (starRingEnd ℂ) v₀ →
      laplaceRay (d : ℝ → ℂ) (2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) v) = 0 := by
    intro v hv hvne
    have hval := hkG v hv hvne
    rw [← hdG, ← fourierTransform_cauchyDatumUpper hv] at hval
    simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at hval
    have hiso : (inner ℂ ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
          ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)))
          ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) d) : ℂ)
        = (inner ℂ ((memLp_cauchyDatumUpper hv).toLp (cauchyDatumUpper v)) d : ℂ) :=
      (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map _ _
    rw [hiso, inner_cauchyDatumUpper hv d] at hval
    have hne : (-(2 * (Real.pi : ℂ) * I)) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    exact (mul_eq_zero.mp hval).resolve_left hne
  -- every point of the right half-plane is reached
  have hlap' : ∀ u : ℂ, 0 < u.re → u ≠ 2 * (Real.pi : ℂ) * I * v₀ →
      laplaceRay (d : ℝ → ℂ) u = 0 := by
    intro u hu hune
    have hpi := Real.pi_pos
    have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    set v : ℂ := (starRingEnd ℂ) (u / (2 * (Real.pi : ℂ) * I)) with hv
    have hu' : 2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) v = u := by
      rw [hv, Complex.conj_conj, mul_div_cancel₀ _ hne]
    have hre : u.re = 2 * Real.pi * v.im := by
      rw [← hu']
      simp [Complex.mul_re, Complex.mul_im]
    have hvim : 0 < v.im := by nlinarith
    have hvne : v ≠ (starRingEnd ℂ) v₀ := by
      intro hc
      refine hune ?_
      rw [← hu', hc, Complex.conj_conj]
    rw [← hu']
    exact hlap v hvim hvne
  -- so the datum vanishes
  have hmem2 : MemLp (d : ℝ → ℂ) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (MeasureTheory.Lp.memLp d).restrict _
  have hpos := ae_eq_zero_of_laplaceRay_eq_zero_of_ne hmem2 (2 * (Real.pi : ℂ) * I * v₀) hlap'
  have hpos' : ∀ᵐ x : ℝ, 0 < x → (d : ℝ → ℂ) x = 0 := by
    have hres := (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hpos
    filter_upwards [hres] with x hx hx0
    exact hx (Set.mem_Ioi.mpr hx0)
  have hneg := (mem_halfLineL2_iff d).mp hd
  have hne0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have hzero : (d : ℝ → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hpos', hneg, hne0] with x h1 h2 h3
    rcases lt_or_gt_of_ne h3 with hx | hx
    · exact h2 hx
    · exact h1 hx
  have hd0 : d = 0 :=
    MeasureTheory.Lp.ext (hzero.trans (MeasureTheory.Lp.coeFn_zero ℂ 2 volume).symm)
  have hG0 : G = 0 := by
    rw [← hdG, hd0, map_zero]
  have : F = P := by
    have := hG0
    rw [hG, sub_eq_zero] at this
    exact this
  rw [this]
  exact hPmem


/-- **The Cauchy kernels below the axis are total in the orthogonal complement of the Hardy
space.**  An `L²` boundary function whose Cauchy transform vanishes on the whole lower half-plane
is a Hardy function.  This is the exact converse of `integral_cauchyTransform_eq_zero`. -/
theorem mem_hardyL2_of_cauchyTransform_eq_zero {F : Lp ℂ 2 (volume : Measure ℝ)}
    (h : ∀ w : ℂ, w.im < 0 → (∫ x : ℝ, (F : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    F ∈ hardyL2 :=
  mem_hardyL2_of_cauchyTransform_eq_zero_of_ne 0 fun w hw _ => h w hw


end RHTower
