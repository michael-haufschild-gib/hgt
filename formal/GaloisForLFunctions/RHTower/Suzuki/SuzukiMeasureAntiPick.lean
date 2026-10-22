import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAntiPickIdentity

/-!
# The measure-level anti-Pick property

The finite anti-Pick identity symmetrizes a double sum.  Its measure analogue symmetrizes a double
integral, and that step is already available: splitting the Cauchy kernel into its real and
imaginary parts turns the anti-Pick sign into a monotone-likelihood kernel condition on the product
measure, whose integrated form is the cross-multiplied expectation order.

The split is what makes this work with no complex integration theory.  Writing
`1/(t - z) = u + i v` with `u = (t - Re z)/|t - z|^(2 : ℕ)` and `v = Im z/|t - z|^(2 : ℕ)`, the two-sample kernel
`v(x) u(y) - v(y) u(x)` collapses to `Im z (t y - t x)/(|t x - z|^(2 : ℕ) |t y - z|^(2 : ℕ))`: the shift `Re z`
cancels, leaving exactly the node increment that monotone likelihood signs.
-/

open MeasureTheory

namespace RHTower

variable {α : Type*}

/-- The real part of the Cauchy kernel. -/
noncomputable def cauchyKernelRe (t : α → ℝ) (z : ℂ) (x : α) : ℝ :=
  (t x - z.re) / Complex.normSq ((t x : ℂ) - z)

/-- The imaginary part of the Cauchy kernel. -/
noncomputable def cauchyKernelIm (t : α → ℝ) (z : ℂ) (x : α) : ℝ :=
  z.im / Complex.normSq ((t x : ℂ) - z)

/-- The real part of a weighted Cauchy term. -/
theorem re_cauchyTerm (w τ : ℝ) (z : ℂ) :
    ((w : ℂ) / ((τ : ℂ) - z)).re = w * ((τ - z.re) / Complex.normSq ((τ : ℂ) - z)) := by
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply]
  ring

theorem re_cauchyTerm_eq (t : α → ℝ) (w : ℝ) (z : ℂ) (x : α) :
    ((w : ℂ) / ((t x : ℂ) - z)).re = w * cauchyKernelRe t z x :=
  re_cauchyTerm w (t x) z

theorem im_cauchyTerm_eq (t : α → ℝ) (w : ℝ) (z : ℂ) (x : α) :
    ((w : ℂ) / ((t x : ℂ) - z)).im = w * cauchyKernelIm t z x := by
  rw [im_cauchyTerm, cauchyKernelIm, mul_div_assoc]

theorem re_cauchyTermOne (t : α → ℝ) (z : ℂ) (x : α) :
    ((1 : ℂ) / ((t x : ℂ) - z)).re = cauchyKernelRe t z x := by
  have h := re_cauchyTerm 1 (t x) z
  rw [Complex.ofReal_one, one_mul] at h
  rw [h, cauchyKernelRe]

theorem im_cauchyTermOne (t : α → ℝ) (z : ℂ) (x : α) :
    ((1 : ℂ) / ((t x : ℂ) - z)).im = cauchyKernelIm t z x := by
  have h := im_cauchyTerm 1 (t x) z
  rw [Complex.ofReal_one, one_mul] at h
  rw [h, cauchyKernelIm]

/-- **The two-sample kernel collapses.**  In the difference `v(x) u(y) - v(y) u(x)` the real part of
the spectral parameter cancels, leaving the node increment scaled by `Im z` over the two squared
denominators.  This is the measure-level shadow of the antisymmetric factor in `(1)`. -/
theorem cauchyKernel_cross_eq (t : α → ℝ) (z : ℂ) (x y : α) :
    cauchyKernelIm t z x * cauchyKernelRe t z y - cauchyKernelIm t z y * cauchyKernelRe t z x
      = z.im * (t y - t x) /
          (Complex.normSq ((t x : ℂ) - z) * Complex.normSq ((t y : ℂ) - z)) := by
  simp only [cauchyKernelRe, cauchyKernelIm]
  rcases eq_or_ne (Complex.normSq ((t x : ℂ) - z)) 0 with hx | hx
  · rw [hx]; simp
  · rcases eq_or_ne (Complex.normSq ((t y : ℂ) - z)) 0 with hy | hy
    · rw [hy]; simp
    · field_simp
      ring

/-- **The kernel condition.**  Above the real axis, monotone likelihood is exactly the sign the
integrated monotone-likelihood theorem consumes. -/
theorem monotoneLikelihood_cauchyKernel {t r : α → ℝ} {z : ℂ} (hz : 0 < z.im) (x y : α)
    (h : 0 ≤ (r x - r y) * (t x - t y)) :
    0 ≤ (r y - r x) *
      (cauchyKernelIm t z x * cauchyKernelRe t z y - cauchyKernelIm t z y * cauchyKernelRe t z x) := by
  rw [cauchyKernel_cross_eq]
  have hsym : (r y - r x) * (z.im * (t y - t x) /
      (Complex.normSq ((t x : ℂ) - z) * Complex.normSq ((t y : ℂ) - z)))
      = z.im * ((r x - r y) * (t x - t y)) /
        (Complex.normSq ((t x : ℂ) - z) * Complex.normSq ((t y : ℂ) - z)) := by
    rw [mul_div_assoc']
    congr 1
    ring
  rw [hsym]
  exact div_nonneg (mul_nonneg hz.le h)
    (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

variable [MeasurableSpace α] {μ : Measure α}

/-- **The measure-level cross-Wronskian order.**  Symmetrizing the double integral turns monotone
likelihood into the cross-multiplied expectation order between the two parts of the kernel. -/
theorem integral_cauchyKernel_crossWronskian_le [SFinite μ] {t r : α → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hu : Integrable (cauchyKernelRe t z) μ)
    (hv : Integrable (cauchyKernelIm t z) μ)
    (hru : Integrable (fun x => r x * cauchyKernelRe t z x) μ)
    (hrv : Integrable (fun x => r x * cauchyKernelIm t z x) μ)
    (hmono : ∀ᵐ p : α × α ∂μ.prod μ, 0 ≤ (r p.1 - r p.2) * (t p.1 - t p.2)) :
    (∫ x, r x * cauchyKernelIm t z x ∂μ) * (∫ x, cauchyKernelRe t z x ∂μ)
      ≤ (∫ x, r x * cauchyKernelRe t z x ∂μ) * (∫ x, cauchyKernelIm t z x ∂μ) := by
  refine HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel hu hv hru hrv ?_
  filter_upwards [hmono] with p hp
  exact monotoneLikelihood_cauchyKernel hz p.1 p.2 hp

/-- **The imaginary part of the numerator against the conjugate denominator**, in measure form:
splitting both transforms into real and imaginary parts expresses it by four real integrals. -/
theorem im_measureNumerator_mul_conj_denominator {t r : α → ℝ} {z : ℂ}
    (hN : Integrable (fun x => ((r x : ℝ) : ℂ) / ((t x : ℂ) - z)) μ)
    (hD : Integrable (fun x => (1 : ℂ) / ((t x : ℂ) - z)) μ) :
    ((∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ) *
        (starRingEnd ℂ) (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ)).im
      = (∫ x, r x * cauchyKernelIm t z x ∂μ) * (∫ x, cauchyKernelRe t z x ∂μ)
        - (∫ x, r x * cauchyKernelRe t z x ∂μ) * (∫ x, cauchyKernelIm t z x ∂μ) := by
  have hNre : (∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ).re
      = ∫ x, r x * cauchyKernelRe t z x ∂μ := by
    rw [show (∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ).re
        = ∫ x, (((r x : ℝ) : ℂ) / ((t x : ℂ) - z)).re ∂μ from by
      simpa using (Complex.reCLM.integral_comp_comm hN).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => re_cauchyTerm_eq t (r x) z x)
  have hNim : (∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ).im
      = ∫ x, r x * cauchyKernelIm t z x ∂μ := by
    rw [show (∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ).im
        = ∫ x, (((r x : ℝ) : ℂ) / ((t x : ℂ) - z)).im ∂μ from by
      simpa using (Complex.imCLM.integral_comp_comm hN).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => im_cauchyTerm_eq t (r x) z x)
  have hDre : (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ).re
      = ∫ x, cauchyKernelRe t z x ∂μ := by
    rw [show (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ).re
        = ∫ x, ((1 : ℂ) / ((t x : ℂ) - z)).re ∂μ from by
      simpa using (Complex.reCLM.integral_comp_comm hD).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => re_cauchyTermOne t z x)
  have hDim : (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ).im
      = ∫ x, cauchyKernelIm t z x ∂μ := by
    rw [show (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ).im
        = ∫ x, ((1 : ℂ) / ((t x : ℂ) - z)).im ∂μ from by
      simpa using (Complex.imCLM.integral_comp_comm hD).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => im_cauchyTermOne t z x)
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hNre, hNim, hDre, hDim]
  ring

/-- **Theorem B's anti-Pick property.**  For a positive base measure with monotone response, the
ratio of the two Cauchy transforms is anti-Herglotz above the real axis — the measure analogue of
Theorem A, with the same symmetrization carried out on the product measure. -/
theorem im_measureShiftRatio_nonpos [SFinite μ] {t r : α → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hN : Integrable (fun x => ((r x : ℝ) : ℂ) / ((t x : ℂ) - z)) μ)
    (hD : Integrable (fun x => (1 : ℂ) / ((t x : ℂ) - z)) μ)
    (hu : Integrable (cauchyKernelRe t z) μ)
    (hv : Integrable (cauchyKernelIm t z) μ)
    (hru : Integrable (fun x => r x * cauchyKernelRe t z x) μ)
    (hrv : Integrable (fun x => r x * cauchyKernelIm t z x) μ)
    (hmono : ∀ᵐ p : α × α ∂μ.prod μ, 0 ≤ (r p.1 - r p.2) * (t p.1 - t p.2)) :
    ((∫ x, ((r x : ℝ) : ℂ) / ((t x : ℂ) - z) ∂μ) /
        (∫ x, (1 : ℂ) / ((t x : ℂ) - z) ∂μ)).im ≤ 0 := by
  refine im_ratio_nonpos_of_im_mul_conj_nonpos ?_
  rw [im_measureNumerator_mul_conj_denominator hN hD, sub_nonpos]
  exact integral_cauchyKernel_crossWronskian_le hz hu hv hru hrv hmono

end RHTower
