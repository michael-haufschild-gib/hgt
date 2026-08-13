import GaloisForLFunctions.HTGeometry.LeafCauchyTransform
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge

/-!
# The Cauchy transform maps the upper half plane to itself

The Cauchy kernel has imaginary part `Im z / |x − z|²` at every real `x`, so integrating it against a
probability measure gives a value with strictly positive imaginary part.  This is the Herglotz
positivity the whole Nevanlinna layer rests on, and it is not recorded anywhere in the corpus.

Applied to an analytic carrier family it constrains the Möbius data directly: the transform of the
leaf at `∞` is `a/c`, so `a` cannot vanish where `c` does not; and the transform of the leaf at a
real `τ` is `(aτ + b)/(cτ + d)`, so that value lies in the open upper half plane and in particular
the denominator `cτ + d` never vanishes above the real axis.

* **`im_cauchyTransform_pos`** — the Herglotz positivity;
* **`im_infinityCauchy_pos`**, `a_ne_zero_of_c_ne_zero`;
* **`im_finiteCauchy_pos`**, **`mobiusDenominator_ne_zero`**.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-! ### Herglotz positivity -/

/-- **The Cauchy transform of a probability measure lies in the open upper half plane.**  The kernel
has imaginary part `Im z / |x − z|²`, positive at every real point. -/
theorem im_cauchyTransform_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ} (hz : 0 < z.im) :
    0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  have hzne : z.im ≠ 0 := ne_of_gt hz
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ :=
    _root_.HTGeometry.integrable_cauchy_kernel μ hzne
  have hpos : ∀ x : ℝ, 0 < (((x : ℂ) - z)⁻¹).im := by
    intro x
    have h1 : ((x : ℂ) - z).im = -z.im := by simp
    have hne : ((x : ℂ) - z) ≠ 0 := by
      intro hc
      rw [hc] at h1
      simp only [Complex.zero_im] at h1
      exact hzne (by linarith)
    have hns : 0 < Complex.normSq ((x : ℂ) - z) := Complex.normSq_pos.mpr hne
    rw [Complex.inv_im, h1, neg_neg]
    exact div_pos hz hns
  have hcomm : (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im = ∫ x, (((x : ℂ) - z)⁻¹).im ∂μ :=
    (Complex.imCLM.integral_comp_comm hint).symm
  rw [hcomm, integral_pos_iff_support_of_nonneg (fun x => le_of_lt (hpos x)) hint.im]
  have hsupp : (Function.support fun x : ℝ => (((x : ℂ) - z)⁻¹).im) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos x)
  rw [hsupp, measure_univ]
  norm_num

/-! ### Constraints on an analytic carrier family -/

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The projective quotient `a/c` lies in the open upper half plane: it is the Cauchy transform of
the leaf at infinity. -/
theorem im_infinityCauchy_pos {z : ℂ} (hz : 0 < z.im) (hc : F.c z ≠ 0) :
    0 < (F.a z / F.c z).im := by
  rw [← F.infinity_cauchy z hz.ne' hc]
  exact im_cauchyTransform_pos _ hz

/-- **`a` cannot vanish where `c` does not.**  A zero of `a` would make the leaf transform at
infinity vanish, but a Cauchy transform has positive imaginary part. -/
theorem a_ne_zero_of_c_ne_zero {z : ℂ} (hz : 0 < z.im) (hc : F.c z ≠ 0) : F.a z ≠ 0 := by
  intro ha
  have h := im_infinityCauchy_pos F hz hc
  rw [ha, zero_div] at h
  simp at h

/-- The Möbius value at a real parameter lies in the open upper half plane: it is the Cauchy
transform of the leaf at that parameter. -/
theorem im_finiteCauchy_pos (tau : ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < ((F.a z * tau + F.b z) / (F.c z * tau + F.d z)).im := by
  rw [← F.finite_cauchy tau z hz.ne']
  exact im_cauchyTransform_pos _ hz

/-- **The Möbius denominator never vanishes above the real axis.**  If it did, the leaf transform at
that parameter would be zero, contradicting Herglotz positivity. -/
theorem mobiusDenominator_ne_zero (tau : ℝ) {z : ℂ} (hz : 0 < z.im) :
    F.c z * tau + F.d z ≠ 0 := by
  intro hden
  have h := im_finiteCauchy_pos F tau hz
  rw [hden, div_zero] at h
  simp at h

end GaloisForLFunctions.HTGeometry
