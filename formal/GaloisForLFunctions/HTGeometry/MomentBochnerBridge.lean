import GaloisForLFunctions.HTGeometry.GaussMomentConvergence

/-!
# From lower integrals to Bochner integrals

The weak-limit machinery produces bounds on `∫⁻ ENNReal.ofReal (x^{2k})`, while the moment
convergence theorem consumes Bochner integrals.  For a nonnegative measurable integrand the two are
linked by `hasFiniteIntegral_iff_ofReal` and `integral_eq_lintegral_of_nonneg_ae`.

Integrability of the *odd* powers then follows by domination: `|x|ᵏ ≤ 1 + x^{2k}` pointwise, because
`t ≤ 1 + t²` for every real `t`.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A nonnegative measurable function with finite lower integral is integrable. -/
theorem integrable_of_lintegral_ofReal_lt_top {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlt : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  exact hlt

/-- A bound on the lower integral bounds the Bochner integral. -/
theorem integral_le_toReal_of_lintegral_le {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x) {C : ENNReal} (hCtop : C ≠ ⊤)
    (hC : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ C) :
    ∫ x, f x ∂μ ≤ C.toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hCtop hC

/-- `|x|ᵏ ≤ 1 + x^{2k}`, since `t ≤ 1 + t²` for every real `t`. -/
theorem abs_pow_le_one_add_even (k : ℕ) (x : ℝ) : |x ^ k| ≤ 1 + x ^ (2 * k) := by
  have h1 : |x ^ k| = |x| ^ k := abs_pow x k
  have h2 : x ^ (2 * k) = (|x| ^ k) ^ 2 := by
    rw [mul_comm, pow_mul, ← abs_pow, sq_abs]
  rw [h1, h2]
  nlinarith [pow_nonneg (abs_nonneg x) k]

/-- Integrability of `xᵏ` follows from that of `x^{2k}` against a finite measure. -/
theorem integrable_pow_of_integrable_even {μ : Measure ℝ} [IsFiniteMeasure μ] (k : ℕ)
    (h2 : Integrable (fun x : ℝ => x ^ (2 * k)) μ) :
    Integrable (fun x : ℝ => x ^ k) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h2)
    (measurable_id.pow_const k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_pow_le_one_add_even k x

/-- A truncated power is integrable against any finite measure. -/
theorem integrable_truncPow {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ} (hR : 0 < R) (k : ℕ) :
    Integrable (truncPow R k) μ := by
  refine Integrable.mono' (integrable_const (R ^ k))
    (continuous_truncPow R k).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_truncPow_le hR.le k x

/-- Even moments of a positive moment form are strictly positive. -/
theorem moment_even_pos (h : PositiveMomentForm s) (k : ℕ) : 0 < s (2 * k) := by
  have hpow : (Polynomial.X : Polynomial ℝ) ^ k * Polynomial.X ^ k
      = Polynomial.X ^ (2 * k) := by
    rw [← pow_add, two_mul]
  have hX : momentInner s (Polynomial.X ^ k) (Polynomial.X ^ k) = s (2 * k) := by
    rw [momentInner_def, hpow, momentFunctional_X_pow]
  rw [← hX]
  exact h.pos_of_ne_zero _ (pow_ne_zero k Polynomial.X_ne_zero)

end HTGeometry
