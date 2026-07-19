import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# The regularized transform inherits hypertranscendence from its Cauchy transform

The regularized Herglotz transform is a polynomial affine gauge of a Cauchy transform: the
Nevanlinna subtraction turns it into `z` times the weighted mass plus `1 + z ^ 2` times the Cauchy
transform of the weighted measure.  Both corrections are polynomial, and the multiplier `1 + z ^ 2`
is not the zero polynomial, so the gauge carries no differential relation across.

The statement is on the complement of the real axis, which is where the Cauchy transform is
analytic and where the gauge identity holds.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

/-- The complement of the real axis, where a Cauchy transform is analytic. -/
def offRealAxis : Set ℂ := {z : ℂ | z.im ≠ 0}

@[simp]
theorem mem_offRealAxis {z : ℂ} : z ∈ offRealAxis ↔ z.im ≠ 0 := Iff.rfl

theorem isOpen_offRealAxis : IsOpen offRealAxis :=
  isOpen_ne.preimage Complex.continuous_im

/-- The Nevanlinna multiplier is not the zero polynomial. -/
theorem one_add_X_sq_ne_zero : (1 + Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp at h0

/-- The Cauchy transform of a finite measure is smooth off the real axis. -/
theorem contDiffAt_cauchyTransform (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ}
    (hz : z.im ≠ 0) : ContDiffAt ℂ (⊤ : ℕ∞) (cauchyTransform ν) z :=
  (analyticOnNhd_cauchyTransform ν isOpen_offRealAxis (fun _ hw => hw) z hz).contDiffAt

/-- **The regularized Herglotz transform inherits hypertranscendence from its Cauchy transform.**
Off the real axis, if the Cauchy transform of the Nevanlinna-weighted measure satisfies no
algebraic differential equation, neither does the regularized transform. -/
theorem not_differentiallyAlgebraicOn_regularizedHerglotzTransform
    (μ : Measure ℝ) (u : ℝ → ℝ) (hu : Measurable u)
    [IsFiniteMeasure (nevanlinnaWeightedMeasure μ u)]
    (hC : ¬ DifferentiallyAlgebraicOn
      (cauchyTransform (nevanlinnaWeightedMeasure μ u)) offRealAxis) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => ∫ t, regularizedHerglotzKernel t z * (Real.exp (u t) : ℂ) ∂μ) offRealAxis := by
  refine not_differentiallyAlgebraicOn_polynomialGauge isOpen_offRealAxis
    (1 + Polynomial.X ^ 2)
    (Polynomial.C (((nevanlinnaWeightedMeasure μ u).real Set.univ : ℝ) : ℂ) * Polynomial.X)
    one_add_X_sq_ne_zero ?_ (fun z hz => contDiffAt_cauchyTransform _ hz) hC
  intro z hz
  rw [regularizedHerglotzTransform_eq μ u hu hz, cauchyTransform]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_pow]
  ring

end

end GaloisForLFunctions.HTGeometry
