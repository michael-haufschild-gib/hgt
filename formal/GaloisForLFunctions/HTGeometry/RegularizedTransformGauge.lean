import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# The regularized transform inherits hypertranscendence from its Cauchy transform

The regularized Herglotz transform is a polynomial affine gauge of a Cauchy transform: the
Nevanlinna subtraction turns it into `z` times the weighted mass plus `1 + z ^ (2 : ℕ)` times the Cauchy
transform of the weighted measure.  Both corrections are polynomial, and the multiplier `1 + z ^ (2 : ℕ)`
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
theorem one_add_X_sq_ne_zero : (1 + Polynomial.X ^ (2 : ℕ) : Polynomial ℂ) ≠ 0 := by
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
    (1 + Polynomial.X ^ (2 : ℕ))
    (Polynomial.C (((nevanlinnaWeightedMeasure μ u).real Set.univ : ℝ) : ℂ) * Polynomial.X)
    one_add_X_sq_ne_zero ?_ (fun z hz => contDiffAt_cauchyTransform _ hz) hC
  intro z hz
  rw [regularizedHerglotzTransform_eq μ u hu hz, cauchyTransform]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_pow]
  ring

/-- A differential relation on a set restricts to any subset. -/
theorem differentiallyAlgebraicOn_mono {f : ℂ → ℂ} {U V : Set ℂ} (hVU : V ⊆ U)
    (h : DifferentiallyAlgebraicOn f U) : DifferentiallyAlgebraicOn f V := by
  obtain ⟨n, P, hP, hrel⟩ := h
  exact ⟨n, P, hP, fun z hz => hrel z (hVU hz)⟩

/-- The upper half-plane, where the packet arguments place their nodes, avoids the real axis. -/
theorem upperHalfPlane_subset_offRealAxis : upperHalfPlane ⊆ offRealAxis :=
  fun _ hz => ne_of_gt hz

/-- **The Herglotz presentation of any finite carrier inherits relation-freeness.**  For a finite
measure and any mass constant, the normalized presentation `z * M + (1 + z ^ (2 : ℕ)) * C` satisfies no
algebraic differential equation on an open set off the real axis whenever its Cauchy transform `C`
satisfies none there.  This is the gauge with no reference to how the measure was produced. -/
theorem not_differentiallyAlgebraicOn_herglotzPresentation
    (ν : Measure ℝ) [IsFiniteMeasure ν] (M : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hUne : ∀ z ∈ U, z.im ≠ 0)
    (hC : ¬ DifferentiallyAlgebraicOn (cauchyTransform ν) U) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => z * M + (1 + z ^ (2 : ℕ)) * cauchyTransform ν z) U := by
  refine not_differentiallyAlgebraicOn_polynomialGauge hU
    (1 + Polynomial.X ^ (2 : ℕ)) (Polynomial.C M * Polynomial.X)
    one_add_X_sq_ne_zero ?_ (fun z hz => contDiffAt_cauchyTransform ν (hUne z hz)) hC
  intro z _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_pow]
  ring

/-- **The half-plane form composes.**  Relation-freeness of the Cauchy transform on the upper
half-plane — the form the packet arguments produce — already gives it for the Herglotz presentation
there. -/
theorem not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane
    (ν : Measure ℝ) [IsFiniteMeasure ν] (M : ℂ)
    (hC : ¬ DifferentiallyAlgebraicOn (cauchyTransform ν) upperHalfPlane) :
    ¬ DifferentiallyAlgebraicOn
      (fun z => z * M + (1 + z ^ (2 : ℕ)) * cauchyTransform ν z) upperHalfPlane :=
  not_differentiallyAlgebraicOn_herglotzPresentation ν M isOpen_upperHalfPlane
    (fun _ hz => ne_of_gt hz) hC

end

end GaloisForLFunctions.HTGeometry
