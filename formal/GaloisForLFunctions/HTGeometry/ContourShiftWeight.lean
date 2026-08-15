import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The shifted-line transform is the transform of the exponentially weighted profile

Moving the frequency contour up by `σ` is the same as weighting the physical profile by `e^{σL}`:

`∫ e^{-i(x+iσ)L} F(L) dL = ∫ e^{-ixL} (e^{σL} F(L)) dL`,

because the exponent splits exactly.  The identity is pointwise in the integrand, so it holds with
no integrability hypothesis at all — both sides are the same integral of the same function.

Consequently a shifted-line `L²` bound *is* an `L²` bound on the weighted profile, by Plancherel:
the two statements `f(·+iσ) ∈ L²` and `e^{σL}F ∈ L²` are the same statement read on the two sides
of the transform, which is the passage from `(24)` to `(25)`.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The physical weight attached to the contour shift. -/
def contourWeight (σ L : ℝ) : ℂ := (Real.exp (σ * L) : ℂ)

/-- **The exponent splits.** -/
theorem exp_shifted_line (σ x L : ℝ) :
    Complex.exp (-Complex.I * ((x : ℂ) + (σ : ℂ) * Complex.I) * (L : ℂ))
      = Complex.exp (-Complex.I * (x : ℂ) * (L : ℂ)) * contourWeight σ L := by
  have hI : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  rw [contourWeight, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (-(σ : ℂ) * (L : ℂ)) * hI

/-- **The shifted-line transform is the transform of the weighted profile.**  No integrability
hypothesis: the integrands are equal pointwise. -/
theorem shiftedLineTransform_eq (F : ℝ → X) (σ x : ℝ) :
    (∫ L : ℝ, Complex.exp (-Complex.I * ((x : ℂ) + (σ : ℂ) * Complex.I) * (L : ℂ)) • F L)
      = ∫ L : ℝ, Complex.exp (-Complex.I * (x : ℂ) * (L : ℂ))
          • (contourWeight σ L • F L) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  simp only [exp_shifted_line, smul_smul]

omit [NormedSpace ℂ X] in
/-- The weight has the expected modulus. -/
theorem norm_contourWeight (σ L : ℝ) : ‖contourWeight σ L‖ = Real.exp (σ * L) := by
  rw [contourWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **The weighted profile has the physical weighted norm.** -/
theorem norm_contourWeight_smul (σ L : ℝ) (v : X) :
    ‖contourWeight σ L • v‖ = Real.exp (σ * L) * ‖v‖ := by
  rw [norm_smul, norm_contourWeight]

end GaloisForLFunctions.HTGeometry
