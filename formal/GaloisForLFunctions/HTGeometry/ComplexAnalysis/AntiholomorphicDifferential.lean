import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CompensatedSlices
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The antiholomorphic differential on a complex normed space

The projection `A ↦ (A + i A ∘ i)/2` extracts the conjugate-linear part of a real-linear
functional. Its evaluation on a direction agrees with the antiholomorphic coefficient on
that complex line. Applied to the real Fréchet derivative, it defines `∂̄` independently of
coordinates and obeys the holomorphic multiplier rule.
-/

open Complex
open scoped InnerProductSpace

noncomputable section
namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Antiholomorphic part of a real-linear complex-valued functional. -/
def antiholomorphicPart (A : E →L[ℝ] ℂ) : E →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (A + Complex.I • A.comp
    ((Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ))

theorem antiholomorphicPart_apply (A : E →L[ℝ] ℂ) (v : E) :
    antiholomorphicPart A v = (A v + Complex.I * A (Complex.I • v)) / 2 := by
  change (2⁻¹ : ℂ) * (A v + Complex.I * A (Complex.I • v)) = _
  ring

/-- Evaluation of the antiholomorphic part is the antiholomorphic complex-line coefficient. -/
theorem antiholomorphicPart_eq_slice (A : E →L[ℝ] ℂ) (v : E) :
    antiholomorphicPart A v = wirtingerAntihol (realLinearSlice A v) := by
  rw [antiholomorphicPart_apply, wirtingerAntihol]
  simp only [realLinearSlice_apply, one_smul]

theorem antiholomorphicPart_add (A B : E →L[ℝ] ℂ) :
    antiholomorphicPart (A + B) = antiholomorphicPart A + antiholomorphicPart B := by
  ext v
  simp only [antiholomorphicPart_apply, add_apply]
  ring

theorem antiholomorphicPart_smul (c : ℂ) (A : E →L[ℝ] ℂ) :
    antiholomorphicPart (c • A) = c • antiholomorphicPart A := by
  ext v
  simp only [antiholomorphicPart_apply, smul_apply, smul_eq_mul]
  ring

/-- A complex-linear differential has no antiholomorphic part. -/
theorem antiholomorphicPart_restrictScalars (A : E →L[ℂ] ℂ) :
    antiholomorphicPart (A.restrictScalars ℝ) = 0 := by
  ext v
  rw [antiholomorphicPart_apply]
  change (A v + Complex.I * A (Complex.I • v)) / 2 = 0
  rw [map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

/-- Coordinate-free antiholomorphic differential, viewed as a real continuous linear map. -/
def dbarDifferential (f : E → ℂ) (x : E) : E →L[ℝ] ℂ :=
  antiholomorphicPart (fderiv ℝ f x)

/-- The differential's value on a direction equals the `∂̄` coefficient of that line. -/
theorem dbarDifferential_apply (f : E → ℂ) (x v : E) :
    dbarDifferential f x v = wirtingerAntihol (realLinearSlice (fderiv ℝ f x) v) :=
  antiholomorphicPart_eq_slice _ _

/-- The antiholomorphic differential obeys the Leibniz rule. -/
theorem dbarDifferential_mul {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbarDifferential (fun y => f y * g y) x =
      f x • dbarDifferential g x + g x • dbarDifferential f x := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [dbarDifferential, h.fderiv, antiholomorphicPart_add,
    antiholomorphicPart_smul, antiholomorphicPart_smul]
  rfl

/-- Holomorphic functions have zero antiholomorphic differential. -/
theorem dbarDifferential_eq_zero {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℂ f x) : dbarDifferential f x = 0 := by
  rw [dbarDifferential, (hf.hasFDerivAt.restrictScalars ℝ).fderiv,
    antiholomorphicPart_restrictScalars]

/-- Multiplication by a holomorphic function commutes with the antiholomorphic differential. -/
theorem dbarDifferential_holomorphic_mul {h f : E → ℂ} {x : E}
    (hh : DifferentiableAt ℂ h x) (hf : DifferentiableAt ℝ f x) :
    dbarDifferential (fun y => h y * f y) x = h x • dbarDifferential f x := by
  rw [dbarDifferential_mul (hh.restrictScalars ℝ) hf,
    dbarDifferential_eq_zero hh, smul_zero, add_zero]

end HTGeometry
