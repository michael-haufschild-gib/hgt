import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Positive-even Laplace escape

Pointwise positivity, evenness, and a functional-equation reflection do not force bilateral-Laplace
zeros onto the fixed axis.  Two positive even shells already cancel exactly at `a + πi`.

This module certifies the finite algebraic core of ULF exponential-admission escape mechanics.  The
paper theorem smooths the shells by a positive Gaussian and proves density in the positive even
Schwartz cone.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Bilateral-Laplace response of an even two-shell positive source with shells at `±1` and
`±2`. The coefficients are the positive weights that cancel at `a + πi`. -/
def positiveEvenTwoShellLaplace (a : ℝ) (z : ℂ) : ℂ :=
  (Real.cosh (2 * a) : ℂ) * Complex.cosh z +
    (Real.cosh a : ℂ) * Complex.cosh (2 * z)

/-- Both source weights in `positiveEvenTwoShellLaplace` are strictly positive. -/
theorem positiveEvenTwoShellLaplace_weights_pos (a : ℝ) :
    0 < Real.cosh a ∧ 0 < Real.cosh (2 * a) :=
  ⟨Real.cosh_pos a, Real.cosh_pos (2 * a)⟩

/-- A positive even two-shell source has an exact off-axis bilateral-Laplace zero at `a + πi`.
This is the algebraic core of exponential-admission escape. -/
theorem positiveEvenTwoShellLaplace_offAxis_zero (a : ℝ) :
    positiveEvenTwoShellLaplace a ((a : ℂ) + (Real.pi : ℂ) * I) = 0 := by
  have h1 : Complex.cosh ((a : ℂ) + (Real.pi : ℂ) * I) = -(Real.cosh a : ℂ) := by
    rw [Complex.cosh_add_pi_mul_I, ← Complex.ofReal_cosh]
  have harg : 2 * ((a : ℂ) + (Real.pi : ℂ) * I) =
      ((2 * a : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * I := by
    push_cast
    ring
  have h2 : Complex.cosh (2 * ((a : ℂ) + (Real.pi : ℂ) * I)) =
      (Real.cosh (2 * a) : ℂ) := by
    rw [harg, Complex.cosh_periodic, ← Complex.ofReal_cosh]
  rw [positiveEvenTwoShellLaplace, h1, h2]
  ring

/-- The explicit point `1 + πi` is genuinely off both the real and imaginary axes. -/
theorem positiveEvenTwoShellLaplace_explicit_offAxis :
    positiveEvenTwoShellLaplace 1 ((1 : ℂ) + (Real.pi : ℂ) * I) = 0 :=
  positiveEvenTwoShellLaplace_offAxis_zero 1

end GaloisForLFunctions.HTGeometry
