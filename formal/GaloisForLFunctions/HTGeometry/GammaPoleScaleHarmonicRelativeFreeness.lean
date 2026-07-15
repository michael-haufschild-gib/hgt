import GaloisForLFunctions.HTGeometry.GammaPoleRelativeLogFreeness

/-!
# Joint relative freeness of the Gamma pole scale and harmonic boundary

The factorially normalized pole germ at `-n` has two kinds of boundary coordinates:

* the reciprocal signed factorial scale, which fixes the transverse size of the pole; and
* the generalized harmonic jets, which determine its regular Taylor deformation.

For descent with coefficients in `ℂ(z)`, absolute freeness over `ℂ` is insufficient: the pole
position `n` is itself available as a rational coefficient.  This file proves the exact relative
statement.  Every finite family consisting of the scale and harmonic boundary coordinates is
algebraically independent over the full rational pole-position field `ℂ(n)`.

The proof does not use asymptotic or numerical estimates.  `MvPolynomial.optionEquivLeft`
identifies a polynomial in the distinguished scale and the harmonic variables with a univariate
polynomial over the harmonic coordinate ring.  Evaluation is then exactly
`reciprocalSignedFactorialEval`, whose injectivity is already known.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaPoleScaleHarmonicNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm :=
  ratNatEval.toAlgebra

/-- The distinguished factorial scale followed by a finite harmonic boundary frame. -/
def gammaPoleScaleAndHarmonicFamily (m : ℕ) : Option (Fin m) → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => harmonicJetGerm (j : ℕ)

/-- Evaluation of a rational-pole-position polynomial on the scale--harmonic frame. -/
def gammaPoleScaleAndHarmonicEval (m : ℕ) :
    MvPolynomial (Option (Fin m)) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval (gammaPoleScaleAndHarmonicFamily m)

/-- Separating the scale coordinate turns joint boundary evaluation into the existing reciprocal
factorial evaluation over the complete harmonic polynomial ring. -/
theorem gammaPoleScaleAndHarmonicEval_eq_comp (m : ℕ) :
    gammaPoleScaleAndHarmonicEval m =
      (reciprocalSignedFactorialEval m).comp
        (MvPolynomial.optionEquivLeft GammaPoleRationalBase (Fin m)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleScaleAndHarmonicEval, reciprocalSignedFactorialEval,
      harmonicJetEval]
  · intro j
    cases j with
    | none =>
        simp [gammaPoleScaleAndHarmonicEval, gammaPoleScaleAndHarmonicFamily,
          reciprocalSignedFactorialEval]
    | some j =>
        simp [gammaPoleScaleAndHarmonicEval, gammaPoleScaleAndHarmonicFamily,
          reciprocalSignedFactorialEval, harmonicJetEval]

theorem gammaPoleScaleAndHarmonicEval_injective (m : ℕ) :
    Function.Injective (gammaPoleScaleAndHarmonicEval m) := by
  rw [gammaPoleScaleAndHarmonicEval_eq_comp]
  exact (reciprocalSignedFactorialEval_injective m).comp
    (MvPolynomial.optionEquivLeft GammaPoleRationalBase (Fin m)).injective

/-- **Relative scale--boundary freeness.**  The reciprocal factorial scale and every finite
harmonic boundary frame are jointly algebraically independent over `ℂ(n)`. -/
theorem algebraicIndependent_gammaPoleScaleAndHarmonicFamily (m : ℕ) :
    AlgebraicIndependent GammaPoleRationalBase
      (gammaPoleScaleAndHarmonicFamily m) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndHarmonicEval, MvPolynomial.aeval_def] using
    gammaPoleScaleAndHarmonicEval_injective m

end

end GaloisForLFunctions
