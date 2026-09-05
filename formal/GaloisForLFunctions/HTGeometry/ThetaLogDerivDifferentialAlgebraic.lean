import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.EllipticGammaStructuralGeneratorSpectrum
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative

/-!
# The theta logarithmic derivative is differentially algebraic

The logarithmic derivative of a theta function is not elliptic: a quasiperiod step changes it by the
constant `-2πi`.  Its derivative is elliptic, though, and differential algebraicity is stable under
integration, so the logarithmic derivative itself satisfies an algebraic differential equation over
the rational coordinate field.

Every jet and every translate of it does too, so the whole family of atoms used to normalize a
mixed-constraint source consists of differentially algebraic germs.

* `differentialAlgebraicOver_ratFunc_thetaLogDerivMero`;
* `differentialAlgebraicOver_ratFunc_differentialJet_thetaLogDerivMero`;
* `differentialAlgebraicOver_ratFunc_addTranslationMeroEquiv_thetaLogDerivMero`,
  and its jets.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-- **The theta logarithmic derivative is differentially algebraic over `ℂ(z)`.**  Its derivative is
elliptic, and differential algebraicity passes to antiderivatives. -/
theorem differentialAlgebraicOver_ratFunc_thetaLogDerivMero (τ : ℂ) (hτ : 0 < τ.im) :
    DifferentialAlgebraicOver (RatFunc ℂ) (thetaLogDerivMero τ hτ) :=
  differentialAlgebraicOver_of_deriv'
    (differentialAlgebraicOver_of_mem_ellipticMeroField (linearIndependent_one_of_im_pos hτ)
      (thetaLogDerivMero_deriv_mem_ellipticMeroField τ hτ))

/-- Differential algebraicity over the rational coordinate field passes to every jet. -/
theorem differentialAlgebraicOver_ratFunc_differentialJet
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) (j : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (differentialJet j x) := by
  induction j with
  | zero => simpa using hx
  | succ k ih =>
      rw [differentialJet_succ]
      exact differentialAlgebraicOver_deriv ih

/-- Every jet of the theta logarithmic derivative is differentially algebraic over `ℂ(z)`. -/
theorem differentialAlgebraicOver_ratFunc_differentialJet_thetaLogDerivMero
    (τ : ℂ) (hτ : 0 < τ.im) (j : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (differentialJet j (thetaLogDerivMero τ hτ)) :=
  differentialAlgebraicOver_ratFunc_differentialJet
    (differentialAlgebraicOver_ratFunc_thetaLogDerivMero τ hτ) j

/-- **Every translate of the theta logarithmic derivative is differentially algebraic over
`ℂ(z)`.** -/
theorem differentialAlgebraicOver_ratFunc_addTranslationMeroEquiv_thetaLogDerivMero
    (q τ : ℂ) (hτ : 0 < τ.im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv q (thetaLogDerivMero τ hτ)) :=
  differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum hτ hτ
    (differentialAlgebraicOver_addTranslationMeroEquiv_thetaLogDerivMero q τ τ τ hτ le_sup_left)

/-- Every jet of every translate of the theta logarithmic derivative is differentially algebraic
over `ℂ(z)`: the whole atom family of the triptic normal form. -/
theorem differentialAlgebraicOver_ratFunc_differentialJet_addTranslationMeroEquiv_thetaLogDerivMero
    (q τ : ℂ) (hτ : 0 < τ.im) (j : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (differentialJet j (addTranslationMeroEquiv q (thetaLogDerivMero τ hτ))) :=
  differentialAlgebraicOver_ratFunc_differentialJet
    (differentialAlgebraicOver_ratFunc_addTranslationMeroEquiv_thetaLogDerivMero q τ hτ) j

end

end GaloisForLFunctions.HTGeometry
