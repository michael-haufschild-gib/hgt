import GaloisForLFunctions.RHTower.SelbergMaassPositiveRationalTrace

/-!
# Maass trace to rationally conjugated principal groups

A rationally conjugated principal target has positive rational lifts. The
finite trace theorems are therefore direct specializations of the generic
positive-rational trace construction. This gives the analytic trace map used
in double-coset constructions between rational conjugate groups.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open SelbergMaassTraceEnergy
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

variable (N : ℕ) (g : GL (Fin 2) ℚ)
  {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex (rationalConjugateGroup N g)]

/-- Finite trace to a rationally conjugated principal group retains real `C²`
regularity. -/
theorem rationalConjugateMaassTrace_smooth_of_data (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions 𝒢)
    (heigen : IsMaassEigenfunction lam f.1) :
    IsRealSmoothUpperHalfPlane (maassTraceFunction (H := rationalConjugateGroup N g) f) :=
  positiveRationalMaassTrace_smooth_of_data
    (rationalConjugateGroup_hasPositiveRationalLifts N g) lam f heigen

/-- Finite trace to a rationally conjugated principal group retains its Maass
eigen-equation. -/
theorem rationalConjugateMaassTrace_eigen_of_data (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions 𝒢)
    (heigen : IsMaassEigenfunction lam f.1) (z : ℍ) :
    positiveHyperbolicLaplacian (maassTraceFunction (H := rationalConjugateGroup N g) f) z =
      (lam : ℂ) * maassTraceFunction (H := rationalConjugateGroup N g) f z :=
  positiveRationalMaassTrace_eigen_of_data
    (rationalConjugateGroup_hasPositiveRationalLifts N g) lam f heigen z

/-- Finite trace to a rationally conjugated principal group preserves decay at
every integral cusp. -/
theorem rationalConjugateMaassTrace_cuspidal_of_data
    (f : glUpperHalfPlaneInvariantFunctions 𝒢)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    IsCuspidalAtIntegralCusps (maassTraceFunction (H := rationalConjugateGroup N g) f) :=
  positiveRationalMaassTrace_cuspidal_of_data
    (rationalConjugateGroup_hasPositiveRationalLifts N g) f hcusp

/-- Finite trace with exact invariance, Maass equation, and integral-cusp decay
at a rationally conjugated principal target. -/
def rationalConjugateMaassTraceData_of_data (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions 𝒢)
    (heigen : IsMaassEigenfunction lam f.1)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    {F : glUpperHalfPlaneInvariantFunctions (rationalConjugateGroup N g) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} :=
  positiveRationalMaassTraceData_of_data
    (rationalConjugateGroup_hasPositiveRationalLifts N g) lam f heigen hcusp

end

end GaloisForLFunctions.RHTower
