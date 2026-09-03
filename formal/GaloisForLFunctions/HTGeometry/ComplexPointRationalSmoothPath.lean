import GaloisForLFunctions.HTGeometry.ComplexPointRationalFunctionEvaluation
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Rationally smooth paths of complex-valued scheme points

A path of complex-valued points on an integral scheme is rationally smooth when every rational
function represented by a regular germ at every point of the path has a smooth evaluated pullback.
The definition quantifies over the actual function field and actual local germs; it is independent
of a chosen affine presentation or coordinate generators.

This is the global rational-observable part of algebraic analytification.  It does not assert that
the resulting differential-space definition has already been compared with a manifold
analytification.
-/

namespace AlgebraicGeometry

noncomputable section

namespace Scheme.ComplexPointPath

/-- A path of complex-valued points is rationally smooth when every rational function which is
regular at every point of the path has a smooth evaluated pullback.  Quantification over every
regular-germ assignment makes the definition independent of proof-relevant germ choices. -/
def IsRationallySmooth
    (X : Scheme) [IrreducibleSpace X] (point : ℝ → X.ComplexPoint) : Prop :=
  ∀ (f : X.functionField)
    (regular : ∀ t, X.RationalFunctionRegularAtComplexPoint (point t) f),
      ContDiff ℝ ⊤ (fun t => (regular t).value)

/-- Every regular rational observable along a rationally smooth path evaluates smoothly. -/
theorem IsRationallySmooth.contDiff_value
    {X : Scheme} [IrreducibleSpace X] {point : ℝ → X.ComplexPoint}
    (h : IsRationallySmooth X point)
    (f : X.functionField)
    (regular : ∀ t, X.RationalFunctionRegularAtComplexPoint (point t) f) :
    ContDiff ℝ ⊤ (fun t => (regular t).value) :=
  h f regular

end Scheme.ComplexPointPath

end

end AlgebraicGeometry
