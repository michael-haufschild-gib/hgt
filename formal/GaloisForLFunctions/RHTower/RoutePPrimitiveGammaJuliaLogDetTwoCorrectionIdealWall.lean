import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogFullWeakTraceNoGo
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.HTGeometry.OperatorDeterminantSufficiency

/-!
# Forced det₂ correction ideal for full Route-P transport to Xi

For arbitrary bounded left/right mixing of the full all-depth Route-P carrier,
the exact additive correction to the ordered reciprocal-Xi operator lies in
Schatten class two but outside weak Schatten-one.  Thus an additive
irregular-RH weld cannot use an ordinary Fredholm or weak-trace counterterm:
its correction is genuinely Hilbert--Schmidt and requires genus-one
regularization.
-/

open scoped BigOperators InnerProductSpace
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

/-- Additive correction required to relocate a bounded full Route-P channel to Xi. -/
def routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  xiOrderedSignedPrimeOperator -
    (A ∘L routePPrimitiveGammaJuliaLogBalancedOperator ∘L C)

/-- Every exact additive Route-P-to-Xi correction is Schatten-two. -/
theorem routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_memSchattenClass_two
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    MemSchattenClass 2
      (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection A C) := by
  have hsourceTwo : MemSchattenClass 2
      (A ∘L routePPrimitiveGammaJuliaLogBalancedOperator ∘L C) :=
    (routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_memWeakSchattenClass_one A C).memSchattenClass_of_lt
      (by norm_num) (by norm_num)
  simpa only [routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection,
      sub_eq_add_neg] using
    GaloisForLFunctions.HTGeometry.memSchattenClass_add (by norm_num)
      xiOrderedSignedPrimeOperator_memSchattenClass_two
      (GaloisForLFunctions.HTGeometry.memSchattenClass_neg hsourceTwo)

/-- The forced correction is genuinely Hilbert--Schmidt. -/
theorem routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_isHilbertSchmidt
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection A C).IsHilbertSchmidt := by
  exact (memSchattenClass_two_iff_isHilbertSchmidt _).mp
    (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_memSchattenClass_two A C)

/-- The forced Hilbert--Schmidt correction cannot lie in weak Schatten-one. -/
theorem routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_not_memWeakSchattenClass_one
    (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RouteKSignedPrimeHilbert)
    (C : RouteKSignedPrimeHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert) :
    ¬ MemWeakSchattenClass 1
      (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection A C) := by
  intro hcorrection
  have hsum :=
    (routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_memWeakSchattenClass_one A C).one_add
      hcorrection
  apply xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one
  simpa [routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection] using hsum

/-- Exact ideal wall for additive irregular-RH transport from full Route P to Xi. -/
theorem routePPrimitive_GammaJulia_logPrimeHarmonic_detTwoCorrectionIdealWall :
    ∀ (A : RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
        RouteKSignedPrimeHilbert)
      (C : RouteKSignedPrimeHilbert →L[ℂ]
        RoutePPrimitiveGammaJuliaLogBalancedHilbert),
      MemSchattenClass 2
          (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection A C) ∧
        ¬ MemWeakSchattenClass 1
          (routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection A C) := by
  exact fun A C =>
    ⟨routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_memSchattenClass_two A C,
      routePPrimitiveGammaJuliaLogBalancedDetTwoCorrection_not_memWeakSchattenClass_one A C⟩

end

end RHTower
