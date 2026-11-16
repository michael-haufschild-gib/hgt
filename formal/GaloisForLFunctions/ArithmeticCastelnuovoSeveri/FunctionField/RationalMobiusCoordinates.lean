import GaloisForLFunctions.HTGeometry.RatFuncMobiusEquiv
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction-ring coordinates for Möbius substitutions

Transport the existing rational-function automorphism to the literal
fraction field of the polynomial ring. This supplies coefficient-field
maps for radical equations presented with `AdjoinRoot`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped nonZeroDivisors
variable {K : Type*} [Field K]

/-- A nondegenerate projective substitution acts on the polynomial fraction field. -/
def fractionRingMobiusEquiv (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    FractionRing K[X] ≃ₐ[K] FractionRing K[X] :=
  ((IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)).restrictScalars K).trans
    ((RatFunc.mobiusEquiv a b c d hdet).trans
      ((IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)).restrictScalars K).symm)

/-- The transported automorphism has the prescribed fractional-linear coordinate. -/
theorem fractionRingMobiusEquiv_coordinate (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    fractionRingMobiusEquiv a b c d hdet (algebraMap K[X] (FractionRing K[X]) X) =
      (algebraMap K (FractionRing K[X]) a * algebraMap K[X] (FractionRing K[X]) X +
        algebraMap K (FractionRing K[X]) b) /
      (algebraMap K (FractionRing K[X]) c * algebraMap K[X] (FractionRing K[X]) X +
        algebraMap K (FractionRing K[X]) d) := by
  let e := IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)
  change e.symm (RatFunc.mobiusEquiv a b c d hdet
    (e (algebraMap K[X] (FractionRing K[X]) X))) = _
  rw [e.commutes, RatFunc.algebraMap_X, RatFunc.mobiusEquiv_X, RatFunc.mobius]
  simp only [map_div₀, map_add, map_mul, ← RatFunc.algebraMap_X, e.symm.commutes,
    (e.symm.restrictScalars K).commutes]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
