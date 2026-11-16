import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusDicksonQuotientDegree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalCoordinateRelativeDegree

/-!
# The Dickson quotient inside an ambient function field

Transport the rational quotient degree through realization at any
transcendental coordinate. The resulting index concerns actual
intermediate fields of the ambient extension.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The Dickson quotient has its exact relative degree inside every transcendental coordinate field. -/
theorem frobeniusDicksonCoordinate_relfinrank {x : L} (hx : Transcendental K x)
    (q : ℕ) (hq : 2 ≤ q) (c : Kˣ) :
    K⟮algebraMap K L c * (1 + (x ^ q - x) ^ (q - 1)) ^ (q + 1) /
      (x ^ q - x) ^ (q * (q - 1))⟯.relfinrank K⟮x⟯ = q * (q ^ 2 - 1) := by
  let P : K[X] := C (c : K) * (frobeniusDicksonPolynomial q) ^ (q + 1)
  let Q : K[X] := (frobeniusAdditivePolynomial q) ^ (q * (q - 1))
  let f : RatFunc K := algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q
  let φ : RatFunc K →ₐ[K] L := K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom
  have hvalue : ((RatFunc.algEquivOfTranscendental x hx) f : L) =
      algebraMap K L c * (1 + (x ^ q - x) ^ (q - 1)) ^ (q + 1) /
        (x ^ q - x) ^ (q * (q - 1)) := by
    change φ (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) = _
    rw [map_div₀]
    change ((RatFunc.algEquivOfTranscendental x hx) (algebraMap K[X] (RatFunc K) P) : L) /
      ((RatFunc.algEquivOfTranscendental x hx) (algebraMap K[X] (RatFunc K) Q) : L) = _
    rw [rationalCoordinate_polynomial, rationalCoordinate_polynomial]
    simp only [P, Q, frobeniusDicksonPolynomial, frobeniusAdditivePolynomial,
      map_mul, map_pow, map_add, map_sub, map_one, aeval_C, aeval_X]
  have h := rationalCoordinate_relfinrank hx f
  rw [hvalue] at h
  exact h.trans (frobeniusDicksonQuotient_finrank q hq c)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
