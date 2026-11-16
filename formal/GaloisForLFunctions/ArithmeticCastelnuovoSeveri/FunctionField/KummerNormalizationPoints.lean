import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizationConstantBaseChange
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialPrimePoints

/-!
# Extension points of a fixed Kummer normalization

Separable constant extension commutes with normalization. Tensor adjunction
then identifies algebra points of the extended normalization with maps from
the original normalization into the extended constant field. Rational prime
ideals of the extended normalization therefore count those same maps.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct
variable (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (c : Kˣ) (b R n : ℕ)
local notation "L" => KummerBranchField c b R n
local notation "LE" => KummerBranchField (Units.map (RingHom.toMonoidHom (algebraMap K E)) c) b R n
local notation "B" => integralClosure K[X] L
local notation "BE" => integralClosure E[X] LE

/-- Points of the extended normalization are exactly maps from the original normalization into the enlarged constants. -/
def kummerNormalizationExtensionPointEquiv : (BE →ₐ[E] E) ≃ (B →ₐ[K] E) :=
  ((kummerNormalizationConstantTensorEquiv K E c b R n).symm.arrowCongr
    (AlgEquiv.refl : E ≃ₐ[E] E)).trans (AlgHom.liftEquiv K E B E).symm

/-- Rational primes after constant extension are exactly algebra points of the original normalization over that extension. -/
def kummerNormalizationExtensionPrimeEquiv : RationalPolynomialPrimes E BE ≃ (B →ₐ[K] E) :=
  (rationalPolynomialPointEquiv E BE).symm.trans
    (kummerNormalizationExtensionPointEquiv K E c b R n)

/-- The rational prime count after constant extension counts maps from one fixed normalization ring. -/
theorem kummerNormalizationExtensionPrimes_card :
    Nat.card (RationalPolynomialPrimes E BE) = Nat.card (B →ₐ[K] E) :=
  Nat.card_congr (kummerNormalizationExtensionPrimeEquiv K E c b R n)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
