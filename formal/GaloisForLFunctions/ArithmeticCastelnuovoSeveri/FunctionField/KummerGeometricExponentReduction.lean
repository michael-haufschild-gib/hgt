import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExponentReduction
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentParity

/-!
# Two function fields behind geometric-sum branch exponents

For covering degree `q+1`, geometric-sum branch exponents reduce to zero
or one according to the parity of their length. These are explicit
isomorphisms of function fields over the rational base, valid over any field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K]

/-- Every even geometric-sum branch exponent gives the exponent-zero function field. -/
def kummerGeometricExponentEvenEquiv (c : Kˣ) (b q n : ℕ) :
    KummerBranchField c b (kummerExponent q (2 * n)) q ≃ₐ[FractionRing K[X]]
      KummerBranchField c b 0 q :=
  (kummerExponentReductionEquiv c b (kummerExponent q (2 * n)) q).trans
    (kummerExponentCongrEquiv c b _ 0 q (kummerExponent_even_mod q n))

/-- Every odd geometric-sum branch exponent gives the exponent-one function field. -/
def kummerGeometricExponentOddEquiv (c : Kˣ) (b q n : ℕ) :
    KummerBranchField c b (kummerExponent q (2 * n + 1)) q ≃ₐ[FractionRing K[X]]
      KummerBranchField c b 1 q :=
  ((kummerExponentReductionEquiv c b (kummerExponent q (2 * n + 1)) q).trans
    (kummerExponentCongrEquiv c b _ _ q (kummerExponent_odd_mod q n))).trans
    (kummerExponentReductionEquiv c b 1 q).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
