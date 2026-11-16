import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalClassification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerRationalPeriod

/-!
# The exact rational parameter classes

For `Q=q^(n+1)`, vanishing of the regular differential space is
equivalent to the geometric branch length being divisible by `2(n+1)`.
The explicit rational-boundary equivalence makes this the exact
rationality classification of the actual function fields.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)

private theorem cover_dvd_iff_period :
    p ^ (s + 1) + 1 ∣ kummerExponent (p ^ (d + 1)) r ↔ 2 * (n + 1) ∣ r := by
  have hQ : p ^ (s + 1) = (p ^ (d + 1)) ^ (n + 1) := by
    rw [kummerSquareIndex_succ, pow_mul]
  rw [hQ]
  exact kummerExponent_cover_dvd_iff (p ^ (d + 1)) n r
    (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt)

/-- The actual regular differential space vanishes exactly at doubled branch-length periods. -/
theorem primePowerKummer_regularDifferential_finrank_zero_iff_period :
    Module.finrank K (globalRegularDifferentials K L) = 0 ↔ 2 * (n + 1) ∣ r := by
  rw [squareKummer_regularDifferential_finrank_eq_zero_iff]
  exact cover_dvd_iff_period p d n r

/-- The actual prime-power Kummer field is rational exactly at doubled branch-length periods. -/
theorem primePowerKummer_rational_iff_period :
    Nonempty (FractionRing K[X] ≃ₐ[K] L) ↔ 2 * (n + 1) ∣ r := by
  rw [squareKummer_rational_iff]
  exact cover_dvd_iff_period p d n r

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
