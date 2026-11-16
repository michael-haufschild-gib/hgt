import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerThreePointArithmetic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionBranchSplitting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionInfinityRamification

/-!
# All three boundary fibers over extended constants

For the inverse-power three-point family, the origin and infinity each
have one rational normalization prime. Above one there are exactly
`(q-1)gcd(Q+1,R)` primes, all rational. The field degree is fixed while
the constants vary, and the zero exponent is included.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "s" => kummerSquareIndex d n
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "c" => (η⁻¹) ^ a
local notation "δ" => Nat.gcd (p ^ (s + 1) + 1) R
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "B∞" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a

omit [Finite E] in
/-- The reciprocal boundary consists of one rational prime for every exponent and every extended constant field. -/
theorem primePowerKummerExtension_infinity_singleton :
    ∃ P : Ideal B∞, IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B∞ = {P} ∧
      (Ideal.span {(X : E[X])}).inertiaDeg' P = 1 :=
  primePowerThreePointExtensionInfinity_singleton p d n E c a
    (primePowerThreePointExponent_pole_coprime p d n r)

/-- Every prime above one has residue degree one and the exact gcd-reduced ramification index. -/
theorem primePowerKummerExtension_branch_indices
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal = M / ((q - 1) * δ) ∧
      (Ideal.span {X - C (1 : E)}).inertiaDeg' w.asIdeal = 1 := by
  simpa only [primePowerThreePointExponent_gcd] using
    primePowerThreePointExtension_inversePower_branch_indices p d n E a η w

/-- The normalized fibers over zero, one, and infinity have sizes `1`, `(q-1)δ`, and `1`. -/
theorem primePowerKummerExtension_boundary_cards :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C (0 : E)}) B).card = 1 ∧
      (IsDedekindDomain.primesOverFinset (Ideal.span {X - C (1 : E)}) B).card = (q - 1) * δ ∧
      (IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B∞).card = 1 := by
  obtain ⟨P, hP, _⟩ := primePowerThreePointExtension_origin_singleton p d n E c a
  obtain ⟨Q, hQ, _⟩ := primePowerKummerExtension_infinity_singleton p d n r E η
  refine ⟨by rw [hP, Finset.card_singleton], ?_, by rw [hQ, Finset.card_singleton]⟩
  simpa only [primePowerThreePointExponent_gcd] using
    primePowerThreePointExtension_inversePower_branch_primes_card p d n E a η

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
