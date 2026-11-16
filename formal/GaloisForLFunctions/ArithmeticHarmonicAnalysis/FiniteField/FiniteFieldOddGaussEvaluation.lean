import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticGaussEvaluation
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticFixedSubfield
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.SignedFrobeniusPowers
import Mathlib.Algebra.Ring.GeomSum

/-!
# Semiprimitive Gauss sums at odd extension levels

At an odd level, a constant negated by the original Frobenius remains
trace-zero for the larger middle subfield. The original character
order divides the new quadratic norm degree. Quadratic trace-line
evaluation therefore gives the Gauss sum over the full extension.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Fintype E]
    [CharP E p] [Algebra (ZMod p) E]

/-- At every odd extension level, a semiprimitive Gauss sum is the middle-field size times its trace-zero character value. -/
theorem finiteField_odd_semiprimitive_gauss (h t : ℕ) (ht : Odd t)
    (hdegree : Module.finrank (ZMod p) E = 2 * (h * t))
    (χ : MulChar E ℂ) (hχ : χ ≠ 1) (horder : χ ^ (p ^ h + 1) = 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (η : E) (hη0 : η ≠ 0) (hη : η ^ p ^ h = -η) :
    gaussSum χ (finiteFieldTraceCharacter (L := E) ψ) =
      (p : ℂ) ^ (h * t) * χ η := by
  classical
  let F := frobeniusFixedSubfield p E (h * t)
  letI : Fintype F := Fintype.ofFinite _
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : @IsScalarTower (ZMod p) F E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    @ZMod.instIsScalarTower p F E _ _ Algebra.toModule Algebra.toModule Algebra.toModule
  have htwo : Module.finrank F E = 2 :=
    finiteField_frobeniusFixedSubfield_finrank_two p E (h * t) hdegree
  have hcF : Nat.card F = p ^ (h * t) := by
    rw [frobeniusFixedSubfield_card, hdegree,
      Nat.gcd_eq_right (dvd_mul_left (h * t) 2)]
  have hηtrace : Algebra.trace F E η = 0 := by
    apply (algebraMap F E).injective
    rw [finiteField_quadratic_trace htwo, hcF, map_zero,
      frobenius_negated_power_odd p h t η hη ht, add_neg_cancel]
  have hdiv : p ^ h + 1 ∣ p ^ (h * t) + 1 := by
    simpa only [pow_mul, one_pow] using Odd.nat_add_dvd_pow_add_pow (p ^ h) 1 ht
  have hlarge : χ ^ (Fintype.card F + 1) = 1 := by
    rw [← Nat.card_eq_fintype_card, hcF]
    obtain ⟨a, ha⟩ := hdiv
    rw [ha, pow_mul, horder, one_pow]
  let ψF := finiteFieldTraceCharacter (L := F) ψ
  have hψF : ψF ≠ 1 := (finiteFieldTraceCharacter_ne_one_iff ψ).mpr hψ
  have heval := finiteField_quadratic_gauss_evaluation htwo χ hχ hlarge ψF hψF η hη0 hηtrace
  change gaussSum χ (finiteFieldTraceCharacter (L := E)
    (finiteFieldTraceCharacter (L := F) ψ)) = Fintype.card F * χ η at heval
  rw [finiteFieldTraceCharacter_tower (L := F) (M := E) ψ,
    ← Nat.card_eq_fintype_card, hcF, Nat.cast_pow] at heval
  exact heval

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
