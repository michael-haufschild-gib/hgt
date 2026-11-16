import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDivisorExponentModel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalizedPrimeFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerSmallDivisors

/-!
# An additive model at geometric length two

For `Q=q^(2n+1)`, the factor `q+1` divides `Q+1`.
Removing this common branch exponent identifies the normalized curve
with `z^((Q+1)/(q+1))=η⁻¹(u-u^(q²))` over the same constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
local notation "q" => p ^ (d + 1)
local notation "s" => kummerSquareIndex d (2 * n)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "η" => kummerTraceConstant p s

/-- The length-two model has a linear branch exponent and an additive branch polynomial. -/
abbrev KummerLengthTwoField :=
  KummerBranchField η⁻¹ (q ^ 2 - 2) 1 ((Q + 1) / (q + 1) - 1)

/-- The length-two normalized family with odd covering exponent admits its additive model over the original constant field. -/
def normalizedKummerLengthTwoEquiv :
    NormalizedKummerField p s d 1 ≃ₐ[K] KummerLengthTwoField p d n := by
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hR : kummerExponent q 2 = q + 1 := by
    simp only [kummerExponent, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, pow_zero, pow_one, zero_add, add_comm]
  have hd : q + 1 ∣ Q + 1 := by
    rw [← hR, kummerSquareIndex_succ, pow_mul]
    exact (kummerExponent_dvd_cover_iff q (2 * n + 1) 2 hq
      (Nat.succ_pos _) (Nat.zero_lt_succ 1)).mpr (Or.inr ⟨rfl, ⟨n, by ring⟩⟩)
  have hfactor : ((Q + 1) / (q + 1)) * (q + 1) = Q + 1 := Nat.div_mul_cancel hd
  have hA : 1 ≤ (Q + 1) / (q + 1) := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hfactor
    exact Nat.succ_ne_zero _ hfactor.symm
  have hcover : ((Q + 1) / (q + 1) - 1 + 1) * (q + 1) - 1 = Q := by
    rw [Nat.sub_add_cancel hA, hfactor, Nat.add_sub_cancel]
  have hbranch : (q - 2 + 1) * (q + 1) - 1 = q ^ 2 - 2 := by
    have hsub : q - 2 + 2 = q := Nat.sub_add_cancel hq
    have hmul : (q - 2 + 1) * (q + 1) + 1 = q ^ 2 := by nlinarith only [hsub]
    omega
  have e := kummerDivisorExponentEquiv η⁻¹ (q - 2) q ((Q + 1) / (q + 1) - 1)
  rw [hcover, hbranch] at e
  change KummerBranchField (η⁻¹ ^ kummerExponent q 2) (q - 2)
    (kummerExponent q 2) Q ≃ₐ[K]
    KummerBranchField η⁻¹ (q ^ 2 - 2) 1 ((Q + 1) / (q + 1) - 1)
  rw [hR]
  exact e

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
