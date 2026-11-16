import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExponentReduction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRadicalRescaling

/-!
# Normalized branch exponent reduction

Reducing the branch exponent modulo the covering degree also preserves
coefficient normalization: its removed power is absorbed by rescaling
the radical with a constant-field unit.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable {K : Type*} [Field K] (b R n : ℕ)

/-- Coefficient normalization by the same exponent also survives reduction modulo the covering degree. -/
def kummerNormalizedExponentReductionEquiv (η : Kˣ) :
    KummerBranchField (η⁻¹ ^ (R % (n + 1))) b (R % (n + 1)) n ≃ₐ[K]
      KummerBranchField (η⁻¹ ^ R) b R n := by
  let ξ : Kˣ := η ^ (R / (n + 1))
  have hc : η⁻¹ ^ R * ξ ^ (n + 1) = η⁻¹ ^ (R % (n + 1)) := by
    have he : R = R / (n + 1) * (n + 1) + R % (n + 1) := by
      simpa only [Nat.mul_comm (n + 1) (R / (n + 1))] using
        (Nat.div_add_mod R (n + 1)).symm
    change η⁻¹ ^ R * (η ^ (R / (n + 1))) ^ (n + 1) = _
    rw [← pow_mul]
    conv_lhs => arg 1; rw [he, pow_add]
    rw [inv_pow, inv_pow]
    group
  let e := kummerRadicalRescalingEquiv (η⁻¹ ^ R) ξ b (R % (n + 1)) n
  have e' : KummerBranchField (η⁻¹ ^ (R % (n + 1))) b (R % (n + 1)) n ≃ₐ[K]
      KummerBranchField (η⁻¹ ^ R) b (R % (n + 1)) n := by
    rw [← hc]
    exact e
  exact e'.trans ((kummerExponentReductionEquiv (η⁻¹ ^ R) b R n).symm.restrictScalars K)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
