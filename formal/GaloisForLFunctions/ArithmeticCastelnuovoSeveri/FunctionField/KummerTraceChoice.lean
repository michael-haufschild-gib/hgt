import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRadicalRescaling
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers

/-!
# Independence of the trace-zero coefficient

Any nonzero trace-zero constant differs from the chosen one by a
Frobenius-fixed ratio. This ratio is a norm, so radical rescaling gives
an isomorphism over the original finite constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)

/-- Nonzero trace-zero constants, including the canonical choice. -/
def KummerTraceChoices :=
  {η : (SquareConstantField p s)ˣ //
    (η : SquareConstantField p s) ^ p ^ (s + 1) = -(η : SquareConstantField p s)}

/-- The specified square field supplies a nonzero trace-zero choice unconditionally. -/
def canonicalKummerTraceChoice : KummerTraceChoices p s :=
  ⟨kummerTraceConstant p s, kummerTraceConstant_frobenius p s⟩

/-- Every allowed trace coefficient differs from the canonical coefficient by a covering-degree power. -/
theorem kummerTraceChoice_exists_rescaling (η : KummerTraceChoices p s) (R : ℕ) :
    ∃ ξ : (SquareConstantField p s)ˣ,
      η.val⁻¹ ^ R * ξ ^ (p ^ (s + 1) + 1) = (kummerTraceConstant p s)⁻¹ ^ R := by
  let K := SquareConstantField p s
  let a : K := ((η.val : K) / (kummerTraceConstant p s : K)) ^ R
  have ha0 : a ≠ 0 := pow_ne_zero R (div_ne_zero η.val.ne_zero (kummerTraceConstant p s).ne_zero)
  have ha : a ^ p ^ (s + 1) = a := by
    change (((η.val : K) / (kummerTraceConstant p s : K)) ^ R) ^ p ^ (s + 1) = _
    rw [← pow_mul, Nat.mul_comm R, pow_mul, kummerTraceConstant_ratio_fixed p s _ η.property]
  obtain ⟨ξ, hξ⟩ := (squareConstantField_exists_norm_iff p s a).mpr ha
  have hξ0 : ξ ≠ 0 := by
    intro h
    exact ha0 (hξ.symm.trans (by rw [h, zero_pow (Nat.succ_ne_zero _)]))
  let u : Kˣ := Units.mk0 ξ hξ0
  have hu : u ^ (p ^ (s + 1) + 1) = (η.val / kummerTraceConstant p s) ^ R := Units.ext hξ
  refine ⟨u, ?_⟩
  rw [hu, ← mul_pow, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Changing the nonzero trace-zero constant preserves the Kummer field over its stated constants. -/
def kummerTraceChoiceEquiv (η : KummerTraceChoices p s) (b R : ℕ) :
    SquareKummerField p s ((kummerTraceConstant p s)⁻¹ ^ R) b R ≃ₐ[SquareConstantField p s]
      SquareKummerField p s (η.val⁻¹ ^ R) b R := by
  let ξ := Classical.choose (kummerTraceChoice_exists_rescaling p s η R)
  have hξ := Classical.choose_spec (kummerTraceChoice_exists_rescaling p s η R)
  exact hξ ▸ kummerRadicalRescalingEquiv (η.val⁻¹ ^ R) ξ b R (p ^ (s + 1))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
