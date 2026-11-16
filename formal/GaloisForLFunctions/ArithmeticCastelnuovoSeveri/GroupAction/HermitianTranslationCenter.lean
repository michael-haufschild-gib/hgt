import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianNoncommutativeAutomorphisms

/-!
# The center of the Hermitian translation group

A translation commutes with every translation precisely when its first
coordinate vanishes. Its second coordinate then lies in the quadratic
trace kernel. Thus the center has exactly Q elements, in every characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "HK" => HermitianAffinePoint p s K

/-- A Hermitian translation is central exactly when its first coordinate is zero. -/
theorem hermitianTranslation_commutes_iff (P : HK) :
    (∀ U : HK, P * U = U * P) ↔ P.val.1 = 0 := by
  constructor
  · intro h
    have hcross (a : K) : P.val.1 ^ Q * a = a ^ Q * P.val.1 := by
      let U := hermitianAffinePointWithFirst p s a
      have he := congrArg (fun T : HK => T.val.2) (h U)
      change P.val.2 + U.val.2 + P.val.1 ^ Q * a =
        U.val.2 + P.val.2 + a ^ Q * P.val.1 at he
      rw [add_comm U.val.2 P.val.2] at he
      exact add_left_cancel he
    have hfixed : P.val.1 ^ Q = P.val.1 := by
      simpa only [mul_one, one_pow, one_mul] using hcross 1
    by_contra ha
    obtain ⟨t, ht⟩ := squareConstantField_exists_not_fixed p s
    have he := hcross t
    rw [hfixed, mul_comm (t ^ Q) P.val.1] at he
    exact ht (mul_left_cancel₀ ha he).symm
  · intro ha U
    apply Subtype.ext
    apply Prod.ext
    · change P.val.1 + U.val.1 = U.val.1 + P.val.1
      exact add_comm _ _
    · change P.val.2 + U.val.2 + P.val.1 ^ Q * U.val.1 =
        U.val.2 + P.val.2 + U.val.1 ^ Q * P.val.1
      rw [ha, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
        zero_mul, mul_zero, add_zero, add_zero, add_comm]

/-- Central Hermitian translation parameters are exactly the trace-zero constants. -/
def hermitianTranslationCenterEquivTraceKernel :
    {P : HK // ∀ U : HK, P * U = U * P} ≃ (squareFieldTrace p s).ker where
  toFun P := ⟨P.val.val.2, by
    change P.val.val.2 ^ Q + P.val.val.2 = 0
    have h := P.val.property
    rw [(hermitianTranslation_commutes_iff p s P.val).mp P.property,
      zero_pow (Nat.succ_ne_zero Q)] at h
    exact h⟩
  invFun b := ⟨⟨(0, b.val), by
      change b.val ^ Q + b.val = (0 : K) ^ (Q + 1)
      rw [zero_pow (Nat.succ_ne_zero Q)]
      exact b.property⟩,
    (hermitianTranslation_commutes_iff p s _).mpr rfl⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hermitianTranslation_commutes_iff p s P.val).mp P.property).symm rfl
  right_inv b := Subtype.ext rfl

/-- The center of the actual Hermitian translation group has order Q. -/
theorem hermitianTranslation_center_card :
    Nat.card {P : HK // ∀ U : HK, P * U = U * P} = Q :=
  (Nat.card_congr (hermitianTranslationCenterEquivTraceKernel p s)).trans
    (squareFieldTrace_kernel_card p s)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
