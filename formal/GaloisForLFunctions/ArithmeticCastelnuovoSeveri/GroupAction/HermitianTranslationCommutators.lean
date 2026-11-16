import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationCenter

/-!
# Commutators in the Hermitian translation group

The commutator of parameters with first coordinates a and c is the
vertical translation by `a^Q*c-c^Q*a`. Every trace-zero constant occurs
in this way. Consequently the central elements are exactly the individual
commutators, uniformly in odd and even characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "HK" => HermitianAffinePoint p s K

/-- A trace-zero constant defines a vertical Hermitian translation. -/
def hermitianVerticalTranslation (b : (squareFieldTrace p s).ker) : HK :=
  ⟨(0, b.val), by
    change b.val ^ Q + b.val = (0 : K) ^ (Q + 1)
    rw [zero_pow (Nat.succ_ne_zero Q)]
    exact b.property⟩

private theorem hermitianCommutator_trace (a c : K) :
    squareFieldTrace p s (a ^ Q * c - c ^ Q * a) = 0 := by
  simp only [squareFieldTrace_apply, sub_pow_char_pow, mul_pow,
    squareConstantField_frobenius_sq]
  ring

/-- The commutator is the vertical translation by the alternating Frobenius pairing. -/
theorem hermitianTranslation_commutator_eq (P U : HK) :
    P * U * (U * P)⁻¹ = hermitianVerticalTranslation p s
      ⟨P.val.1 ^ Q * U.val.1 - U.val.1 ^ Q * P.val.1,
        hermitianCommutator_trace p s P.val.1 U.val.1⟩ := by
  let Z := hermitianVerticalTranslation p s
    ⟨P.val.1 ^ Q * U.val.1 - U.val.1 ^ Q * P.val.1,
      hermitianCommutator_trace p s P.val.1 U.val.1⟩
  have h : P * U = Z * (U * P) := by
    apply Subtype.ext
    apply Prod.ext
    · change P.val.1 + U.val.1 = 0 + (U.val.1 + P.val.1)
      ring
    · change P.val.2 + U.val.2 + P.val.1 ^ Q * U.val.1 =
        (P.val.1 ^ Q * U.val.1 - U.val.1 ^ Q * P.val.1) +
          (U.val.2 + P.val.2 + U.val.1 ^ Q * P.val.1) +
            (0 : K) ^ Q * (U.val.1 + P.val.1)
      rw [zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_mul]
      ring
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- Every commutator commutes with every Hermitian translation. -/
theorem hermitianTranslation_commutator_central (P U V : HK) :
    (P * U * (U * P)⁻¹) * V = V * (P * U * (U * P)⁻¹) := by
  apply (hermitianTranslation_commutes_iff p s _).mpr
    (show (P * U * (U * P)⁻¹).val.1 = 0 from by
      rw [hermitianTranslation_commutator_eq]
      rfl)

/-- Central Hermitian translations are exactly individual commutators. -/
theorem hermitianTranslation_central_iff_commutator (Z : HK) :
    (∀ V : HK, Z * V = V * Z) ↔ ∃ P U : HK, Z = P * U * (U * P)⁻¹ := by
  constructor
  · intro hZ
    have ha := (hermitianTranslation_commutes_iff p s Z).mp hZ
    have ht : Z.val.2 ^ Q = -Z.val.2 := by
      apply eq_neg_of_add_eq_zero_left
      have h := Z.property
      rwa [ha, zero_pow (Nat.succ_ne_zero Q)] at h
    let t := Z.val.2 * squareTraceOne p s
    have hdiff : t - t ^ Q = Z.val.2 := by
      change Z.val.2 * squareTraceOne p s - (Z.val.2 * squareTraceOne p s) ^ Q = _
      rw [mul_pow, ht]
      calc
        _ = Z.val.2 * ((squareTraceOne p s) ^ Q + squareTraceOne p s) := by ring
        _ = _ := by rw [← squareFieldTrace_apply, squareTraceOne_trace, mul_one]
    refine ⟨hermitianAffinePointWithFirst p s 1, hermitianAffinePointWithFirst p s t, ?_⟩
    rw [hermitianTranslation_commutator_eq]
    apply Subtype.ext
    apply Prod.ext
    · exact ha
    · change Z.val.2 = (1 : K) ^ Q * t - t ^ Q * 1
      rw [one_pow, one_mul, mul_one, hdiff]
  · rintro ⟨P, U, rfl⟩ V
    exact hermitianTranslation_commutator_central p s P U V

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
