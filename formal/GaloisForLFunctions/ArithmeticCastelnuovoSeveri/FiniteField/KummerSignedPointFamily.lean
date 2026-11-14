import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTracePointFamilies

/-!
# The signed Frobenius family of rational Kummer fibers

The second family consists of ordinates satisfying `β^Q=(-1)^R β` outside
the `q`-power fixed field. Their normalized branch values are nonzero and
Frobenius-fixed, so every such ordinate has exactly `Q+1` rational points
above it. This family is disjoint from the trace-one construction.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable (p : ℕ) [Fact p.Prime]

private theorem neg_one_primePower_pred (s d : ℕ) :
    (-1 : SquareConstantField p s) ^ (p ^ (d + 1) - 1) = 1 := by
  apply mul_right_cancel₀ (neg_ne_zero.mpr (one_ne_zero : (1 : SquareConstantField p s) ≠ 0))
  rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos), one_mul]
  simpa only [iterateFrobenius_def, one_pow] using
    map_neg (iterateFrobenius (SquareConstantField p s) p (d + 1)) 1

/-- The signed Frobenius condition makes the normalized branch value Frobenius-fixed. -/
theorem normalizedKummerBranch_signed_fixed (s d r : ℕ) (b : SquareConstantField p s)
    (hb : b ^ p ^ (s + 1) = (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * b) :
    ((normalizedKummerBranch p s d r).eval b) ^ p ^ (s + 1) =
      (normalizedKummerBranch p s d r).eval b := by
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  have hsign : ((-1 : SquareConstantField p s) ^ R) ^ (p ^ (d + 1) - 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm R (p ^ (d + 1) - 1), pow_mul,
      neg_one_primePower_pred, one_pow]
  have ht : (b ^ (p ^ (d + 1) - 1)) ^ p ^ (s + 1) = b ^ (p ^ (d + 1) - 1) := by
    rw [← pow_mul, Nat.mul_comm (p ^ (d + 1) - 1) (p ^ (s + 1)), pow_mul,
      hb, mul_pow, hsign, one_mul]
  have hc : (((kummerTraceConstant p s : SquareConstantField p s)⁻¹) ^ R) ^ p ^ (s + 1) =
      (-1) ^ R * ((kummerTraceConstant p s : SquareConstantField p s)⁻¹) ^ R := by
    rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul, inv_pow,
      kummerTraceConstant_frobenius, inv_neg, neg_pow]
  have hf : ((1 - b ^ (p ^ (d + 1) - 1)) ^ R) ^ p ^ (s + 1) =
      (1 - b ^ (p ^ (d + 1) - 1)) ^ R := by
    rw [← pow_mul, Nat.mul_comm R (p ^ (s + 1)), pow_mul, sub_pow_char_pow, one_pow, ht]
  rw [normalizedKummerBranch_eval, mul_pow, mul_pow, hc, hb, hf]
  rcases neg_one_pow_eq_or (SquareConstantField p s) R with h | h
  · change ((-1 : SquareConstantField p s) ^ R * _) * ((-1) ^ R * b) * _ = _
    rw [h]
    ring
  · change ((-1 : SquareConstantField p s) ^ R * _) * ((-1) ^ R * b) * _ = _
    rw [h]
    ring

/-- Outside the `q`-power fixed field, the branch value cannot vanish. -/
theorem normalizedKummerBranch_ne_zero_of_not_fixed (s d r : ℕ) (b : SquareConstantField p s)
    (hb : b ^ p ^ (d + 1) ≠ b) : (normalizedKummerBranch p s d r).eval b ≠ 0 := by
  have hb0 : b ≠ 0 := by
    intro h
    exact hb (by rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have ht : 1 - b ^ (p ^ (d + 1) - 1) ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    apply hb
    rw [← Nat.sub_add_cancel (Nat.one_le_pow (d + 1) p (Fact.out : p.Prime).pos), pow_succ, he, one_mul]
  rw [normalizedKummerBranch_eval]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Units.ne_zero _))) hb0)
    (pow_ne_zero _ ht)

/-- The signed parameters exclude precisely the branch zeros. -/
abbrev KummerSignedParameters (s d r : ℕ) :=
  {b : SquareConstantField p s //
    b ^ p ^ (s + 1) = (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * b ∧
      b ^ p ^ (d + 1) ≠ b}

/-- Each signed parameter supplies exactly `Q+1` rational affine points. -/
theorem kummerSignedParameter_fiber_card (s d r : ℕ) (b : KummerSignedParameters p s d r) :
    Nat.card {z : SquareConstantField p s |
      z ^ (p ^ (s + 1) + 1) = (normalizedKummerBranch p s d r).eval b.val} =
        p ^ (s + 1) + 1 :=
  squareConstantField_norm_fiber_card_of_fixed p s _
    (normalizedKummerBranch_ne_zero_of_not_fixed p s d r b.val b.property.2)
    (normalizedKummerBranch_signed_fixed p s d r b.val b.property.1)

/-- No ordinate in the trace-one family satisfies the signed Frobenius equation. -/
theorem kummerTraceFamilyPoint_not_signed (s d r : ℕ) (a : KummerTraceScalars p s d)
    (u : KummerTraceParameters p s d r) :
    (kummerTraceFamilyPoint p s d r a u) ^ p ^ (s + 1) ≠
      (-1) ^ kummerExponent (p ^ (d + 1)) (r + 1) * kummerTraceFamilyPoint p s d r a u := by
  rcases u with ⟨u, hu, huA⟩
  intro he
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  have hu0 := kummerTraceParameter_ne_zero p s d r ⟨u, hu, huA⟩
  have hp : (u ^ R) ^ p ^ (s + 1) = (-1) ^ R * u ^ R := by
    change ((kummerTraceScalar p s d a : SquareConstantField p s) * u ^ R) ^ p ^ (s + 1) =
      (-1) ^ R * ((kummerTraceScalar p s d a : SquareConstantField p s) * u ^ R) at he
    rw [mul_pow, kummerTraceScalar_fixed, mul_left_comm] at he
    exact mul_left_cancel₀ (Units.ne_zero _) he
  have hp' : (u ^ p ^ (s + 1)) ^ R = (-1) ^ R * u ^ R := by
    rw [← pow_mul, Nat.mul_comm (p ^ (s + 1)) R, pow_mul]
    exact hp
  let t := -(u ^ p ^ (s + 1)) / u
  have htR : t ^ R = 1 := by
    change (-(u ^ p ^ (s + 1)) / u) ^ R = 1
    rw [div_pow, neg_pow, hp']
    rcases neg_one_pow_eq_or (SquareConstantField p s) R with h | h
    · rw [h, one_mul, one_mul, div_self (pow_ne_zero _ hu0)]
    · rw [h]
      simp only [neg_one_mul, neg_neg, div_self (pow_ne_zero _ hu0)]
  have hA := kummerExponent_mul_add (p ^ (d + 1) - 1) (r + 1)
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)] at hA
  have htA : t ^ p ^ ((d + 1) * (r + 1)) = t := by
    rw [pow_mul p, ← hA, pow_succ, pow_mul, htR, one_pow, one_mul]
  let D := (iterateFrobenius (SquareConstantField p s) p ((d + 1) * (r + 1))).eqLocusField
    (RingHom.id _)
  have htD : t ∈ D := htA
  have hrecip : 1 - t = u⁻¹ := by
    change 1 - (-(u ^ p ^ (s + 1)) / u) = u⁻¹
    field_simp
    linear_combination hu
  have huD := D.inv_mem (D.sub_mem D.one_mem htD)
  rw [hrecip, inv_inv] at huD
  apply huA
  change u ^ p ^ ((d + 1) * (r + 1)) = u at huD
  simpa only [pow_mul p] using huD

/-- The two explicitly constructed families of rational ordinates are disjoint. -/
theorem kummerTrace_signed_disjoint (s d r : ℕ) :
    Disjoint
      (Set.range (fun x : KummerTraceScalars p s d × KummerTraceParameters p s d r =>
        kummerTraceFamilyPoint p s d r x.1 x.2))
      (Set.range (fun b : KummerSignedParameters p s d r => b.val)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨⟨a, u⟩, rfl⟩ ⟨b, hb⟩
  apply kummerTraceFamilyPoint_not_signed p s d r a u
  change b.val = kummerTraceFamilyPoint p s d r a u at hb
  simpa only [hb] using b.property.1

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
