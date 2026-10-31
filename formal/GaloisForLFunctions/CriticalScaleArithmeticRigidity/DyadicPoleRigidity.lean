import GaloisForLFunctions.CriticalScaleArithmeticRigidity.SuccessorProjection

/-!
# Successor transversality and the dyadic pole

Successor projection loses at least three quarters of every conductor
above two. Dyadic dilation detects the remaining parity coefficient in
the constant mode. Together these observations control all nonconstant
packet mass with a constant independent of the conductor cutoff.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open BezoutValuationIncidence

/-- The constant-mode change produced by dilation by two. -/
def dyadicPoleDefect (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  packetMean Q (fun n => conductorPacket Q a (2 * n) - conductorPacket Q a n)

/-- Complete-period coefficient mass after removing the constant conductor. -/
def nonconstantPacketMass (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 Q, if m = 1 then 0 else (m.totient : ℝ) * a m ^ 2

/-- Successor approximation error together with the actual dyadic pole reading. -/
def jointRigidityEnergy (Q : ℕ) (a b : ℕ → ℝ) : ℝ :=
  packetMean Q (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2) +
    dyadicPoleDefect Q a ^ 2

theorem nonconstantPacketMass_nonneg (Q : ℕ) (a : ℕ → ℝ) :
    0 ≤ nonconstantPacketMass Q a := by
  apply sum_nonneg
  intro m _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem jointRigidityEnergy_nonneg (Q : ℕ) (a b : ℕ → ℝ) :
    0 ≤ jointRigidityEnergy Q a b :=
  add_nonneg (packetMean_sq_nonneg Q _) (sq_nonneg _)

private theorem totient_ge_two {m : ℕ} (hm : 3 ≤ m) : 2 ≤ m.totient := by
  have hp : 0 < m.totient := Nat.totient_pos.mpr (by omega)
  have hn : m.totient ≠ 1 := by
    intro h
    rcases Nat.totient_eq_one_iff.mp h with h | h <;> omega
  omega

private theorem moebiusReal_sq_le_one (m : ℕ) : moebiusReal m ^ 2 ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;>
    norm_num [moebiusReal, h]

/-- Every non-parity successor multiplier has squared modulus at most one quarter. -/
theorem successorMultiplier_sq_le_quarter {m : ℕ} (hm : 3 ≤ m) :
    sieveLagMultiplier m 1 ^ 2 ≤ (1 / 4 : ℝ) := by
  rw [sieveLagMultiplier_eq_moebius_totient_quotient, Nat.gcd_one_right, Nat.div_one,
    div_pow]
  have hphi : (2 : ℝ) ≤ m.totient := by exact_mod_cast totient_ge_two hm
  have hphi0 : 0 < (m.totient : ℝ) := by linarith only [hphi]
  apply (div_le_iff₀ (by positivity : 0 < (m.totient : ℝ) ^ 2)).mpr
  nlinarith only [moebiusReal_sq_le_one m, hphi, sq_nonneg ((m.totient : ℝ) - 2)]

/-- The successor leakage has a uniform three-quarters floor outside constants and parity. -/
theorem successorLeakage_ge_three_quarters {m : ℕ} (hm : 3 ≤ m) :
    (3 / 4 : ℝ) * m.totient ≤ shiftLeakageWeight m 1 := by
  have h := successorMultiplier_sq_le_quarter hm
  have he : (3 / 4 : ℝ) ≤ 1 - sieveLagMultiplier m 1 ^ 2 := by linarith only [h]
  simpa only [shiftLeakageWeight, mul_comm] using
    mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m.totient)

@[simp] theorem successorLeakage_one : shiftLeakageWeight 1 1 = 0 := by
  norm_num [shiftLeakageWeight, sieveLagMultiplier_eq_moebius_totient_quotient, moebiusReal]

@[simp] theorem successorLeakage_two : shiftLeakageWeight 2 1 = 0 := by
  norm_num [shiftLeakageWeight, sieveLagMultiplier_eq_moebius_totient_quotient, moebiusReal,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- The dyadic pole reading is exactly the retained parity coefficient. -/
theorem dyadicPoleDefect_eq (Q : ℕ) (a : ℕ → ℝ) :
    dyadicPoleDefect Q a = if 2 ∈ Icc 1 Q then a 2 else 0 := by
  have hbase := packetMean_dilate Q a 1
  simp only [one_mul, Nat.dvd_one] at hbase
  rw [dyadicPoleDefect, packetMean_sub, packetMean_dilate, hbase, ← sum_sub_distrib]
  have he (m : ℕ) (_hm : m ∈ Icc 1 Q) :
      (if m ∣ 2 then a m * (m.totient : ℝ) else 0) -
        (if m = 1 then a m * (m.totient : ℝ) else 0) =
      if m = 2 then a 2 else 0 := by
    by_cases hm1 : m = 1
    · subst m
      norm_num
    by_cases hm2 : m = 2
    · subst m
      norm_num
    have hndvd : ¬m ∣ 2 := by
      rw [Nat.dvd_prime Nat.prime_two]
      exact not_or.mpr ⟨hm1, hm2⟩
    simp only [if_neg hndvd, if_neg hm1, if_neg hm2, sub_self]
  rw [sum_congr rfl he, sum_ite_eq']

private theorem parity_square_sum (Q : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, if m = 2 then a 2 ^ 2 else 0) = dyadicPoleDefect Q a ^ 2 := by
  rw [sum_ite_eq', dyadicPoleDefect_eq]
  split_ifs <;> ring

/-- A complete-period successor approximation and one dyadic pole reading control every
nonconstant conductor, uniformly in the packet cutoff. -/
theorem three_quarters_nonconstantPacketMass_le_jointRigidityEnergy
    (Q : ℕ) (a b : ℕ → ℝ) :
    (3 / 4 : ℝ) * nonconstantPacketMass Q a ≤ jointRigidityEnergy Q a b := by
  have hpoint (m : ℕ) (hm : m ∈ Icc 1 Q) :
      (3 / 4 : ℝ) * (if m = 1 then 0 else (m.totient : ℝ) * a m ^ 2) ≤
        shiftLeakageWeight m 1 * a m ^ 2 + (if m = 2 then a 2 ^ 2 else 0) := by
    by_cases hm1 : m = 1
    · subst m
      simp only [ite_true, successorLeakage_one, zero_mul]
      norm_num
    by_cases hm2 : m = 2
    · subst m
      simp only [Nat.totient_two, Nat.cast_one, one_mul, if_neg (by decide : (2 : ℕ) ≠ 1),
        ite_true, successorLeakage_two, zero_mul, zero_add]
      nlinarith only [sq_nonneg (a 2)]
    have hm3 : 3 ≤ m := by have := (mem_Icc.mp hm).1; omega
    have h := mul_le_mul_of_nonneg_right (successorLeakage_ge_three_quarters hm3)
      (sq_nonneg (a m))
    simpa only [if_neg hm1, if_neg hm2, add_zero, mul_assoc] using h
  have hsum := sum_le_sum hpoint
  rw [← mul_sum, sum_add_distrib, parity_square_sum] at hsum
  exact hsum.trans (add_le_add_right (packetMean_shift_error_ge_leakage Q a b 1)
    (dyadicPoleDefect Q a ^ 2))

#print axioms dyadicPoleDefect_eq
#print axioms successorLeakage_ge_three_quarters
#print axioms three_quarters_nonconstantPacketMass_le_jointRigidityEnergy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
