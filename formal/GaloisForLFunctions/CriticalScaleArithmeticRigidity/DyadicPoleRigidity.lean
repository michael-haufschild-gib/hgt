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

/-- The pole reading is bounded by the complete-period square energy. -/
theorem packetMean_sq_le_mean_sq (Q : ℕ) (f : ℕ → ℝ) :
    packetMean Q f ^ 2 ≤ packetMean Q (fun n => f n ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq (range Q.factorial) f (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hcs
  have hM : (0 : ℝ) < Q.factorial := by exact_mod_cast Nat.factorial_pos Q
  unfold packetMean
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hM) hM).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hcs hM.le]

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
  exact hsum.trans (add_le_add (packetMean_shift_error_ge_leakage Q a b 1) le_rfl)

/-- The same rigidity is witnessed by two literal arithmetic difference energies. -/
theorem three_quarters_mass_le_successor_add_dilation_energy
    (Q : ℕ) (a b : ℕ → ℝ) :
    (3 / 4 : ℝ) * nonconstantPacketMass Q a ≤
      packetMean Q (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2) +
        packetMean Q (fun n => (conductorPacket Q a (2 * n) - conductorPacket Q a n) ^ 2) :=
  (three_quarters_nonconstantPacketMass_le_jointRigidityEnergy Q a b).trans
    (add_le_add le_rfl (packetMean_sq_le_mean_sq Q _))

/-- Zero nonconstant mass means exactly that every retained coefficient above one vanishes. -/
theorem nonconstantPacketMass_eq_zero_iff (Q : ℕ) (a : ℕ → ℝ) :
    nonconstantPacketMass Q a = 0 ↔ ∀ m ∈ Icc 2 Q, a m = 0 := by
  have hnonneg (m : ℕ) (_ : m ∈ Icc 1 Q) :
      0 ≤ (if m = 1 then 0 else (m.totient : ℝ) * a m ^ 2) := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [nonconstantPacketMass, sum_eq_zero_iff_of_nonneg hnonneg]
  constructor
  · intro hz m hm
    have hm1 : m ∈ Icc 1 Q :=
      mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩
    have hmne : m ≠ 1 := by have := (mem_Icc.mp hm).1; omega
    have he := hz m hm1
    rw [if_neg hmne] at he
    have hphi : (m.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm1).1).ne'
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hphi)
  · intro hz m hm
    by_cases hm1 : m = 1
    · rw [if_pos hm1]
    · have hm2 : m ∈ Icc 2 Q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega,
        (mem_Icc.mp hm).2⟩
      rw [if_neg hm1, hz m hm2, zero_pow two_ne_zero, mul_zero]

/-- A packet with zero nonconstant mass is the constant mode at every integer. -/
theorem conductorPacket_of_nonconstant_mass_eq_zero (Q : ℕ) (a : ℕ → ℝ)
    (hz : nonconstantPacketMass Q a = 0) (n : ℕ) :
    conductorPacket Q a n = if 1 ∈ Icc 1 Q then a 1 else 0 := by
  have ha := (nonconstantPacketMass_eq_zero_iff Q a).mp hz
  have he (m : ℕ) (hm : m ∈ Icc 1 Q) :
      a m * ramanujanLagCoefficient m n = if m = 1 then a 1 else 0 := by
    by_cases hm1 : m = 1
    · subst m
      simp only [ite_true, ramanujanLagCoefficient_of_dvd (one_dvd n),
        Nat.totient_one, Nat.cast_one, mul_one]
    · rw [if_neg hm1, ha m (mem_Icc.mpr
        ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩), zero_mul]
  rw [conductorPacket, sum_congr rfl he, sum_ite_eq']

/-- Joint successor and pole neutrality has exactly the constant packet as its kernel. -/
theorem jointRigidityEnergy_eq_zero_iff (Q : ℕ) (a b : ℕ → ℝ) :
    jointRigidityEnergy Q a b = 0 ↔
      (∀ m ∈ Icc 2 Q, a m = 0) ∧ (∀ m ∈ Icc 1 Q, b m = a m) := by
  constructor
  · intro hz
    have hM : nonconstantPacketMass Q a = 0 := by
      have hg := three_quarters_nonconstantPacketMass_le_jointRigidityEnergy Q a b
      rw [hz] at hg
      linarith only [hg, nonconstantPacketMass_nonneg Q a]
    have hshift (n : ℕ) : conductorPacket Q a (n + 1) = conductorPacket Q a n := by
      rw [conductorPacket_of_nonconstant_mass_eq_zero Q a hM,
        conductorPacket_of_nonconstant_mass_eq_zero Q a hM]
    have hlin (n : ℕ) : conductorPacket Q (fun m => a m - b m) n =
        conductorPacket Q a n - conductorPacket Q b n := by
      simp only [conductorPacket, sub_mul, sum_sub_distrib]
    have herr : packetMean Q (fun n =>
        (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2) = 0 := by
      have hn := packetMean_sq_nonneg Q (fun n => conductorPacket Q a (n + 1) - conductorPacket Q b n)
      change _ + dyadicPoleDefect Q a ^ 2 = 0 at hz
      linarith only [hz, hn, sq_nonneg (dyadicPoleDefect Q a)]
    have he : packetMean Q (fun n =>
        (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2) =
        packetMean Q (fun n => conductorPacket Q (fun m => a m - b m) (n + 0) ^ 2) := by
      congr 1
      funext n
      simp only [Nat.add_zero, hlin, hshift]
    rw [he, packetMean_shift_sq] at herr
    have hcoeff := (sum_eq_zero_iff_of_nonneg (fun m (_ : m ∈ Icc 1 Q) =>
      mul_nonneg (Nat.cast_nonneg m.totient) (sq_nonneg (a m - b m)))).mp herr
    refine ⟨(nonconstantPacketMass_eq_zero_iff Q a).mp hM, fun m hm => ?_⟩
    have hphi : (m.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp (hcoeff m hm)).resolve_left hphi))).symm
  · rintro ⟨ha, hb⟩
    have hM := (nonconstantPacketMass_eq_zero_iff Q a).mpr ha
    have hbPacket (n : ℕ) : conductorPacket Q b n = conductorPacket Q a n := by
      exact sum_congr rfl fun m hm => congrArg (fun z => z * ramanujanLagCoefficient m n) (hb m hm)
    have hs (n : ℕ) : conductorPacket Q a (n + 1) - conductorPacket Q b n = 0 := by
      rw [hbPacket, conductorPacket_of_nonconstant_mass_eq_zero Q a hM,
        conductorPacket_of_nonconstant_mass_eq_zero Q a hM, sub_self]
    have hd (n : ℕ) : conductorPacket Q a (2 * n) - conductorPacket Q a n = 0 := by
      rw [conductorPacket_of_nonconstant_mass_eq_zero Q a hM,
        conductorPacket_of_nonconstant_mass_eq_zero Q a hM, sub_self]
    simp only [jointRigidityEnergy, dyadicPoleDefect, hs, hd, zero_pow two_ne_zero,
      packetMean, sum_const_zero, zero_div, add_zero]

/-- No larger cutoff-independent coefficient can replace three quarters. -/
theorem universal_joint_rigidity_lower_iff (C : ℝ) :
    (∀ Q a b, C * nonconstantPacketMass Q a ≤ jointRigidityEnergy Q a b) ↔
      C ≤ (3 / 4 : ℝ) := by
  constructor
  · intro hC
    let a : ℕ → ℝ := fun m => if m = 3 then 1 else 0
    have hM : nonconstantPacketMass 3 a = 2 := by
      norm_num [nonconstantPacketMass, a, Finset.sum_Icc_succ_top,
        Nat.totient_prime Nat.prime_three]
    have hE : jointRigidityEnergy 3 a (shiftProjection 1 a) = 3 / 2 := by
      rw [jointRigidityEnergy, packetMean_shift_error_eq_projection_add_leakage]
      simp only [sub_self, zero_pow two_ne_zero, mul_zero, sum_const_zero, zero_add]
      norm_num [dyadicPoleDefect_eq, shiftLeakageWeight, a, Finset.sum_Icc_succ_top,
        sieveLagMultiplier_eq_moebius_totient_quotient, moebiusReal,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three,
        Nat.totient_prime Nat.prime_three]
    have hw := hC 3 a (shiftProjection 1 a)
    rw [hM, hE] at hw
    linarith only [hw]
  · intro hC Q a b
    exact (mul_le_mul_of_nonneg_right hC (nonconstantPacketMass_nonneg Q a)).trans
      (three_quarters_nonconstantPacketMass_le_jointRigidityEnergy Q a b)

#print axioms dyadicPoleDefect_eq
#print axioms successorLeakage_ge_three_quarters
#print axioms three_quarters_nonconstantPacketMass_le_jointRigidityEnergy
#print axioms universal_joint_rigidity_lower_iff
#print axioms jointRigidityEnergy_eq_zero_iff

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
