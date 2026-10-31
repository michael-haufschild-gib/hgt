import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus

/-!
# Coherent pole transport and dissipative prime rows

On prime-supported input, the actual generator splits into a coherent
constant row and diagonal nonconstant rows. Complete-period orthogonality
separates their norms and shows that the coherent row does not contribute
to the input's self-pairing. Removing it has sharp relative cost `log 2/2`.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence ArithmeticIntersectionTheory

theorem packetMean_add (Q : ℕ) (f g : ℕ → ℝ) :
    packetMean Q (fun n => f n + g n) = packetMean Q f + packetMean Q g := by
  simp only [packetMean, sum_add_distrib, add_div]

theorem packetMean_const (Q : ℕ) (c : ℝ) : packetMean Q (fun _ => c) = c := by
  have hQ : (Q.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos Q).ne'
  simp only [packetMean, sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hQ]

private theorem normalizedPacket_eq_raw (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q a n =
      conductorPacket Q (fun m => a m / Real.sqrt (m.totient : ℝ)) n := by
  apply sum_congr rfl
  intro m hm
  rw [normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
  ring

/-- The normalized arithmetic coefficients retain the exact complete-period pairing. -/
theorem packetMean_normalizedPacket_mul (Q : ℕ) (a b : ℕ → ℝ) :
    packetMean Q (fun n => normalizedConductorPacket Q a n * normalizedConductorPacket Q b n) =
      ∑ m ∈ Icc 1 Q, a m * b m := by
  have h := packetMean_shift_mul Q (fun m => a m / Real.sqrt (m.totient : ℝ))
    (fun m => b m / Real.sqrt (m.totient : ℝ)) 0 0
  simp only [Nat.add_zero, Nat.dist_self, ramanujanLagCoefficient_of_dvd (dvd_zero _)] at h
  simp only [normalizedPacket_eq_raw]
  rw [h]
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  calc
    _ = (a m * b m / Real.sqrt (m.totient : ℝ) ^ 2) * m.totient := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg m.totient), div_mul_cancel₀ _ hphi]

theorem packetMean_normalizedPacket_sq (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n => normalizedConductorPacket Q a n ^ 2) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  simpa only [pow_two] using packetMean_normalizedPacket_mul Q a a

/-- The literal generator sends prime input to one coherent constant and diagonal prime rows. -/
theorem arithmeticPrimeGenerator_primeOnly_decomposition (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q (primeOnly a) n = primePoleResponse Q a -
      normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n := by
  rw [arithmeticPrimeGenerator_eq_jet, primePoleResponse,
    normalizedConductorPacket_primeOnly, sum_filter, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [primeOnly, if_pos hp]
    rw [ramanujanDivisorJet_prime hp, normalizedRamanujanMode_eq_coefficient hp.pos]
    ring
  · simp only [primeOnly, if_neg hp, zero_mul, sub_self]

private theorem primeOnly_product_sum (Q : ℕ) (a b : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, primeOnly a m * primeOnly b m) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, a p * b p := by
  rw [sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp only [primeOnly, hp, if_true, if_false, zero_mul]

/-- The coherent row and the remaining prime rows are exactly orthogonal. -/
theorem arithmeticPrimeGenerator_primeOnly_period_sq (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n => arithmeticPrimeGenerator Q (primeOnly a) n ^ 2) =
      primePoleResponse Q a ^ 2 +
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, tameDifferent p ^ 2 * a p ^ 2 := by
  have hpoint (n : ℕ) : arithmeticPrimeGenerator Q (primeOnly a) n ^ 2 =
      (primePoleResponse Q a ^ 2 - 2 * primePoleResponse Q a *
        normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n) +
      normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n ^ 2 := by
    rw [arithmeticPrimeGenerator_primeOnly_decomposition]
    ring
  simp only [hpoint, packetMean_add, packetMean_sub, packetMean_const,
    packetMean_const_mul, packetMean_primeOnly_eq_zero, mul_zero, sub_zero]
  rw [show packetMean Q (fun n =>
      normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n ^ 2) =
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, tameDifferent p ^ 2 * a p ^ 2 by
    rw [show (fun n => normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n ^ 2) =
        (fun n => normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n *
          normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n) by
          funext n; ring,
      packetMean_normalizedPacket_mul, primeOnly_product_sum]
    exact sum_congr rfl fun p _ => by ring]

/-- The coherent constant row contributes nothing to the input's self-pairing. -/
theorem arithmeticPrimeGenerator_primeOnly_self_pairing (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n => normalizedConductorPacket Q (primeOnly a) n *
      arithmeticPrimeGenerator Q (primeOnly a) n) =
        -(∑ p ∈ (Icc 1 Q).filter Nat.Prime, tameDifferent p * a p ^ 2) := by
  have hpoint (n : ℕ) : normalizedConductorPacket Q (primeOnly a) n *
      arithmeticPrimeGenerator Q (primeOnly a) n =
        primePoleResponse Q a * normalizedConductorPacket Q (primeOnly a) n -
          normalizedConductorPacket Q (primeOnly a) n *
            normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n := by
    rw [arithmeticPrimeGenerator_primeOnly_decomposition]
    ring
  simp only [hpoint, packetMean_sub, packetMean_const_mul, packetMean_primeOnly_eq_zero,
    mul_zero, zero_sub, packetMean_normalizedPacket_mul, primeOnly_product_sum]
  congr 1
  exact sum_congr rfl fun p _ => by ring

/-- Output centering removes precisely the coherent row on prime-supported input. -/
theorem primeCenteredGenerator_period_sq (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n =>
      (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2) =
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, tameDifferent p ^ 2 * a p ^ 2 := by
  have heq (n : ℕ) : (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2 =
      normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n *
        normalizedConductorPacket Q (primeOnly (fun p => tameDifferent p * a p)) n := by
    rw [arithmeticPrimeGenerator_primeOnly_decomposition]
    ring
  simp only [heq, packetMean_normalizedPacket_mul, primeOnly_product_sum]
  exact sum_congr rfl fun p _ => by ring

private theorem log_succ_nat_le_nat_log_two (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * Real.log 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Real.log_le_log (by positivity : 0 < ((n : ℝ) + 1) + 1)
      (show ((n : ℝ) + 1) + 1 ≤ 2 * ((n : ℝ) + 1) by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith only [hn])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)] at h
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [h, ih]

private theorem prime_tame_square_le_sharp_adjunction {p : ℕ} (hp : p.Prime) :
    tameDifferent p ^ 2 ≤ (Real.log 2 / 2) * (Real.log p + tameDifferent p) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpR).ne'
  have hpm : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hlog := log_succ_nat_le_nat_log_two (p - 1)
  rw [Nat.cast_sub hp.pos, Nat.cast_one, sub_add_cancel] at hlog
  have hfirst := div_le_div_of_nonneg_right hlog
    (mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr hpR.le))
  have hid : (((p : ℝ) - 1) * Real.log 2) / ((p : ℝ) * ((p : ℝ) - 1)) = Real.log 2 / p := by
    field_simp [hp0, hpm]
  rw [hid] at hfirst
  have hinv : 1 / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
  have hlast : Real.log 2 / (p : ℝ) ≤ Real.log 2 / 2 := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have ht := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
  simp only [pow_one] at ht
  have heq : tameDifferent p ^ 2 =
      (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) * (Real.log p + tameDifferent p) := by
    rw [ht]
    field_simp [hp0, hpm]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hfirst.trans hlast)
    (add_nonneg (Real.log_natCast_nonneg p) (tameDifferent_nonneg p))

/-- The centered prime output has a cutoff-independent sharp adjunction bound. -/
theorem primeCenteredGenerator_period_sq_le (Q : ℕ) (a : ℕ → ℝ) :
    packetMean Q (fun n =>
      (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2) ≤
        (Real.log 2 / 2) * primeAdjunctionMass Q (primeOnly a) := by
  rw [primeCenteredGenerator_period_sq, primeAdjunctionMass_primeOnly, mul_sum]
  apply sum_le_sum
  intro p hp
  exact (mul_le_mul_of_nonneg_right (prime_tame_square_le_sharp_adjunction (mem_filter.mp hp).2)
    (sq_nonneg (a p))).trans_eq (by ring)

/-- Conductor two attains the exact uniform centered-output constant. -/
theorem optimal_primeCenteredGenerator_constant_iff {Q : ℕ} (hQ : 2 ≤ Q) (C : ℝ) :
    (∀ a : ℕ → ℝ, packetMean Q (fun n =>
      (arithmeticPrimeGenerator Q (primeOnly a) n - primePoleResponse Q a) ^ 2) ≤
        C * primeAdjunctionMass Q (primeOnly a)) ↔ Real.log 2 / 2 ≤ C := by
  constructor
  · intro hC
    let a : ℕ → ℝ := fun m => if m = 2 then 1 else 0
    have h2 : 2 ∈ (Icc 1 Q).filter Nat.Prime :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by decide, hQ⟩, Nat.prime_two⟩
    have ht := tameDifferent_prime_pow Nat.prime_two (show (1 : ℕ) ≠ 0 by decide)
    norm_num only [pow_one, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at ht
    have h := hC a
    rw [primeCenteredGenerator_period_sq, primeAdjunctionMass_primeOnly] at h
    simp only [a, ite_pow, one_pow, zero_pow two_ne_zero, mul_ite, mul_one, mul_zero,
      sum_ite_eq', if_pos h2, ht, Nat.cast_ofNat] at h
    have hpos : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
    by_contra hc
    have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hc) hpos
    nlinarith only [h, hlt]
  · intro hC a
    exact (primeCenteredGenerator_period_sq_le Q a).trans
      (mul_le_mul_of_nonneg_right hC (primeAdjunctionMass_nonneg Q (primeOnly a)))

#print axioms arithmeticPrimeGenerator_primeOnly_period_sq
#print axioms arithmeticPrimeGenerator_primeOnly_self_pairing
#print axioms primeCenteredGenerator_period_sq_le
#print axioms optimal_primeCenteredGenerator_constant_iff

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
