import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalPrimePowerSum

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

@[simp] theorem selbergMoebiusReciprocalCoeff_prime {p : ℕ} (hp : p.Prime) :
    selbergMoebiusReciprocalCoeff p = -(1 / (p : ℝ)) := by
  rw [selbergMoebiusReciprocalCoeff, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

@[simp] theorem selbergMoebiusReciprocalCoeff_prime_pow_two_add
    {p i : ℕ} (hp : p.Prime) :
    selbergMoebiusReciprocalCoeff (p ^ (i + 2)) = 0 := by
  rw [selbergMoebiusReciprocalCoeff,
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  norm_num

theorem selbergPrincipalCoeff_prime_pow_zero {p i : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ i) 1 = selbergMoebiusReciprocalCoeff (p ^ i) := by
  rw [show (1 : ℕ) = p ^ 0 by simp, selbergPrincipalCoeff_prime_pow_sum hp]
  simp

theorem selbergPrincipalCoeff_zero_prime_pow {p j : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff 1 (p ^ j) = selbergMoebiusReciprocalCoeff (p ^ j) := by
  rw [show (1 : ℕ) = p ^ 0 by simp, selbergPrincipalCoeff_prime_pow_sum hp]
  simp

theorem selbergPrincipalCoeff_prime_pow_diagonal_succ
    {p i : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ (i + 1)) (p ^ (i + 1)) =
      1 / ((p : ℝ) ^ (i + 1)) + 1 / ((p : ℝ) ^ (i + 2)) := by
  rw [selbergPrincipalCoeff_prime_pow_sum hp, min_self]
  let f : ℕ → ℝ := fun k =>
    reciprocalNatArithmetic (p ^ k) *
      selbergMoebiusReciprocalCoeff (p ^ (i + 1 - k)) *
      selbergMoebiusReciprocalCoeff (p ^ (i + 1 - k))
  change (∑ k ∈ Finset.range (i + 1 + 1), f k) = _
  have hiMem : i ∈ Finset.range (i + 1 + 1) := Finset.mem_range.mpr (by omega)
  have hisMem : i + 1 ∈ Finset.range (i + 1 + 1) := Finset.mem_range.mpr (by omega)
  have hiErase : i ∈ (Finset.range (i + 1 + 1)).erase (i + 1) :=
    Finset.mem_erase.mpr ⟨by omega, hiMem⟩
  calc
    (∑ k ∈ Finset.range (i + 1 + 1), f k) =
        (∑ k ∈ (Finset.range (i + 1 + 1)).erase (i + 1), f k) + f (i + 1) :=
      (Finset.sum_erase_add _ f hisMem).symm
    _ = ((∑ k ∈ ((Finset.range (i + 1 + 1)).erase (i + 1)).erase i, f k) + f i) +
          f (i + 1) := by
      rw [Finset.sum_erase_add _ f hiErase]
    _ = f i + f (i + 1) := by
      rw [show (∑ k ∈ ((Finset.range (i + 1 + 1)).erase (i + 1)).erase i, f k) = 0 by
        apply Finset.sum_eq_zero
        intro k hk
        have hkRange : k < i + 2 := Finset.mem_range.mp
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        have hkis : k ≠ i + 1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
        have hle : k + 2 ≤ i + 1 := by omega
        have hsub : i + 1 - k = (i + 1 - k - 2) + 2 := by omega
        dsimp [f]
        rw [hsub, selbergMoebiusReciprocalCoeff_prime_pow_two_add hp]
        ring]
      ring
    _ = 1 / ((p : ℝ) ^ (i + 1)) + 1 / ((p : ℝ) ^ (i + 2)) := by
      have hp0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
      have hps0 : p ^ (i + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      dsimp [f]
      rw [show i + 1 - i = 1 by omega,
        show i + 1 - (i + 1) = 0 by omega, pow_one, pow_zero,
        selbergMoebiusReciprocalCoeff_prime hp,
        selbergMoebiusReciprocalCoeff_one,
        reciprocalNatArithmetic_apply hp0,
        reciprocalNatArithmetic_apply hps0]
      push_cast
      ring

theorem selbergPrincipalCoeff_prime_pow_adjacent
    {p i : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ (i + 1)) (p ^ i) =
      -(1 / ((p : ℝ) ^ (i + 1))) := by
  rw [selbergPrincipalCoeff_prime_pow_sum hp, min_eq_right (by omega)]
  rw [Finset.sum_eq_single i]
  · have hpi0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [show i + 1 - i = 1 by omega, show i - i = 0 by omega,
      pow_one, pow_zero, selbergMoebiusReciprocalCoeff_prime hp,
      selbergMoebiusReciprocalCoeff_one, reciprocalNatArithmetic_apply hpi0]
    push_cast
    ring
  · intro k hk hki
    have hkle : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have htwo : 2 ≤ i + 1 - k := by omega
    have hsub : i + 1 - k = (i + 1 - k - 2) + 2 := by omega
    rw [hsub, selbergMoebiusReciprocalCoeff_prime_pow_two_add hp]
    ring
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem selbergPrincipalCoeff_prime_pow_distant
    {p i t : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ (i + t + 2)) (p ^ i) = 0 := by
  rw [selbergPrincipalCoeff_prime_pow_sum hp, min_eq_right (by omega)]
  apply Finset.sum_eq_zero
  intro k hk
  have hkle : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have htwo : 2 ≤ i + t + 2 - k := by omega
  have hsub : i + t + 2 - k = (i + t + 2 - k - 2) + 2 := by omega
  rw [hsub, selbergMoebiusReciprocalCoeff_prime_pow_two_add hp]
  ring

theorem selbergPrincipalCoeff_prime_pow_comm {p i j : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ i) (p ^ j) = selbergPrincipalCoeff (p ^ j) (p ^ i) := by
  rw [selbergPrincipalCoeff_prime_pow_sum hp, selbergPrincipalCoeff_prime_pow_sum hp,
    min_comm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem selbergPrincipalCoeff_prime_pow_adjacent_symm
    {p i : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ i) (p ^ (i + 1)) =
      -(1 / ((p : ℝ) ^ (i + 1))) := by
  rw [selbergPrincipalCoeff_prime_pow_comm hp]
  exact selbergPrincipalCoeff_prime_pow_adjacent hp

theorem selbergPrincipalCoeff_prime_pow_distant_symm
    {p i t : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ i) (p ^ (i + t + 2)) = 0 := by
  rw [selbergPrincipalCoeff_prime_pow_comm hp]
  exact selbergPrincipalCoeff_prime_pow_distant hp

end

end RHTower.Sieve
