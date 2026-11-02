import GaloisForLFunctions.CompletedArithmeticForms.PrimeIncidenceDefectsHaveAnExactHarmonicDiagonal

/-!
# Large-prime incidence packets have a logarithmic defect gap

Prime divisibility supports above the square-root horizon are disjoint. Their
prime jumps have an exact harmonic diagonal. Removing the harmonic mean reduces
the packet mass without changing those jumps, leaving a logarithmic defect gap.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CompletedArithmeticForms
open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- The divisibility spikes of a finite prime family. -/
def largePrimeIncidence (P : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, b p * (if p ∣ n then 1 else 0)

/-- Harmonic centering removes exactly the pole component of the spike packet. -/
def centeredPrimeIncidencePacket (P : Finset ℕ) (b : ℕ → ℝ) (N n : ℕ) : ℝ :=
  largePrimeIncidence P b n -
    (∑ j ∈ Icc 1 N, largePrimeIncidence P b j / j) / (harmonic N : ℝ)

private theorem harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem sum_inv_multiples (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), 1 / (n : ℝ)) =
      (1 / (d : ℝ)) * (harmonic (N / d) : ℝ) := by
  rw [harmonic_real_eq_sum, mul_sum]
  refine (sum_bij' (fun k _ => d * k) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [mem_Icc, mem_filter] at hk ⊢
    refine ⟨⟨Nat.mul_pos hd (by omega), ?_⟩, ⟨k, rfl⟩⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hk.2
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd, Nat.div_le_div_right hnN⟩
  · intro k _
    exact Nat.mul_div_cancel_left k hd
  · intro n hn
    exact (Nat.mul_comm d (n / d)).trans (Nat.div_mul_cancel (mem_filter.mp hn).2)
  · intro k _
    simp only [Nat.cast_mul, one_div, mul_inv_rev]
    ring

private theorem product_gt_horizon {N p q : ℕ} (hp : N < p ^ 2) (hq : N < q ^ 2) :
    N < p * q := by
  rcases le_total p q with hpq | hqp
  · exact hp.trans_le (by simpa only [sq] using Nat.mul_le_mul_left p hpq)
  · exact hq.trans_le (by simpa only [sq, mul_comm] using Nat.mul_le_mul_left q hqp)

private theorem largePrimeIncidence_sq (P : Finset ℕ) (b : ℕ → ℝ) {N n : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, N < p ^ 2)
    (hn : n ∈ Icc 1 N) :
    largePrimeIncidence P b n ^ 2 = ∑ p ∈ P, b p ^ 2 * (if p ∣ n then 1 else 0) := by
  let z := fun p : ℕ => b p * (if p ∣ n then 1 else 0)
  have hcross (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) (hne : p ≠ q) : z p * z q = 0 := by
    by_cases hpn : p ∣ n
    · by_cases hqn : q ∣ n
      · have hcop := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hne
        have hh := Nat.le_of_dvd (mem_Icc.mp hn).1 (hcop.mul_dvd_of_dvd_of_dvd hpn hqn)
        exact False.elim ((not_lt_of_ge (hh.trans (mem_Icc.mp hn).2))
          (product_gt_horizon (hlarge p hp) (hlarge q hq)))
      · simp only [z, if_neg hqn, mul_zero]
    · simp only [z, if_neg hpn, mul_zero, zero_mul]
  change (∑ p ∈ P, z p) ^ 2 = _
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, z p * z q := by
      rw [sq, sum_mul]
      exact sum_congr rfl fun p _ => mul_sum _ _ _
    _ = ∑ p ∈ P, z p ^ 2 := by
      apply sum_congr rfl
      intro p hp
      rw [sum_eq_single_of_mem p hp (fun q hq hqp => hcross p hp q hq hqp.symm), sq]
    _ = _ := sum_congr rfl fun p _ => by
      dsimp only [z]
      split_ifs <;> simp only [mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0)]

private theorem largePrimeIncidence_mass (P : Finset ℕ) (b : ℕ → ℝ) (N : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, N < p ^ 2) :
    (∑ n ∈ Icc 1 N, largePrimeIncidence P b n ^ 2 / n) =
      ∑ p ∈ P, (harmonic (N / p) : ℝ) / p * b p ^ 2 := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ P, (b p ^ 2 * (if p ∣ n then 1 else 0)) / n := by
      apply sum_congr rfl
      intro n hn
      rw [largePrimeIncidence_sq P b hP hlarge hn, sum_div]
    _ = ∑ p ∈ P, ∑ n ∈ Icc 1 N, (b p ^ 2 * (if p ∣ n then 1 else 0)) / n := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      have heq : (∑ n ∈ Icc 1 N, (b p ^ 2 * (if p ∣ n then 1 else 0)) / n) =
          b p ^ 2 * ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) := by
        rw [sum_filter, mul_sum]
        apply sum_congr rfl
        intro n _
        by_cases hpn : p ∣ n <;> simp only [hpn, if_true, if_false, mul_one, mul_zero, zero_div]
        ring
      rw [heq, sum_inv_multiples N p (hP p hp).pos]
      ring

private theorem harmonic_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (harmonic N : ℝ) := by
  rw [harmonic_real_eq_sum]
  have hterm : (1 : ℝ) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    simpa only [Nat.cast_one, div_one] using
      (single_le_sum (f := fun n : ℕ => (1 : ℝ) / n)
        (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n))
        (mem_Icc.mpr ⟨le_rfl, hN⟩ : 1 ∈ Icc 1 N))
  exact zero_lt_one.trans_le hterm

/-- The harmonic mean subtracts one rank-one square from the disjoint diagonal. -/
theorem centered_largePrime_incidence_mass_eq (P : Finset ℕ) (b : ℕ → ℝ) {N : ℕ}
    (hN : 1 ≤ N) (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, N < p ^ 2) :
    (∑ n ∈ Icc 1 N, centeredPrimeIncidencePacket P b N n ^ 2 / n) =
      (∑ p ∈ P, (harmonic (N / p) : ℝ) / p * b p ^ 2) -
        (∑ n ∈ Icc 1 N, largePrimeIncidence P b n / n) ^ 2 / (harmonic N : ℝ) := by
  let T := ∑ n ∈ Icc 1 N, largePrimeIncidence P b n / n
  let H := (harmonic N : ℝ)
  have hH : H ≠ 0 := (harmonic_pos hN).ne'
  have hexpand : (∑ n ∈ Icc 1 N, centeredPrimeIncidencePacket P b N n ^ 2 / n) =
      (∑ n ∈ Icc 1 N, largePrimeIncidence P b n ^ 2 / n) -
        2 * (T / H) * T + (T / H) ^ 2 * H := by
    calc
      _ = ∑ n ∈ Icc 1 N, (largePrimeIncidence P b n ^ 2 / n -
          2 * (T / H) * (largePrimeIncidence P b n / n) + (T / H) ^ 2 * (1 / n)) := by
        apply sum_congr rfl
        intro n _
        change (largePrimeIncidence P b n - T / H) ^ 2 / n = _
        ring
      _ = (∑ n ∈ Icc 1 N, largePrimeIncidence P b n ^ 2 / n) -
          2 * (T / H) * (∑ n ∈ Icc 1 N, largePrimeIncidence P b n / n) +
          (T / H) ^ 2 * (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
      _ = _ := by rw [← harmonic_real_eq_sum]
  rw [hexpand, largePrimeIncidence_mass P b N hP hlarge]
  change _ - 2 * (T / H) * T + (T / H) ^ 2 * H = _ - T ^ 2 / H
  field_simp
  ring

private theorem centered_jump_eq (P : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    jumpEnergy N (centeredPrimeIncidencePacket P b N) = jumpEnergy N (incidencePacket P b) := by
  have hpacket (n : ℕ) : incidencePacket P b n =
      largePrimeIncidence P b n - ∑ p ∈ P, b p / p := by
    simp only [incidencePacket, largePrimeIncidence, ← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  unfold jumpEnergy
  apply sum_congr rfl
  intro kn _
  have hdiff : centeredPrimeIncidencePacket P b N (kn.1 * kn.2) -
      centeredPrimeIncidencePacket P b N kn.2 =
      incidencePacket P b (kn.1 * kn.2) - incidencePacket P b kn.2 := by
    rw [hpacket, hpacket]
    simp only [centeredPrimeIncidencePacket]
    ring
  rw [hdiff]

/-- The pole-centered large-prime packet retains half the horizon logarithm as
an unconditional Dirichlet gap. -/
theorem largePrime_incidence_defect_gap (P : Finset ℕ) (b : ℕ → ℝ) {N : ℕ}
    (hN : 2 ≤ N) (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, N < p ^ 2) :
    Real.log (N : ℝ) / 2 *
        (∑ n ∈ Icc 1 N, centeredPrimeIncidencePacket P b N n ^ 2 / n) ≤
      poleDefect N (atomAmplitude (centeredPrimeIncidencePacket P b N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 ≤ Real.log (N : ℝ) / 2 := div_nonneg (Real.log_natCast_nonneg N) zero_le_two
  have hH : 0 < (harmonic N : ℝ) := harmonic_pos (by omega)
  have hmass := centered_largePrime_incidence_mass_eq P b (by omega : 1 ≤ N) hP hlarge
  have hmassLe : (∑ n ∈ Icc 1 N, centeredPrimeIncidencePacket P b N n ^ 2 / n) ≤
      ∑ p ∈ P, (harmonic (N / p) : ℝ) / p * b p ^ 2 := by
    rw [hmass]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hH.le)
  rw [← jumpEnergy_eq_poleDefect, centered_jump_eq,
    jumpEnergy_prime_incidence_eq_harmonic_diagonal P b hP N]
  apply (mul_le_mul_of_nonneg_left hmassLe hL).trans
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hlogp : Real.log (N : ℝ) / 2 ≤ Real.log p := by
    have hh := Real.log_le_log hN0 (show (N : ℝ) ≤ (p : ℝ) ^ 2 by exact_mod_cast (hlarge p hp).le)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh]
  have hHp : 0 ≤ (harmonic (N / p) : ℝ) := by
    rw [harmonic_real_eq_sum]
    exact sum_nonneg fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)
  have hh := mul_le_mul_of_nonneg_right hlogp
    (mul_nonneg (div_nonneg hHp hp0.le) (sq_nonneg (b p)))
  exact hh.trans_eq (by ring)

#print axioms centered_largePrime_incidence_mass_eq
#print axioms largePrime_incidence_defect_gap

end GaloisForLFunctions.CompletedArithmeticForms
