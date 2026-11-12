import GaloisForLFunctions.MatomakiRadziwill.LadderMeanValue

/-!
# Ramaré's identity at one scale of the ladder

`Pr` is a finite set of primes (one scale) and `ω(n) = #{p ∈ Pr : p ∣ n}` (`omegaIn`).  For a prime
`p ∣ n`: `ω(n) ≤ ω(n/p) + 1` (`omegaIn_le_div_add_one`), with equality when `p ∈ Pr` and `p² ∤ n`
(`omegaIn_div_add_one_of_not_sq_dvd`).  Hence (`sum_inv_omegaIn_div_le_one`,
`sum_inv_omegaIn_div_eq_one`)

`Σ_{p ∈ Pr, p ∣ n} 1/(ω(n/p) + 1) ≤ 1`, with equality when `ω(n) ≥ 1` and no `p ∈ Pr` has `p² ∣ n`.

This is Ramaré's identity `Σ_{p ∣ n} 1/ω(n) = 1` with the weight moved to the cofactor, the form in
which `Σ_n f(n) n^{-s}` factors into prime blocks times cofactor polynomials.
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `ω_Pr(n) = #{p ∈ Pr : p ∣ n}`. -/
def omegaIn (Pr : Finset ℕ) (n : ℕ) : ℕ := (Pr.filter (· ∣ n)).card

/-- A prime `q ≠ p` dividing `n` divides `n/p`, for a prime `p ∣ n`. -/
theorem dvd_div_of_prime_ne {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hpn : p ∣ n) (hqn : q ∣ n) : q ∣ n / p := by
  obtain ⟨k, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left k hp.pos]
  rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) hqp
  · exact h

/-- `ω(n) ≤ ω(n/p) + 1` for a prime `p ∣ n`. -/
theorem omegaIn_le_div_add_one {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {p n : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) : omegaIn Pr n ≤ omegaIn Pr (n / p) + 1 := by
  classical
  have hsub : Pr.filter (· ∣ n) ⊆ insert p (Pr.filter (· ∣ n / p)) := by
    intro q hq
    rw [mem_filter] at hq
    rw [mem_insert, mem_filter]
    by_cases hqp : q = p
    · exact Or.inl hqp
    · exact Or.inr ⟨hq.1, dvd_div_of_prime_ne hp (hPr q hq.1) hqp hpn hq.2⟩
  unfold omegaIn
  exact (card_le_card hsub).trans (card_insert_le _ _)

/-- `ω(n/p) + 1 = ω(n)` for `p ∈ Pr`, `p ∣ n`, `p² ∤ n`. -/
theorem omegaIn_div_add_one_of_not_sq_dvd {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {p n : ℕ}
    (hpPr : p ∈ Pr) (hpn : p ∣ n) (hsq : ¬ p ^ 2 ∣ n) : omegaIn Pr (n / p) + 1 = omegaIn Pr n := by
  classical
  have hp := hPr p hpPr
  have hnot : ¬ p ∣ n / p := by
    intro h
    apply hsq
    obtain ⟨k, hk⟩ := h
    obtain ⟨m, rfl⟩ := hpn
    rw [Nat.mul_div_cancel_left m hp.pos] at hk
    exact ⟨k, by rw [hk]; ring⟩
  have heq : Pr.filter (· ∣ n) = insert p (Pr.filter (· ∣ n / p)) := by
    ext q
    rw [mem_filter, mem_insert, mem_filter]
    constructor
    · intro hq
      by_cases hqp : q = p
      · exact Or.inl hqp
      · exact Or.inr ⟨hq.1, dvd_div_of_prime_ne hp (hPr q hq.1) hqp hpn hq.2⟩
    · rintro (rfl | hq)
      · exact ⟨hpPr, hpn⟩
      · exact ⟨hq.1, (hq.2.trans (Nat.div_dvd_of_dvd hpn))⟩
  have hpnot : p ∉ Pr.filter (· ∣ n / p) := by
    rw [mem_filter]; exact fun h => hnot h.2
  unfold omegaIn
  rw [heq, card_insert_of_notMem hpnot]

/-- **Ramaré's weights sum to at most one.** -/
theorem sum_inv_omegaIn_div_le_one {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) (n : ℕ) :
    ∑ p ∈ Pr.filter (· ∣ n), (1 : ℝ) / (omegaIn Pr (n / p) + 1) ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos (omegaIn Pr n) with h0 | hpos
  · have hempty : Pr.filter (· ∣ n) = ∅ := by
      unfold omegaIn at h0
      exact card_eq_zero.mp h0
    rw [hempty, sum_empty]
    exact zero_le_one
  have hterm : ∀ p ∈ Pr.filter (· ∣ n),
      (1 : ℝ) / (omegaIn Pr (n / p) + 1) ≤ 1 / (omegaIn Pr n : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    have h := omegaIn_le_div_add_one hPr (hPr p hp.1) hp.2 (n := n)
    have h' : (omegaIn Pr n : ℝ) ≤ omegaIn Pr (n / p) + 1 := by exact_mod_cast h
    have hpos' : (0 : ℝ) < omegaIn Pr n := by exact_mod_cast hpos
    exact one_div_le_one_div_of_le hpos' h'
  calc ∑ p ∈ Pr.filter (· ∣ n), (1 : ℝ) / (omegaIn Pr (n / p) + 1)
      ≤ ∑ p ∈ Pr.filter (· ∣ n), 1 / (omegaIn Pr n : ℝ) := sum_le_sum hterm
    _ = 1 := by
        rw [sum_const, nsmul_eq_mul]
        have hpos' : (0 : ℝ) < omegaIn Pr n := by exact_mod_cast hpos
        unfold omegaIn at hpos' ⊢
        field_simp

/-- **Ramaré's identity.**  If `ω(n) ≥ 1` and no `p ∈ Pr` has `p² ∣ n`, the weights sum to one. -/
theorem sum_inv_omegaIn_div_eq_one {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime) {n : ℕ}
    (hpos : 1 ≤ omegaIn Pr n) (hsq : ∀ p ∈ Pr, ¬ p ^ 2 ∣ n) :
    ∑ p ∈ Pr.filter (· ∣ n), (1 : ℝ) / (omegaIn Pr (n / p) + 1) = 1 := by
  classical
  have hterm : ∀ p ∈ Pr.filter (· ∣ n),
      (1 : ℝ) / (omegaIn Pr (n / p) + 1) = 1 / (omegaIn Pr n : ℝ) := by
    intro p hp
    rw [mem_filter] at hp
    have h := omegaIn_div_add_one_of_not_sq_dvd hPr hp.1 hp.2 (hsq p hp.1)
    rw [← h]
    push_cast
    ring
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  have hpos' : (0 : ℝ) < omegaIn Pr n := by exact_mod_cast hpos
  unfold omegaIn at hpos' ⊢
  field_simp

end

end GaloisForLFunctions.MatomakiRadziwill
