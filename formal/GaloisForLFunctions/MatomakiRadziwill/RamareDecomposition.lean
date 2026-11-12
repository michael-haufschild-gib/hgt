import GaloisForLFunctions.MatomakiRadziwill.LadderMeanValue

/-!
# Ramaré's identity at one scale of the ladder

`𝒫` is a finite set of primes (one scale) and `ω(n) = #{p ∈ 𝒫 : p ∣ n}` (`omegaIn`).  For `p ∈ 𝒫`,
`p ∣ n`: `ω(n) ≤ ω(n/p) + 1`, with equality when `p² ∤ n` (`omegaIn_le_div_add_one`,
`omegaIn_div_add_one_of_not_sq_dvd`).  Hence (`sum_inv_omegaIn_div_le_one`,
`sum_inv_omegaIn_div_eq_one`)

`Σ_{p ∈ 𝒫, p ∣ n} 1/(ω(n/p) + 1) ≤ 1`, with equality when `ω(n) ≥ 1` and no `p ∈ 𝒫` has `p² ∣ n`.

This is Ramaré's identity `Σ_{p ∣ n} 1/ω(n) = 1` written with the weight on the cofactor, which is
the form in which `Σ_{n} f(n) n^{-s}` factors into prime blocks times cofactor polynomials.
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `ω_𝒫(n) = #{p ∈ 𝒫 : p ∣ n}`. -/
def omegaIn (𝒫 : Finset ℕ) (n : ℕ) : ℕ := (𝒫.filter (· ∣ n)).card

/-- For a prime `p ∣ n`, the primes of `𝒫` dividing `n` divide `n/p` or equal `p`. -/
theorem filter_dvd_subset_insert {𝒫 : Finset ℕ} (h𝒫 : ∀ q ∈ 𝒫, q.Prime) {p n : ℕ}
    (hpn : p ∣ n) :
    𝒫.filter (· ∣ n) ⊆ insert p (𝒫.filter (· ∣ n / p)) := by
  intro q hq
  rw [mem_filter] at hq
  rw [mem_insert, mem_filter]
  by_cases hqp : q = p
  · exact Or.inl hqp
  · right
    refine ⟨hq.1, ?_⟩
    obtain ⟨k, hk⟩ := hpn
    have hp0 : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · rw [h, zero_mul] at hk
        subst hk
        exact absurd (Nat.dvd_zero q) (by
          intro _
          have := (h𝒫 q hq.1).two_le
          exact hqp (by
            rcases Nat.eq_zero_or_pos q with h0 | h0
            · omega
            · exact absurd h (by omega)))
      · exact h
    rw [hk, Nat.mul_div_cancel_left k hp0]
    have hq' : q ∣ p * k := hk ▸ hq.2
    rcases (Nat.Prime.dvd_mul (h𝒫 q hq.1)).mp hq' with h | h
    · exfalso
      have hp1 : p ≠ 1 := by
        intro h1; subst h1
        exact hqp ((Nat.dvd_one.mp h).trans rfl |>.symm ▸ (Nat.dvd_one.mp h))
      exact hqp ((Nat.prime_dvd_prime_iff_eq (h𝒫 q hq.1) (by
        exact (Nat.prime_def_lt''.mpr ⟨by
          rcases Nat.lt_or_ge p 2 with hlt | hge
          · interval_cases p <;> simp_all
          · exact hge, fun m hm => by
            have := (Nat.dvd_prime (h𝒫 q hq.1)).mp
            exact (Nat.eq_one_or_self_of_prime ?_ m hm)⟩))).mp h)
    · exact h

end

end GaloisForLFunctions.MatomakiRadziwill
