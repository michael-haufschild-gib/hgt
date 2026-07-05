/-
Reducing the full-support carrier over `[1,N]` to a four-phase dominant block plus an independent
remainder, in the completely multiplicative Steinhaus model.

The block small-ball law bounds `‖w + Σ_{n∈s} aₙ Xₙ‖ ≤ t` for a prime-supported block `s`, uniformly
in the shift `w`. The certificate carrier `dirichletPoly N` has full support `[1,N]`, whose composite
terms are products of prime phases and hence correlated with any prime block — so the naive
"absorb composites into an independent shift" fails. The remedy is to pick the four dominant primes in
`(N/2, N]`: then no `n ≤ N` is divisible by any `pᵢ` except `pᵢ` itself, so the carrier splits as the
four pure terms `Σᵢ a_{pᵢ} X_{pᵢ}` plus a remainder over integers divisible by none of the `pᵢ`. Since
`X n ω = exp(2πi Σ_{q | n} v_q(n) ω_q)` reads only prime-factor coordinates, the remainder involves no
`pᵢ`-coordinate and is therefore independent of the four dominant phases — exactly the rest-measurable
shift the block law integrates against.
-/
import GaloisForLFunctions.RHTower.RouteBBlockStep

open Complex Finset
open RHTower.SteinhausModel

namespace RHTower

/-- **Isolation of a large divisor.** If `1 ≤ n ≤ N`, `N < 2p`, and `p ∣ n`, then `n = p`: the only
multiple of `p` in `[1, N]` when `p > N/2` is `p` itself. Writing `n = p·k`, the bounds `1 ≤ p·k` and
`p·k ≤ N < 2p` force `k = 1`. -/
theorem eq_of_dvd_of_mem_Icc_of_lt_two_mul {N p n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hN : N < 2 * p) (hdvd : p ∣ n) : n = p := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk] at h1
    · exact hk
  have hk2 : k < 2 := by
    by_contra hc
    rw [not_lt] at hc
    have : 2 * p ≤ p * k := by
      calc 2 * p = p * 2 := by ring
        _ ≤ p * k := Nat.mul_le_mul_left p hc
    omega
  have : k = 1 := by omega
  rw [this, mul_one]

/-- **The dominant multiples are exactly the four primes.** With four large primes `p₁,…,p₄ ∈ [1,N]`
each exceeding `N/2` (so `N < 2pᵢ`), the integers in `[1,N]` divisible by some `pᵢ` are precisely
`{p₁,p₂,p₃,p₄}`. Each `pᵢ` is divisible by itself and in range; conversely a divisible `n` is isolated
onto its dominant prime. -/
theorem dominant_multiples_eq {N p1 p2 p3 p4 : ℕ}
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4) :
    (Finset.Icc 1 N).filter (fun n => p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)
      = {p1, p2, p3, p4} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hnI, hdvd⟩
    rcases hdvd with h | h | h | h
    · exact Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN1 h)
    · exact Or.inr (Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN2 h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN3 h)))
    · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hN4 h)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨hp1I, Or.inl dvd_rfl⟩
    · exact ⟨hp2I, Or.inr (Or.inl dvd_rfl)⟩
    · exact ⟨hp3I, Or.inr (Or.inr (Or.inl dvd_rfl))⟩
    · exact ⟨hp4I, Or.inr (Or.inr (Or.inr dvd_rfl))⟩

/-- **Carrier dominant-block decomposition.** With four distinct large primes `p₁,…,p₄` in `[1,N]`
(each `> N/2`), any finite carrier over `[1,N]` splits as the four dominant terms plus a sum over the
integers divisible by none of the `pᵢ`. -/
theorem carrier_dominant_decomp {N p1 p2 p3 p4 : ℕ} (f : ℕ → ℂ)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) :
    ∑ n ∈ Finset.Icc 1 N, f n
      = (f p1 + f p2 + f p3 + f p4)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)), f n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
        (fun n => p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n) f]
  congr 1
  rw [dominant_multiples_eq hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4]
  rw [show ({p1, p2, p3, p4} : Finset ℕ) = insert p1 (insert p2 (insert p3 {p4})) from rfl]
  rw [Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]),
      Finset.sum_insert (by simp [h34]),
      Finset.sum_singleton]
  ring

/-- **The character reads only prime-factor coordinates.** If `ω` and `ω'` agree on every prime factor
of `n`, then `X n ω = X n ω'`. -/
theorem X_congr_of_eqOn_primeFactors (n : ℕ) {ω ω' : Omega}
    (h : ∀ q ∈ n.primeFactors, ω q = ω' q) : X n ω = X n ω' := by
  unfold X
  congr 3
  apply Finset.sum_congr rfl
  intro q hq
  rw [h q hq]

/-- A prime not dividing `n` is not among its prime factors. -/
theorem not_mem_primeFactors_of_not_dvd {p n : ℕ} (hdvd : ¬ p ∣ n) :
    p ∉ n.primeFactors := by
  rw [Nat.mem_primeFactors]
  rintro ⟨_, hpn, _⟩
  exact hdvd hpn

/-- **Rest terms avoid the block coordinates.** For `n` divisible by none of the four primes, none of
`p₁,…,p₄` is a prime factor of `n`; hence `X n` reads only coordinates outside `{p₁,p₂,p₃,p₄}`, so the
remainder sum is independent of the four dominant phases. -/
theorem primeFactors_disjoint_block {p1 p2 p3 p4 n : ℕ}
    (hn : ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n)) :
    Disjoint n.primeFactors ({p1, p2, p3, p4} : Finset ℕ) := by
  rw [not_or, not_or, not_or] at hn
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hn
  rw [Finset.disjoint_right]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact not_mem_primeFactors_of_not_dvd hd1
  · exact not_mem_primeFactors_of_not_dvd hd2
  · exact not_mem_primeFactors_of_not_dvd hd3
  · exact not_mem_primeFactors_of_not_dvd hd4

end RHTower
