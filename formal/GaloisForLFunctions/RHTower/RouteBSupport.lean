/-
Route B support arithmetic (doc 84 §10 — the coefficient-vanishing lemma and
large-prime squarefreeness of the mollified product's support).

For P = F_N·M_y with M supported on [1, y] and N < (y+1)² (the matched
θ = 1/2 regime, y = ⌊√N⌋), the coefficient of m is
b_m = Σ_{e ∣ m, e ≤ y, m ≤ N·e} λ_e. Two structural facts, pure arithmetic:

* `window_lt_of_two_large_primes` / `boundary_filter_empty` /
  `boundary_coeff_eq_zero` — if two distinct primes > y divide n, the
  divisor window {e ∣ n : e ≤ y, n ≤ N·e} is EMPTY, so b_n = 0: the
  boundary band (N, Ny] carries only single-large-prime terms. This is
  what makes the carrier conditionally LINEAR in every large-prime phase
  simultaneously (doc 84 §10).
* `not_support_of_large_prime_sq` — no support element is divisible by the
  square of a prime > y: each large prime appears at most once.
-/
import Mathlib

namespace RHTower

/-- Two distinct primes above `y` dividing `n` push every `y`-bounded divisor
of `n` strictly below the truncation window: `e * N < n`. -/
theorem window_lt_of_two_large_primes
    {N y n p q e : ℕ} (hNy : N < (y + 1) ^ 2)
    (hp : p.Prime) (hq : q.Prime) (hpy : y < p) (hqy : y < q) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hn : 0 < n)
    (he : e ∣ n) (hey : e ≤ y) :
    e * N < n := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hn
  have hpe : ¬ p ∣ e := fun h => absurd (Nat.le_of_dvd hepos h) (by omega)
  have hqe : ¬ q ∣ e := fun h => absurd (Nat.le_of_dvd hepos h) (by omega)
  have hcop : Nat.Coprime (p * q) e :=
    Nat.Coprime.mul_left ((hp.coprime_iff_not_dvd).mpr hpe)
      ((hq.coprime_iff_not_dvd).mpr hqe)
  have hpqn : p * q ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr hpq) hpn hqn
  have hall : (p * q) * e ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpqn he
  have hle : (p * q) * e ≤ n := Nat.le_of_dvd hn hall
  have hyy : N < (y + 1) * (y + 1) := by
    have h2 : (y + 1) ^ 2 = (y + 1) * (y + 1) := sq (y + 1)
    rw [h2] at hNy
    exact hNy
  have hpq2 : N < p * q :=
    lt_of_lt_of_le hyy (Nat.mul_le_mul (by omega) (by omega))
  calc e * N < e * (p * q) := mul_lt_mul_of_pos_left hpq2 hepos
    _ = (p * q) * e := Nat.mul_comm e (p * q)
    _ ≤ n := hle

/-- The mollified product's divisor window at a two-large-prime boundary
element is empty. -/
theorem boundary_filter_empty
    {N y n p q : ℕ} (hNy : N < (y + 1) ^ 2)
    (hp : p.Prime) (hq : q.Prime) (hpy : y < p) (hqy : y < q) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hn : 0 < n) :
    n.divisors.filter (fun e => e ≤ y ∧ n ≤ N * e) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  rintro e hmem ⟨hey, hwin⟩
  have he : e ∣ n := (Nat.mem_divisors.mp hmem).1
  have hlt : e * N < n :=
    window_lt_of_two_large_primes hNy hp hq hpy hqy hpq hpn hqn hn he hey
  have hlt' : N * e < n := by rwa [Nat.mul_comm] at hlt
  exact Nat.lt_irrefl n (Nat.lt_of_le_of_lt hwin hlt')

/-- **The coefficient-vanishing lemma (doc 84 §10).** Every coefficient of the
mollified product at a two-large-prime element vanishes, for ANY mollifier
weights supported on [1, y] — sharp μ and BV alike. -/
theorem boundary_coeff_eq_zero
    (lam : ℕ → ℝ) {N y n p q : ℕ} (hNy : N < (y + 1) ^ 2)
    (hp : p.Prime) (hq : q.Prime) (hpy : y < p) (hqy : y < q) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hn : 0 < n) :
    ∑ e ∈ n.divisors.filter (fun e => e ≤ y ∧ n ≤ N * e), lam e = 0 := by
  rw [boundary_filter_empty hNy hp hq hpy hqy hpq hpn hqn hn]
  exact Finset.sum_empty

/-- No support element of the mollified product is divisible by the square of
a prime above `y`: each large prime appears at most linearly (the conditional
linearity substrate, doc 84 §§4, 10). -/
theorem not_support_of_large_prime_sq
    {N y m p e : ℕ} (hNy : N < (y + 1) ^ 2)
    (hp : p.Prime) (hpy : y < p) (hsq : p ^ 2 ∣ m) (hm : 0 < m)
    (he : e ∣ m) (hey : e ≤ y) (hwin : m ≤ N * e) : False := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hm
  have hpe : ¬ p ∣ e := fun h => absurd (Nat.le_of_dvd hepos h) (by omega)
  have hcop : Nat.Coprime (p ^ 2) e :=
    Nat.Coprime.pow_left 2 ((hp.coprime_iff_not_dvd).mpr hpe)
  have hall : p ^ 2 * e ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hsq he
  have hle : p ^ 2 * e ≤ m := Nat.le_of_dvd hm hall
  have hp2 : N < p ^ 2 :=
    lt_of_lt_of_le hNy (Nat.pow_le_pow_left (by omega) 2)
  have hgt : N * e < p ^ 2 * e := mul_lt_mul_of_pos_right hp2 hepos
  exact Nat.lt_irrefl m (Nat.lt_of_le_of_lt hwin (Nat.lt_of_lt_of_le hgt hle))

end RHTower

namespace RHTower

/-- **The window-geometry lemma (doc 85 §3).** A divisor window of
multiplicative length below `min d e` contains no common multiple of `d` and
`e` unless `d = e`: if `lcm d e ∣ k` and `k ≤ min d e` with `k > 0`, then
`d = e`. This is the geometric fact that disables the off-diagonal Möbius
cancellation in the boundary band of the mollified product — the mechanism
behind the windowed-divisor criticality V_bd ~ loglog N. -/
theorem window_diagonal_only {d e k : ℕ} (hk0 : 0 < k)
    (hdvd : Nat.lcm d e ∣ k) (hkle : k ≤ min d e) : d = e := by
  have hlcm_le : Nat.lcm d e ≤ k := Nat.le_of_dvd hk0 hdvd
  have hlcm_pos : 0 < Nat.lcm d e := Nat.pos_of_dvd_of_pos hdvd hk0
  have hd_le : d ≤ Nat.lcm d e := Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_left d e)
  have he_le : e ≤ Nat.lcm d e := Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right d e)
  have h1 : d ≤ min d e := le_trans hd_le (le_trans hlcm_le hkle)
  have h2 : e ≤ min d e := le_trans he_le (le_trans hlcm_le hkle)
  have := min_le_left d e
  have := min_le_right d e
  omega

end RHTower

namespace RHTower

/-- **The singleton-window lemma (doc 85 §3′).** For m = p·d with p prime
above both y and N/minFac(d), the mollified divisor window collapses to {d}:
any e ∣ p·d with e ≤ y and p·d ≤ N·e equals d. Consequence: b_{p·d} = λ_d
exactly — a cancellation-free sub-family whose Mertens mass delivers the
loglog lower bound on the boundary variance. -/
theorem singleton_window_coeff {N y p d e : ℕ}
    (hp : p.Prime) (hpy : y < p) (hd : 0 < d)
    (hbig : N < p * d.minFac)
    (he : e ∣ p * d) (hey : e ≤ y) (hwin : p * d ≤ N * e) : e = d := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he (Nat.mul_pos hp.pos hd)
  have hpe : ¬ p ∣ e := fun h => absurd (Nat.le_of_dvd hepos h) (by omega)
  have hed : e ∣ d :=
    (Nat.Coprime.dvd_of_dvd_mul_left ((hp.coprime_iff_not_dvd).mpr hpe).symm he)
  by_contra hne
  have helt : e < d := lt_of_le_of_ne (Nat.le_of_dvd hd hed) hne
  obtain ⟨t, ht⟩ := hed
  have ht2 : 2 ≤ t := by
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t <;> omega
    · exact h
  have htd : t ∣ d := ⟨e, by rw [ht]; ring⟩
  have hmf : d.minFac ≤ t := Nat.minFac_le_of_dvd ht2 htd
  have hde : e * d.minFac ≤ d := by
    calc e * d.minFac ≤ e * t := Nat.mul_le_mul_left e hmf
      _ = d := by rw [ht]
  have h1 : p * d * d.minFac ≤ N * e * d.minFac :=
    Nat.mul_le_mul_right _ hwin
  have h2 : N * (e * d.minFac) ≤ N * d := Nat.mul_le_mul_left N hde
  have h3 : p * d.minFac * d ≤ N * d := by
    calc p * d.minFac * d = p * d * d.minFac := by ring
      _ ≤ N * e * d.minFac := h1
      _ = N * (e * d.minFac) := by ring
      _ ≤ N * d := h2
  have h4 : p * d.minFac ≤ N := Nat.le_of_mul_le_mul_right h3 hd
  omega

end RHTower
