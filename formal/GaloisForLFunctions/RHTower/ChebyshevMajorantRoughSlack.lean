import GaloisForLFunctions.RHTower.Matveev.FeldmanCommonDivisor

/-!
# The rough slack of Chebyshev majorants

A *`K`-term Chebyshev majorant* of level `N` is a real vector `c₁, …, c_K` whose floor
combination `G(j) = Σ_{k ≤ K} c_k ⌊j/k⌋` satisfies `G(j) ≥ 1` for `1 ≤ j ≤ N`.  By Legendre's
formula `log M! = Σ_{n ≤ M} ⌊M/n⌋ Λ(n)` and `⌊⌊N/k⌋/n⌋ = ⌊⌊N/n⌋/k⌋`,

`Σ_k c_k log ⌊N/k⌋! = Σ_{n ≤ N} Λ(n) G(⌊N/n⌋) ≥ ψ(N)`,

which is Chebyshev's upper bound method.

**Jump law** (`floorComb_rough`).  If `r ≥ 2` has no prime factor `≤ K`, then the only
`k ≤ K` dividing `r` is `k = 1`, so `G(r) = G(r − 1) + G(1)`.

**Theorem** (`sum_mul_log_factorial_ge`).  Every `K`-term majorant overshoots `ψ(N)` by at least
the von Mangoldt mass of the `n ≤ N` for which `⌊N/n⌋ ≥ 2` is `K`-rough:

`Σ_k c_k log ⌊N/k⌋! ≥ Σ_{n ≤ N} Λ(n) + Σ_{n ≤ N, ⌊N/n⌋ ≥ 2 K-rough} Λ(n)`.

Indeed `G(r) = G(r − 1) + G(1) ≥ 2` at such `r`.  The extra mass contains every block
`N/(p+1) < n ≤ N/p` with `p > K` prime, so a `K`-term majorant cannot be sharper than the prime
mass of these blocks, which is of order `N/(K log K)`.
-/

open Finset ArithmeticFunction

noncomputable section

namespace RHTower.ChebyshevMajorant

/-- The floor combination `G(j) = Σ_{k ≤ K} c_k ⌊j/k⌋`. -/
def floorComb (K : ℕ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, c k * ((j / k : ℕ) : ℝ)

/-- `r` has no prime factor `≤ K`. -/
def KRough (K r : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ r → K < p

/-- `G(1) = c₁`. -/
theorem floorComb_one {K : ℕ} (hK : 1 ≤ K) (c : ℕ → ℝ) : floorComb K c 1 = c 1 := by
  unfold floorComb
  rw [sum_eq_single 1]
  · simp
  · intro k hk hk1
    have : 1 < k := lt_of_le_of_ne (mem_Icc.mp hk).1 (Ne.symm hk1)
    simp [Nat.div_eq_of_lt this]
  · intro h
    exact absurd (mem_Icc.mpr ⟨le_rfl, hK⟩) h

/-- A `K`-rough `r ≥ 2` has no divisor `k` with `2 ≤ k ≤ K`. -/
theorem not_dvd_of_rough {K r k : ℕ} (hr : KRough K r) (hk2 : 2 ≤ k) (hkK : k ≤ K) :
    ¬ k ∣ r := by
  intro hkr
  have hp := Nat.minFac_prime (by omega : k ≠ 1)
  have hle := Nat.minFac_le (by omega : 0 < k)
  have := hr _ hp ((Nat.minFac_dvd k).trans hkr)
  omega

/-- **Jump law.**  At a `K`-rough `r ≥ 2`, `G(r) = G(r − 1) + G(1)`. -/
theorem floorComb_rough {K r : ℕ} (hK : 1 ≤ K) (c : ℕ → ℝ) (hr2 : 2 ≤ r)
    (hr : KRough K r) : floorComb K c r = floorComb K c (r - 1) + floorComb K c 1 := by
  rw [floorComb_one hK]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel, floorComb]
  have hterm : ∀ k ∈ Icc 1 K, c k * (((m + 1) / k : ℕ) : ℝ) =
      c k * ((m / k : ℕ) : ℝ) + if k = 1 then c k else 0 := by
    intro k hk
    rw [Nat.succ_div]
    by_cases hk1 : k = 1
    · subst hk1
      simp
      ring
    · have hk2 : 2 ≤ k := by have := (mem_Icc.mp hk).1; omega
      rw [if_neg (not_dvd_of_rough hr hk2 (mem_Icc.mp hk).2), if_neg hk1]
      simp
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq']
  simp [hK]

/-- At a `K`-rough `r` with `2 ≤ r ≤ N`, a majorant has `G(r) ≥ 2`. -/
theorem two_le_floorComb_rough {N K r : ℕ} (hK : 1 ≤ K) {c : ℕ → ℝ}
    (hG : ∀ j ∈ Icc 1 N, 1 ≤ floorComb K c j) (hr2 : 2 ≤ r) (hrN : r ≤ N)
    (hr : KRough K r) : 2 ≤ floorComb K c r := by
  rw [floorComb_rough hK c hr2 hr]
  have h1 := hG (r - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have h2 := hG 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  linarith

/-- **Chebyshev's identity for floor combinations.**
`Σ_k c_k log ⌊N/k⌋! = Σ_{n ≤ N} Λ(n) G(⌊N/n⌋)`. -/
theorem sum_mul_log_factorial_eq (N K : ℕ) (c : ℕ → ℝ) :
    ∑ k ∈ Icc 1 K, c k * Real.log ((N / k).factorial : ℝ) =
      ∑ n ∈ Icc 1 N, Λ n * floorComb K c (N / n) := by
  have hk : ∀ k ∈ Icc 1 K, Real.log ((N / k).factorial : ℝ) =
      ∑ n ∈ Icc 1 N, (((N / n) / k : ℕ) : ℝ) * Λ n := by
    intro k _
    rw [GaloisForLFunctions.RHTower.Matveev.log_factorial_eq_sum_vonMangoldt]
    have hsub : Icc 1 (N / k) ⊆ Icc 1 N :=
      Icc_subset_Icc le_rfl (Nat.div_le_self N k)
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun n _ => ?_
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k n]
    · intro n hn hn'
      have hlt : N / k < n := by
        simp only [mem_Icc, not_and, not_le] at hn'
        exact hn' (mem_Icc.mp hn).1
      have h0 : N / n / k = 0 := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul,
          Nat.div_eq_of_lt hlt]
      simp [h0]
  rw [sum_congr rfl fun k hk' => by rw [hk k hk'], ]
  simp only [mul_sum, floorComb]
  rw [sum_comm]
  refine sum_congr rfl fun n _ => sum_congr rfl fun k _ => ?_
  ring

open Classical in
/-- **The rough slack.**  Every `K`-term Chebyshev majorant of level `N` overshoots `ψ(N)` by at
least the von Mangoldt mass of the `n ≤ N` with `⌊N/n⌋ ≥ 2` free of prime factors `≤ K`. -/
theorem sum_mul_log_factorial_ge {N K : ℕ} (hK : 1 ≤ K) {c : ℕ → ℝ}
    (hG : ∀ j ∈ Icc 1 N, 1 ≤ floorComb K c j) :
    ∑ n ∈ Icc 1 N, Λ n +
        ∑ n ∈ (Icc 1 N).filter (fun n => 2 ≤ N / n ∧ KRough K (N / n)), Λ n ≤
      ∑ k ∈ Icc 1 K, c k * Real.log ((N / k).factorial : ℝ) := by
  rw [sum_mul_log_factorial_eq, sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hq1 : 1 ≤ N / n := Nat.div_pos hnN (by omega)
  have hqN : N / n ≤ N := Nat.div_le_self N n
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  split_ifs with h
  · have := two_le_floorComb_rough hK hG h.1 hqN h.2
    nlinarith
  · have := hG (N / n) (mem_Icc.mpr ⟨hq1, hqN⟩)
    nlinarith

end RHTower.ChebyshevMajorant
