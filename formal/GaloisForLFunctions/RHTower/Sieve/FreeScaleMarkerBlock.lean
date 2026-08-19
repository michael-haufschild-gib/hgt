import GaloisForLFunctions.RHTower.Sieve.MultiBlockFrame

/-!
# Marker blocks indexed by their reciprocal start range

Defining a marker block by a dyadic range of primes forces the physical scale to be a product
`m·M₀`, because only then does the block's reciprocal start range match the realisable range
`[√y/2, √y − 1]` of the outer factors at cofactor scale `y`.  Indexing the block by its *start*
range instead removes that constraint entirely: for any `X` and any `m`, the primes with
`X/p ∈ [m/2, m−1]` are exactly `bigPrimeSet (X/m) (X/(m/2))`, and consecutive halvings of `m` give
consecutive, disjoint prime ranges.  So the whole construction runs at an arbitrary physical scale.
-/

namespace RHTower.Sieve

open Finset

/-- **The reciprocal start of a prime range.**  `p` lies in `(X/b, X/a]` exactly when its
reciprocal start `X/p` lies in `[a, b−1]`. -/
theorem start_mem_of_mem_bigPrimeSet {X a b p : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hp : p ∈ bigPrimeSet (X / b) (X / a)) :
    a ≤ X / p ∧ X / p < b := by
  have hpp : p.Prime := prime_of_mem_bigPrimeSet hp
  have hp0 : 0 < p := hpp.pos
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hlow, hhigh⟩, -⟩ := hp
  constructor
  · -- `p ≤ X/a` gives `a ≤ X/p`
    have h1 : p * a ≤ X := (Nat.le_div_iff_mul_le ha).1 hhigh
    exact (Nat.le_div_iff_mul_le hp0).2 (by rw [mul_comm]; exact h1)
  · -- `X/b < p` gives `X/p < b`
    have h2 : X / b < p := by omega
    have h3 : X < p * b := (Nat.div_lt_iff_lt_mul hb).1 h2
    exact (Nat.div_lt_iff_lt_mul hp0).2 (by rw [mul_comm]; exact h3)

/-- The `k`-th start scale of a free-scale construction. -/
def freeStart (m k : ℕ) : ℕ := m / 2 ^ k

theorem freeStart_zero (m : ℕ) : freeStart m 0 = m := by
  rw [freeStart, pow_zero, Nat.div_one]

theorem freeStart_succ (m k : ℕ) : freeStart m (k + 1) = freeStart m k / 2 := by
  rw [freeStart, freeStart, pow_succ, Nat.div_div_eq_div_mul]

theorem freeStart_anti (m : ℕ) {j k : ℕ} (h : j ≤ k) : freeStart m k ≤ freeStart m j := by
  rw [freeStart, freeStart]
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) h) (by positivity)

/-- The `k`-th marker block of a free-scale construction: the primes whose reciprocal start lies
in `[m/2^{k+1}, m/2^k − 1]`. -/
def freeBlock (X m k : ℕ) : Finset ℕ :=
  bigPrimeSet (X / freeStart m k) (X / freeStart m (k + 1))

/-- **Every marker of the `k`-th free block has its start in the realisable range.** -/
theorem start_mem_freeBlock {X m k p : ℕ} (hk : 0 < freeStart m (k + 1))
    (hp : p ∈ freeBlock X m k) :
    freeStart m (k + 1) ≤ X / p ∧ X / p < freeStart m k := by
  have hk0 : 0 < freeStart m k := lt_of_lt_of_le hk (freeStart_anti m (by omega))
  exact start_mem_of_mem_bigPrimeSet hk hk0 hp

/-- **The free blocks all sit inside the single prime range `(X/m, X/(m/2^{K₀+1})]`.** -/
theorem freeBlock_subset_range (X m : ℕ) {k K₀ : ℕ} (hk : k ≤ K₀)
    (hpos : 0 < freeStart m (K₀ + 1)) :
    freeBlock X m k ⊆ bigPrimeSet (X / freeStart m 0) (X / freeStart m (K₀ + 1)) := by
  intro p hp
  have h0k : 0 < freeStart m k := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  rw [freeBlock, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hlow, hhigh⟩, hpp⟩ := hp
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, hpp⟩
  · have hmono : X / freeStart m 0 ≤ X / freeStart m k :=
      Nat.div_le_div_left (freeStart_anti m (Nat.zero_le k)) h0k
    omega
  · exact le_trans hhigh (Nat.div_le_div_left (freeStart_anti m (by omega)) hpos)

/-- **Every prime of the whole range lies in exactly one free block.** -/
theorem exists_freeBlock {X m K₀ p : ℕ} (hm : 0 < freeStart m (K₀ + 1))
    (hp : p ∈ bigPrimeSet (X / freeStart m 0) (X / freeStart m (K₀ + 1))) :
    ∃ k, k ≤ K₀ ∧ p ∈ freeBlock X m k := by
  classical
  induction K₀ with
  | zero => exact ⟨0, le_rfl, hp⟩
  | succ K ih =>
      by_cases hle : p ≤ X / freeStart m (K + 1)
      · have hmK : 0 < freeStart m (K + 1) :=
          lt_of_lt_of_le hm (freeStart_anti m (by omega))
        have hp' : p ∈ bigPrimeSet (X / freeStart m 0) (X / freeStart m (K + 1)) := by
          rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨hp.1.1, hle⟩, hp.2⟩
        obtain ⟨k, hk, hmem⟩ := ih hmK hp'
        exact ⟨k, by omega, hmem⟩
      · refine ⟨K + 1, le_rfl, ?_⟩
        rw [freeBlock, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc]
        rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩

/-! ## Exact halving of the start scales -/

/-- With `2^{K₀+1} ∣ m` every start scale halves exactly. -/
theorem freeStart_two_mul {m K₀ k : ℕ} (hdvd : 2 ^ (K₀ + 1) ∣ m) (hk : k ≤ K₀) :
    2 * freeStart m (k + 1) = freeStart m k := by
  obtain ⟨u, rfl⟩ := hdvd
  have h1 : freeStart (2 ^ (K₀ + 1) * u) k = 2 ^ (K₀ + 1 - k) * u := by
    rw [freeStart, show (2 : ℕ) ^ (K₀ + 1) = 2 ^ k * 2 ^ (K₀ + 1 - k) by
      rw [← pow_add]; congr 1; omega, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  have h2 : freeStart (2 ^ (K₀ + 1) * u) (k + 1) = 2 ^ (K₀ - k) * u := by
    rw [freeStart, show (2 : ℕ) ^ (K₀ + 1) = 2 ^ (k + 1) * 2 ^ (K₀ - k) by
      rw [← pow_add]; congr 1; omega, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  rw [h1, h2, ← mul_assoc, ← pow_succ']
  congr 2
  omega

/-- **The two start conditions of the fibre, exactly.**  Every marker of the `k`-th free block has
its reciprocal start in `[m_k/2, m_k − 1]`, with no rounding loss. -/
theorem freeBlock_start_bounds {X m K₀ k p : ℕ} (hdvd : 2 ^ (K₀ + 1) ∣ m) (hk : k ≤ K₀)
    (hpos : 0 < freeStart m (K₀ + 1)) (hp : p ∈ freeBlock X m k) :
    ((freeStart m k : ℕ) : ℝ) / 2 ≤ ((X / p : ℕ) : ℝ)
      ∧ ((X / p : ℕ) : ℝ) + 1 ≤ ((freeStart m k : ℕ) : ℝ) := by
  have hk1 : 0 < freeStart m (k + 1) := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  obtain ⟨hlow, hhigh⟩ := start_mem_freeBlock hk1 hp
  have hhalf := freeStart_two_mul hdvd hk
  constructor
  · have hlowR : ((freeStart m (k + 1) : ℕ) : ℝ) ≤ ((X / p : ℕ) : ℝ) := by exact_mod_cast hlow
    have hcast : ((freeStart m k : ℕ) : ℝ) = 2 * ((freeStart m (k + 1) : ℕ) : ℝ) := by
      rw [← hhalf]
      push_cast
      ring
    rw [hcast]
    linarith
  · have : X / p + 1 ≤ freeStart m k := by omega
    exact_mod_cast this

/-- The start scales of a construction based at `2^{K₀+1}·u`. -/
theorem freeStart_pow_mul {K₀ u k : ℕ} (hk : k ≤ K₀ + 1) :
    freeStart (2 ^ (K₀ + 1) * u) k = 2 ^ (K₀ + 1 - k) * u := by
  rw [freeStart, show (2 : ℕ) ^ (K₀ + 1) = 2 ^ k * 2 ^ (K₀ + 1 - k) by
    rw [← pow_add]; congr 1; omega, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]

theorem freeStart_pow_mul_pos {K₀ u k : ℕ} (hu : 0 < u) (hk : k ≤ K₀ + 1) :
    0 < freeStart (2 ^ (K₀ + 1) * u) k := by
  rw [freeStart_pow_mul hk]
  positivity

theorem dvd_pow_mul (K₀ u : ℕ) : 2 ^ (K₀ + 1) ∣ 2 ^ (K₀ + 1) * u := Dvd.intro u rfl

end RHTower.Sieve
