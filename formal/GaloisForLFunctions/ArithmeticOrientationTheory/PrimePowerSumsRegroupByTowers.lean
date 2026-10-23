import GaloisForLFunctions.ArithmeticOrientationTheory.TheFrustrationOfATowerIsRankOne
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.Data.Nat.Log

/-!
# Prime-power sums regroup by towers

A sum over the prime powers up to a horizon `M` is a sum over the primes `p ≤ M` of sums over
the exponents `1 ≤ k ≤ log_p M`: the fibre of the least prime factor over `p` is the tower of
`p` below `M`.  This is the bookkeeping that connects a global prime-power sum, such as the
von Mangoldt-weighted prime side of a Weil form at horizon `M`, to its tower decomposition.

* **Regrouping** (`sum_primePow_eq_sum_towers`): for every `F`,
  `Σ_{m ≤ M, m prime power} F(m) = Σ_{p ≤ M prime} Σ_{1 ≤ k ≤ log_p M} F(p^k)`.
* **Von Mangoldt sums** (`sum_vonMangoldt_mul_eq_sum_towers`): the same for `Σ_{m ≤ M} Λ(m) F(m)`,
  since `Λ` vanishes off the prime powers.
* **The global product part is the sum of the tower squares**
  (`sum_vonMangoldt_productCorr_eq_sum_towers`): for a profile supported on `[1, X]` and a
  horizon `M ≥ X²`, `Σ_{m ≤ M} Λ(m) m^{−1/2} P_q(m) = Σ_{p ≤ M} log p · (S_p(q)² − q(1)²)`, with
  `S_p(q)` the tower Mellin value through exponent `log_p X`.  The frustrating part of the odd
  Weil prime side at any horizon beyond the square of the support is exactly the sum of the
  rank-one tower squares.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### Regrouping -/

/-- The least prime factor of a prime power `≤ M` is a prime `≤ M`. -/
theorem minFac_mem_primes_of_mem_primePows {M m : ℕ} (hm : m ∈ (Icc 1 M).filter IsPrimePow) :
    m.minFac ∈ (Icc 1 M).filter Nat.Prime := by
  simp only [mem_filter, mem_Icc] at hm ⊢
  obtain ⟨⟨h1, hM⟩, hpp⟩ := hm
  have hm1 : m ≠ 1 := by rintro rfl; exact not_isPrimePow_one hpp
  have hp := Nat.minFac_prime hm1
  exact ⟨⟨hp.one_lt.le, (Nat.minFac_le (by omega)).trans hM⟩, hp⟩

/-- The fibre of the least prime factor over a prime `p` is the tower of `p` below `M`. -/
theorem primePows_fiber_eq_tower {M p : ℕ} (hp : p.Prime) (hpM : p ≤ M) :
    ((Icc 1 M).filter IsPrimePow).filter (fun m => m.minFac = p) =
      (Icc 1 (Nat.log p M)).image (fun k => p ^ k) := by
  ext m
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨⟨_, hM⟩, hpp⟩, hmin⟩
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    have hqp : q = p := by rw [← hmin, hq.pow_minFac hk.ne']
    subst hqp
    exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hq.one_lt hM⟩, rfl⟩
  · rintro ⟨k, ⟨hk1, hk⟩, rfl⟩
    have hM0 : M ≠ 0 := by have := hp.two_le; omega
    refine ⟨⟨⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_le_of_le_log hM0 hk⟩,
      (isPrimePow_nat_iff _).2 ⟨p, k, hp, by omega, rfl⟩⟩, hp.pow_minFac (by omega)⟩

/-- **Regrouping**: a sum over the prime powers up to `M` is a sum over primes of tower sums. -/
theorem sum_primePow_eq_sum_towers (F : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ (Icc 1 M).filter IsPrimePow, F m =
      ∑ p ∈ (Icc 1 M).filter Nat.Prime, ∑ k ∈ Icc 1 (Nat.log p M), F (p ^ k) := by
  rw [← sum_fiberwise_of_maps_to (g := Nat.minFac) (t := (Icc 1 M).filter Nat.Prime)
    (fun m hm => minFac_mem_primes_of_mem_primePows hm) F]
  refine sum_congr rfl fun p hp => ?_
  have hpP : p.Prime := (mem_filter.1 hp).2
  have hpM : p ≤ M := (mem_Icc.1 (mem_filter.1 hp).1).2
  rw [primePows_fiber_eq_tower hpP hpM,
    sum_image (fun a _ b _ h => Nat.pow_right_injective hpP.two_le h)]

/-- **Von Mangoldt sums regroup by towers**: `Λ` vanishes off the prime powers. -/
theorem sum_vonMangoldt_mul_eq_sum_towers (F : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, Λ m * F m =
      ∑ p ∈ (Icc 1 M).filter Nat.Prime, ∑ k ∈ Icc 1 (Nat.log p M), Λ (p ^ k) * F (p ^ k) := by
  rw [← sum_primePow_eq_sum_towers (fun m => Λ m * F m) M, sum_filter_of_ne]
  intro m _ hne
  exact vonMangoldt_ne_zero_iff.1 (left_ne_zero_of_mul hne)

/-! ### The global product part -/

/-- A sum over `range (n + 1)` of a sequence vanishing at `0` is a sum over `Icc 1 n`. -/
theorem sum_range_succ_eq_sum_Icc {g : ℕ → ℝ} (h0 : g 0 = 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), g k = ∑ k ∈ Icc 1 n, g k := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- Beyond twice the support exponent the product correlation of a tower vanishes. -/
theorem productCorr_prime_pow_eq_zero (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K k : ℕ}
    (hq : ∀ i, K < i → q (p ^ i) = 0) (hk : 2 * K < k) : productCorr q (p ^ k) = 0 := by
  rw [productCorr_prime_pow q hp k]
  refine sum_eq_zero fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
  by_cases hiK : K < i
  · rw [hq i hiK, zero_mul]
  · have : K < k - i := by omega
    rw [hq (k - i) this, mul_zero]

/-- The tower product part is stable under extending the exponent range beyond `2K`. -/
theorem sum_Icc_vonMangoldt_productCorr_eq_towerProductPart (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime)
    {K L : ℕ} (hq : ∀ i, K < i → q (p ^ i) = 0) (hL : 2 * K ≤ L) :
    ∑ k ∈ Icc 1 L, Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k) =
      towerProductPart q p K := by
  unfold towerProductPart
  rw [sum_range_succ_eq_sum_Icc (by simp)]
  symm
  apply sum_subset
  · intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  · intro k hk hk'
    simp only [mem_Icc, not_and, not_le] at hk hk'
    rw [productCorr_prime_pow_eq_zero q hp hq (hk' hk.1), mul_zero]

/-- A profile supported on `[1, X]` vanishes on the tower of `p` beyond exponent `log_p X`. -/
theorem vanish_beyond_log {q : ℕ → ℝ} {X : ℕ} (hq : ∀ n, X < n → q n = 0) {p : ℕ}
    (hp : p.Prime) (i : ℕ) (hi : Nat.log p X < i) : q (p ^ i) = 0 := by
  apply hq
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · exact Nat.one_le_pow _ _ hp.pos
  · exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt X)
      (Nat.pow_le_pow_right hp.pos hi)

/-- **The global product part is the sum of the tower squares.**  For a profile supported on
`[1, X]` and a horizon `M ≥ X²`,
`Σ_{m ≤ M} Λ(m) m^{−1/2} P_q(m) = Σ_{p ≤ M} log p · (S_p(q)² − q(1)²)`. -/
theorem sum_vonMangoldt_productCorr_eq_sum_towers (q : ℕ → ℝ) {X : ℕ}
    (hq : ∀ n, X < n → q n = 0) {M : ℕ} (hM : X ^ 2 ≤ M) :
    ∑ m ∈ Icc 1 M, Λ m * (m : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q m =
      ∑ p ∈ (Icc 1 M).filter Nat.Prime,
        Real.log p * (towerMellin q p (Nat.log p X) ^ 2 - q 1 ^ 2) := by
  have h := sum_vonMangoldt_mul_eq_sum_towers
    (fun m => (m : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q m) M
  simp only [← mul_assoc] at h
  rw [h]
  refine sum_congr rfl fun p hp => ?_
  have hpP : p.Prime := (mem_filter.1 hp).2
  have hpM : p ≤ M := (mem_Icc.1 (mem_filter.1 hp).1).2
  have hvan := vanish_beyond_log hq hpP
  have hL : 2 * Nat.log p X ≤ Nat.log p M := by
    refine le_trans ?_ (Nat.log_mono_right hM)
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp
    · apply Nat.le_log_of_pow_le hpP.one_lt
      rw [pow_mul']
      exact Nat.pow_le_pow_left (Nat.pow_log_le_self p hX.ne') 2
  rw [sum_Icc_vonMangoldt_productCorr_eq_towerProductPart q hpP hvan hL,
    sum_vonMangoldt_productCorr_prime_pow q hpP hvan]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
