import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail
import Mathlib.NumberTheory.Chebyshev
noncomputable section
/-! The full prime-pair overlap kernel is summable. This retains every cross
term of the original prime-square vector series. -/

open Filter
open scoped Topology
namespace RHTower

private theorem summable_primeCount_div_sq :
    Summable (fun n : ℕ => if n.Prime then (n.primeCounting : ℝ) / (n : ℝ)^2 else 0) := by
  have hlog : Summable ({n : ℕ | n.Prime}.indicator
      (fun n : ℕ => 1 / ((n : ℝ) * Real.log n))) := by
    apply summable_subtype_iff_indicator.mp
    change Summable (fun p : Nat.Primes => 1 / ((p : ℝ) * Real.log (p : ℝ)))
    simpa only [Real.rpow_one] using
      (Sieve.summable_primes_one_div_mul_log_rpow (s := 1) zero_lt_one)
  have hcount : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) ≤ (Real.log 4 + 1) * n / Real.log n := by
    simpa only [Nat.floor_natCast] using
      (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).eventually
        (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  apply (hlog.mul_left (Real.log 4 + 1)).of_norm_bounded_eventually_nat
  filter_upwards [hcount, eventually_ge_atTop 2] with n hn hn2
  by_cases hp : n.Prime
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hp]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ 1 : 0 < 2) hn2)
    calc
      _ ≤ ((Real.log 4 + 1) * n / Real.log n) / (n : ℝ)^2 :=
        div_le_div_of_nonneg_right hn (sq_nonneg _)
      _ = _ := by field_simp
  · simp [hp]

private def primeTriangle (p q : ℕ) : ℝ :=
  if p.Prime ∧ q.Prime ∧ q ≤ p then 1 / (p : ℝ)^2 else 0

private theorem primeTriangle_zero (p q : ℕ) (hq : q ∉ p.primesLE) :
    primeTriangle p q = 0 := by
  unfold primeTriangle
  split_ifs with h
  · exact (hq (Nat.mem_primesLE.mpr ⟨h.2.2, h.2.1⟩)).elim
  · rfl

private theorem tsum_primeTriangle (p : ℕ) :
    (∑' q, primeTriangle p q) =
      if p.Prime then (p.primeCounting : ℝ) / (p : ℝ)^2 else 0 := by
  rw [tsum_eq_sum (s := p.primesLE) (primeTriangle_zero p)]
  by_cases hp : p.Prime
  · rw [if_pos hp]
    calc
      _ = ∑ _q ∈ p.primesLE, 1 / (p : ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro q hq
        obtain ⟨hqp, hqprime⟩ := Nat.mem_primesLE.mp hq
        exact if_pos ⟨hp, hqprime, hqp⟩
      _ = _ := by simp [Nat.primesLE_card_eq_primeCounting, div_eq_mul_inv]
  · simp [primeTriangle, hp]

private theorem summable_primeTriangle :
    Summable (fun pq : ℕ × ℕ => primeTriangle pq.1 pq.2) := by
  apply (summable_prod_of_nonneg (by intro pq; change 0 ≤ primeTriangle pq.1 pq.2; unfold primeTriangle; split_ifs <;> positivity)).mpr
  constructor
  · intro p
    exact summable_of_ne_finset_zero (s := p.primesLE) (primeTriangle_zero p)
  · simpa only [tsum_primeTriangle] using summable_primeCount_div_sq

/-- All prime-square cross terms have a summable common majorant. -/
theorem summable_prime_pair_max_inv_sq :
    Summable (fun pq : Nat.Primes × Nat.Primes =>
      1 / ((max (pq.1 : ℕ) (pq.2 : ℕ) : ℕ) : ℝ)^2) := by
  have hswap : Summable (fun pq : ℕ × ℕ => primeTriangle pq.2 pq.1) :=
    summable_primeTriangle.comp_injective (i := Prod.swap) (Equiv.prodComm ℕ ℕ).injective
  have hsum := summable_primeTriangle.add hswap
  have hsub := hsum.comp_injective
    (i := fun pq : Nat.Primes × Nat.Primes => ((pq.1 : ℕ), (pq.2 : ℕ)))
    (by intro x y h; exact Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hsub
  intro pq
  change _ ≤ primeTriangle (pq.1 : ℕ) (pq.2 : ℕ) +
    primeTriangle (pq.2 : ℕ) (pq.1 : ℕ)
  rcases le_total (pq.1 : ℕ) (pq.2 : ℕ) with h | h
  · rw [max_eq_right h]
    have heq : primeTriangle (pq.2 : ℕ) (pq.1 : ℕ) = 1 / ((pq.2 : ℕ) : ℝ)^2 :=
      if_pos ⟨pq.2.prop, pq.1.prop, h⟩
    rw [heq]
    have hn : 0 ≤ primeTriangle (pq.1 : ℕ) (pq.2 : ℕ) := by
      unfold primeTriangle; split_ifs <;> positivity
    exact le_add_of_nonneg_left hn
  · rw [max_eq_left h]
    have heq : primeTriangle (pq.1 : ℕ) (pq.2 : ℕ) = 1 / ((pq.1 : ℕ) : ℝ)^2 :=
      if_pos ⟨pq.1.prop, pq.2.prop, h⟩
    rw [heq]
    have hn : 0 ≤ primeTriangle (pq.2 : ℕ) (pq.1 : ℕ) := by
      unfold primeTriangle; split_ifs <;> positivity
    exact le_add_of_nonneg_right hn
end RHTower
