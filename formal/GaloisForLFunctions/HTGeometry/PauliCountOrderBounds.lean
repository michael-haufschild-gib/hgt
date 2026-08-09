import GaloisForLFunctions.HTGeometry.AnticommutingPauliObserverRankDominance

/-!
# Orders of the two Pauli counts

The nonidentity weight-at-most-`q` Pauli count is `O_q(n^q)` and the product-input observer rank is
`Ω_q(n^q)`.  Both are elementary: every binomial coefficient is below the corresponding power, and
the observer rank already contains one full top binomial term.

These are the order identifications a comparison between a rarity exponent and a ramp exponent
needs, with the constants explicit rather than asymptotic.
-/

open scoped BigOperators

namespace Quantum

/-- **The nonidentity Pauli weight count is `O_q(n^q)`**, with the constant `q 3^q`. -/
theorem nonidentityPauliWeightCount_le (n q : ℕ) (hn : 1 ≤ n) :
    nonidentityPauliWeightCount n q ≤ q * 3 ^ q * n ^ q := by
  rw [nonidentityPauliWeightCount]
  calc ∑ j ∈ Finset.range q, 3 ^ (j + 1) * n.choose (j + 1)
      ≤ ∑ _j ∈ Finset.range q, 3 ^ q * n ^ q := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjq : j + 1 ≤ q := Finset.mem_range.mp hj
        refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hjq) ?_
        exact (Nat.choose_le_pow n (j + 1)).trans (Nat.pow_le_pow_right hn hjq)
    _ = q * 3 ^ q * n ^ q := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_assoc]

/-- **The observer rank contains a full top binomial term.** -/
theorem two_mul_choose_le_productInputObserverRank (n q : ℕ) (hq : 1 ≤ q) :
    2 * n.choose q ≤ productInputObserverRank n q := by
  rw [productInputObserverRank]
  refine Nat.mul_le_mul_left 2 ?_
  have hmem : q - 1 ∈ Finset.range q := Finset.mem_range.mpr (by omega)
  have hval : q - 1 + 1 = q := by omega
  calc n.choose q = n.choose (q - 1 + 1) := by rw [hval]
    _ ≤ ∑ j ∈ Finset.range q, n.choose (j + 1) :=
        Finset.single_le_sum (f := fun j => n.choose (j + 1)) (fun _ _ => Nat.zero_le _) hmem

/-- Beyond twice the weight, the descending factorial base is at least half the register. -/
theorem half_le_succ_sub (n q : ℕ) (h : 2 * q ≤ n) :
    ((n : ℝ) / 2) ≤ ((n + 1 - q : ℕ) : ℝ) := by
  have hcast : ((n + 1 - q : ℕ) : ℝ) = (n : ℝ) + 1 - (q : ℝ) := by
    have hle : q ≤ n + 1 := by omega
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcast]
  have hqn : (2 : ℝ) * (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  linarith

/-- **The observer rank is `Ω_q(n^q)`**, with the constant `2 / (2^q q!)`. -/
theorem pow_le_productInputObserverRank (n q : ℕ) (hq : 1 ≤ q) (h : 2 * q ≤ n) :
    2 * ((n : ℝ) / 2) ^ q / (q.factorial : ℝ) ≤ (productInputObserverRank n q : ℝ) := by
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos q
  have hbase : ((n : ℝ) / 2) ^ q ≤ ((n + 1 - q : ℕ) : ℝ) ^ q :=
    pow_le_pow_left₀ (by positivity) (half_le_succ_sub n q h) q
  have hchoose : ((n + 1 - q : ℕ) : ℝ) ^ q / (q.factorial : ℝ) ≤ (n.choose q : ℝ) :=
    Nat.pow_le_choose q n
  have hrank : (2 * n.choose q : ℝ) ≤ (productInputObserverRank n q : ℝ) := by
    exact_mod_cast two_mul_choose_le_productInputObserverRank n q hq
  calc 2 * ((n : ℝ) / 2) ^ q / (q.factorial : ℝ)
      = 2 * (((n : ℝ) / 2) ^ q / (q.factorial : ℝ)) := by ring
    _ ≤ 2 * (((n + 1 - q : ℕ) : ℝ) ^ q / (q.factorial : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbase hfac.le) (by norm_num)
    _ ≤ 2 * (n.choose q : ℝ) := mul_le_mul_of_nonneg_left hchoose (by norm_num)
    _ ≤ (productInputObserverRank n q : ℝ) := hrank

end Quantum
