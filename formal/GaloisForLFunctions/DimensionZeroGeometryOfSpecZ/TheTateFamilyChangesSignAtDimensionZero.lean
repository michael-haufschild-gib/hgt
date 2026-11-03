import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily

/-!
# The Tate family changes sign at dimension zero

Jordan's totient `J_k(n) = Σ_{d∣n} μ(n/d)d^k` is multiplicative in every real dimension `k`, with
`J_k(p^a) = p^{k(a−1)}(p^k − 1)` at prime powers. The factor `p^k − 1` has the sign of `k`. Hence:

* **Positive dimension is positive** (`jordanTotient_pos`): `J_k(n) > 0` for `k > 0`, `n ≥ 1`. These are
  the point counts `φ(n)#ℙ^{k−1}(ℤ/n)` at integer `k`.
* **Negative dimension carries the parity** (`neg_one_pow_mul_jordanTotient_pos`): for `k < 0`,
  `(−1)^{ω(n)} J_k(n) > 0`: the Tate family has the sign `(−1)^{ω(n)}` of the number of distinct prime
  factors.
* **The order of vanishing at dimension zero is `ω(n)`** (`tendsto_jordanTotient_div_pow`):
  `J_k(n)/k^{ω(n)} → ∏_{p ∣ n} log p > 0` as `k → 0`.

So `k = 0` is a wall between two regimes: counts (positive) for `k > 0`, parity-signed values for
`k < 0`. An integer with `ω(n)` distinct primes enters the Taylor expansion of the Tate family only at
order `ω(n)`, with a coefficient of the sign `sign(k)^{ω(n)}`; the first jet `∂_kJ_k|₀ = Λ` sees exactly
the integers where the two regimes agree up to sign, `ω(n) = 1`, the prime powers. Weil's arithmetic
term is the derivative at the wall. This is the exact form of the identification of the
dimension-zero derivative with the parity barrier: positivity transported from `k > 0` to the first jet
must survive the parity sign that appears at `k < 0` in every coefficient with `ω(n) ≥ 2`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ ArithmeticDegenerationTheory
open scoped ArithmeticFunction.omega

/-- **Positive dimension is positive**: `J_k(n) > 0` for `k > 0`, `n ≥ 1`. -/
theorem jordanTotient_pos {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 1 ≤ n) : 0 < jordanTotient k n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [jordanTotient_prime_pow hp k ha]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (sub_pos.mpr (Real.one_lt_rpow hp1 hk))
  | zero => omega
  | one => rw [jordanTotient_one]; norm_num
  | coprime a b ha hb hab iha ihb =>
    have h := (isMultiplicative_jordanFun k).map_mul_of_coprime hab
    simp only [jordanFun_apply] at h
    rw [h]
    exact mul_pos (iha (by omega)) (ihb (by omega))

/-- **Negative dimension carries the parity**: `(−1)^{ω(n)} J_k(n) > 0` for `k < 0`, `n ≥ 1`. -/
theorem neg_one_pow_mul_jordanTotient_pos {k : ℝ} (hk : k < 0) {n : ℕ} (hn : 1 ≤ n) :
    0 < (-1 : ℝ) ^ ω n * jordanTotient k n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp ha.ne', jordanTotient_prime_pow hp k ha,
      pow_one]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have h1 : (p : ℝ) ^ k < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 hk
    have h2 : 0 < (p : ℝ) ^ (k * (a - 1 : ℕ)) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  | zero => omega
  | one => rw [jordanTotient_one, ArithmeticFunction.cardDistinctFactors_one]; norm_num
  | coprime a b ha hb hab iha ihb =>
    have h := (isMultiplicative_jordanFun k).map_mul_of_coprime hab
    simp only [jordanFun_apply] at h
    rw [h, ArithmeticFunction.cardDistinctFactors_mul hab, pow_add]
    have := mul_pos (iha (by omega)) (ihb (by omega))
    linarith [show (-1 : ℝ) ^ ω a * (-1) ^ ω b * (jordanTotient k a * jordanTotient k b) =
      (-1) ^ ω a * jordanTotient k a * ((-1) ^ ω b * jordanTotient k b) by ring]

/-- The product of the logarithms of the distinct prime factors. -/
def logRadical (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, Real.log p

theorem logRadical_pos {n : ℕ} : 0 < logRadical n :=
  Finset.prod_pos fun p hp => Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)

theorem logRadical_mul {a b : ℕ} (hab : a.Coprime b) :
    logRadical (a * b) = logRadical a * logRadical b := by
  rw [logRadical, Nat.Coprime.primeFactors_mul hab, Finset.prod_union hab.disjoint_primeFactors]
  rfl

/-- `(p^k − 1)/k → log p`. -/
theorem tendsto_rpow_sub_one_div {p : ℝ} (hp : 0 < p) :
    Tendsto (fun k : ℝ => (p ^ k - 1) / k) (𝓝[≠] 0) (𝓝 (Real.log p)) := by
  have h := (Real.hasStrictDerivAt_const_rpow hp 0).hasDerivAt.tendsto_slope_zero
  simp only [zero_add, Real.rpow_zero, one_mul, smul_eq_mul] at h
  refine h.congr fun k => ?_
  ring

/-- **The order of vanishing of the Tate family at dimension zero is `ω(n)`**:
`J_k(n)/k^{ω(n)} → ∏_{p∣n} log p` as `k → 0`. -/
theorem tendsto_jordanTotient_div_pow {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun k : ℝ => jordanTotient k n / k ^ ω n) (𝓝[≠] 0) (𝓝 (logRadical n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp ha.ne', pow_one]
    rw [logRadical, Nat.primeFactors_prime_pow ha.ne' hp, Finset.prod_singleton]
    have h1 : Tendsto (fun k : ℝ => (p : ℝ) ^ (k * (a - 1 : ℕ))) (𝓝[≠] 0) (𝓝 1) := by
      have hc : Continuous fun k : ℝ => (p : ℝ) ^ (k * (a - 1 : ℕ)) :=
        continuous_const.rpow (continuous_id.mul continuous_const) fun _ => Or.inl hp0.ne'
      have := hc.tendsto 0
      simp only [zero_mul, Real.rpow_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h := h1.mul (tendsto_rpow_sub_one_div hp0)
    rw [one_mul] at h
    refine h.congr fun k => ?_
    rw [jordanTotient_prime_pow hp k ha]
    ring
  | zero => omega
  | one =>
    simp only [jordanTotient_one, ArithmeticFunction.cardDistinctFactors_one, pow_zero, div_one,
      logRadical, Nat.primeFactors_one, Finset.prod_empty]
    exact tendsto_const_nhds
  | coprime a b ha hb hab iha ihb =>
    have h := (iha (by omega)).mul (ihb (by omega))
    rw [← logRadical_mul hab] at h
    refine h.congr fun k => ?_
    have hm := (isMultiplicative_jordanFun k).map_mul_of_coprime hab
    simp only [jordanFun_apply] at hm
    rw [hm, ArithmeticFunction.cardDistinctFactors_mul hab, pow_add, mul_div_mul_comm]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
