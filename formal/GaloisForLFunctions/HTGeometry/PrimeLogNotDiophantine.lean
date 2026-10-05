import GaloisForLFunctions.HTGeometry.DirichletBoxLinearForm

/-!
# The prime logarithms are not polynomially Diophantine over unbounded support

Let `p₀ < p₁ < …` be the primes.  By Bertrand's postulate `p_{n+1} ≤ 2 p_n`, so `p_n ≤ 2^{n+1}` and
`Σ_{i<s} log p_i ≤ s²`, which is `o(3^s)`.  Dirichlet's box principle for `s` logarithms with entries
bounded by `2` (`not_polynomially_diophantine`) then gives, for every `γ > 0` and every exponent
`κ`, a nonzero mode `m` with `H(m) = 3` and `|Σ m_i log p_i| < γ 3^{−κ}`: no fixed-exponent
Diophantine condition holds for `(log p)_∞` once the support size is free.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **Bertrand's postulate for consecutive primes.** -/
theorem nth_prime_succ_le_two_mul (n : ℕ) : Nat.nth Nat.Prime (n + 1) ≤ 2 * Nat.nth Nat.Prime n := by
  set p := Nat.nth Nat.Prime n with hp
  have hp0 : p ≠ 0 := (Nat.prime_nth_prime n).ne_zero
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp0
  have hcount : Nat.count Nat.Prime (p + 1) = n + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOf_prime, if_pos
      (Nat.prime_nth_prime n)]
  have hcq : n + 1 < Nat.count Nat.Prime (q + 1) := by
    have hmono : Nat.count Nat.Prime (p + 1) ≤ Nat.count Nat.Prime q :=
      Nat.count_monotone _ (by omega)
    have hlt : Nat.count Nat.Prime q < Nat.count Nat.Prime (q + 1) :=
      Nat.count_lt_count_succ_iff.mpr hq
    omega
  have := Nat.nth_lt_of_lt_count hcq
  omega

theorem nth_prime_le_two_pow (n : ℕ) : Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => rw [Nat.nth_prime_zero_eq_two]; norm_num
  | succ n ih =>
      calc Nat.nth Nat.Prime (n + 1) ≤ 2 * Nat.nth Nat.Prime n := nth_prime_succ_le_two_mul n
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1 + 1) := by ring

theorem log_nth_prime_le (n : ℕ) : Real.log (Nat.nth Nat.Prime n) ≤ n + 1 := by
  have hp : (0 : ℝ) < Nat.nth Nat.Prime n := by exact_mod_cast (Nat.prime_nth_prime n).pos
  calc Real.log (Nat.nth Nat.Prime n) ≤ Real.log ((2 : ℝ) ^ (n + 1)) :=
        Real.log_le_log hp (by exact_mod_cast nth_prime_le_two_pow n)
    _ = (n + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    _ ≤ n + 1 := by
        have := Real.log_two_lt_d9
        have : (0 : ℝ) ≤ n + 1 := by positivity
        nlinarith

/-- `Σ_{i<s} log p_i` is `o(3^s)`. -/
theorem tendsto_sum_log_nth_prime_div :
    Tendsto (fun s : ℕ => (∑ i ∈ Finset.range s, Real.log (Nat.nth Nat.Prime i)) /
      ((3 : ℝ) ^ s - 1)) atTop (𝓝 0) := by
  have hpow := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1 : ℝ) < 3 by norm_num)
  have hmaj : Tendsto (fun s : ℕ => 2 * ((s : ℝ) ^ 2 / (3 : ℝ) ^ s) + 2 * (1 / (3 : ℝ) ^ s))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℕ => 1 / (3 : ℝ) ^ s) atTop (𝓝 0) := by
      simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
        (by norm_num : (1 : ℝ) / 3 < 1) |>.congr fun s => by rw [one_div_pow, one_div]
    simpa using (hpow.const_mul 2).add (h1.const_mul 2)
  refine squeeze_zero' (Eventually.of_forall fun s => ?_) ?_ hmaj
  · refine div_nonneg (Finset.sum_nonneg fun i _ => Real.log_nonneg ?_) ?_
    · exact_mod_cast (Nat.prime_nth_prime i).one_lt.le
    · have : (1 : ℝ) ≤ 3 ^ s := one_le_pow₀ (by norm_num)
      linarith
  · filter_upwards [eventually_ge_atTop 1] with s hs
    have h3 : (0 : ℝ) < 3 ^ s := by positivity
    have h31 : (3 : ℝ) ^ s / 2 ≤ 3 ^ s - 1 := by
      have : (3 : ℝ) ≤ 3 ^ s := by
        calc (3 : ℝ) = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ s := pow_le_pow_right₀ (by norm_num) hs
      linarith
    have hsum : ∑ i ∈ Finset.range s, Real.log (Nat.nth Nat.Prime i) ≤ (s : ℝ) ^ 2 + 1 := by
      calc ∑ i ∈ Finset.range s, Real.log (Nat.nth Nat.Prime i)
          ≤ ∑ i ∈ Finset.range s, ((i : ℝ) + 1) :=
            Finset.sum_le_sum fun i _ => log_nth_prime_le i
        _ ≤ ∑ _i ∈ Finset.range s, (s : ℝ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have : (i : ℝ) + 1 ≤ s := by
              have := Finset.mem_range.mp hi
              exact_mod_cast this
            exact this
        _ = (s : ℝ) ^ 2 := by simp [sq]
        _ ≤ (s : ℝ) ^ 2 + 1 := by linarith
    have hnum0 : 0 ≤ ∑ i ∈ Finset.range s, Real.log (Nat.nth Nat.Prime i) :=
      Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (Nat.prime_nth_prime i).one_lt.le)
    calc (∑ i ∈ Finset.range s, Real.log (Nat.nth Nat.Prime i)) / ((3 : ℝ) ^ s - 1)
        ≤ ((s : ℝ) ^ 2 + 1) / ((3 : ℝ) ^ s / 2) :=
          div_le_div₀ (by positivity) hsum (by positivity) h31
      _ = 2 * ((s : ℝ) ^ 2 / (3 : ℝ) ^ s) + 2 * (1 / (3 : ℝ) ^ s) := by field_simp

/-- **`(log p)_∞` is not polynomially Diophantine.**  For every `γ > 0` and every exponent `κ`
there is a nonzero integer mode `m` on the first `s` primes, with entries bounded by `2` (so
`H(m) = 3`), and `|Σ m_i log p_i| < γ 3^{−κ}`. -/
theorem primeLog_not_polynomially_diophantine {γ : ℝ} (hγ : 0 < γ) (κ : ℕ) :
    ∃ (s : ℕ) (m : Fin s → ℤ), 0 < s ∧ m ≠ 0 ∧ (∀ i, |m i| ≤ 2) ∧
      |∑ i, (m i : ℝ) * Real.log (Nat.nth Nat.Prime (i : ℕ))| < γ * (3 : ℝ) ^ (-(κ : ℤ)) :=
  not_polynomially_diophantine (ℓ := fun i => Real.log (Nat.nth Nat.Prime i))
    (fun i => Real.log_nonneg (by exact_mod_cast (Nat.prime_nth_prime i).one_lt.le))
    tendsto_sum_log_nth_prime_div hγ κ

end GaloisForLFunctions.HTGeometry
