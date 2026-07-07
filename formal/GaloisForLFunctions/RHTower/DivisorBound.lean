/-
The divisor bound `d(n) ≪_ε n^ε`.

For every `ε > 0` there is a constant `C` with `d(n) = #divisors(n) ≤ C · n^ε` for all `n ≥ 1`.  This
is the classical estimate that upgrades the fourth-moment diagonal `∑_{n≤N} d(n)² n^{-2σ}` from
convergent-for-`σ>3/2` (the crude `d(n) ≤ n` bound) to convergent-for-`σ>1/2` — Carlson's actual
range — and is absent from mathlib (which has only `Nat.card_divisors_le_self`).

The proof is elementary and constant-explicit.  Writing `n = ∏ p^{a_p}` over its prime factors,
`d(n) = ∏ (a_p + 1)`.  For each prime `p ≥ 2` and the ratio `q = p^ε > 1`, Bernoulli's inequality
`1 + a(q−1) ≤ q^a` gives a per-prime bound `a + 1 ≤ C_p · (p^{a})^ε` with the explicit constant
`C_p = max(1, 2/(p^ε − 1))`.  Since `C_p = 1` once `p^ε ≥ 3`, only the finitely many "small" primes
`p < 3^{1/ε}` contribute, so `∏_p C_p ≤ ∏_{p ∈ S} C_p =: C` over the fixed finite set `S`, and
`∏_p (p^{a_p})^ε = n^ε`.
-/
import Mathlib

open Real Finset

namespace RHTower

/-- `(p^ε)^a = (p^a)^ε` for `p ≥ 1`. -/
theorem rpow_pow_comm (p : ℕ) (a : ℕ) (ε : ℝ) :
    ((p : ℝ) ^ ε) ^ a = ((p : ℝ) ^ (a : ℝ)) ^ ε := by
  rw [← Real.rpow_natCast ((p : ℝ) ^ ε) a, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), mul_comm]

/-- **Per-prime bound.**  For `q > 1`, `a + 1 ≤ max(1, 2/(q−1)) · q^a`: Bernoulli's inequality
`1 + a(q−1) ≤ q^a` controls the linear factor by the geometric one, with an explicit constant. -/
theorem succ_le_const_mul_pow {q : ℝ} (hq : 1 < q) (a : ℕ) :
    (a + 1 : ℝ) ≤ max 1 (2 / (q - 1)) * q ^ a := by
  have hbern : 1 + (a : ℝ) * (q - 1) ≤ q ^ a := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ q - 1) a
    simpa using this
  have hqa_pos : (0 : ℝ) < q ^ a := by positivity
  have hC1 : (1 : ℝ) ≤ max 1 (2 / (q - 1)) := le_max_left _ _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp only [Nat.cast_zero, pow_zero, mul_one]; linarith
  · -- a ≥ 1: use (a+1) ≤ (max ..)·(1 + a(q-1)) ≤ (max ..)·q^a
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hq1 : (0 : ℝ) < q - 1 := by linarith
    have key : (a + 1 : ℝ) ≤ max 1 (2 / (q - 1)) * (1 + (a : ℝ) * (q - 1)) := by
      have hC2 : 2 / (q - 1) ≤ max 1 (2 / (q - 1)) := le_max_right _ _
      -- (a+1) ≤ (2/(q-1))·(1 + a(q-1))  since  RHS ≥ (2/(q-1))·(a(q-1)) = 2a ≥ a+1
      have hlow : (2 / (q - 1)) * (1 + (a : ℝ) * (q - 1)) = 2 / (q - 1) + 2 * a := by
        field_simp
      calc (a + 1 : ℝ) ≤ 2 * a := by linarith
        _ ≤ 2 / (q - 1) + 2 * a := by
            have : (0 : ℝ) ≤ 2 / (q - 1) := by positivity
            linarith
        _ = (2 / (q - 1)) * (1 + (a : ℝ) * (q - 1)) := hlow.symm
        _ ≤ max 1 (2 / (q - 1)) * (1 + (a : ℝ) * (q - 1)) := by
            apply mul_le_mul_of_nonneg_right hC2; positivity
    calc (a + 1 : ℝ) ≤ max 1 (2 / (q - 1)) * (1 + (a : ℝ) * (q - 1)) := key
      _ ≤ max 1 (2 / (q - 1)) * q ^ a := by
          apply mul_le_mul_of_nonneg_left hbern; linarith

/-- The per-prime constant `C_p = max(1, 2/(p^ε − 1))`. -/
noncomputable def dvbConst (ε : ℝ) (p : ℕ) : ℝ := max 1 (2 / ((p : ℝ) ^ ε - 1))

theorem one_le_dvbConst (ε : ℝ) (p : ℕ) : 1 ≤ dvbConst ε p := le_max_left _ _

theorem zero_lt_dvbConst (ε : ℝ) (p : ℕ) : 0 < dvbConst ε p :=
  lt_of_lt_of_le one_pos (one_le_dvbConst ε p)

/-- For a prime `p`, `p^ε > 1`. -/
theorem one_lt_prime_rpow {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) : 1 < (p : ℝ) ^ ε := by
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  calc (1 : ℝ) = (1 : ℝ) ^ ε := (Real.one_rpow ε).symm
    _ < (p : ℝ) ^ ε := Real.rpow_lt_rpow zero_le_one h1 hε

/-- The per-prime bound in the divisor form: `a_p + 1 ≤ C_p · (p^{a_p})^ε`. -/
theorem succ_factorization_le {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    (a + 1 : ℝ) ≤ dvbConst ε p * ((p : ℝ) ^ (a : ℝ)) ^ ε := by
  have hq : 1 < (p : ℝ) ^ ε := one_lt_prime_rpow hp hε
  have := succ_le_const_mul_pow hq a
  rwa [rpow_pow_comm p a ε, ← dvbConst] at this

/-- **The divisor bound.**  For every `ε > 0` there is `C > 0` with `d(n) ≤ C · n^ε` for all `n ≥ 1`.
The constant is `C = ∏_{p < M, p prime} C_p` over the fixed finite set of small primes
`p < M = ⌊3^{1/ε}⌋ + 1`; each remaining prime has `C_p = 1`. -/
theorem card_divisors_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  set M : ℕ := ⌊(3 : ℝ) ^ (1 / ε)⌋₊ + 1 with hM
  set S : Finset ℕ := (Finset.range M).filter Nat.Prime with hS
  refine ⟨∏ p ∈ S, dvbConst ε p, Finset.prod_pos fun p _ => zero_lt_dvbConst ε p, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  set T : Finset ℕ := n.primeFactors.filter (fun p => (p : ℝ) ^ ε < 3) with hT
  -- Small primes dividing `n` lie in `S`.
  have hTS : T ⊆ S := by
    intro p hpT
    rw [hT, Finset.mem_filter] at hpT
    obtain ⟨hp, hlt⟩ := hpT
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, Nat.prime_of_mem_primeFactors hp⟩
    have hpε : (p : ℝ) < (3 : ℝ) ^ (1 / ε) := by
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ ε := by positivity
      have hlt' := Real.rpow_lt_rpow h0 hlt (by positivity : (0 : ℝ) < 1 / ε)
      rwa [← Real.rpow_mul (by positivity), mul_one_div, div_self (ne_of_gt hε),
        Real.rpow_one] at hlt'
    have hpM : (p : ℝ) < (M : ℝ) := lt_of_lt_of_le hpε (le_of_lt (by
      rw [hM]; push_cast; exact Nat.lt_floor_add_one _))
    exact_mod_cast hpM
  -- Large primes contribute a factor `C_p = 1`.
  have hlarge : ∀ p ∈ n.primeFactors, p ∉ T → dvbConst ε p = 1 := by
    intro p hp hpnot
    have h3 : 3 ≤ (p : ℝ) ^ ε := by
      by_contra h
      exact hpnot (by rw [hT, Finset.mem_filter]; exact ⟨hp, not_le.mp h⟩)
    rw [dvbConst, max_eq_left]
    rw [div_le_one (by linarith)]; linarith
  rw [Nat.card_divisors hn0]
  push_cast
  -- Step 1: termwise per-prime bound.
  have hstep1 : ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          dvbConst ε p * ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ)) ^ ε := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      exact succ_factorization_le (Nat.prime_of_mem_primeFactors hp).two_le hε _
  -- Step 2: `∏ p^{a_p} = n`.
  have hprodn : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ)) = (n : ℝ) := by
    have hnat : ∏ p ∈ n.primeFactors, (p : ℕ) ^ (n.factorization p) = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
    calc ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ))
        = ∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ) : ℝ)) := by
          apply Finset.prod_congr rfl; intro p _
          rw [Real.rpow_natCast]; push_cast; ring
      _ = ((∏ p ∈ n.primeFactors, (p : ℕ) ^ (n.factorization p) : ℕ) : ℝ) := by
          rw [Nat.cast_prod]
      _ = (n : ℝ) := by rw [hnat]
  -- Step 3: the constant product over `n`'s primes is at most the one over `S`.
  have hconst : ∏ p ∈ n.primeFactors, dvbConst ε p ≤ ∏ p ∈ S, dvbConst ε p := by
    have hrestrict : ∏ p ∈ n.primeFactors, dvbConst ε p = ∏ p ∈ T, dvbConst ε p :=
      (Finset.prod_subset (Finset.filter_subset _ _)
        (fun p hp hpnot => hlarge p hp hpnot)).symm
    rw [hrestrict]
    have hsplit := Finset.prod_sdiff (f := dvbConst ε) hTS
    have hge1 : (1 : ℝ) ≤ ∏ p ∈ S \ T, dvbConst ε p := by
      calc (1 : ℝ) = ∏ _p ∈ S \ T, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ p ∈ S \ T, dvbConst ε p :=
          Finset.prod_le_prod (fun p _ => zero_le_one) (fun p _ => one_le_dvbConst ε p)
    have hTpos : (0 : ℝ) ≤ ∏ p ∈ T, dvbConst ε p :=
      Finset.prod_nonneg (fun p _ => (zero_lt_dvbConst ε p).le)
    calc ∏ p ∈ T, dvbConst ε p
        ≤ (∏ p ∈ S \ T, dvbConst ε p) * ∏ p ∈ T, dvbConst ε p :=
          le_mul_of_one_le_left hTpos hge1
      _ = ∏ p ∈ S, dvbConst ε p := hsplit
  -- Assemble.
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          dvbConst ε p * ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ)) ^ ε := hstep1
    _ = (∏ p ∈ n.primeFactors, dvbConst ε p)
          * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ)) ^ ε :=
        Finset.prod_mul_distrib
    _ = (∏ p ∈ n.primeFactors, dvbConst ε p)
          * (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ((n.factorization p : ℕ) : ℝ))) ^ ε := by
        rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    _ = (∏ p ∈ n.primeFactors, dvbConst ε p) * (n : ℝ) ^ ε := by rw [hprodn]
    _ ≤ (∏ p ∈ S, dvbConst ε p) * (n : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hconst (by positivity)

end RHTower
