import GaloisForLFunctions.RHTower.Sieve.LogMoebiusBounded

/-!
# The squarefree totient divisor identity

The function `f(n) = μ²(n)/φ(n)` is multiplicative, and so is `n ↦ n/φ(n)`; on a prime power `p^i`
with `i ≥ 1` both equal `p/(p−1)`, since the divisors of `p^i` contribute only `d = 1` and `d = p`
to the first sum.  Hence

`∑_{d ∣ n} μ²(d)/φ(d) = n/φ(n)`.

This is the identity that converts a `1/φ` weight into a `1/n` weight at the cost of one divisor
convolution, and it is what makes `∑_{e ≤ N} 1/φ(e)` comparable with `log N`.
-/

open ArithmeticFunction Finset

namespace RHTower.Sieve

theorem not_squarefree_zero : ¬ Squarefree (0 : ℕ) := by
  intro h
  have := h 0 ⟨0, rfl⟩
  simp at this

/-- `μ²(n)/φ(n)`: the reciprocal totient supported on the squarefree integers. -/
noncomputable def sqfreeTotientInv : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then 1 / (Nat.totient n : ℝ) else 0, by
    simp⟩

theorem sqfreeTotientInv_apply (n : ℕ) :
    sqfreeTotientInv n = if Squarefree n then 1 / (Nat.totient n : ℝ) else 0 := rfl

/-- `n/φ(n)`. -/
noncomputable def totientRatio : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) / (Nat.totient n : ℝ), by simp⟩

theorem totientRatio_apply (n : ℕ) :
    totientRatio n = (n : ℝ) / (Nat.totient n : ℝ) := rfl

theorem isMultiplicative_sqfreeTotientInv : sqfreeTotientInv.IsMultiplicative := by
  constructor
  · rw [sqfreeTotientInv_apply]
    simp
  · intro m n hmn
    rw [sqfreeTotientInv_apply, sqfreeTotientInv_apply, sqfreeTotientInv_apply]
    by_cases hsq : Squarefree (m * n)
    · obtain ⟨-, hm, hn⟩ := Nat.squarefree_mul_iff.mp hsq
      have hm0 : m ≠ 0 := fun h => not_squarefree_zero (h ▸ hm)
      have hn0 : n ≠ 0 := fun h => not_squarefree_zero (h ▸ hn)
      have hφm : (0 : ℝ) < (Nat.totient m : ℝ) := by
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
        exact_mod_cast this
      have hφn : (0 : ℝ) < (Nat.totient n : ℝ) := by
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
        exact_mod_cast this
      rw [if_pos hsq, if_pos hm, if_pos hn, Nat.totient_mul hmn]
      push_cast
      field_simp
    · rw [if_neg hsq]
      have hsplit : ¬ Squarefree m ∨ ¬ Squarefree n := by
        by_cases hm : Squarefree m
        · exact Or.inr fun hn => hsq (Nat.squarefree_mul_iff.mpr ⟨hmn, hm, hn⟩)
        · exact Or.inl hm
      rcases hsplit with h | h
      · rw [if_neg h, zero_mul]
      · rw [if_neg h, mul_zero]

theorem isMultiplicative_totientRatio : totientRatio.IsMultiplicative := by
  constructor
  · rw [totientRatio_apply]
    simp
  · intro m n hmn
    rw [totientRatio_apply, totientRatio_apply, totientRatio_apply]
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hφm : (0 : ℝ) < (Nat.totient m : ℝ) := by
      have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
      exact_mod_cast this
    have hφn : (0 : ℝ) < (Nat.totient n : ℝ) := by
      have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
      exact_mod_cast this
    rw [Nat.totient_mul hmn]
    push_cast
    field_simp

/-- **The squarefree totient divisor identity.** -/
theorem zeta_mul_sqfreeTotientInv :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * sqfreeTotientInv
      = totientRatio := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_zeta.natCast.mul isMultiplicative_sqfreeTotientInv) _
    isMultiplicative_totientRatio).mpr ?_
  intro p i hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp, totientRatio_apply]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [sqfreeTotientInv_apply]
  · have hsub : Finset.range 2 ⊆ Finset.range (i + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hvanish : ∀ x ∈ Finset.range (i + 1), x ∉ Finset.range 2 →
        sqfreeTotientInv (p ^ x) = 0 := by
      intro x _ hx
      have hx2 : 2 ≤ x := by
        simp only [Finset.mem_range, not_lt] at hx
        exact hx
      rw [sqfreeTotientInv_apply, if_neg]
      intro hsq
      have hdvd : p * p ∣ p ^ x := by
        have : p ^ 2 ∣ p ^ x := pow_dvd_pow p hx2
        simpa [pow_two] using this
      have := hsq p hdvd
      rw [Nat.isUnit_iff] at this
      exact hp.ne_one this
    rw [← Finset.sum_subset hsub hvanish]
    have h0 : sqfreeTotientInv (p ^ 0) = 1 := by
      simp [sqfreeTotientInv_apply]
    have h1 : sqfreeTotientInv (p ^ 1) = 1 / ((p : ℝ) - 1) := by
      rw [pow_one, sqfreeTotientInv_apply, if_pos hp.squarefree, Nat.totient_prime hp]
      congr 1
      have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      rw [this]
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    rw [Nat.totient_prime_pow hp hi]
    have hcast : ((p ^ (i - 1) * (p - 1) : ℕ) : ℝ) = (p : ℝ) ^ (i - 1) * ((p : ℝ) - 1) := by
      push_cast [Nat.cast_sub hp.one_lt.le]
      ring
    rw [hcast]
    have hpow : (p : ℝ) ^ i = (p : ℝ) ^ (i - 1) * (p : ℝ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [Nat.cast_pow, hpow]
    have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hne2 : (p : ℝ) ^ (i - 1) ≠ 0 := by positivity
    field_simp
    ring

/-- **The divisor form.**  For every `n ≥ 1`, `∑_{d ∣ n} μ²(d)/φ(d) = n/φ(n)`. -/
theorem sum_divisors_sqfreeTotientInv (n : ℕ) :
    ∑ d ∈ n.divisors, (if Squarefree d then 1 / (Nat.totient d : ℝ) else 0)
      = (n : ℝ) / (Nat.totient n : ℝ) := by
  have h : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      * sqfreeTotientInv) n = totientRatio n := by
    rw [zeta_mul_sqfreeTotientInv]
  rw [coe_zeta_mul_apply, totientRatio_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => rfl

end RHTower.Sieve
