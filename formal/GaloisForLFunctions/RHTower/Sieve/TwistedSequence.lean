import GaloisForLFunctions.RHTower.Sieve.TwistTransfer

/-!
# The twisted sequence

The exceptional frequency of Halász's theorem is removed by twisting: `g(n) = f(n)n^{−iτ}`.  The twist
preserves everything the theorem asks of `f` — complete multiplicativity, the value at `1`, the bound
`‖g‖ ≤ 1` — and it moves the distance: `g` is close to the trivial character exactly when `f` is close to
`n^{iτ}`.  The original partial sum is recovered from the twisted ones through the transfer of
`TwistTransfer.lean`, so a bound proved under a *uniform* distance hypothesis for `g` becomes a bound for
`f` at the cost of `1 + |τ| log N`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex

/-- A sequence twisted by the character `n^{−iτ}`. -/
def twistSeq (f : ℕ → ℂ) (τ : ℝ) : ℕ → ℂ := fun n => f n * (n : ℂ) ^ (-(τ : ℂ) * I)

theorem twistSeq_apply (f : ℕ → ℂ) (τ : ℝ) (n : ℕ) :
    twistSeq f τ n = f n * (n : ℂ) ^ (-(τ : ℂ) * I) := rfl

/-- The twist has modulus one on the positive integers, so it preserves a bound on the coefficients. -/
theorem norm_twistSeq_le {f : ℕ → ℂ} {B : ℝ} (hf : ∀ n, ‖f n‖ ≤ B) (hB : 0 ≤ B) (τ : ℝ) (n : ℕ) :
    ‖twistSeq f τ n‖ ≤ B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases eq_or_ne τ 0 with rfl | hτ
    · rw [twistSeq]
      simp only [Nat.cast_zero, Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero,
        mul_one]
      exact hf 0
    · rw [twistSeq]
      have hw : (-(τ : ℂ) * I) ≠ 0 := by
        refine mul_ne_zero (neg_ne_zero.2 ?_) Complex.I_ne_zero
        exact_mod_cast hτ
      rw [Nat.cast_zero, Complex.zero_cpow hw, mul_zero, norm_zero]
      exact hB
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hphase : ‖((n : ℂ)) ^ (-(τ : ℂ) * I)‖ = 1 := by
      have hre : (-(τ : ℂ) * I).re = 0 := by simp
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hnR, hre,
        Real.rpow_zero]
    rw [twistSeq, norm_mul, hphase, mul_one]
    exact hf n

theorem twistSeq_one (f : ℕ → ℂ) (τ : ℝ) : twistSeq f τ 1 = f 1 := by
  rw [twistSeq]
  simp

/-- The twist of a completely multiplicative sequence is completely multiplicative. -/
theorem twistSeq_mul {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (τ : ℝ) (a b : ℕ) :
    twistSeq f τ (a * b) = twistSeq f τ a * twistSeq f τ b := by
  rw [twistSeq, twistSeq, twistSeq, hf a b]
  have hcpow : ((a * b : ℕ) : ℂ) ^ (-(τ : ℂ) * I)
      = ((a : ℂ)) ^ (-(τ : ℂ) * I) * ((b : ℂ)) ^ (-(τ : ℂ) * I) := by
    have h := Complex.mul_cpow_ofReal_nonneg (a := (a : ℝ)) (b := (b : ℝ))
      (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-(τ : ℂ) * I)
    rw [← Complex.ofReal_natCast a, ← Complex.ofReal_natCast b, ← Complex.ofReal_mul] at *
    rw [← h]
    congr 2
    push_cast
    ring
  rw [hcpow]
  ring

/-- Untwisting recovers the original sequence on the positive integers. -/
theorem twistSeq_mul_cpow (f : ℕ → ℂ) (τ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    twistSeq f τ n * (n : ℂ) ^ ((τ : ℂ) * I) = f n := by
  have hn0 : ((n : ℂ)) ≠ 0 := by
    have : (0 : ℕ) < n := hn
    exact_mod_cast Nat.cast_ne_zero.2 (by omega)
  have hne : ((n : ℂ)) ^ ((τ : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn0)
  rw [twistSeq, show (-(τ : ℂ) * I) = -((τ : ℂ) * I) by ring, Complex.cpow_neg]
  field_simp

/-- The partial sums of a sequence are the twisted partial sums against the twist. -/
theorem sum_Icc_eq_sum_twistSeq_mul_cpow (f : ℕ → ℂ) (τ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n)
      = ∑ n ∈ Finset.Icc 1 N, twistSeq f τ n * (n : ℂ) ^ ((τ : ℂ) * I) :=
  Finset.sum_congr rfl fun _ hn => (twistSeq_mul_cpow f τ (Finset.mem_Icc.1 hn).1).symm

/-- **The exceptional frequency, removed.**  A bound valid for every partial sum of the twisted sequence
bounds the original partial sum at the cost of `1 + |τ| log N`.  This is what makes a mean value estimate
proved under a uniform distance hypothesis applicable to a function close to a character. -/
theorem norm_sum_Icc_le_of_twisted_bound {f : ℕ → ℂ} (τ : ℝ) {N : ℕ} {S : ℝ}
    (hS : ∀ m : ℕ, m ≤ N → ‖∑ n ∈ Finset.Icc 1 m, twistSeq f τ n‖ ≤ S) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ (1 + |τ| * Real.log N) * S := by
  rw [sum_Icc_eq_sum_twistSeq_mul_cpow f τ N]
  exact norm_sum_Icc_mul_cpow_mul_I_le hS

end RHTower.Sieve
end
