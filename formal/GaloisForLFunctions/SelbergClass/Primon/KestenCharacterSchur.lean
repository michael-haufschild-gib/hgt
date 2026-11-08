import GaloisForLFunctions.SelbergClass.Primon.SemicircleCharacters

/-!
# Character truncations realize arithmetic Schur renormalization

The even Chebyshev expansion of each prime likelihood has geometric
coefficients. Its finite projection Gram matrix is the arithmetic Schur
prefix, and its remainder Gram matrix is the exact geometric residual.
-/

open Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The first `N` even-character modes of the prime likelihood. -/
def kestenCharacterTruncation (p : Nat.Primes) (N : ℕ) : SemicircleL2 :=
  ∑ n ∈ Finset.range N, (p : ℝ)⁻¹ ^ n • spectralCharacterVector (2 * n)

/-- Pairing a likelihood with a character truncation gives the arithmetic Schur prefix. -/
theorem inner_likelihood_characterTruncation (p q : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenLikelihoodVector p) (kestenCharacterTruncation q N) =
      arithmeticSchurPrefixKernel N (primeReciprocal p) (primeReciprocal q) 1 1 := by
  simp only [kestenCharacterTruncation, inner_sum, inner_smul_right,
    inner_likelihood_spectralCharacter_even, arithmeticSchurPrefixKernel,
    arithmeticSchurValuationCoordinate, primeReciprocal, one_mul]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Character truncations realize the finite arithmetic Schur Gram kernel. -/
theorem inner_characterTruncation (p q : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenCharacterTruncation p N) (kestenCharacterTruncation q N) =
      arithmeticSchurPrefixKernel N (primeReciprocal p) (primeReciprocal q) 1 1 := by
  simp only [kestenCharacterTruncation, sum_inner, inner_smul_left, conj_trivial,
    inner_sum, inner_smul_right, inner_spectralCharacterVector,
    arithmeticSchurPrefixKernel, arithmeticSchurValuationCoordinate, one_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have he (i j : ℕ) : 2 * i = 2 * j ↔ i = j := by omega
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hn, if_true, primeReciprocal]
  ring

/-- Truncation removes exactly the first `N` even coordinates and preserves every later one. -/
theorem inner_characterResidual_evenCharacter (p : Nat.Primes) (N n : ℕ) :
    inner ℝ (kestenLikelihoodVector p - kestenCharacterTruncation p N)
        (spectralCharacterVector (2 * n)) =
      if n < N then 0 else (p : ℝ)⁻¹ ^ n := by
  rw [inner_sub_left, inner_likelihood_spectralCharacter_even]
  simp only [kestenCharacterTruncation, sum_inner, inner_smul_left, conj_trivial,
    inner_spectralCharacterVector]
  have he (i j : ℕ) : 2 * i = 2 * j ↔ i = j := by omega
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> ring

/-- The real Schur prefix kernel is symmetric. -/
private theorem schurPrefix_comm (p q : Nat.Primes) (N : ℕ) :
    arithmeticSchurPrefixKernel N (primeReciprocal p) (primeReciprocal q) 1 1 =
      arithmeticSchurPrefixKernel N (primeReciprocal q) (primeReciprocal p) 1 1 := by
  unfold arithmeticSchurPrefixKernel
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The actual spectral truncation error is exactly the geometric Schur residual. -/
theorem inner_likelihood_characterResidual (p q : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenLikelihoodVector p - kestenCharacterTruncation p N)
        (kestenLikelihoodVector q - kestenCharacterTruncation q N) =
      (primeReciprocal p * primeReciprocal q) ^ N /
        (1 - primeReciprocal p * primeReciprocal q) := by
  have hpq : primeReciprocal p * primeReciprocal q < primeReciprocal q := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right (primeReciprocal_lt_one p) (primeReciprocal_pos q)
  have hqr : primeReciprocal p * primeReciprocal q < 1 :=
    hpq.trans (primeReciprocal_lt_one q)
  have hs := arithmeticSchurKernel_sub_prefix_eq_residual N
    (primeReciprocal p) (primeReciprocal q) 1 1 (sub_ne_zero.mpr hqr.ne')
  have hc : inner ℝ (kestenCharacterTruncation p N) (kestenLikelihoodVector q) =
      arithmeticSchurPrefixKernel N (primeReciprocal p) (primeReciprocal q) 1 1 := by
    rw [real_inner_comm, inner_likelihood_characterTruncation, schurPrefix_comm]
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_kestenLikelihoodVector, inner_primeHardyKernel,
    inner_likelihood_characterTruncation, hc, inner_characterTruncation]
  simp only [arithmeticSchurKernel, mul_one] at hs
  calc
    _ = 1 / (1 - primeReciprocal p * primeReciprocal q) -
        arithmeticSchurPrefixKernel N (primeReciprocal p) (primeReciprocal q) 1 1 := by ring
    _ = _ := by simpa only [mul_one_div] using hs

/-- The squared `L²` truncation error is an exact geometric tail. -/
theorem norm_sq_kestenCharacterResidual (p : Nat.Primes) (N : ℕ) :
    ‖kestenLikelihoodVector p - kestenCharacterTruncation p N‖ ^ 2 =
      (primeReciprocal p ^ 2) ^ N / (1 - primeReciprocal p ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_likelihood_characterResidual]
  ring

/-- The even-character expansion converges to the actual likelihood in semicircle `L²`. -/
theorem tendsto_kestenCharacterTruncation (p : Nat.Primes) :
    Tendsto (kestenCharacterTruncation p) atTop (𝓝 (kestenLikelihoodVector p)) := by
  have hpq : primeReciprocal p * primeReciprocal p < primeReciprocal p := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right (primeReciprocal_lt_one p) (primeReciprocal_pos p)
  have h := tendsto_arithmeticSchur_residual_atTop
    (q := primeReciprocal p) (r := primeReciprocal p) (a := 1) (b := 1)
    (mul_nonneg (primeReciprocal_pos p).le (primeReciprocal_pos p).le)
    (hpq.trans (primeReciprocal_lt_one p))
  have hs : Tendsto (fun N =>
      ‖kestenLikelihoodVector p - kestenCharacterTruncation p N‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [← real_inner_self_eq_norm_sq, inner_likelihood_characterResidual]
    simpa only [arithmeticSchurKernel, mul_one, mul_one_div] using h
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, norm_sub_rev] using hs.sqrt
end
end GaloisForLFunctions.SelbergClass.Primon

