import GaloisForLFunctions.RHTower.Sieve.GhsInnerFirstMoment
/-!
# The support of a convolution

A nonzero coefficient of `a ⍟ b` at `k` forces a factorisation `k = de` with both factors in the supports of `a` and
`b`.  So a convolution of two sequences supported in `[1, M]` is supported in `[1, M²]`, and a convolution of two
prime-supported sequences is carried by the products of two primes.

This is what makes the product of the two prime polynomials of the Granville–Harper–Soundararajan convolution a
single finitely supported Dirichlet series — `L(a,s)L(b,s) = L(a ⍟ b, s)` — to which the large-values first moment
applies directly, with no Cauchy–Schwarz splitting and no trivial size of either factor.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The support of a convolution, with independent bounds.**  A nonzero coefficient of `a ⍟ b` at `k`
forces a factorisation `k = de` with `d` in the support of `a` and `e` in that of `b`, so a convolution of
sequences supported in `[1, M]` and `[1, L]` is supported in `[1, ML]`. -/
theorem convolution_mem_Icc_of_support_mul {a b : ℕ → ℂ} {M L : ℕ}
    (ha : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k : ℕ, b k ≠ 0 → k ∈ Finset.Icc 1 L)
    {k : ℕ} (hk : (LSeries.convolution a b) k ≠ 0) : k ∈ Finset.Icc 1 (M * L) := by
  classical
  rw [LSeries.convolution_def] at hk
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hane : a x.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxne
    exact hxne rfl
  have hbne : b x.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxne
    exact hxne rfl
  have h1 := Finset.mem_Icc.1 (ha x.1 hane)
  have h2 := Finset.mem_Icc.1 (hb x.2 hbne)
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · rw [← hx.1]
    have h1' : 1 ≤ x.1 := h1.1
    have h2' : 1 ≤ x.2 := h2.1
    exact Nat.one_le_iff_ne_zero.2 (by omega)
  · rw [← hx.1]
    exact Nat.mul_le_mul h1.2 h2.2

/-- The equal-bound case: a convolution of two sequences supported in `[1, M]` is supported in `[1, M²]`. -/
theorem convolution_mem_Icc_of_support {a b : ℕ → ℂ} {M : ℕ}
    (ha : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k : ℕ, b k ≠ 0 → k ∈ Finset.Icc 1 M)
    {k : ℕ} (hk : (LSeries.convolution a b) k ≠ 0) : k ∈ Finset.Icc 1 (M * M) :=
  convolution_mem_Icc_of_support_mul ha hb hk

/-- The convolution of two prime-supported sequences is supported on the products of two primes. -/
theorem convolution_support_prime_mul {a b : ℕ → ℂ}
    (ha : ∀ k : ℕ, a k ≠ 0 → Nat.Prime k) (hb : ∀ k : ℕ, b k ≠ 0 → Nat.Prime k)
    {k : ℕ} (hk : (LSeries.convolution a b) k ≠ 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ k = p * q := by
  classical
  rw [LSeries.convolution_def] at hk
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hane : a x.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxne
    exact hxne rfl
  have hbne : b x.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxne
    exact hxne rfl
  exact ⟨x.1, x.2, ha x.1 hane, hb x.2 hbne, hx.1.symm⟩

end RHTower.Sieve
end
