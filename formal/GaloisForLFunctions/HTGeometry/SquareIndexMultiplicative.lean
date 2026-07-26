import Mathlib

/-!
# The square-index restriction of a multiplicative function

If `f` is multiplicative then so is `n ↦ f (n ^ 2)`, because coprimality is preserved by squaring.
Consequently the Dirichlet series `∑ₙ f(n²) n^(-s)` has an Euler product, and its logarithm is
`∑_p f(p²) p^(-s)` up to a series supported on prime powers `p^k`, `k ≥ 2`, which converges in
`Re s > 1/2` whenever `f(n) ≪ n^ε`.

For `f = a_F` the coefficients of an element of the Selberg class this says: the prime-square
logarithmic density `∑_{p ≤ x} a_F(p²)/p` is the polar datum at `s = 1` of the single Dirichlet
series `∑ₙ a_F(n²) n^(-s)`, whose local factor at `p` is the even part
`(F_p(X) + F_p(-X))/2` of the Euler factor of `F`, evaluated at `X = p^(-s/2)`.  That series
satisfies the Dirichlet-series, Ramanujan and Euler-product axioms of the Selberg class outright;
only the analytic continuation and the functional equation are missing.
-/

namespace HTGeometry

open ArithmeticFunction

/-- **Square-index restriction preserves multiplicativity.** -/
theorem isMultiplicative_comp_sq {R : Type*} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (1 : R) = f 1 ∧ ∀ {m n : ℕ}, Nat.Coprime m n → f ((m * n) ^ 2) = f (m ^ 2) * f (n ^ 2) := by
  refine ⟨hf.1.symm, ?_⟩
  intro m n hmn
  rw [mul_pow]
  exact hf.2 (Nat.Coprime.pow 2 2 hmn)

/-- The value at `1` is unchanged: `f (1 ^ 2) = 1`. -/
theorem comp_sq_one {R : Type*} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) : f (1 ^ 2) = 1 := by
  simpa using hf.1

/-- Coprimality of squares, the only arithmetic input. -/
theorem coprime_sq_sq {m n : ℕ} (h : Nat.Coprime m n) : Nat.Coprime (m ^ 2) (n ^ 2) :=
  Nat.Coprime.pow 2 2 h

end HTGeometry
