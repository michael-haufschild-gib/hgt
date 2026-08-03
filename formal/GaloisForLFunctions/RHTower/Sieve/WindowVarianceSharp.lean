import GaloisForLFunctions.RHTower.Sieve.WindowMultiplicity

/-!
# The trivial variance bound is attained

For the constant sequence every window sum is `L`, so

`∑_{x < X} ‖∑_{x < n ≤ x+L} 1‖² = X L²`,

while the general bound `sum_normSq_window_le` gives `L² ∑_{n < X+L+1} ‖1‖² = L²(X+L+1)`.  The two
agree up to the boundary factor `(X+L+1)/X`, so no coefficient-free improvement of the trivial bound
is possible.

Any saving must therefore use arithmetic properties of the coefficients — it cannot come from a
sharper treatment of the windows.  Together with the exactness of the overlap kernel this closes off
the non-arithmetic routes entirely.
-/

namespace RHTower.Sieve

open Finset

/-- Every window of length `L` carries mass `L` for the constant sequence. -/
theorem sum_window_one (x L : ℕ) : ∑ _n ∈ Finset.Ioc x (x + L), (1 : ℂ) = (L : ℂ) := by
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  simp

/-- **The trivial variance bound is attained by the constant sequence.** -/
theorem sum_normSq_window_one (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ _n ∈ Finset.Ioc x (x + L), (1 : ℂ)‖ ^ 2 = (X : ℝ) * (L : ℝ) ^ 2 := by
  have hterm : ∀ x ∈ Finset.range X,
      ‖∑ _n ∈ Finset.Ioc x (x + L), (1 : ℂ)‖ ^ 2 = (L : ℝ) ^ 2 := by
    intro x _
    rw [sum_window_one, Complex.norm_natCast]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end RHTower.Sieve
