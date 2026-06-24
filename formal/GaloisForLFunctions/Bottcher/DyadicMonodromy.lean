/-
# Böttcher tower — Tier 3b (algebraic side): dyadic multipliers of unbounded order

The exact-Prüfer-monodromy theorem (`bottcher-exact-pruefer-monodromy.md`) produces,
around a depth-`n` Cantor cylinder, a monodromy multiplier `exp(2πi/2ⁿ)` — a primitive
`2ⁿ`-th root of unity. This file pins the purely algebraic content the disconnected
assembly needs from that: those multipliers have **unbounded order**, so the
`mono` hypothesis of `algIndep_of_unbounded_monodromy` has its order requirement met.

The remaining (analytic) half of `mono` — that continuation around the cylinder loop
is a field automorphism of the germ field fixing `φ_{c₂}` and scaling `φ_{c₁}` by this
multiplier — is the contour-integral / period content (T3a), built separately.
-/
import GaloisForLFunctions.Bottcher.AlgIndep
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Bottcher

/-- The depth-`n` dyadic monodromy multiplier `exp(2πi/2ⁿ)` is a primitive `2ⁿ`-th
root of unity; its order is exactly `2ⁿ`. -/
theorem orderOf_dyadicRoot (n : ℕ) :
    orderOf (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))) = 2 ^ n :=
  ((Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num))).eq_orderOf).symm

/-- The dyadic multipliers have **unbounded order**: for every bound `d` there is a
complex root of unity of order `> d`. This is the order half of the `mono` hypothesis
in `algIndep_of_unbounded_monodromy` (disconnected-case independence). -/
theorem exists_complex_orderOf_gt (d : ℕ) : ∃ ζ : ℂ, d < orderOf ζ := by
  refine ⟨Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ d : ℕ) : ℂ)), ?_⟩
  rw [orderOf_dyadicRoot]
  exact Nat.lt_two_pow_self

end Bottcher
