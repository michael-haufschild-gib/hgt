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

namespace Bottcher

/-- Named depth-`n` dyadic Prüfer multiplier. -/
noncomputable def dyadicRoot (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ n : ℕ) : ℂ))

/-- The named depth-`n` dyadic Prüfer multiplier has exact order `2^n`. -/
theorem orderOf_dyadicRoot_named (n : ℕ) : orderOf (dyadicRoot n) = 2 ^ n := by
  unfold dyadicRoot
  exact orderOf_dyadicRoot n

/-- The exact Prüfer tower is coherent: the next depth multiplier squares to the current one. -/
theorem dyadicRoot_succ_sq (n : ℕ) : dyadicRoot (n + 1) ^ 2 = dyadicRoot n := by
  unfold dyadicRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hpow : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  field_simp [pow_succ, hpow]
  exact_mod_cast (show 2 * 2 ^ n = 2 ^ (n + 1) by rw [pow_succ'])

/-- Every named depth-`n` dyadic Prüfer multiplier has a square root at depth `n+1`, again with exact
Prüfer order. -/
theorem dyadicRoot_square_root (n : ℕ) :
    ∃ η : ℂ, η ^ 2 = dyadicRoot n ∧ orderOf η = 2 ^ (n + 1) :=
  ⟨dyadicRoot (n + 1), dyadicRoot_succ_sq n, orderOf_dyadicRoot_named (n + 1)⟩

end Bottcher
