import GaloisForLFunctions.RHTower.Sieve.DirichletUniformTailBound

/-!
# The Littlewood shape, packaged

Every structural step of the estimate is now a theorem, so the whole chain can be stated once: five
checkable hypotheses per dyadic block above the split point, and the conclusion

```text
‖∑_{n < A·2^R} n^(-1-it)‖ ≤ (1 + log (A·2^S - 1)) + (R - S)·ε.
```

The first four hypotheses are the schedule conditions of the `k`-th derivative test at the classical
scale; the fifth is the depth criterion that turns the block saving into the uniform bound `ε`.
Nothing else about `t`, the orders `k r`, or the split point enters.
-/

namespace RHTower.Sieve

open Finset

/-- **Littlewood shape.**  With an order schedule meeting the classical-scale conditions and the
depth criterion on every dyadic block above the split point, the partial sum on the line
`Re s = 1` obeys a harmonic term plus a count of blocks times the uniform saving. -/
theorem norm_dirichlet_partial_littlewood_shape {t : ℝ} (ht : 0 < t) {A S R : ℕ} (hA : 1 ≤ A)
    (hSR : S ≤ R) (k : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε)
    (hk : ∀ r, S ≤ r → r < R → 2 ≤ k r)
    (hfac : ∀ r, S ≤ r → r < R → Nat.factorial (k r - 1) ≤ A * 2 ^ r)
    (hlow : ∀ r, S ≤ r → r < R → 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r, S ≤ r → r < R →
      t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
        * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeep : ∀ r, S ≤ r → r < R →
      3 * (2 : ℝ) ^ (k r) * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  refine norm_dirichlet_partial_two_regime_uniform hA hSR fun r hrS hrR => ?_
  have hN : 1 ≤ A * 2 ^ r := by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  have hspan : A * 2 ^ (r + 1) = 2 * (A * 2 ^ r) := by ring
  rw [hspan]
  refine le_trans
    (dirichlet_block_saving_of_small_factorial ht hN (by omega) (by omega) (hk r hrS hrR)
      (hfac r hrS hrR) (hlow r hrS hrR) (hhigh r hrS hrR)) ?_
  exact block_saving_le_of_log_ge hN hε (hdeep r hrS hrR)

end RHTower.Sieve
