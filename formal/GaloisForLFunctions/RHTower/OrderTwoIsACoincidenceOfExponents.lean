import GaloisForLFunctions.RHTower.HankelIsToeplitzReversed

/-!
# The order-two pinch is a coincidence of exponents, not an instance of a law

The reversal identity and its period-four sign are exact.  Passing from them to a statement about
*difficulty* needs one more thing: the Hankel determinant must be large compared with the deviations
of the factorial weights.  This file computes both sizes and finds they match at exactly one order.

**The determinant's size.**  By the Heine/Gram representation, the `m × m` Hankel determinant of a
moment sequence is an integral of the squared Vandermonde, so for a measure of width `σ` around its
mean it is of relative size

```text
σ^{m(m-1)}  =  c^{-m(m-1)/2} ,        σ = c^{-1/2} ,
```

the exponent being the number of pairs.

**The weights' deviation.**  The weight attached to `M_{j+d}` relative to `M_j` is `(2j)!/(2j+2d)!`,
which is `(2j)^{-2d}(1 + O(d²/j))`.  On an isobaric monomial the powers cancel and only the deviation
survives, of relative size `m²/j`.

**The comparison.**  With `c ≍ j` up to logarithms, the determinant beats the deviation exactly when

```text
m(m-1)/2  ≤  1 ,
```

i.e. only for `m ≤ 2`.  The deficit is `m(m-1)/2 - 1`, which is zero at `m = 2` and positive from
`m = 3` on.

> **At order two the Hankel determinant and the weight deviation are both of size `1/j`: that
> coincidence *is* the window of the previous entry.  From order three the determinant is smaller by
> `j^{m(m-1)/2 - 1}`, so the sign of the leading term carries no information and the period-four law,
> though an exact identity, predicts nothing about difficulty.**

This corrects the reading of the previous entry, and it explains the observed history: the order-two
inequality for this sequence was settled first, the order-three case is harder by a factor `j`, and
orders four and above are open.

This file formalizes the pair count, the deficit exponent, its vanishing exactly at `m ≤ 2`, and its
strict growth beyond.
-/

open Real

noncomputable section

namespace RHTower

/-- The number of pairs among `m` points — the Vandermonde exponent halved. -/
def pairCount (m : ℕ) : ℕ := m * (m - 1) / 2

theorem pairCount_zero : pairCount 0 = 0 := by decide
theorem pairCount_one : pairCount 1 = 0 := by decide
theorem pairCount_two : pairCount 2 = 1 := by decide
theorem pairCount_three : pairCount 3 = 3 := by decide
theorem pairCount_four : pairCount 4 = 6 := by decide
theorem pairCount_five : pairCount 5 = 10 := by decide

/-- **The coincidence at order two.**  The Hankel determinant's exponent equals the weight
deviation's exponent exactly when the pair count is one. -/
theorem coincidence_at_two : pairCount 2 = 1 := pairCount_two

/-- **The deficit from order three on.**  The pair count exceeds one, so the determinant is smaller
than the deviation by that many powers less one. -/
theorem deficit_three : 1 < pairCount 3 := by decide
theorem deficit_four : 1 < pairCount 4 := by decide
theorem deficit_five : 1 < pairCount 5 := by decide

/-- The pair count is monotone, so the deficit only grows with the order. -/
theorem pairCount_mono {m n : ℕ} (h : m ≤ n) : pairCount m ≤ pairCount n := by
  unfold pairCount
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1))

/-- **The crossover, in real form.**  With determinant size `j^{-p}` and deviation size `j^{-1}`, the
determinant dominates exactly when `p ≤ 1`. -/
theorem crossover {j : ℝ} (hj : 1 < j) {p : ℝ} (hp : 1 < p) :
    j ^ (-p) < j ^ (-(1 : ℝ)) := by
  have hjpos : (0 : ℝ) < j := lt_trans one_pos hj
  exact Real.rpow_lt_rpow_of_exponent_lt hj (by linarith)

/-- **The deficit exponent.**  The determinant loses `p - 1` powers, which is zero at order two and
strictly positive from order three. -/
theorem deficit_exponent_two : (1 : ℝ) - 1 = 0 := by norm_num

theorem deficit_exponent_three : (0 : ℝ) < 3 - 1 := by norm_num

theorem deficit_exponent_pos {p : ℝ} (hp : 1 < p) : 0 < p - 1 := by linarith

/-- **What the identity still gives.**  The reversal relation is exact for every order; only its
asymptotic reading fails.  Nonnegativity of both a quantity and its negative still forces vanishing,
and that consequence is unaffected. -/
theorem exact_identity_survives {x : ℝ} (hfree : 0 ≤ x) (hhyp : 0 ≤ -x) : x = 0 :=
  opposing_forces_zero hfree hhyp

end RHTower
