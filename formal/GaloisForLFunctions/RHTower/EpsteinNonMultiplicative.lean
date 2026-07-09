/-
The representation numbers of the principal form of discriminant −20 are not
multiplicative, and the failure is already visible at the first coprime pair.

Let `r(n)` count the integer solutions of `x² + 5y² = n`. This form has class
number two: its genus contains the second form `2x² + 2xy + 3y²`, and the two
forms partition the represented residues. The Epstein zeta function
`Z(s) = Σ_{(x,y)≠0} (x² + 5y²)^{-s}` is a Dirichlet series with coefficient
stream `r(n)`; it satisfies a self-dual completed functional equation
`ξ(s) = (√20 / (2π))^{-s} Γ(s) Z(s) = ξ(1 − s)` yet, because the class number
exceeds one, it factors as a sum of two Hecke L-series and provably carries
zeros off the critical line. A Dirichlet series with an Euler product forces its
coefficients to be multiplicative: `a(mn) = a(m)a(n)` for coprime `m, n`. The
representation numbers fail this at once. With `2` and `3` coprime:

* `r(2) = 0` — the form omits `2` (it lies in the non-principal genus);
* `r(3) = 0` — the form omits `3` likewise;
* `r(6) = 4` — the four solutions `(±1, ±1)` give `1 + 5 = 6`.

Hence `r(6) = 4 ≠ 0 = r(2)·r(3)`: the coefficient stream exits every
multiplicative class at the first coprime product, so no Euler product organises
it. Multiplicativity is exactly the clause that excludes this off-line-charge
carrier from the multiplicative coefficient classes.

The count is certified by a bounding box. `repFinset n` filters the square
`[-n, n] × [-n, n]` for solutions, and `repFinset_complete` shows the box is not
lossy: any solution `(x, y)` satisfies `x² ≤ n` and `y² ≤ n`, and for integers
`|x| ≤ x²`, so `|x| ≤ n` and `|y| ≤ n`. Thus `repCount n = card (repFinset n)`
is the true representation number, and the three values are decided by finite
enumeration of the box.
-/
import Mathlib

namespace RHTower

open Finset

/-- The solution set of `x² + 5y² = n` inside the box `[-n, n] × [-n, n]`,
realised as a `Finset` of integer pairs. -/
noncomputable def repFinset (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    fun p => p.1 ^ 2 + 5 * p.2 ^ 2 = n

/-- The representation number of `n` by `x² + 5y²`: the number of integer pairs
`(x, y)` solving `x² + 5y² = n`, counted over the bounding box. -/
noncomputable def repCount (n : ℕ) : ℕ := (repFinset n).card

/-- The bounding box loses no solutions: every integer solution of
`x² + 5y² = n` lies in `[-n, n] × [-n, n]` and hence in `repFinset n`. From
`x² + 5y² = n` with `5y² ≥ 0` one gets `x² ≤ n ≤ n²`, and `abs_le_of_sq_le_sq'`
turns this into `-n ≤ x ≤ n`; symmetrically for `y`. This justifies that
`repCount` counts all solutions. -/
theorem repFinset_complete (n : ℕ) :
    ∀ x y : ℤ, x ^ 2 + 5 * y ^ 2 = n → (x, y) ∈ repFinset n := by
  intro x y h
  have hx2 : x ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg y]
  have hy2 : y ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg x]
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hxsq : x ^ 2 ≤ (n : ℤ) ^ 2 := le_trans hx2 (Int.le_self_sq _)
  have hysq : y ^ 2 ≤ (n : ℤ) ^ 2 := le_trans hy2 (Int.le_self_sq _)
  have hxb := abs_le_of_sq_le_sq' hxsq hn0
  have hyb := abs_le_of_sq_le_sq' hysq hn0
  rw [repFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨⟨hxb.1, hxb.2⟩, hyb.1, hyb.2⟩, h⟩

/-- `x² + 5y² = 2` has no integer solutions: `r(2) = 0`. -/
theorem repCount_two : repCount 2 = 0 := by decide

/-- `x² + 5y² = 3` has no integer solutions: `r(3) = 0`. -/
theorem repCount_three : repCount 3 = 0 := by decide

/-- `x² + 5y² = 6` has exactly the four solutions `(±1, ±1)`: `r(6) = 4`. -/
theorem repCount_six : repCount 6 = 4 := by decide

/-- The representation numbers of `x² + 5y²` are not multiplicative: `2` and `3`
are coprime, yet `r(2·3) = r(6) = 4 ≠ 0 = 0·0 = r(2)·r(3)`. The coefficient
stream of the Epstein zeta function therefore admits no Euler product. -/
theorem repCount_not_multiplicative :
    Nat.Coprime 2 3 ∧ repCount (2 * 3) ≠ repCount 2 * repCount 3 := by
  refine ⟨by decide, ?_⟩
  rw [show (2 * 3 : ℕ) = 6 from rfl, repCount_six, repCount_two, repCount_three]
  decide

end RHTower
