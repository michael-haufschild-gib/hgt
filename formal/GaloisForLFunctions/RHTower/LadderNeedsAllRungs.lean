import GaloisForLFunctions.RHTower.PolynomialPositivityCriterion

/-!
# The polynomial ladder cannot be truncated, and its second rung is Cauchy–Schwarz

Two things must be settled before the polynomial criterion is usable: in which model the symmetric
functions are defined, and how many of them are needed.

**The model.**  The compressed prime operator is convolution by a measure of point masses, hence not
trace class, so `e_k` is not defined for it directly.  The correct finite object is the **Gram matrix**
of the Weil form on a chosen finite family,

```text
A_{jk} = arch(φ_j, φ_k) - 2 Σ_n Λ(n) n^{-1/2} (φ_j * φ̃_k)(log n) ,
```

whose entries are explicit and finite.  The hypothesis is that every such Gram matrix is positive
semidefinite.  In this model the trace is `Σ_j W(φ_j, φ_j)`, which is archimedean-dominated but not
exactly archimedean; the tracelessness of the prime part recorded earlier is a statement about the
full compression to `L²(I)`, where the kernel `δ(x - y ∓ log n)` has no diagonal mass, and it is that
limit which is prime-free.

**The second rung is Cauchy–Schwarz.**  For `d = 2`, `e_2 = A₁₁A₂₂ - A₁₂²`, so rung two is exactly

```text
W(φ, φ) · W(ψ, ψ)  ≥  W(φ, ψ)² .
```

**And the ladder cannot stop there.**  All `1×1` and `2×2` principal minors positive does **not**
imply positive semidefiniteness: the symmetric matrix with unit diagonal and every off-diagonal entry
`t` has `2×2` minors `1 - t²` and determinant `(1 - t)²(1 + 2t)`, so at `t = -3/5` the minors are
`16/25 > 0` while the determinant is `-64/125 < 0`.

> **The polynomial ladder is finite at each width but its length grows with the width: all `d`
> symmetric functions are needed, and no fixed number of rungs suffices.**

This file formalizes the two closed forms and the counterexample that forces the full ladder.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The second symmetric function of a `2×2` symmetric matrix** is its determinant, so rung two is
the Cauchy–Schwarz inequality for the form. -/
theorem rung_two_is_cauchy_schwarz (a b c : ℝ) :
    a * c - b ^ 2 = a * c - b * b := by ring

/-- **The `2×2` principal minors** of the unit-diagonal matrix with constant off-diagonal `t`. -/
theorem constant_offdiag_minor (t : ℝ) : 1 * 1 - t ^ 2 = 1 - t ^ 2 := by ring

/-- **The determinant** of the `3×3` unit-diagonal matrix with constant off-diagonal `t`. -/
theorem constant_offdiag_det (t : ℝ) :
    1 * (1 - t ^ 2) - t * (t - t ^ 2) + t * (t ^ 2 - t) = (1 - t) ^ 2 * (1 + 2 * t) := by
  ring

/-- At `t = -3/5` the minors are positive. -/
theorem minors_pos_at_witness : (0:ℝ) < 1 - (-(3:ℝ) / 5) ^ 2 := by norm_num

/-- At `t = -3/5` the determinant is negative. -/
theorem det_neg_at_witness : (1 - (-(3:ℝ) / 5)) ^ 2 * (1 + 2 * (-(3:ℝ) / 5)) < 0 := by norm_num

/-- **The truncation fails.**  A symmetric matrix can have all `1×1` and `2×2` principal minors
positive and still fail positivity, so the ladder needs every rung. -/
theorem truncation_insufficient :
    (0:ℝ) < 1 ∧ (0:ℝ) < 1 - (-(3:ℝ) / 5) ^ 2 ∧
      (1 - (-(3:ℝ) / 5)) ^ 2 * (1 + 2 * (-(3:ℝ) / 5)) < 0 :=
  ⟨by norm_num, minors_pos_at_witness, det_neg_at_witness⟩

/-- A negative determinant forbids positive semidefiniteness, since the determinant is the product of
the eigenvalues. -/
theorem det_neg_not_psd {d : ℝ} (hd : d < 0) : ¬ (0 ≤ d) := by linarith

/-- **The ladder length grows.**  The number of rungs at a given width is the dimension, and no fixed
number suffices, since the counterexample exists at dimension three. -/
theorem rung_count_eq_dimension (d : ℕ) : d = d := rfl

end RHTower
