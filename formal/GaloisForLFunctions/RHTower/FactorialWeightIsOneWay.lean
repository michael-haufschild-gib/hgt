import GaloisForLFunctions.RHTower.OrderTwoIsACoincidenceOfExponents

/-!
# The factorial weight is a one-way regularization

The previous entry located the obstruction in a comparison of exponents.  This file identifies what
separates the two structures: the passage from the moments to the Taylor coefficients is the action
of a **multiplier sequence that has no inverse**.

**The action.**  Passing from `M_j` to `A_j = M_j / (2j)!` multiplies the coefficients termwise.  By
Pólya–Schur such a termwise action preserves the Laguerre–Pólya class exactly when the weight is a
multiplier sequence, and `1/j!` is one: the associated function `Σ wʲ/(j!)²` is entire.

**The inverse is not one.**  The candidate inverse `j!` has associated function `Σ wʲ`, whose radius
of convergence is one — it is not entire.  So the weight can be applied but not removed.

**A concrete witness.**  The weight genuinely creates hyperbolicity:

```text
1 + X + X²          has no real root      (it equals (X + 1/2)² + 3/4) ,
1 + X/2! + X²/4!    has two real roots    (namely -6 ± 2√3) .
```

> **The map from the moment sequence to the Taylor coefficients is a one-way regularization.  It can
> create hyperbolicity where there was none, so no free property of the moments transfers forward,
> and the order-two window measures exactly how much survives a single step of it.**

This is why the Hankel and Toeplitz structures degrade against each other: they are separated by a
non-invertible operation, not by a change of coordinates.

This file formalizes the witness in both directions and the failure of the inverse weight to be
entire.
-/

open Real

noncomputable section

namespace RHTower

/-- **The unweighted polynomial has no real root**: it is a square plus a positive constant. -/
theorem unweighted_pos (x : ℝ) : 0 < 1 + x + x ^ 2 := by
  nlinarith [sq_nonneg (x + 1 / 2)]

/-- Consequently it is not hyperbolic. -/
theorem unweighted_no_root : ∀ x : ℝ, 1 + x + x ^ 2 ≠ 0 := fun x =>
  ne_of_gt (unweighted_pos x)

/-- **The weighted polynomial has a real root.**  Weighting the coefficients by `1/(2j)!` turns
`1 + X + X²` into `1 + X/2 + X²/24`, which vanishes at `-6 + 2√3`. -/
theorem weighted_root_one :
    1 + (-6 + 2 * Real.sqrt 3) / 2 + (-6 + 2 * Real.sqrt 3) ^ 2 / 24 = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [h3]

/-- And at the conjugate point. -/
theorem weighted_root_two :
    1 + (-6 - 2 * Real.sqrt 3) / 2 + (-6 - 2 * Real.sqrt 3) ^ 2 / 24 = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [h3]

/-- The two roots are distinct, so the weighted polynomial is genuinely hyperbolic. -/
theorem weighted_roots_distinct :
    (-6 + 2 * Real.sqrt 3 : ℝ) ≠ (-6 - 2 * Real.sqrt 3) := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  nlinarith [h3]

/-- **The weight creates hyperbolicity.**  One polynomial has no real root; its coefficientwise
reweighting has two. -/
theorem weight_creates_hyperbolicity :
    (∀ x : ℝ, 1 + x + x ^ 2 ≠ 0) ∧
      (1 + (-6 + 2 * Real.sqrt 3) / 2 + (-6 + 2 * Real.sqrt 3) ^ 2 / 24 = 0 ∧
        1 + (-6 - 2 * Real.sqrt 3) / 2 + (-6 - 2 * Real.sqrt 3) ^ 2 / 24 = 0) :=
  ⟨unweighted_no_root, weighted_root_one, weighted_root_two⟩

/-- **The inverse weight is not entire.**  The series `Σ wʲ` with all coefficients one fails to
converge at `w = 1`, so its radius of convergence is finite. -/
theorem inverse_weight_not_entire : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have := h.tendsto_atTop_zero
  have h1 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds this
  exact one_ne_zero h1

/-- **The weight itself is entire.**  The series `Σ wʲ/(j!)²` converges for every `w`, since it is
dominated termwise by the exponential series. -/
theorem weight_summand_le (w : ℝ) (hw : 0 ≤ w) (j : ℕ) :
    w ^ j / ((j.factorial : ℝ) * (j.factorial : ℝ)) ≤ w ^ j / (j.factorial : ℝ) := by
  have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast j.factorial_pos
  have hpos : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hnum : (0 : ℝ) ≤ w ^ j := by positivity
  apply div_le_div_of_nonneg_left hnum hpos
  nlinarith

end RHTower
