import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Positive-residue pole forcing

A finite passive scalar response has the form

`a + sum_j ell_j^2 / (pole_j - x)`.

Every summand is increasing across a real interval which contains no pole.  Consequently any
strict descent between two source samples forces a pole strictly between the samples.  This is a
finite statement, but its purpose is cofinal: a family converging to a nonvanishing analytic target
cannot hide persistent source descents by changing residues or multiplying its pole polynomial by
arbitrary scalar normalizers.
-/

open scoped BigOperators

namespace HTGeometry

/-- Finite scalar response with nonnegative spectral residues `ell j ^ 2`. -/
noncomputable def positiveResidueResponse
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pole ell : ι → ℝ) (a x : ℝ) : ℝ :=
  a + ∑ j ∈ s, ell j ^ 2 / (pole j - x)

/-- One positive-residue summand increases across an interval avoided by its pole. -/
theorem positiveResidueTerm_le_of_pole_avoids
    {p e x y : ℝ} (hxy : x < y) (hpole : p < x ∨ y < p) :
    e ^ 2 / (p - x) ≤ e ^ 2 / (p - y) := by
  by_cases he : e = 0
  · simp [he]
  have hprod : 0 < (p - y) * (p - x) := by
    rcases hpole with hpole | hpole
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hneX : p - x ≠ 0 := by
    rcases hpole with hpole | hpole <;> linarith
  have hneY : p - y ≠ 0 := by
    rcases hpole with hpole | hpole <;> linarith
  have hdiff :
      e ^ 2 / (p - y) - e ^ 2 / (p - x) =
        e ^ 2 * (y - x) / ((p - y) * (p - x)) := by
    field_simp [hneX, hneY]
    ring
  have hpos : 0 < e ^ 2 * (y - x) / ((p - y) * (p - x)) :=
    div_pos (mul_pos (sq_pos_of_ne_zero he) (sub_pos.mpr hxy)) hprod
  linarith

/-- A finite positive-residue response is nondecreasing on every pole-free interval. -/
theorem positiveResidueResponse_le_of_poles_avoid
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pole ell : ι → ℝ) (a : ℝ) {x y : ℝ}
    (hxy : x < y) (hpole : ∀ j ∈ s, pole j < x ∨ y < pole j) :
    positiveResidueResponse s pole ell a x ≤
      positiveResidueResponse s pole ell a y := by
  unfold positiveResidueResponse
  apply add_le_add_right
  exact Finset.sum_le_sum fun j hj =>
    positiveResidueTerm_le_of_pole_avoids hxy (hpole j hj)

/-- **Positive-residue descent--pole law.**  If neither sample is a pole, every strict response
descent forces a spectral pole strictly between the samples. -/
theorem exists_pole_between_of_positiveResidueResponse_descent
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pole ell : ι → ℝ) (a : ℝ) {x y : ℝ}
    (hxy : x < y)
    (hleft : ∀ j ∈ s, pole j ≠ x)
    (hright : ∀ j ∈ s, pole j ≠ y)
    (hdescent : positiveResidueResponse s pole ell a y <
      positiveResidueResponse s pole ell a x) :
    ∃ j ∈ s, pole j ∈ Set.Ioo x y := by
  by_contra hnone
  push Not at hnone
  have hpole : ∀ j ∈ s, pole j < x ∨ y < pole j := by
    intro j hj
    by_cases hjx : pole j ≤ x
    · exact Or.inl (lt_of_le_of_ne hjx (hleft j hj))
    · have hxj : x < pole j := lt_of_not_ge hjx
      have hjy : y ≤ pole j := by
        by_contra hnot
        exact hnone j hj ⟨hxj, lt_of_not_ge hnot⟩
      exact Or.inr (lt_of_le_of_ne hjy (Ne.symm (hright j hj)))
  exact (not_lt_of_ge
    (positiveResidueResponse_le_of_poles_avoid s pole ell a hxy hpole)) hdescent

end HTGeometry
