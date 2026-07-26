import GaloisForLFunctions.RHTower.HedenmalmInfiniteOrientationSingularities

/-!
# The critical-line lower bound on the Xi zero abscissa

The functional equation reflects the Xi zero set across the critical line, so a zero to the left of
it produces one to the right.  Since the zero set is infinite, and in particular nonempty, there is
always a zero with real part at least `1/2`; equivalently the supremum of the real parts of the Xi
zeros is at least `1/2`.

This is the unconditional input `Θ ≥ 1/2` that the order laws for additive Möbius convolutions use:
it needs no information about where the zeros actually lie, only that one exists and that the set is
reflection-symmetric.
-/

namespace RHTower

/-- **Reflection symmetry of the Xi zero set.** -/
theorem xiZeroSet_one_sub {ρ : ℂ} (hρ : ρ ∈ xiZeroSet) : 1 - ρ ∈ xiZeroSet := by
  change xi (1 - ρ) = 0
  rw [xi_one_sub]
  exact hρ

/-- **`Θ ≥ 1/2`.**  Some Xi zero has real part at least `1/2`.  A zero strictly to the left of the
critical line reflects to one strictly to the right. -/
theorem exists_xiZeroSet_half_le_re : ∃ ρ ∈ xiZeroSet, (1 / 2 : ℝ) ≤ ρ.re := by
  obtain ⟨ρ, hρ⟩ := xiZeroSet_infinite.nonempty
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with h | h
  · exact ⟨ρ, hρ, h⟩
  · refine ⟨1 - ρ, xiZeroSet_one_sub hρ, ?_⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- Every abscissa strictly below the critical line is exceeded by a Xi zero: the form in which the
lower bound enters a contradiction against a half-plane of holomorphy. -/
theorem exists_xiZeroSet_lt_re {b : ℝ} (hb : b < 1 / 2) : ∃ ρ ∈ xiZeroSet, b < ρ.re := by
  obtain ⟨ρ, hρ, hre⟩ := exists_xiZeroSet_half_le_re
  exact ⟨ρ, hρ, lt_of_lt_of_le hb hre⟩

/-- The reflected witness: some Xi zero has real part at most `1/2`.  Together with
`exists_xiZeroSet_half_le_re` this brackets the zero set around the critical line. -/
theorem exists_xiZeroSet_re_le_half : ∃ ρ ∈ xiZeroSet, ρ.re ≤ (1 / 2 : ℝ) := by
  obtain ⟨ρ, hρ, hre⟩ := exists_xiZeroSet_half_le_re
  refine ⟨1 - ρ, xiZeroSet_one_sub hρ, ?_⟩
  simp only [Complex.sub_re, Complex.one_re]
  linarith

end RHTower
