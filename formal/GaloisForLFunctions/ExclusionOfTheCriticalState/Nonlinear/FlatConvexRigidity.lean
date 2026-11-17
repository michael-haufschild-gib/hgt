import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexPotential

/-!
# Exact degeneracy of the flat convex loss

The tangent error controls half the squared gradient displacement. The
flat gradient identifies precisely the nonpositive half-line; consequently
the loss vanishes exactly on the diagonal or between two nonpositive
arguments. This describes the degeneracy retained by the smooth flat test.
-/

open Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- Smooth convex descent strengthens the tangent inequality to a gradient-square bound. -/
theorem gradient_displacement_le_tangent_error (x y : ℝ) :
    (gradient x - gradient y) ^ 2 / 2 ≤
      potential x - potential y - gradient y * (x - y) := by
  have hl := (tangent_error_bounds (x - (gradient x - gradient y)) y).1
  have hu := (tangent_error_bounds (x - (gradient x - gradient y)) x).2
  nlinarith only [hl, hu]

private theorem gradient_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : gradient x = 0 := by
  have he : -|x| = x := by rw [abs_of_nonpos hx]; ring
  simpa only [he] using gradient_zero_on_negative x

private theorem potential_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : potential x = 0 := by
  have he : -|x| = x := by rw [abs_of_nonpos hx]; ring
  simpa only [he] using potential_zero_on_negative x

/-- The flat gradient loses no distinctions inside the positive half-line. -/
theorem gradient_strictMono_positive : StrictMonoOn gradient (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (gradient_contDiff 0).continuous.continuousOn
  intro x hx
  rw [interior_Ioi] at hx
  rw [(gradient_hasDerivAt x).deriv]
  exact expNegInvGlue.pos_of_pos hx

private theorem gradient_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < gradient x := by
  have h := gradient_strictMono_positive (by change 0 < x / 2; linarith only [hx]) hx
    (by linarith only [hx] : x / 2 < x)
  exact lt_of_le_of_lt (gradient_nonneg _) h

/-- The exact zero set of the nonlinear gradient. -/
theorem gradient_zero_iff (x : ℝ) : gradient x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    by_contra hx
    have hp := gradient_pos_of_pos (lt_of_not_ge hx)
    rw [h] at hp
    exact (lt_irrefl _) hp
  · exact gradient_eq_zero_of_nonpos

/-- The potential and its gradient have the same entire flat region. -/
theorem potential_zero_iff (x : ℝ) : potential x = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    have hs := gradient_square_le x
    rw [h, mul_zero] at hs
    have hg : gradient x = 0 := by nlinarith only [hs, sq_nonneg (gradient x)]
    exact (gradient_zero_iff x).mp hg
  · exact potential_eq_zero_of_nonpos

/-- Equality of transformed values collapses exactly the nonpositive half-line. -/
theorem gradient_eq_iff (x y : ℝ) :
    gradient x = gradient y ↔ x = y ∨ (x ≤ 0 ∧ y ≤ 0) := by
  constructor
  · intro h
    by_cases hx : 0 < x
    · by_cases hy : 0 < y
      · left
        rcases lt_trichotomy x y with hxy | hxy | hxy
        · exact False.elim ((ne_of_lt (gradient_strictMono_positive hx hy hxy)) h)
        · exact hxy
        · exact False.elim ((ne_of_lt (gradient_strictMono_positive hy hx hxy)) h.symm)
      · have hz := gradient_eq_zero_of_nonpos (le_of_not_gt hy)
        have hp := gradient_pos_of_pos hx
        rw [h, hz] at hp
        exact False.elim ((lt_irrefl _) hp)
    · have hx0 := le_of_not_gt hx
      have hz : gradient y = 0 := h.symm.trans (gradient_eq_zero_of_nonpos hx0)
      exact Or.inr ⟨hx0, (gradient_zero_iff y).mp hz⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [gradient_eq_zero_of_nonpos hx, gradient_eq_zero_of_nonpos hy]

/-- Exact nullset of the asymmetric tangent loss, including its flat degeneracy. -/
theorem tangent_error_zero_iff (x y : ℝ) :
    potential x - potential y - gradient y * (x - y) = 0 ↔
      x = y ∨ (x ≤ 0 ∧ y ≤ 0) := by
  constructor
  · intro h
    have hs := gradient_displacement_le_tangent_error x y
    rw [h] at hs
    have he : gradient x = gradient y := by
      nlinarith only [hs, sq_nonneg (gradient x - gradient y)]
    exact (gradient_eq_iff x y).mp he
  · rintro (rfl | ⟨hx, hy⟩)
    · ring
    · rw [potential_eq_zero_of_nonpos hx, potential_eq_zero_of_nonpos hy,
        gradient_eq_zero_of_nonpos hy]
      ring

#print axioms gradient_displacement_le_tangent_error
#print axioms gradient_zero_iff
#print axioms potential_zero_iff
#print axioms gradient_eq_iff
#print axioms tangent_error_zero_iff
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
