import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace RHTower

noncomputable section

/-- Completed determinant norm of the two projective Euler sheets. -/
def projectiveEulerCompletedNorm (s : ℂ) : ℂ := completedRiemannZeta (2 * s)

/-- Doubling the completed-zeta argument descends the functional-equation reflection from `1-s`
to `1/2-s`. -/
theorem projectiveEulerCompletedNorm_reflection (s : ℂ) :
    projectiveEulerCompletedNorm (1 / 2 - s) = projectiveEulerCompletedNorm s := by
  rw [projectiveEulerCompletedNorm, projectiveEulerCompletedNorm]
  rw [show (2 : ℂ) * (1 / 2 - s) = 1 - 2 * s by ring,
    completedRiemannZeta_one_sub]

/-- The anti-holomorphic reflection associated with the descended functional equation fixes
exactly the vertical line `Re(s)=1/4`. -/
theorem projectiveEulerNorm_reflection_fixed_iff (s : ℂ) :
    (1 / 2 : ℂ) - star s = s ↔ s.re = 1 / 4 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.star_def] at hre ⊢
    linarith
  · intro hre
    apply Complex.ext
    · norm_num [Complex.star_def]
      linarith
    · simp

end

end RHTower
