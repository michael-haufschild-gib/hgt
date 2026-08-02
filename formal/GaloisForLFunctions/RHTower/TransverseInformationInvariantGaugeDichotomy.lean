import GaloisForLFunctions.RHTower.DeningerMeyerInvariantEvaluationGaugeFrontier

/-!
# Exact invariant-gauge dichotomy

A nonzero exponential eigenfunctional admits finite invariant upper control
exactly when its character has zero real rate.  No topology, norm, seminorm,
or common gauge is required.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Exact invariant-gauge dichotomy.**  A finite nonnegative invariant
gauge can dominate a nonzero exponential eigenfunctional if and only if
the character has zero real rate.  In the neutral case, the modulus of the
eigenfunctional is itself a canonical gauge. -/
theorem invariantGauge_bounded_eigenfunctional_iff_re_eq_zero
    {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (V : ℝ → X →ₗ[ℂ] X) (E : X →ₗ[ℂ] ℂ) (hE : E ≠ 0)
    (z : ℂ)
    (heigen : ∀ (c : ℝ) (u : X),
      E (V c u) = Complex.exp ((c : ℂ) * z) * E u) :
    (∃ gauge : X → ℝ,
        (∀ u, 0 ≤ gauge u) ∧
        (∀ (c : ℝ) (u : X), gauge (V c u) = gauge u) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖E u‖ ≤ C * gauge u) ↔
      z.re = 0 := by
  constructor
  · rintro ⟨gauge, hnonneg, hinvariant, hbounded⟩
    exact re_eq_zero_of_invariantGauge_bounded_eigenfunctional
      V E hE gauge hnonneg hinvariant hbounded z heigen
  · intro hz
    refine
      ⟨fun u => ‖E u‖, fun u => norm_nonneg _, ?_,
        1, zero_le_one, ?_⟩
    · intro c u
      change ‖E (V c u)‖ = ‖E u‖
      rw [heigen c u, norm_mul, Complex.norm_exp]
      simp [Complex.mul_re, hz]
    · intro u
      simp

end

end RHTower
