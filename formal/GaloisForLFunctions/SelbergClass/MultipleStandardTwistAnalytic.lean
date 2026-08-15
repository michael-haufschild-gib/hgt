import GaloisForLFunctions.SelbergClass.MultipleStandardTwistTensor
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# Joint analyticity of damped multiple standard twists

For positive damping, the Cartesian multiple-standard-twist series is already
globally Fréchet differentiable by its summable derivative majorant.  The
project's finite-dimensional polydisc theorem upgrades that genuinely
`ℂ^N` statement to an `AnalyticOnNhd` certificate.  This records only the
regular damped object; it does not assert meromorphic continuation of the
undamped tensor, any polar description, or either Selberg conjecture.
-/

namespace GaloisForLFunctions.SelbergClass

/-- Positive damping makes the multiple standard twist jointly analytic on
the full complex parameter space. -/
theorem analyticOnNhd_dampedMultipleStandardTwist {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℕ → ℂ) (C B κ : Fin N → ℝ)
    (ha : ∀ (i : Fin N) (n : ℕ+),
      ‖a i (n : ℕ)‖ ≤ C i * ((n : ℕ) : ℝ) ^ B i)
    (hκ : ∀ i, 0 < κ i) {α X : ℝ} (hα : 0 < α) (hX : 0 < X) :
    AnalyticOnNhd ℂ (dampedMultipleStandardTwist a κ α X) Set.univ := by
  apply GaloisForLFunctions.HTGeometry.analyticOnNhd_of_differentiable
  exact differentiable_dampedMultipleStandardTwist hN a C B κ ha hκ hα hX

/-- The damped tensor attached to published `S♯` input data is jointly
analytic on `ℂ^N`. -/
theorem MultipleStandardTwistData.analyticOnNhd_damped {N : ℕ}
    (D : MultipleStandardTwistData N) {X : ℝ} (hX : 0 < X) :
    AnalyticOnNhd ℂ (D.damped X) Set.univ := by
  apply GaloisForLFunctions.HTGeometry.analyticOnNhd_of_differentiable
  exact D.differentiable_damped hX

end GaloisForLFunctions.SelbergClass
