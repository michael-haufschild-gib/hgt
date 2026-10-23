import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogLinearGrowth
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiMellinSubquadratic
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiSubquadraticGrowth

set_option autoImplicit false

/-!
# Theta-tail constants in the Mellin and `Λ₀` growth bounds

The upper-theta Mellin bounds and the `completedRiemannZeta₀` growth bounds are stated for any
theta-tail decay pair `‖θ(x) − 1‖ ≤ C e^{−p x}` (`x ≥ 1`, `1 ≤ C`, `0 < p`).
`exists_riemannThetaTail_exp_bound` supplies such a pair, so each bound holds with explicit
`2C/p` prefactor for one fixed pair, uniformly in `s`.
-/

noncomputable section

namespace RiemannGaussian

/-- Quadratic Mellin bound for the upper theta integral. -/
theorem norm_mellin_riemannThetaUpper_le_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖mellin riemannThetaUpper s‖ ≤ (2 * C / p) * Real.exp (2 * (s.re - 1) ^ 2 / p) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_mellin_riemannThetaUpper_le hC hp htail⟩

/-- Quadratic growth of `Λ₀` with the theta-tail constants. -/
theorem norm_completedRiemannZeta₀_le_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤ (2 * C / p) * Real.exp ((2 / p) * (‖s‖ + 1) ^ 2) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_completedRiemannZeta₀_le hC hp htail⟩

/-- Log-linear Mellin bound for the upper theta integral. -/
theorem norm_mellin_riemannThetaUpper_le_logLinear_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖mellin riemannThetaUpper s‖ ≤
        (2 * C / p) * Real.exp (mellinLogLinearCost p (s.re - 1)) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_mellin_riemannThetaUpper_le_logLinear hC hp htail⟩

/-- `exp(O(R log R))` growth of `Λ₀` with the theta-tail constants. -/
theorem norm_completedRiemannZeta₀_le_logLinear_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        (2 * C / p) *
          Real.exp ((Real.log (max 1 (2 / p)) + 1) * xiLogLinearScale (‖s‖ + 1)) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_completedRiemannZeta₀_le_logLinear hC hp htail⟩

/-- Exponent-`4/3` Mellin bound for the upper theta integral. -/
theorem norm_mellin_riemannThetaUpper_le_fourThirds_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖mellin riemannThetaUpper s‖ ≤
        (2 * C / p) * Real.exp (mellinFourThirdsCost p (max 0 (s.re - 1))) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_mellin_riemannThetaUpper_le_fourThirds hC hp htail⟩

/-- Exponent-`4/3` growth of `Λ₀` with the theta-tail constants. -/
theorem norm_completedRiemannZeta₀_le_fourThirds_uniform :
    ∃ C p : ℝ, 1 ≤ C ∧ 0 < p ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤
        (2 * C / p) * Real.exp (mellinFourThirdsCoefficient p * (‖s‖ + 1) ^ (4 / 3 : ℝ)) := by
  obtain ⟨C, p, hC, hp, htail⟩ := exists_riemannThetaTail_exp_bound
  exact ⟨C, p, hC, hp, norm_completedRiemannZeta₀_le_fourThirds hC hp htail⟩

end RiemannGaussian
