import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralBound

/-!
# Splitting the mixed term for Dirichlet polynomials

The mixed integral `∫ 2|F||F'|` of Gallagher's reduction is separated by the same pointwise
inequality `2ab ≤ εa² + ε^{-1}b²` used for trigonometric polynomials:

`∫_A^B 2|F||F'| ≤ ε ∫_A^B |F|² + ε^{-1} ∫_A^B |F'|²`.

With `DirichletIntegralBound.lean` bounding both integrals on the right, the balancing parameter is
chosen to be `log N`, the largest frequency, which equalises the two contributions.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The mixed integral of a Dirichlet polynomial, split into the two energies.** -/
theorem integral_mixed_dirPoly_le (N : ℕ) (a : Fin N → ℂ) {A B ε : ℝ} (hAB : A ≤ B)
    (hε : 0 < ε) :
    (∫ t in A..B, 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖)
      ≤ ε * (∫ t in A..B, ‖dirPoly N a t‖ ^ (2 : ℕ))
        + (1 / ε) * (∫ t in A..B, ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) := by
  have hc1 : Continuous (fun t : ℝ => ‖dirPoly N a t‖ ^ (2 : ℕ)) :=
    ((continuous_dirPoly N a).norm).pow 2
  have hc2 : Continuous (fun t : ℝ => ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) :=
    ((continuous_dirPoly N (dirDerivCoeff N a)).norm).pow 2
  have hcmix : Continuous (fun t : ℝ =>
      2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) :=
    (continuous_const.mul (continuous_dirPoly N a).norm).mul
      (continuous_dirPoly N (dirDerivCoeff N a)).norm
  have hcrhs : Continuous (fun t : ℝ =>
      ε * ‖dirPoly N a t‖ ^ (2 : ℕ) + (1 / ε) * ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) :=
    (continuous_const.mul hc1).add (continuous_const.mul hc2)
  have hmono : (∫ t in A..B, 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖)
      ≤ ∫ t in A..B, (ε * ‖dirPoly N a t‖ ^ (2 : ℕ)
          + (1 / ε) * ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) := by
    refine intervalIntegral.integral_mono_on hAB (hcmix.intervalIntegrable _ _)
      (hcrhs.intervalIntegrable _ _) ?_
    intro t _
    exact two_mul_le_amgm _ _ hε
  have hi1 : IntervalIntegrable (fun t : ℝ => ε * ‖dirPoly N a t‖ ^ (2 : ℕ)) volume A B :=
    (continuous_const.mul hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun t : ℝ => (1 / ε) * ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) volume A B :=
    (continuous_const.mul hc2).intervalIntegrable _ _
  have hsplit : (∫ t in A..B, (ε * ‖dirPoly N a t‖ ^ (2 : ℕ)
        + (1 / ε) * ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)))
      = ε * (∫ t in A..B, ‖dirPoly N a t‖ ^ (2 : ℕ))
        + (1 / ε) * (∫ t in A..B, ‖dirPoly N (dirDerivCoeff N a) t‖ ^ (2 : ℕ)) := by
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hmono
  exact hmono

end RHTower.Sieve
