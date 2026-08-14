import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality

/-!
# Exact scalar gluing at the Route T transition seam

The base layer and derivative--complement receiver are not unrelated alternatives.  Both are
controlled by the same scalar `u = mu * (1 - alpha)`.  Away from `u = 1`, one of them carries any
requested fixed exponent margin.  This module proves the exact trichotomy and converts its only
unresolved branch into a narrow amplitude window around `alpha = 1 - 1 / mu`.
-/

noncomputable section
namespace RHTower.Sieve

/-- **Base/derivative/seam trichotomy.**  At margin `eps`, either the base layer decays by `eps`,
both derivative--complement powers lie `eps` below the first receiver, or the common phase scalar
lies in the width-`2 eps` transition seam around one. -/
theorem routeT_base_or_derivative_margin_or_transition_seam
    {mu tau alpha s eps : ℝ}
    (halpha : alpha ≤ 1) (htau : tau ≤ mu) (hs : 0 ≤ s) :
    1 - mu * (1 - alpha) ≤ -eps ∨
      (maynardDerivativeComplementHeightExponent tau alpha s ≤
          mu * (1 - alpha) - eps ∧
        maynardDerivativeComplementLengthExponent tau alpha ≤
          mu * (1 - alpha) - eps) ∨
      (1 - eps < mu * (1 - alpha) ∧
        mu * (1 - alpha) < 1 + eps) := by
  let u : ℝ := mu * (1 - alpha)
  by_cases hbase : 1 + eps ≤ u
  · left
    dsimp only [u] at hbase ⊢
    linarith
  by_cases hderiv : u ≤ 1 - eps
  · right
    left
    have hdelta : 0 ≤ 1 - alpha := by linarith
    have htauDelta : tau * (1 - alpha) ≤ mu * (1 - alpha) :=
      mul_le_mul_of_nonneg_right htau hdelta
    dsimp only [u] at hderiv
    constructor <;>
      dsimp only [maynardDerivativeComplementHeightExponent,
        maynardDerivativeComplementLengthExponent] <;> linarith
  · right
    right
    dsimp only [u] at hbase hderiv ⊢
    exact ⟨lt_of_not_ge hderiv, lt_of_not_ge hbase⟩

/-- In positive height exponent, the scalar transition seam is literally an amplitude window of
radius `eps / mu` around `1 - 1 / mu`. -/
theorem routeT_transition_seam_alpha_window
    {mu alpha eps : ℝ} (hmu : 0 < mu)
    (hseam : 1 - eps < mu * (1 - alpha) ∧
      mu * (1 - alpha) < 1 + eps) :
    1 - 1 / mu - eps / mu < alpha ∧
      alpha < 1 - 1 / mu + eps / mu := by
  constructor
  · have hquot : 1 - alpha < (1 + eps) / mu := by
      rw [lt_div_iff₀ hmu]
      nlinarith [hseam.2]
    rw [show 1 - 1 / mu - eps / mu = 1 - (1 + eps) / mu by
      field_simp; ring]
    linarith
  · have hquot : (1 - eps) / mu < 1 - alpha := by
      rw [div_lt_iff₀ hmu]
      nlinarith [hseam.1]
    rw [show 1 - 1 / mu + eps / mu = 1 - (1 - eps) / mu by
      field_simp; ring]
    linarith

end RHTower.Sieve
