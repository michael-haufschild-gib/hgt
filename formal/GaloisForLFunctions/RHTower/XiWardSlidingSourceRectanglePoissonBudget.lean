import GaloisForLFunctions.RHTower.XiWardPoissonSemigroupDissipation

/-!
# Sliding source-rectangle Poisson budget

The triangular Ward receiver is a difference of two source-rectangle energies.  Poisson
dissipation makes this annulus nonnegative, while positivity of the wide energy bounds it by the
narrow energy.  Integrating over the source translation therefore leaves one zero-independent
quadratic pole--Gamma--von-Mangoldt statistic carrying the full `3π` charge of every strict-right
multiplicity copy.

This supplies the source-only receiver and isolates the remaining quantitative problem: an
asymptotic upper bound for the narrow energy.  It does not assert that upper bound.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Translation-averaged narrow-line energy of paired source rectangles. -/
def xiWardSlidingSourceRectangleNarrowEnergy
    (z₁ z₂ z₁' z₂' : ℝ → ℂ) : ℝ :=
  2 * ∫ u : ℝ,
    xiWardPairedSourceRectangleRealEnergyAtLine
      (51 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u)

/-- Poisson dissipation bounds the translated source annulus by its narrow-line source energy. -/
theorem xiWardSlidingSourceRectangleAnnulusEnergy_le_narrow
    (z₁ z₂ z₁' z₂' : ℝ → ℂ)
    (hnarrow : Integrable (fun u : ℝ =>
      xiWardPairedSourceRectangleRealEnergyAtLine
        (51 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u)))
    (hwide : Integrable (fun u : ℝ =>
      xiWardPairedSourceRectangleRealEnergyAtLine
        (1051 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u))) :
    xiWardSlidingSourceRectangleAnnulusEnergy z₁ z₂ z₁' z₂' ≤
      xiWardSlidingSourceRectangleNarrowEnergy z₁ z₂ z₁' z₂' := by
  have hannulus : Integrable (fun u : ℝ =>
      xiWardPairedSourceRectangleAnnulusEnergy
        (z₁ u) (z₂ u) (z₁' u) (z₂' u)) := by
    change Integrable
      ((fun u : ℝ => xiWardPairedSourceRectangleRealEnergyAtLine
        (51 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u)) -
      fun u : ℝ => xiWardPairedSourceRectangleRealEnergyAtLine
        (1051 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u))
    exact hnarrow.sub hwide
  have hintegral :
      (∫ u : ℝ, xiWardPairedSourceRectangleAnnulusEnergy
        (z₁ u) (z₂ u) (z₁' u) (z₂' u)) ≤
      ∫ u : ℝ, xiWardPairedSourceRectangleRealEnergyAtLine
        (51 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u) := by
    exact integral_mono hannulus hnarrow fun u =>
      xiWardPairedSourceRectangleAnnulusEnergy_le_narrow
        (z₁ u) (z₂ u) (z₁' u) (z₂' u)
  unfold xiWardSlidingSourceRectangleAnnulusEnergy
    xiWardSlidingSourceRectangleNarrowEnergy
  linarith

/-- The narrow-line source statistic retains the triangular receiver's full `3π` charge. -/
theorem card_mul_three_pi_le_xiWardSlidingSourceRectangleNarrowEnergy
    (S : Finset XiRightUpperZeroCopy)
    (z₁ z₂ z₁' z₂' : ℝ → ℂ)
    (hresponseNarrow : ∀ᵐ u : ℝ ∂volume, ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ))
            (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hresponseWide : ∀ᵐ u : ℝ ∂volume, ∀ t : ℝ,
      xiWardPairedSourceRectangleResponse
          (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))
            (z₁ u) (z₂ u) (z₁' u) (z₂' u) =
        ∑ q ∈ xiWardHalfCellPacket S u,
          xiAntiCausalWardSchwarzPairResponse q
            (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)))
    (hnarrow : Integrable (fun u : ℝ =>
      xiWardPairedSourceRectangleRealEnergyAtLine
        (51 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u)))
    (hwide : Integrable (fun u : ℝ =>
      xiWardPairedSourceRectangleRealEnergyAtLine
        (1051 / 100) (z₁ u) (z₂ u) (z₁' u) (z₂' u))) :
    (S.card : ℝ) * (3 * Real.pi) ≤
      xiWardSlidingSourceRectangleNarrowEnergy z₁ z₂ z₁' z₂' := by
  exact (card_mul_three_pi_le_xiWardSlidingSourceRectangleAnnulusEnergy
    S z₁ z₂ z₁' z₂' hresponseNarrow hresponseWide).trans
      (xiWardSlidingSourceRectangleAnnulusEnergy_le_narrow
        z₁ z₂ z₁' z₂' hnarrow hwide)

end

end RHTower
