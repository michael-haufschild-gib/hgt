/-
# One-step Gaussian decoupling for a generic normalized four-curve

Combining generic osculating coordinates, vector Taylor control, and the
abstract perturbative theorem gives the finite one-step decoupling estimate
needed in Bourgain's power-scale recurrence.
-/
import GaloisForLFunctions.RHTower.BourgainGenericFrequencyPerturbation

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp one-step Gaussian decoupling for two generic curve pieces.

All curve-specific work is exposed as three quantitative facts: invertibility
of the two-base jet map, uniform vector quadratic remainders, and smallness of
the resulting scaled perturbation. -/
theorem integral_bourgainGenericExactPaired_gaussian_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H)
        (φ₃ φ₄ : ℝ → ℝ) {D a b ρ : ℝ}
        (hD : 0 < D) (_hρ : 0 ≤ ρ)
        (hunit :
          IsUnit (bourgainGenericPhaseCoordinateMatrix φ₃ φ₄ a b)),
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainGenericScaledPhaseContinuousLinearEquiv
          φ₃ φ₄ hscale hunit
      let X := bourgainIndependentParabolaNaturalScale H
      let δ :=
        bourgainGenericFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ρ
      (∀ n : Fin H,
        ‖bourgainGenericFourCurve φ₃ φ₄
              (a + (bourgainIndex n : ℝ) / D) -
            bourgainGenericFourCurveQuadraticModel φ₃ φ₄ a
              ((bourgainIndex n : ℝ) / D)‖ ≤ ρ) →
      (∀ n : Fin H,
        ‖bourgainGenericFourCurve φ₃ φ₄
              (b + (bourgainIndex n : ℝ) / D) -
            bourgainGenericFourCurveQuadraticModel φ₃ φ₄ b
              ((bourgainIndex n : ℝ) / D)‖ ≤ ρ) →
      δ ≤ 1 / 24 →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainPairedTripleCloud
              (bourgainGenericExactLeftFrequency
                φ₃ φ₄ hscale hunit D)
              (bourgainGenericExactRightFrequency
                φ₃ φ₄ hscale hunit D))
            (bourgainPairedTripleWeight c₁ c₂) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, habstract⟩ :=
    integral_bourgainPairedTripleCloud_gaussian_subpower_of_perturbation
      hε
  refine ⟨C, hC, ?_⟩
  intro H hH φ₃ φ₄ D a b ρ hD hρ hunit
  dsimp only
  intro hleft hright hsmall c₁ c₂
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainGenericScaledPhaseContinuousLinearEquiv
      φ₃ φ₄ hscale hunit
  let X := bourgainIndependentParabolaNaturalScale H
  let δ :=
    bourgainGenericFrequencyPerturbationSize X
      ‖(E.symm : BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖ ρ
  have hperturb :=
    bourgainGenericExactFrequencies_scaledPerturbation
      hH φ₃ φ₄ hD hρ hunit hleft hright X
  change
    (∀ n j,
      |X j *
        (bourgainGenericExactLeftFrequency
            φ₃ φ₄ hscale hunit D n j -
          bourgainLeftParabolaSample (H : ℝ) n j)| ≤ δ) ∧
    (∀ n j,
      |X j *
        (bourgainGenericExactRightFrequency
            φ₃ φ₄ hscale hunit D n j -
          bourgainRightParabolaSample (H : ℝ) n j)| ≤ δ)
      at hperturb
  obtain ⟨hleftPerturb, hrightPerturb⟩ := hperturb
  exact habstract H hH
    (bourgainGenericExactLeftFrequency
      φ₃ φ₄ hscale hunit D)
    (bourgainGenericExactRightFrequency
      φ₃ φ₄ hscale hunit D)
    (bourgainGenericFrequencyPerturbationSize_nonneg
      X (norm_nonneg _) hρ)
    hsmall hleftPerturb hrightPerturb c₁ c₂

end

end RHTower
