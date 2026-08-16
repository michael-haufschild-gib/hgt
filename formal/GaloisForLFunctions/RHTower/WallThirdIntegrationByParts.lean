import GaloisForLFunctions.RHTower.WallGeneratorThirdJet
import GaloisForLFunctions.RHTower.WallTailIntegrationByParts
import GaloisForLFunctions.HTGeometry.PhaseGeneratorThirdIntegrationByParts

/-!
# The three-fold expansion for the literal Gamma wall

`(45)` for the wall phase: three integrations by parts leave three boundary terms and a remainder
whose amplitude is `O((1+|t|)^{-3})`.

The two-fold expansion suffices for the strip `L²` statement, but not for the derivative one:
multiplication by the frequency is physical differentiation, and after transport the two-fold
remainder integrates `t^{p-2}`, which diverges as soon as `p > 1` — precisely the range
`σ > 1/2` in which the derivative wall `(42)` bites.  The three-fold remainder integrates `t^{p-3}`,
absolutely convergent throughout `0 < σ < 1`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- **`(45)`: the three-fold expansion of the wall phase integral.** -/
theorem wall_phase_ibp_thrice {E : ℂ → ℂ} {T : X →L[ℂ] X} {σ L : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) {a b : ℝ}
    (hgap : ∀ t ∈ uIcc a b, 0 < wallFloor T σ t + L) :
    (∫ t in a..b, wallPhaseMap E T σ L t * 1)
      = (Complex.I : ℂ) • (wallPhaseMap E T σ L b * invFamily (wallGeneratorShift T σ L) b
            - wallPhaseMap E T σ L a * invFamily (wallGeneratorShift T σ L) a)
        + (wallPhaseMap E T σ L b * invFamilyProduct (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) b
            - wallPhaseMap E T σ L a * invFamilyProduct (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) a)
        - (Complex.I : ℂ) • (wallPhaseMap E T σ L b * invFamilyProduct2 (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) b
            - wallPhaseMap E T σ L a * invFamilyProduct2 (wallGeneratorShift T σ L)
              (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) a)
        + (Complex.I : ℂ) • ∫ t in a..b, wallPhaseMap E T σ L t
            * invFamilyProduct2Deriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
              (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t := by
  refine phase_ibp_thrice_of_continuousOn
    (Eder := fun t => (-(Complex.I) : ℂ) • (wallPhaseMap E T σ L t * wallGeneratorShift T σ L t))
    (fun t _ => rfl) (fun t ht => isUnit_wallGeneratorShift hσ0 hσ1 (hgap t ht))
    (fun t _ => hasDerivAt_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShift T hσ0 hσ1 L t)
    (fun t _ => hasDerivAt_wallGeneratorShiftD1 hσ0 hσ1 t)
    (fun t _ => hasDerivAt_wallGeneratorD2 hσ0 hσ1 t) ?_
  exact (continuous_wallGeneratorD3 hσ0 hσ1).continuousOn

end GaloisForLFunctions.RHTower
