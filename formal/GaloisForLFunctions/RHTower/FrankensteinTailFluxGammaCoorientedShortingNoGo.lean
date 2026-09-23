import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePApertureTailFluxBridge
import GaloisForLFunctions.RHTower.GammaCoorientedPositiveConeNoShorting

/-!
# P-G188 tail flux cannot be shorted by positive Gamma reflection pairing

The exact P-G188/CCM aperture flux supplies a positive weight on every promoted
prime-depth cell.  Pairing those weights against the reflection-odd Gamma exterior
does annihilate before coorientation is retained.  After the physical horizontal
coorientation is restored, both reflected terms have the same sign and their
charge is strictly positive away from the balanced section.

This closes the natural positive-Schur shorting attempt.  Any surviving source
shorting law must carry genuinely sign-changing cross-incidence data; reflection
parity alone cannot provide it.
-/

namespace RHTower

noncomputable section

/-- Natural positive Schur coupling of two P-G188 infinitesimal tail-flux cells. -/
def frankensteinTailFluxGammaPairWeight
    (i j : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveBurnolApertureDefectFlux i *
    routePPrimitiveBurnolApertureDefectFlux j

theorem frankensteinTailFluxGammaPairWeight_pos
    (i j : Nat.Primes × ℕ) :
    0 < frankensteinTailFluxGammaPairWeight i j := by
  exact mul_pos
    (routePPrimitiveBurnolApertureDefectFlux_pos i)
    (routePPrimitiveBurnolApertureDefectFlux_pos j)

theorem frankensteinTailFluxGammaPairWeight_swap
    (i j : Nat.Primes × ℕ) :
    frankensteinTailFluxGammaPairWeight j i =
      frankensteinTailFluxGammaPairWeight i j := by
  rw [frankensteinTailFluxGammaPairWeight,
    frankensteinTailFluxGammaPairWeight]
  ring

/-- Naive reflection pairing cancels because it has forgotten which orientation
carries horizontal displacement. -/
theorem frankensteinTailFluxGamma_uncooriented_swap_annihilates
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    frankensteinTailFluxGammaPairWeight i j *
        xiGammaEulerPrimitiveReflectionOddExterior a i j +
      frankensteinTailFluxGammaPairWeight j i *
        xiGammaEulerPrimitiveReflectionOddExterior a j i = 0 := by
  rw [frankensteinTailFluxGammaPairWeight_swap,
    xiGammaEulerPrimitiveReflectionOddExterior_swap]
  ring

/-- Physical coorientation reverses together with the Gamma exterior.  Thus a
positive P-G188 pair has strictly positive horizontal charge off the balanced
section, rather than shorting it. -/
theorem frankensteinTailFluxGamma_cooriented_swap_noShorting
    (a : ℝ) (ha : a ≠ 0) (i j : Nat.Primes × ℕ) (hij : i ≠ j) :
    0 < a *
      (frankensteinTailFluxGammaPairWeight i j *
          xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j +
        frankensteinTailFluxGammaPairWeight j i *
          xiGammaEulerPrimitiveCoorientedReflectionOddExterior a j i) := by
  have hheight : xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
      xiGammaEulerBoundaryHalfHeight j.1 j.2 := by
    intro h
    exact hij
      (PrimitivePromotedCellHodgeRigidity.xiGammaEulerBoundaryHalfHeight_cell_injective h)
  have hheight' : xiGammaEulerBoundaryHalfHeight j.1 j.2 ≠
      xiGammaEulerBoundaryHalfHeight i.1 i.2 := Ne.symm hheight
  have hw := frankensteinTailFluxGammaPairWeight_pos i j
  have hw' := frankensteinTailFluxGammaPairWeight_pos j i
  have hg := xiGammaEulerPrimitiveCoorientedReflectionGauge_pos a i j hheight
  have hg' := xiGammaEulerPrimitiveCoorientedReflectionGauge_pos a j i hheight'
  rw [xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge,
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge]
  have hsum : 0 <
      frankensteinTailFluxGammaPairWeight i j *
          xiGammaEulerPrimitiveCoorientedReflectionGauge a i j +
        frankensteinTailFluxGammaPairWeight j i *
          xiGammaEulerPrimitiveCoorientedReflectionGauge a j i :=
    add_pos (mul_pos hw hg) (mul_pos hw' hg')
  calc
    a *
        (frankensteinTailFluxGammaPairWeight i j *
            (a * xiGammaEulerPrimitiveCoorientedReflectionGauge a i j) +
          frankensteinTailFluxGammaPairWeight j i *
            (a * xiGammaEulerPrimitiveCoorientedReflectionGauge a j i)) =
      a ^ (2 : ℕ) *
        (frankensteinTailFluxGammaPairWeight i j *
            xiGammaEulerPrimitiveCoorientedReflectionGauge a i j +
          frankensteinTailFluxGammaPairWeight j i *
            xiGammaEulerPrimitiveCoorientedReflectionGauge a j i) := by ring
    _ > 0 := mul_pos (sq_pos_of_ne_zero ha) hsum

end

end RHTower
