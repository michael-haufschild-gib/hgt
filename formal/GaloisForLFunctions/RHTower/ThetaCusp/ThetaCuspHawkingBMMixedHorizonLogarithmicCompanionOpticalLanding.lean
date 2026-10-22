import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionPhysical
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer

/-!
# Finite-radiation optical landing of the BM logarithmic companion

The existing gauge-fixed Einstein radiation vector has a canonical complex-linear horizon optical
reader. Composing it with the explicit logarithmic sheet response makes the Xi monodromy response
source-faithful at the finite radiation level. Freezing the conjugate first slot gives a genuinely
complex-linear Gram cokernel whose self-readout is exactly the horizon helicity flux. This avoids
the invalid move of treating `normSq` itself as complex-linear.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical complex-linear horizon optical reader on the four-coordinate BM radiation space. -/
def d4BMXiMixedHorizonRadiationOpticalProjection
    (q : XiZeroCopy) : EuclideanSpace ℂ (Fin 4) →ₗ[ℂ] ℂ where
  toFun radiation :=
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q * radiation 0
  map_add' x y := by
    simp
    ring
  map_smul' c x := by
    simp
    ring

/-- Applying canonical reader to actual full Einstein radiation is existing optical source
projection. -/
theorem d4BMXiMixedHorizonRadiationOpticalProjection_apply
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonRadiationOpticalProjection q
        (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
          amplitude orthogonalMixing q) =
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q :=
  rfl

/-- Concrete sheet response of an actual four-coordinate BM radiation source. -/
def d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse
    (n k : ℕ) (q : XiZeroCopy) (logSheet : ℂ → ℂ) :
    EuclideanSpace ℂ (Fin 4) →ₗ[ℂ] (ℂ → ℂ) :=
  d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse
    n k q (d4BMXiMixedHorizonRadiationOpticalProjection q) logSheet

/-- On actual Einstein radiation, deck response is optical amplitude times exact Xi monodromy
mode. -/
theorem d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse_sub_apply
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (logPlus logMinus : ℂ → ℂ) (z : ℂ) (hz : ‖z‖ₑ < 1)
    (hlog : logPlus z - logMinus z = 2 * Real.pi * Complex.I) :
    ((d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse
          n k q logPlus -
        d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse
          n k q logMinus)
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
        amplitude orthogonalMixing q)) z =
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q *
        d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  simpa only [d4BMXiMixedHorizonRadiationLogarithmicCompanionSheetResponse,
    d4BMXiMixedHorizonRadiationOpticalProjection_apply] using
      d4BMXiMixedHorizonProjectedLogarithmicCompanionSheetResponse_sub_apply
        n k q (d4BMXiMixedHorizonRadiationOpticalProjection q)
        logPlus logMinus
        (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
          amplitude orthogonalMixing q) z hz hlog

/-- Complex-linear Gram cokernel obtained by freezing conjugate optical amplitude of actual
radiation in first slot. -/
def d4BMXiMixedHorizonRadiationOpticalGramCokernel
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    EuclideanSpace ℂ (Fin 4) →ₗ[ℂ] ℂ where
  toFun radiation :=
    (starRingEnd ℂ) (d4BMMixedHorizonOpticalSourceProjection
      amplitude orthogonalMixing q) *
      d4BMXiMixedHorizonRadiationOpticalProjection q radiation
  map_add' x y := by
    simp
    ring
  map_smul' c x := by
    simp
    ring

/-- Frozen Gram cokernel applied to its generating radiation is exact optical squared modulus. -/
theorem d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonRadiationOpticalGramCokernel amplitude orthogonalMixing q
        (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
          amplitude orthogonalMixing q) =
      (Complex.normSq
        (d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q) : ℂ) := by
  change
    (starRingEnd ℂ) (d4BMMixedHorizonOpticalSourceProjection
        amplitude orthogonalMixing q) *
        d4BMXiMixedHorizonRadiationOpticalProjection q
          (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
            amplitude orthogonalMixing q) = _
  rw [d4BMXiMixedHorizonRadiationOpticalProjection_apply]
  rw [mul_comm, Complex.mul_conj]

/-- Same Gram readout is exact gauge-fixed horizon orthogonal-helicity flux. -/
theorem d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply_eq_flux
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonRadiationOpticalGramCokernel amplitude orthogonalMixing q
        (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
          amplitude orthogonalMixing q) =
      (d4ThetaFullEinsteinGaugeFixedHorizonOrthogonalHelicityFlux
        amplitude orthogonalMixing q : ℂ) := by
  rw [d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply,
    normSq_d4BMMixedHorizonOpticalSourceProjection]

/-- Finite-radiation monodromy coefficient read by canonical optical Gram. -/
def d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiMixedHorizonComplexMonodromyJump n k q *
    d4BMXiMixedHorizonRadiationOpticalGramCokernel amplitude orthogonalMixing q
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
        amplitude orthogonalMixing q)

/-- Canonical finite-radiation deck/Gram coefficient is exactly existing causal optical section. -/
theorem d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient_eq_causalOpticalSection
    (n k : ℕ) (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient
        n k amplitude orthogonalMixing q =
      d4BMXiMixedHorizonCausalOpticalSection
        n k amplitude orthogonalMixing q := by
  rw [d4BMXiMixedHorizonFiniteRadiationOpticalDeckCoefficient,
    d4BMXiMixedHorizonRadiationOpticalGramCokernel_apply]
  rfl

end

end RHTower
