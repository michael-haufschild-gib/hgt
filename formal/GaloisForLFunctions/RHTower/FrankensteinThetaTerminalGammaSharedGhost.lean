import GaloisForLFunctions.RHTower.FrankensteinGammaCompositionScaleZeroDescent

/-!
# Terminal theta multiplicity jets as shared Gamma ghosts

Identifies fitted inverse-Gamma ghost at every retained prime with inverse-square norm gain of
literal terminal theta-source multiplicity jet. Two-prime shared-ghost naturality is therefore a
single coefficient-faithful source statement retaining prime labels and exact divisor multiplicity.
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal terminal multiplicity-jet gain at one retained prime. -/
def xiThetaTerminalMultiplicityPrimeGhost
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  (‖xiThetaTerminalMultiplicityCutJet rho 0‖ /
    ‖xiThetaTerminalMultiplicityCutJet rho (Real.log (p : ℝ))‖) ^ 2

/-- The fitted inverse Gamma ghost is not an auxiliary scalar: it is exactly the gain of the
first surviving theta-source multiplicity jet. -/
theorem xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiThetaTerminalMultiplicityPrimeGhost rho p =
      primeGammaLocalInverseOrientedGhost
        (primeDepthBVWoldXiCenteredRate rho) p := by
  let q : XiZeroCopy := ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  calc
    xiThetaTerminalMultiplicityPrimeGhost rho p =
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy q p := by
      symm
      simpa only [q, xiThetaTerminalMultiplicityPrimeGhost] using
        frankensteinThetaPrimeTranslationEnergy_eq_inverse_sq_terminalJetGain q p
    _ = (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate rho) := by
      simpa only [q] using
        HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy_eq q p
    _ = primeGammaLocalInverseOrientedGhost
        (primeDepthBVWoldXiCenteredRate rho) p := rfl

theorem xiThetaTerminalMultiplicityPrimeGhost_pos
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    0 < xiThetaTerminalMultiplicityPrimeGhost rho p := by
  rw [xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost]
  exact primeGammaLocalInverseOrientedGhost_pos _ _

/-- One source-derived scalar is simultaneously the terminal theta-jet gain at primes two and
three. No prime-local countercharacter is part of the datum. -/
def XiThetaTerminalMultiplicityTwoThreeSharedGhost
    (rho : XiDivisorSupport) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    c = xiThetaTerminalMultiplicityPrimeGhost rho deningerCalderonWittPrimeTwo ∧
    c = xiThetaTerminalMultiplicityPrimeGhost rho deningerCalderonWittPrimeThree

theorem xiThetaTerminalMultiplicityTwoThreeSharedGhost_iff_gammaWard
    (rho : XiDivisorSupport) :
    XiThetaTerminalMultiplicityTwoThreeSharedGhost rho ↔
      PrimeGammaTwoThreeSharedInverseOrientedGhostWard
        (primeDepthBVWoldXiCenteredRate rho) := by
  constructor
  · rintro ⟨c, hc, htwo, hthree⟩
    refine ⟨c, hc, ?_, ?_⟩
    · apply (primeGammaInverseOrientedGhostWardEquation_iff
        hc _ deningerCalderonWittPrimeTwo).2
      exact htwo.trans
        (xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost
          rho deningerCalderonWittPrimeTwo)
    · apply (primeGammaInverseOrientedGhostWardEquation_iff
        hc _ deningerCalderonWittPrimeThree).2
      exact hthree.trans
        (xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost
          rho deningerCalderonWittPrimeThree)
  · rintro ⟨c, hc, htwo, hthree⟩
    refine ⟨c, hc, ?_, ?_⟩
    · exact ((primeGammaInverseOrientedGhostWardEquation_iff
        hc _ deningerCalderonWittPrimeTwo).1 htwo).trans
          (xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost
            rho deningerCalderonWittPrimeTwo).symm
    · exact ((primeGammaInverseOrientedGhostWardEquation_iff
        hc _ deningerCalderonWittPrimeThree).1 hthree).trans
          (xiThetaTerminalMultiplicityPrimeGhost_eq_localInverseGammaGhost
            rho deningerCalderonWittPrimeThree).symm

theorem xiThetaTerminalMultiplicityTwoThreeSharedGhost_iff_line
    (rho : XiDivisorSupport) :
    XiThetaTerminalMultiplicityTwoThreeSharedGhost rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiThetaTerminalMultiplicityTwoThreeSharedGhost_iff_gammaWard,
    primeGammaTwoThreeSharedInverseOrientedGhostWard_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- The actual two-prime terminal-jet source law constructs the coefficient-faithful natural
reporter on the genuine Calderon-Witt prime--archimedean boundaries. -/
theorem xiThetaTerminalMultiplicityTwoThreeSharedGhost_constructs_naturalReporter
    (rho : XiDivisorSupport)
    (h : XiThetaTerminalMultiplicityTwoThreeSharedGhost rho) :
    Nonempty
      (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  apply (primeGammaTwoThreeSourceNaturalReporter_nonempty_iff _).2
  exact sourceNaturality_of_primeGammaTwoThreeSharedGhost
    ((xiThetaTerminalMultiplicityTwoThreeSharedGhost_iff_gammaWard rho).1 h)

end

end RHTower

