import GaloisForLFunctions.RHTower.FZZCigarFermiCouplingExchange
import GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation
import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# FZZ Fermi-characteristic / parity-Mellin amplitude no-go

The FZZ shared-coupling characteristic is a literal normalized Fourier amplitude
of the integrated Fermi coupling density.  It is nonzero at every real momentum.
The source-native FZZ parity Mellin amplitude, in contrast, has an actual divisor:
every `XiZeroCopy` supplies a parity-Mellin zero, and the corpus proves this type is
nonempty.

Therefore no momentum assignment—not merely no affine calibration—can make the
Fermi characteristic itself equal the FZZ parity-Mellin amplitude at every complex
spectral point.  The contradiction is at one actual divisor point: the latter
amplitude vanishes and the former does not.

This kills the FZZ-P subroute

`shared Fermi characteristic -> global source/Mellin amplitude identity
  -> parity-Mellin divisor -> Ward passivity -> RH`.

The positive classification is sharp: the characteristic can remain a nonzero
normalizing factor, but cannot carry the divisor.  Any viable source-to-Mellin
transmutation must introduce a literal divisor-bearing marked, cross-charge, or
nonlocal Ward factor; relabelling this nonzero characteristic as the source divisor
is excluded.
-/

namespace RHTower

noncomputable section

/-- No choice of Fermi coupling scale and real momentum assignment realizes the complete
parity-Mellin source amplitude as the everywhere-nonzero Fermi characteristic. -/
theorem not_exists_fzzFermiCouplingCharacteristic_mellin_identification :
    ¬ ∃ (v : ℝ) (momentum : ℂ → ℝ), ∀ rho : ℂ,
      fzzCigarParityMellin rho =
        GaloisForLFunctions.RHTower.fzzFermiCouplingCharacteristic v (momentum rho) := by
  rintro ⟨v, momentum, h⟩
  let q : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hmode : FZZCigarParityMellinMode (deningerDivisorThetaEigen q) :=
    fzzCigarParityMellinMode_deningerDivisorThetaEigen q
  have hident := h (deningerDivisorThetaEigen q)
  rw [FZZCigarParityMellinMode] at hmode
  rw [hmode] at hident
  exact (GaloisForLFunctions.RHTower.fzzFermiCouplingCharacteristic_ne_zero
    v (momentum (deningerDivisorThetaEigen q))) hident.symm

/-- Closed FZZ-P route class: a nonvanishing Fermi characteristic is not the divisor-carrying
parity-Mellin source amplitude under any global momentum frame. -/
def FZZCigarFermiCharacteristicMellinAmplitudeRouteKilled : Prop :=
  ¬ ∃ (v : ℝ) (momentum : ℂ → ℝ), ∀ rho : ℂ,
    fzzCigarParityMellin rho =
      GaloisForLFunctions.RHTower.fzzFermiCouplingCharacteristic v (momentum rho)

theorem fzzCigarFermiCharacteristicMellinAmplitudeRouteKilled :
    FZZCigarFermiCharacteristicMellinAmplitudeRouteKilled :=
  not_exists_fzzFermiCouplingCharacteristic_mellin_identification

end

end RHTower
