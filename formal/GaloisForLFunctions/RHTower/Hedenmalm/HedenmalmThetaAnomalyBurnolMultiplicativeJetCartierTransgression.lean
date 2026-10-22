import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolMultiplicativeJetConnection
import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux

/-!
# Arithmetic multiplicative jets as Cartier head-energy transgression

The arithmetic connection recovered by differentiating the exact completed `6 = 2 * 3` Burnol
syzygy is the source variable of Cartier's Archimedean head-energy transgression.  At every
hypothetical right-half Xi divisor, the division-free Hermitian jet numerator pairs with the
strictly positive oriented Cartier head flux to give the frame-energy-weighted transferred energy
defect.

This identifies two previously separate Route P receivers.  It does not prove their common
horizontal class vanishes.  Instead, strict positivity shows that the positive Cartier completion
amplifies that class on the right half of the critical strip; a successful Ward law must therefore
contribute a genuinely opposite signed source term before positive energy completion.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- **Normalized multiplicative-jet/Cartier transgression.**  The Cartier head-energy defect is
the oriented head flux paired with minus twice the imaginary part of the arithmetic spectral
connection. -/
theorem xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_neg_two_connection_im_mul_headFlux
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom =
      -2 * (burnolMultiplicativeJetSpectralConnection
          (xiSpectralPointSupport rho)).im *
        burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  have him :
      (xiSpectralPointSupport rho).im = 1 / 2 - (rho : ℂ).re := by
    simpa only [q, xiSpectralPoint_eq_support] using xiSpectralPoint_im_eq q
  rw [xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux rho h,
    burnolMultiplicativeJetSpectralConnection_eq, him]
  ring

/-- **Division-free multiplicative-jet/Cartier bridge.**  Frame energy times the transferred
Cartier head-energy defect is exactly twice the oriented head flux times the imaginary part of the
Hermitian arithmetic jet numerator.  No division by the frame energy occurs. -/
theorem xiDivisor_burnolMultiplicativeJet_frameEnergy_mul_cartierHeadEnergyDefect_eq_pairing
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolTwoPrimeFrameEnergy (xiSpectralPointSupport rho) *
          (burnolSoninGammaHeadEnergy (1 / 2)
              (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
            burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom) =
      2 * burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) *
        (burnolMultiplicativeJetConnectionNumerator
          (xiSpectralPointSupport rho)).im := by
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  have hhorizontal :
      (thetaXiBurnolGaussianHorizontalGauge q).re =
        2 * ((rho : ℂ).re - 1 / 2) := by
    rw [thetaXiBurnolGaussianHorizontalGauge_eq_multiplicativeJetConnection,
      burnolMultiplicativeJetSpectralConnection_eq, xiSpectralPoint_im_eq]
    simp only [ofReal_re]
    change -2 * (1 / 2 - (rho : ℂ).re) = 2 * ((rho : ℂ).re - 1 / 2)
    ring
  have hjet :
      (2 * ((rho : ℂ).re - 1 / 2)) *
          burnolTwoPrimeFrameEnergy (xiSpectralPointSupport rho) =
        2 * (burnolMultiplicativeJetConnectionNumerator
          (xiSpectralPointSupport rho)).im := by
    rw [← hhorizontal]
    simpa only [q, xiSpectralPoint_eq_support] using
      thetaXiBurnolGaussianHorizontalGauge_mul_frameEnergy_eq_jetNumerator_im q
  rw [xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux rho h]
  calc
    burnolTwoPrimeFrameEnergy (xiSpectralPointSupport rho) *
          ((2 * ((rho : ℂ).re - 1 / 2)) *
            burnolSoninOrientedGammaHeadFlux (1 / 2)
              (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom)) =
        ((2 * ((rho : ℂ).re - 1 / 2)) *
          burnolTwoPrimeFrameEnergy (xiSpectralPointSupport rho)) *
            burnolSoninOrientedGammaHeadFlux (1 / 2)
              (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by ring
    _ = (2 * (burnolMultiplicativeJetConnectionNumerator
          (xiSpectralPointSupport rho)).im) *
            burnolSoninOrientedGammaHeadFlux (1 / 2)
              (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by rw [hjet]
    _ = 2 * burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) *
        (burnolMultiplicativeJetConnectionNumerator
          (xiSpectralPointSupport rho)).im := by ring

/-- On every hypothetical right-half Xi divisor, the anti-Hermitian arithmetic jet numerator has
strictly positive orientation. -/
theorem xiDivisor_burnolMultiplicativeJetConnectionNumerator_im_pos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    0 < (burnolMultiplicativeJetConnectionNumerator
      (xiSpectralPointSupport rho)).im := by
  have hE := burnolTwoPrimeFrameEnergy_pos (xiSpectralPointSupport rho)
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  have him :
      (xiSpectralPointSupport rho).im = 1 / 2 - (rho : ℂ).re := by
    simpa only [q, xiSpectralPoint_eq_support] using xiSpectralPoint_im_eq q
  rw [burnolMultiplicativeJetConnectionNumerator_eq]
  simp only [mul_im, neg_re, ofReal_im, mul_zero, neg_im, ofReal_re, zero_add]
  rw [him]
  nlinarith

/-- The arithmetic-jet/Cartier source pairing is strictly positive at every hypothetical
right-half Xi divisor. -/
theorem xiDivisor_burnolMultiplicativeJet_cartierHeadFlux_pairing_pos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    0 < 2 * burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) *
        (burnolMultiplicativeJetConnectionNumerator
          (xiSpectralPointSupport rho)).im := by
  exact mul_pos
    (mul_pos two_pos
      (xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift_pos rho h))
    (xiDivisor_burnolMultiplicativeJetConnectionNumerator_im_pos rho h)

/-- The division-free transgression is strictly positive on the right half of the critical strip.
This is the exact positive survivor: Cartier completion amplifies rather than cancels the
anti-Hermitian arithmetic connection. -/
theorem xiDivisor_burnolMultiplicativeJet_frameEnergy_mul_cartierHeadEnergyDefect_pos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    0 < burnolTwoPrimeFrameEnergy (xiSpectralPointSupport rho) *
      (burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom) := by
  rw [xiDivisor_burnolMultiplicativeJet_frameEnergy_mul_cartierHeadEnergyDefect_eq_pairing rho h]
  exact xiDivisor_burnolMultiplicativeJet_cartierHeadFlux_pairing_pos rho h

end RHTower
