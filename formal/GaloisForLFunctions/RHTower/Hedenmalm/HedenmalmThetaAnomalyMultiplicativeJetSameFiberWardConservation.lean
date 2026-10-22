import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolMultiplicativeJetCartierTransgression
import GaloisForLFunctions.RHTower.RouteRBurnolThetaSameFiberOrientation

/-!
# Same-fibre multiplicative-jet/theta Ward conservation

The arithmetic multiplicative-jet current and the compact completed-Xi/theta boundary current obey
an exact signed conservation law on every individual Xi multiplicity copy.  A second form identifies
the arithmetic channel with Cartier's physical head-energy transgression.

The conservation law is unconditional but nontrivial off the critical line: on a hypothetical
right-half divisor its theta channel is strictly negative and its arithmetic channel strictly
positive.  Thus total signed-current cancellation is not a Route P producer.  RH requires
channelwise flatness, not conservation of the indefinite two-channel current.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- **Division-free same-fibre Ward conservation.**  Arithmetic frame energy times the normalized
compact-theta boundary current cancels the anti-Hermitian multiplicative-jet numerator times the
completed first-divided Xi energy on every Xi copy. -/
theorem thetaXiMultiplicativeJet_sameFiber_signedWardConservation (q : XiZeroCopy) :
    burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
          (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) +
        (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
          ‖completedXiFirstDividedL2 q.1‖ ^ 2 = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_completedXi_sameFiber,
    burnolMultiplicativeJetConnectionNumerator_eq]
  simp only [mul_im, neg_re, ofReal_im, mul_zero, neg_im, ofReal_re, zero_add]
  ring

/-- **Physical Cartier form of same-fibre Ward conservation.**  At a right-half Xi divisor, the
normalized compact-theta boundary current and Cartier's transferred head-energy defect cancel
after multiplication by their canonical positive channel energies. -/
theorem thetaXiCartier_sameFiber_signedWardConservation
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    2 * burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) *
          (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) +
        ‖completedXiFirstDividedL2 q.1‖ ^ 2 *
          (burnolSoninGammaHeadEnergy (1 / 2)
              (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
            burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom) = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_completedXi_sameFiber,
    xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_neg_two_connection_im_mul_headFlux]
  rw [burnolMultiplicativeJetSpectralConnection_eq]
  simp only [xiSpectralPoint_eq_support]
  ring

/-- The compact-theta Ward channel is strictly negative at every hypothetical right-half Xi
divisor. -/
theorem thetaXiMultiplicativeJet_sameFiber_thetaChannel_neg
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
      (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) < 0 := by
  exact mul_neg_of_pos_of_neg
    (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q))
    (mul_neg_of_pos_of_neg
      (mul_pos Real.pi_pos thetaSource.mass_pos)
      (thetaXiRankTwoBoundaryFlux_neg_of_rightHalf q h))

/-- The arithmetic multiplicative-jet Ward channel is strictly positive at every hypothetical
right-half Xi divisor. -/
theorem thetaXiMultiplicativeJet_sameFiber_arithmeticChannel_pos
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    0 < (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
      ‖completedXiFirstDividedL2 q.1‖ ^ 2 := by
  have hJ :
      0 < (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im := by
    simpa only [xiSpectralPoint_eq_support] using
      xiDivisor_burnolMultiplicativeJetConnectionNumerator_im_pos q.1 h
  exact mul_pos hJ
    (sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero q.1)))

/-- The theta channel vanishes exactly on the critical line. -/
theorem thetaXiMultiplicativeJet_sameFiber_thetaChannel_eq_zero_iff (q : XiZeroCopy) :
    burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
          (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [mul_eq_zero]
  have hE := (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q)).ne'
  simp only [hE, false_or]
  rw [mul_eq_zero]
  have hpiM := (mul_pos Real.pi_pos thetaSource.mass_pos).ne'
  simp only [hpiM, false_or]
  rw [thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero,
    xiSpectralPoint_im_eq]
  constructor <;> intro hz <;> linarith

/-- The arithmetic channel vanishes exactly on the critical line. -/
theorem thetaXiMultiplicativeJet_sameFiber_arithmeticChannel_eq_zero_iff (q : XiZeroCopy) :
    (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
          ‖completedXiFirstDividedL2 q.1‖ ^ 2 = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [mul_eq_zero]
  have hN : ‖completedXiFirstDividedL2 q.1‖ ^ 2 ≠ 0 :=
    (sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero q.1))).ne'
  simp only [hN, or_false]
  rw [burnolMultiplicativeJetConnectionNumerator_eq]
  simp only [mul_im, neg_re, ofReal_im, mul_zero, neg_im, ofReal_re, zero_add]
  rw [mul_eq_zero]
  have hE := (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q)).ne'
  simp only [hE, or_false, neg_eq_zero]
  rw [xiSpectralPoint_im_eq]
  constructor <;> intro hz <;> linarith

/-- Channelwise flatness, unlike total-current conservation, is exactly critical-line placement. -/
theorem thetaXiMultiplicativeJet_sameFiber_channelwiseFlat_iff (q : XiZeroCopy) :
    (burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
          (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) = 0 ∧
        (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
          ‖completedXiFirstDividedL2 q.1‖ ^ 2 = 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiMultiplicativeJet_sameFiber_thetaChannel_eq_zero_iff,
    thetaXiMultiplicativeJet_sameFiber_arithmeticChannel_eq_zero_iff, and_self]

/-- **Nontriviality of the conserved Ward pair.**  On a hypothetical right-half zero, the two
conserved channels have strict opposite signs even though their sum is exactly zero. -/
theorem thetaXiMultiplicativeJet_sameFiber_nontrivial_signedWardPair
    (q : XiZeroCopy) (h : 1 / 2 < (q.1 : ℂ).re) :
    burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
          (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) < 0 ∧
      0 < (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
          ‖completedXiFirstDividedL2 q.1‖ ^ 2 ∧
      burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
            (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) +
          (burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q)).im *
            ‖completedXiFirstDividedL2 q.1‖ ^ 2 = 0 := by
  exact ⟨thetaXiMultiplicativeJet_sameFiber_thetaChannel_neg q h,
    thetaXiMultiplicativeJet_sameFiber_arithmeticChannel_pos q h,
    thetaXiMultiplicativeJet_sameFiber_signedWardConservation q⟩

end RHTower
