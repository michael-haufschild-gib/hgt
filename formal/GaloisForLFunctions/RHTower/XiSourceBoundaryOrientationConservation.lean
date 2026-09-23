import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw
import GaloisForLFunctions.RHTower.XiDepthMobiusGammaOuterInnerWeld
import GaloisForLFunctions.HTGeometry.CayleyPoleResidueTransport
import GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw
import GaloisForLFunctions.RHTower.PrimeValuationNormalCornerDuality

/-!
# Source--boundary orientation conservation for Xi

The complete high-exponent zeta source has a canonical prime-two tail
character.  Its reflected logarithmic modulus is not merely a detector
of the critical line: after multiplicity weighting, it is exactly the
horizontal component of the centered Xi divisor charge.

The same invariant is carried by the rational depth-successor nearby
cycle and by the residue of the completed Xi logarithmic current.  Thus
source-tail orientation survives the scale transition to the divisor
boundary without squaring or loss of sign.
-/

open Complex Filter Set
open scoped Topology BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Reflected prime-two tail asymmetry is exactly twice the signed
horizontal displacement, in logarithmic clock units. -/
theorem reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement
    (s : ℂ) :
    Real.log ‖shellTransferCharacter s‖ -
        Real.log ‖shellTransferCharacter (1 - star s)‖ =
      -2 * (s.re - 1 / 2) * Real.log 2 := by
  rw [log_norm_shellTransferCharacter,
    log_norm_shellTransferCharacter]
  have hstarRe : (star s).re = s.re := by simp
  simp only [sub_re, one_re]
  rw [hstarRe]
  ring

/-- The horizontal component of the centered divisor charge is exactly
the reflected source-tail asymmetry, with multiplicity. -/
theorem centeredDivisorCharge_real_eq_reflectedShellTailLogRatio
    (s : ℂ) (m : ℕ) :
    (-((s - 1 / 2) * (m : ℂ))).re =
      (m : ℝ) / (2 * Real.log 2) *
        (Real.log ‖shellTransferCharacter s‖ -
          Real.log ‖shellTransferCharacter (1 - star s)‖) := by
  rw [reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement]
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hcharge :
      (-((s - 1 / 2) * (m : ℂ))).re =
        -(s.re - 1 / 2) * (m : ℝ) := by
    simp only [neg_re, mul_re, sub_re]
    norm_num
    ring
  rw [hcharge]
  field_simp

/-- For the Riemann source point `c = 1`, the source-horizon escape
rate is the negative reflected prime-tail entropy jump. -/
theorem riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy
    (s : ℂ) :
    sourceCayleyTransverseRate 1 s =
      -(Real.log ‖shellTransferCharacter s‖ -
          Real.log ‖shellTransferCharacter (1 - star s)‖) /
        Real.log 2 := by
  rw [reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement]
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  field_simp
  ring

/-- Base-normalized reflected entropy of the canonical prime-two source
tail. -/
def riemannReflectedSourceEntropy (s : ℂ) : ℝ :=
  (Real.log ‖shellTransferCharacter s‖ -
      Real.log ‖shellTransferCharacter (1 - star s)‖) /
    Real.log 2

/-- Reflected prime-tail entropy is exactly the negative Riemann
source-horizon escape rate. -/
theorem riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate
    (s : ℂ) :
    riemannReflectedSourceEntropy s =
      -sourceCayleyTransverseRate 1 s := by
  rw [riemannReflectedSourceEntropy,
    riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy]
  ring

/-- Critical-line reflection reverses the normalized source entropy. -/
theorem riemannReflectedSourceEntropy_reflection
    (s : ℂ) :
    riemannReflectedSourceEntropy (1 - star s) =
      -riemannReflectedSourceEntropy s := by
  have hstarRe : (star s).re = s.re := by simp
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  rw [hstarRe]
  ring

/-- **Entropy-to-asymptotic-type law.** Inside the critical strip, the
sign of reflected arithmetic source entropy selects the Rees species of
the prime-valuation Hellinger sector: negative entropy is equivalent to
flatness beyond every finite Wold Rees order. -/
theorem riemannSourceEntropy_selects_primeValuationReesType
    (s : ℂ) (hstrip : 0 < s.re ∧ s.re < 1) :
    ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow (s.re - 1 / 2)) ↔
      riemannReflectedSourceEntropy s < 0 := by
  have habs : |s.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hstrip.1, hstrip.2]
  rw [primeValuationSquaredHellingerBelow_reesAllOrdersFlat_iff habs,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [sourceCayleyTransverseRate, sub_re, one_re]
  constructor <;> intro h <;> linarith

/-- **Source-normal rank--type product law.** A finite prime-normal packet
has one exact integer rank, simultaneously its Gamma conormal rank,
reciprocal-prime recurrence degree, and least lossless valuation depth.
Independently, the sign of reflected source entropy selects the cofinal
Hellinger--Rees species. -/
theorem sourceNormalRank_entropyType_productLaw
    {N : ℕ} {packet : Fin N → Nat.Primes}
    (hpacket : Function.Injective packet)
    (s : ℂ) (hstrip : 0 < s.re ∧ s.re < 1) :
    Module.finrank ℝ
          (LinearMap.ker
            (GaloisForLFunctions.HTGeometry.packetStreamCoronaConstraint
              ℝ (Fin N))) = N ∧
      (minpoly ℝ
          (xiTransversePrimeValuationTranslation packet)).natDegree = N ∧
      Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix
          N packet).mulVec ∧
      (∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix
            M packet).mulVec) ∧
      (ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
          (primeValuationSquaredHellingerBelow (s.re - 1 / 2)) ↔
        riemannReflectedSourceEntropy s < 0) := by
  have htomo :=
    xiTransversePrimeHalfShiftedValuation_exact_minimal_tomography hpacket
  exact
    ⟨GaloisForLFunctions.HTGeometry.finrank_ker_finPacketStreamCoronaConstraint
        ℝ N,
      xiTransversePrimeValuationTranslation_minpoly_natDegree hpacket,
      htomo.1, htomo.2,
      riemannSourceEntropy_selects_primeValuationReesType s hstrip⟩

/-- At a right-half Xi divisor copy, reflected source entropy is exactly
minus twice the positive modular charge that parametrizes the flat
prime-valuation sector. -/
theorem xiRightReflectedSourceEntropy_eq_neg_two_modularCharge
    (q : XiRightZeroCopy) :
    riemannReflectedSourceEntropy (q.1.1 : ℂ) =
      -2 * xiRightSourceModularCharge q := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [sourceCayleyTransverseRate, sub_re, one_re,
    xiRightSourceModularCharge]
  ring

/-- Multiplicity-weighted Xi charge is minus one half of the Riemann
source-horizon escape rate. -/
theorem centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate
    (s : ℂ) (m : ℕ) :
    (-((s - 1 / 2) * (m : ℂ))).re =
      -(m : ℝ) / 2 * sourceCayleyTransverseRate 1 s := by
  simp only [neg_re, mul_re, sub_re,
    sourceCayleyTransverseRate, one_re]
  norm_num
  ring

/-- **Prime-tail entropy form of Riemann source-horizon conservation.**
At canonical observation time, the Poisson packet tilt of every
transported Riemann-source residue is the negative reflected shell-tail
entropy jump. -/
theorem riemannSourceCayleyResidueMode_horizonConservation_shellTail
    (m rho : ℂ) (tau : ℝ) (r : ℕ) (hrho : rho ≠ 1) :
    let x := sourceCayleyObservationTime 1 rho tau
    x ^ r / r.factorial *
        ‖iteratedDeriv r
          (cayleyPoleResidueMode m 1 rho) (x : ℂ)‖ ^ (2 : ℕ) =
      ‖m‖ ^ (2 : ℕ) *
        Real.exp
          (-(Real.log ‖shellTransferCharacter rho‖ -
              Real.log ‖shellTransferCharacter (1 - star rho)‖) /
            Real.log 2 * tau) *
          poissonOrderWeight tau r := by
  dsimp only
  rw [sourceCayleyResidueMode_horizon_conservation
    m 1 rho tau r hrho]
  rw [riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy]

/-- The two cofinal prime clocks determine the full complex
multiplicity-weighted Xi affine charge, not only its horizontal
component. -/
theorem twoPrimeSourceSpectrum_determines_xiAffineCharge
    {rho eta : ℂ}
    (h :
      twoPrimeShellTransferSpectrum rho =
        twoPrimeShellTransferSpectrum eta) :
    -((rho - 1 / 2) * ((analyticOrderAt xi rho).toNat : ℂ)) =
      -((eta - 1 / 2) * ((analyticOrderAt xi eta).toNat : ℂ)) := by
  have hrho : rho = eta :=
    twoPrimeShellTransferSpectrum_injective h
  subst eta
  rfl

/-- The local completed reciprocal-square orientation term is exactly
the weighted square of reflected arithmetic source entropy. -/
theorem xiZeroCopyThermalOrientationTerm_eq_sourceEntropyDensity
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) =
      riemannReflectedSourceEntropy (q.1 : ℂ) ^ (2 : ℕ) *
          (q.1 : ℂ).im ^ (2 : ℕ) /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
          (q.1 : ℂ).im ^ (2 : ℕ)) ^ (4 : ℕ) := by
  rw [xiZeroCopyReciprocalSquare_im_formula,
    riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  have hrate :
      -sourceCayleyTransverseRate 1 (q.1 : ℂ) =
        -2 * ((q.1 : ℂ).re - 1 / 2) := by
    simp only [sourceCayleyTransverseRate, sub_re, one_re]
    ring
  rw [hrate]
  have hden :
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
          (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    have him : (q.1 : ℂ).im ≠ 0 :=
      xi_divisor_support_im_ne_zero q.1
    nlinarith [sq_pos_of_ne_zero him]
  field_simp [hden]

/-- Global source-entropy orientation energy of the Xi divisor. -/
def xiSourceEntropyOrientationEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    riemannReflectedSourceEntropy (q.1 : ℂ) ^ (2 : ℕ) *
        (q.1 : ℂ).im ^ (2 : ℕ) /
      (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
        (q.1 : ℂ).im ^ (2 : ℕ)) ^ (4 : ℕ)

/-- The global reflected source-entropy energy is exactly the completed
thermal orientation energy. -/
theorem xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy :
    xiSourceEntropyOrientationEnergy =
      xiThermalOrientationEnergy := by
  rw [xiSourceEntropyOrientationEnergy,
    xiThermalOrientationEnergy]
  apply tsum_congr
  intro q
  exact
    (xiZeroCopyThermalOrientationTerm_eq_sourceEntropyDensity q).symm

/-- The total weighted reflected source-entropy energy of all Xi zeros
is unconditionally below `1 / 150000`. -/
theorem xiSourceEntropyOrientationEnergy_lt_one_over_oneHundredFiftyThousand :
    xiSourceEntropyOrientationEnergy < 1 / 150000 := by
  rw [xiSourceEntropyOrientationEnergy_eq_thermalOrientationEnergy]
  exact
    xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand

/-- **Xi source--boundary orientation conservation.**  The nearby-cycle
outer charge, completed Xi residue, and reflected source-tail orientation
carry one horizontal invariant. -/
theorem xiDepthNearby_sourceBoundaryOrientationConservation
    (rho : ℂ) :
    let m := (analyticOrderAt xi rho).toNat
    Tendsto
        (fun w : ℂ =>
          w⁻¹ *
            (depthSuccessorNearbyCycle (rho - 1 / 2) m w⁻¹ - 1))
        (𝓝[≠] 0)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      Tendsto
        (fun s : ℂ =>
          (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      (-((rho - 1 / 2) * (m : ℂ))).re =
        (m : ℝ) / (2 * Real.log 2) *
          (Real.log ‖shellTransferCharacter rho‖ -
            Real.log ‖shellTransferCharacter (1 - star rho)‖) ∧
      sourceCayleyTransverseRate 1 rho =
        -(Real.log ‖shellTransferCharacter rho‖ -
            Real.log ‖shellTransferCharacter (1 - star rho)‖) /
          Real.log 2 := by
  dsimp only
  exact ⟨
    (xiDepthNearby_outerCharge_and_affineResidue_match rho).1,
    (xiDepthNearby_outerCharge_and_affineResidue_match rho).2,
    centeredDivisorCharge_real_eq_reflectedShellTailLogRatio
      rho (analyticOrderAt xi rho).toNat,
    riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy rho⟩

end RHTower
