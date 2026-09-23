import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniQuantizedEscape
import GaloisForLFunctions.HTGeometry.ConstitutiveBalancedDefectZeroIndex

/-!
# Signed-index no-go for quantized theta escape

The quantized Route P obstruction is an unsigned defect number, not a Fredholm index.  One
nonneutral oriented copy has escape multiplicity one and its reflected partner has the same
multiplicity.  The canonical balanced Toeplitz model therefore has zero signed index but unsigned
defect energy two, exactly matching the cofinal reflection-pair theta energy.

Any candidate index that changes sign under reflection cannot represent this positive escape on a
nonneutral pair.  A surviving operator construction must prove vanishing of both defect spaces
(invertibility or sector equivalence), not equality of their dimensions.
-/

open Filter

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Integer multiplicity underlying the real-valued harmonic escape index. -/
def thetaKakutaniEscapeMultiplicity (q : XiZeroCopy) : ℕ :=
  if thetaXiRankTwoBoundaryFlux q = 0 then 0 else 1

theorem thetaKakutaniHarmonicEscapeIndex_eq_natCast
    (q : XiZeroCopy) :
    thetaKakutaniHarmonicEscapeIndex q = thetaKakutaniEscapeMultiplicity q := by
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0 <;>
    simp [thetaKakutaniHarmonicEscapeIndex, thetaKakutaniEscapeMultiplicity, hflux]

/-- Reflection preserves unsigned escape multiplicity. -/
theorem thetaKakutaniEscapeMultiplicity_reflect (q : XiZeroCopy) :
    thetaKakutaniEscapeMultiplicity (xiZeroCopyReflectEquiv q) =
      thetaKakutaniEscapeMultiplicity q := by
  rw [thetaKakutaniEscapeMultiplicity, thetaKakutaniEscapeMultiplicity,
    thetaXiRankTwoBoundaryFlux_reflect]
  simp only [neg_eq_zero]

theorem thetaKakutaniEscapeMultiplicity_eq_zero_iff (q : XiZeroCopy) :
    thetaKakutaniEscapeMultiplicity q = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0 <;>
    simp [thetaKakutaniEscapeMultiplicity, hflux]

theorem thetaKakutaniEscapeMultiplicity_eq_one_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    thetaKakutaniEscapeMultiplicity q = 1 := by
  simp [thetaKakutaniEscapeMultiplicity, hflux]

/-- Balanced reflection always erases the signed Fredholm index, independently of escape size. -/
theorem thetaKakutaniBalancedFredholmIndex_eq_zero (q : XiZeroCopy) :
    doubledIndex (thetaKakutaniEscapeMultiplicity q) = 0 :=
  doubledIndex_eq_zero _

/-- The corresponding unsigned defect energy retains twice the escape multiplicity. -/
theorem thetaKakutaniBalancedUnsignedDefectEnergy_eq
    (q : XiZeroCopy) :
    defectEnergy (thetaKakutaniEscapeMultiplicity q) =
      2 * thetaKakutaniEscapeMultiplicity q :=
  defectEnergy_eq _

/-- On a nonneutral reflected pair, signed index is zero while unsigned defect energy is two. -/
theorem thetaKakutaniBalancedIndex_zero_energy_two_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    doubledIndex (thetaKakutaniEscapeMultiplicity q) = 0 ∧
      defectEnergy (thetaKakutaniEscapeMultiplicity q) = 2 := by
  rw [thetaKakutaniBalancedFredholmIndex_eq_zero,
    thetaKakutaniBalancedUnsignedDefectEnergy_eq,
    thetaKakutaniEscapeMultiplicity_eq_one_of_boundaryFlux_ne_zero q hflux]
  norm_num

/-- Exact operator dictionary: the cofinal reflected theta energy converges to the unsigned defect
energy of the balanced Toeplitz model with the same escape multiplicity. -/
theorem tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass_eq_defectEnergy
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ (2 : ℕ) +
            thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ (2 : ℕ))) /
            primeReciprocalMass s)
      Filter.atTop
      (nhds (defectEnergy (thetaKakutaniEscapeMultiplicity q) : ℝ)) := by
  have henergy : defectEnergy (thetaKakutaniEscapeMultiplicity q) = 2 :=
    (thetaKakutaniBalancedIndex_zero_energy_two_of_boundaryFlux_ne_zero q hflux).2
  simpa [henergy] using
    tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass q hflux

/-- **Signed-index no-go.** A reflection-odd integer invariant cannot equal the positive escape
multiplicity on both members of any nonneutral reflection pair. -/
theorem reflectionOdd_integerIndex_ne_escapeMultiplicity_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0)
    (J : XiZeroCopy → ℤ)
    (hodd : J (xiZeroCopyReflectEquiv q) = -J q) :
    ¬ (J q = (thetaKakutaniEscapeMultiplicity q : ℤ) ∧
      J (xiZeroCopyReflectEquiv q) =
        (thetaKakutaniEscapeMultiplicity (xiZeroCopyReflectEquiv q) : ℤ)) := by
  intro hrep
  have hq : thetaKakutaniEscapeMultiplicity q = 1 :=
    thetaKakutaniEscapeMultiplicity_eq_one_of_boundaryFlux_ne_zero q hflux
  have hreflect : thetaKakutaniEscapeMultiplicity (xiZeroCopyReflectEquiv q) = 1 := by
    rw [thetaKakutaniEscapeMultiplicity_reflect, hq]
  rw [hrep.1, hrep.2, hq, hreflect] at hodd
  norm_num at hodd

end

end RHTower.HedenmalmThetaSource
