import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSingularDepthLowering
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedCofinalDepthCountertransport

/-!
# Source-normal Gamma / BV--Wold Schatten bridge

The singular prime multiplier in inverse-Wold depth lowering is already present in the physical
Route-J source.  One critical Gamma deattenuation has square `p`; hence the two polarized source
legs produce exactly the multiplier which lowers a BV--Wold logarithmic coefficient by one depth.
This identifies the abstract affine graph domain with a source-derived operation.
-/

namespace RHTower

noncomputable section

open PrimitivePromotedCofinalDepth

/-- One source-normal Gamma depth deattenuation has squared gain exactly `p`. -/
theorem criticalDepthDeattenuation_sq_one
    (p : Nat.Primes) (sourceDepth : ℕ) :
    criticalDepthDeattenuation (p, sourceDepth) 1 ^ (2 : ℕ) = (p : ℝ) := by
  simpa using criticalDepthDeattenuation_sq (p, sourceDepth) 1

/-- Affine lowering written entirely in source-normal Gamma coordinates. -/
def primeDepthBVWoldSourceNormalDepthLowering
    (sourceDepth : ℕ) (f : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  criticalDepthDeattenuation (p, sourceDepth) 1 ^ (2 : ℕ) *
      (f p - woldRemainder p) +
    woldRemainder p

/-- Source-normal lowering is exactly the renormalized inverse-Wold operation. -/
theorem primeDepthBVWoldSourceNormalDepthLowering_eq
    (sourceDepth : ℕ) (f : Nat.Primes → ℝ) :
    primeDepthBVWoldSourceNormalDepthLowering sourceDepth f =
      primeDepthBVWoldRenormalizedDepthLowering f := by
  funext p
  rw [primeDepthBVWoldSourceNormalDepthLowering,
    primeDepthBVWoldRenormalizedDepthLowering,
    criticalDepthDeattenuation_sq_one]

/-- The physical two-leg source operation lowers the actual atlas coefficient by one Wold depth. -/
theorem primeDepthBVWoldSourceNormalDepthLowering_relativeLogCoefficient
    (rho : XiDivisorSupport) (sourceDepth e : ℕ) :
    primeDepthBVWoldSourceNormalDepthLowering sourceDepth
        (primeDepthBVWoldXiRelativeLogCoefficient rho (e + 1)) =
      primeDepthBVWoldXiRelativeLogCoefficient rho e := by
  rw [primeDepthBVWoldSourceNormalDepthLowering_eq]
  funext p
  exact
    primeDepthBVWoldRenormalizedDepthLowering_relativeLogCoefficient rho e p

/-- Source-normal graph domain inside the trace-class prime coefficient space. -/
def PrimeDepthBVWoldSourceNormalDepthLoweringTraceDomain
    (sourceDepth : ℕ) (f : Nat.Primes → ℝ) : Prop :=
  Summable f ∧
    Summable (primeDepthBVWoldSourceNormalDepthLowering sourceDepth f)

/-- Source-normal and abstract inverse-Wold graph domains are identical. -/
theorem sourceNormalDepthLoweringTraceDomain_iff
    (sourceDepth : ℕ) (f : Nat.Primes → ℝ) :
    PrimeDepthBVWoldSourceNormalDepthLoweringTraceDomain sourceDepth f ↔
      PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain f := by
  rw [PrimeDepthBVWoldSourceNormalDepthLoweringTraceDomain,
    PrimeDepthBVWoldRenormalizedDepthLoweringTraceDomain,
    primeDepthBVWoldSourceNormalDepthLowering_eq]

/-- The unconditional depth-two family belongs to the physical source-normal graph domain exactly
on the critical line. -/
theorem relativeLogCoefficient_two_mem_sourceNormalDepthLoweringTraceDomain_iff
    (rho : XiDivisorSupport) (sourceDepth : ℕ) :
    PrimeDepthBVWoldSourceNormalDepthLoweringTraceDomain sourceDepth
        (primeDepthBVWoldXiRelativeLogCoefficient rho 2) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [sourceNormalDepthLoweringTraceDomain_iff,
    relativeLogCoefficient_two_mem_renormalizedDepthLoweringTraceDomain_iff]

/-- Global physical source-normal graph admission. -/
def PrimeDepthBVWoldXiSourceNormalDepthLoweringLanding
    (sourceDepth : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeDepthBVWoldSourceNormalDepthLoweringTraceDomain sourceDepth
      (primeDepthBVWoldXiRelativeLogCoefficient rho 2)

/-- Global source-normal depth lowering is exactly RH; this isolates the remaining producer. -/
theorem primeDepthBVWoldXiSourceNormalDepthLoweringLanding_iff_riemannHypothesis
    (sourceDepth : ℕ) :
    PrimeDepthBVWoldXiSourceNormalDepthLoweringLanding sourceDepth ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (relativeLogCoefficient_two_mem_sourceNormalDepthLoweringTraceDomain_iff
        rho sourceDepth).1 (h rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH rho
    exact
      (relativeLogCoefficient_two_mem_sourceNormalDepthLoweringTraceDomain_iff
        rho sourceDepth).2 (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
