import GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue

/-!
# JAS Gamma--theta closed-flat off-wall compatibility no-go

Closedness, dense domain, exact Gamma--theta packet action, and two-prime flatness cannot force the
critical wall.  On a hypothetical nonneutral Xi copy, choose the positive aperture given by the
absolute centered rate.  The complete existing creator package then remains valid, while the same
copy carries exactly one unit of double-logarithmic physical half-density energy.

This module packages that compatibility and proves its global existence equivalent to failure of
RH.  Thus the creator's current operator-theoretic properties are not an RH producer.  A surviving
route must add a law excluding the unit residue, such as genuinely reflected prime-source
linearity or a source-derived trace cancellation.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource

/-- Complete Gamma--theta creator package with the positive-aperture implication discharged. -/
def JASGammaThetaPositiveApertureClosedFlatPackage (x : ℝ) : Prop :=
  0 < x ∧
    ∀ (p q : Nat.Primes) (P : JASGammaThetaSupport) (r : ℕ),
      Dense ((jasGammaThetaCreation x p).domain : Set JASGammaThetaL2) ∧
      (jasGammaThetaCreation x p).IsClosed ∧
      jasGammaThetaCreation x p (jasGammaThetaPacketDomain x p P r) =
        (jasGammaThetaEffectiveGain x p P : ℂ) •
          jasGammaThetaPacket (jasGammaSupportToggle p P) (r + 1) ∧
      jasGammaThetaCreation x q
          (jasGammaThetaSecondPathDomain x p q P r) =
        jasGammaThetaCreation x p
          (jasGammaThetaSecondPathDomain x q p P r)

/-- Every positive aperture carries the complete closed/dense/exact/flat creator package. -/
theorem jasGammaThetaPositiveApertureClosedFlatPackage
    {x : ℝ} (hx : 0 < x) :
    JASGammaThetaPositiveApertureClosedFlatPackage x := by
  refine ⟨hx, ?_⟩
  intro p q P r
  have h := jasGammaThetaClosedCreation_package x p q P r
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 hx⟩

/-- Existing Gamma--theta creator structure at absolute centered rate, coupled to unit physical
double-log residue.  This is the exact certificate surviving on a hypothetical off-wall copy. -/
def JASGammaThetaClosedFlatUnitResidueCertificate (q : XiZeroCopy) : Prop :=
  JASGammaThetaPositiveApertureClosedFlatPackage
      |primeDepthBVWoldXiCenteredRate q.1| ∧
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 1)

/-- The complete current creator package plus unit residue is exactly same-copy nonneutrality. -/
theorem jasGammaThetaClosedFlatUnitResidueCertificate_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    JASGammaThetaClosedFlatUnitResidueCertificate q ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro h
    exact
      (tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_iff_boundaryFlux_ne_zero
        q).1 h.2
  · intro hflux
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      intro hzero
      apply hflux
      rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, hzero]
      ring
    exact ⟨jasGammaThetaPositiveApertureClosedFlatPackage (abs_pos.mpr hrate),
      (tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_iff_boundaryFlux_ne_zero
        q).2 hflux⟩

/-- **Structural no-go.**  Existence of an Xi copy on which all current Gamma--theta creator
properties coexist with unit physical residue is equivalent to failure of RH.  Consequently those
creator properties alone cannot imply residue cancellation or critical-line placement. -/
theorem exists_jasGammaThetaClosedFlatUnitResidueCertificate_iff_not_riemannHypothesis :
    (∃ q : XiZeroCopy, JASGammaThetaClosedFlatUnitResidueCertificate q) ↔
      ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨q, hq⟩ hRH
    have hneutral := (thetaGreenBoundaryNeutral_iff_riemannHypothesis.mpr hRH) q
    exact (jasGammaThetaClosedFlatUnitResidueCertificate_iff_boundaryFlux_ne_zero q).1 hq
      hneutral
  · intro hnot
    by_contra hnone
    apply hnot
    apply thetaGreenBoundaryNeutral_iff_riemannHypothesis.mp
    intro q
    by_contra hflux
    apply hnone
    exact ⟨q,
      (jasGammaThetaClosedFlatUnitResidueCertificate_iff_boundaryFlux_ne_zero q).2 hflux⟩

end

end RHTower
