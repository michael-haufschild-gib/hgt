import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatHaarRadialPacket
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPureTensorPeriodicTrace
import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicWeightedStrongLogDecay

/-!
# Haar-radial trace of genuine rational adelic pure tensors

A uniform finite-place Haar packet lets the profinite integral be taken after
the integer lattice has been split into finitely many residue classes.  Thus
no exchange of Haar integration with an infinite sum is required.  The Haar
average of the genuine rational orbit trace is exactly one periodic weighted
log trace, and its weight is the unit-invariant residue function constructed
by profinite radialization.
-/

noncomputable section

open MeasureTheory
open scoped Classical RestrictedProduct algebraMap

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit

local instance ccmRationalHaarRadialPacketPeriodNeZero
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    NeZero P.period := P.period_neZero

namespace CCMRationalFiniteBruhatHaarRadialPacket

/-- Residue weight before Haar averaging at one profinite coordinate. -/
def sampleFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) (u : U) :
    Fin P.period → ℂ :=
  ccmRationalPeriodicResidueWeight P.period
    (fun n : ℤ => ccmRationalProfiniteHaarResidueSample
      P.period P.restricted (n : ZMod P.period) u)

/-- Residue weight after normalized profinite Haar averaging. -/
def averageFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    Fin P.period → ℂ :=
  ccmRationalPeriodicResidueWeight P.period
    (fun n : ℤ => P.averageWeight (n : ZMod P.period))

theorem residueSample_int_periodic
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) (u : U) :
    Function.Periodic
      (fun n : ℤ => ccmRationalProfiniteHaarResidueSample
        P.period P.restricted (n : ZMod P.period) u)
      (P.period : ℤ) := by
  intro n
  have hcast :
      ((n + (P.period : ℤ) : ℤ) : ZMod P.period) =
        (n : ZMod P.period) := by
    rw [Int.cast_add, Int.cast_natCast]
    simp
  change ccmRationalProfiniteHaarResidueSample
      P.period P.restricted
        ((n + (P.period : ℤ) : ℤ) : ZMod P.period) u = _
  rw [hcast]

theorem averageWeight_int_periodic
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    Function.Periodic
      (fun n : ℤ => P.averageWeight (n : ZMod P.period))
      (P.period : ℤ) := by
  intro n
  have hcast :
      ((n + (P.period : ℤ) : ℤ) : ZMod P.period) =
        (n : ZMod P.period) := by
    rw [Int.cast_add, Int.cast_natCast]
    simp
  change P.averageWeight
      ((n + (P.period : ℤ) : ℤ) : ZMod P.period) = _
  rw [hcast]

theorem residueSample_eq_sampleFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi)
    (u : U) (n : ℤ) :
    ccmRationalProfiniteHaarResidueSample
        P.period P.restricted (n : ZMod P.period) u =
      P.sampleFinWeight u
        (ccmRationalPeriodicResidue P.period n) := by
  exact ccmRationalPeriodic_eq_residueWeight P.period _
    (P.residueSample_int_periodic u) n

theorem averageWeight_eq_averageFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) (n : ℤ) :
    P.averageWeight (n : ZMod P.period) =
      P.averageFinWeight
        (ccmRationalPeriodicResidue P.period n) := by
  exact ccmRationalPeriodic_eq_residueWeight P.period _
    P.averageWeight_int_periodic n

theorem integral_sampleFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi)
    (r : Fin P.period) :
    (∫ u : U, P.sampleFinWeight u r
      ∂ccmRationalProfiniteUnitHaar) = P.averageFinWeight r := by
  simp [sampleFinWeight, averageFinWeight,
    ccmRationalPeriodicResidueWeight,
    averageWeight, ccmRationalProfiniteHaarResidueAverage]

theorem integrable_sampleFinWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi)
    (r : Fin P.period) :
    Integrable (fun u : U => P.sampleFinWeight u r)
      ccmRationalProfiniteUnitHaar := by
  simpa [sampleFinWeight, ccmRationalPeriodicResidueWeight] using
    integrable_ccmRationalProfiniteHaarResidueSample
      P.period P.restricted P.restricted_continuous
        (r.val : ZMod P.period)

end CCMRationalFiniteBruhatHaarRadialPacket

/-- Exact periodic expression for one genuine pure-tensor trace at one
profinite coordinate, using the uniform Haar packet. -/
theorem ccmRationalAdelicBruhatPureTensorOrbitSum_eq_haarPacketTrace
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi)
    (u : U) (bInf : ℝ) :
    (∑' q : ℚ,
      ccmRationalAdelicBruhatPureTensorOrbit f phi bInf u.1 q) =
      ccmRationalPeriodicWeightedTrace P.period (P.sampleFinWeight u)
        (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos) bInf := by
  rw [ccmRationalAdelicBruhatPureTensorOrbitSum_eq_integerSum
    f phi bInf u.1 P.denominator P.denominator_pos
    (fun q hq => P.rationalDenominator q u hq)]
  rw [ccmRationalPeriodicWeightedTrace]
  apply tsum_congr
  intro n
  rw [P.finiteCoefficient n u,
    P.residueSample_eq_sampleFinWeight u n,
    ccmRationalPositiveDenominatorDilation_apply]
  rw [mul_comm]
  congr 1
  ring

/-- Profinite Haar average of the genuine pure-tensor rational orbit trace. -/
def ccmRationalAdelicPureTensorProfiniteHaarLogTrace
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz) (t : ℝ) : ℂ :=
  ∫ u : U, (∑' q : ℚ,
    ccmRationalAdelicBruhatPureTensorOrbit
      f phi (Real.exp t) u.1 q) ∂ccmRationalProfiniteUnitHaar

/-- **Exact pure-tensor Haar radial trace law.** The profinite Haar average
of the actual rational orbit trace is the periodic trace with the averaged,
unit-invariant finite weight. -/
theorem ccmRationalAdelicPureTensorProfiniteHaarLogTrace_eq
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    ccmRationalAdelicPureTensorProfiniteHaarLogTrace f phi =
      ccmRationalPeriodicWeightedLogTrace P.period P.averageFinWeight
        (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos) := by
  funext t
  let fD := ccmRationalPositiveDenominatorDilation
    f P.denominator P.denominator_pos
  let L : Fin P.period → ℂ := fun r => ∑' k : ℤ,
    fD (Real.exp t * ((k : ℝ) * (P.period : ℝ) + (r : ℝ)))
  have horbit (u : U) :
      (∑' q : ℚ, ccmRationalAdelicBruhatPureTensorOrbit
        f phi (Real.exp t) u.1 q) =
        ccmRationalPeriodicWeightedTrace P.period
          (P.sampleFinWeight u) fD (Real.exp t) := by
    exact ccmRationalAdelicBruhatPureTensorOrbitSum_eq_haarPacketTrace
      f phi P u (Real.exp t)
  have hresidue (u : U) :
      ccmRationalPeriodicWeightedTrace P.period
          (P.sampleFinWeight u) fD (Real.exp t) =
        ∑ r : Fin P.period, P.sampleFinWeight u r * L r := by
    rw [ccmRationalPeriodicWeightedTrace_eq_sum_residues
      P.period (P.sampleFinWeight u) fD (Real.exp_ne_zero t)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← tsum_mul_left]
  rw [ccmRationalAdelicPureTensorProfiniteHaarLogTrace]
  calc
    (∫ u : U, (∑' q : ℚ,
        ccmRationalAdelicBruhatPureTensorOrbit
          f phi (Real.exp t) u.1 q) ∂ccmRationalProfiniteUnitHaar) =
        ∫ u : U, ccmRationalPeriodicWeightedTrace P.period
          (P.sampleFinWeight u) fD (Real.exp t)
            ∂ccmRationalProfiniteUnitHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall horbit
    _ = ∫ u : U, ∑ r : Fin P.period,
          P.sampleFinWeight u r * L r
            ∂ccmRationalProfiniteUnitHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hresidue
    _ = ∑ r : Fin P.period, ∫ u : U,
          P.sampleFinWeight u r * L r
            ∂ccmRationalProfiniteUnitHaar := by
      apply integral_finsetSum
      intro r hr
      exact (P.integrable_sampleFinWeight r).mul_const _
    _ = ∑ r : Fin P.period, P.averageFinWeight r * L r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [integral_mul_const, P.integral_sampleFinWeight]
    _ = ccmRationalPeriodicWeightedTrace P.period
        P.averageFinWeight fD (Real.exp t) := by
      rw [ccmRationalPeriodicWeightedTrace_eq_sum_residues
        P.period P.averageFinWeight fD (Real.exp_ne_zero t)]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← tsum_mul_left]
    _ = ccmRationalPeriodicWeightedLogTrace P.period
        P.averageFinWeight fD t := rfl

end GaloisForLFunctions.RHTower
