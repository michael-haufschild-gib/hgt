import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPureTensorPeriodicTrace
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.CCM.CCMRationalPeriodicWeightedStrongLogDecay

/-!
# Physical endpoint and genuine-unit trace for periodic adelic packets

The periodic packet initially reindexes the full rational diagonal, including
zero.  The first CCM endpoint is exactly the missing condition that kills this
zero summand.  Under that unconditional equality, the packet trace is the
actual `ℚˣ` Morita trace and its physical weighted Poisson mode vanishes.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct algebraMap FourierTransform

namespace GaloisForLFunctions
namespace RHTower

/-- If the zero-adele value vanishes, the full rational orbit sum is exactly
the genuine `ℚˣ` orbit sum. -/
theorem ccmRationalAdelicBruhatPureTensorOrbitSum_eq_unitOrbitSum
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (hzero : f 0 * phi.1 0 = 0) :
    (∑' q : ℚ,
      ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b q) =
      ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b (q : ℚ) := by
  let g : CCMRationalUnit → ℚ := fun q => q
  let F : ℚ → ℂ := fun q =>
    ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b q
  have hg : Function.Injective g := Units.val_injective
  have hs : Function.support F ⊆ Set.range g := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h
      subst q
      apply hq
      simpa [F, ccmRationalAdelicBruhatPureTensorOrbit] using hzero
    exact ⟨Units.mk0 q hq0, rfl⟩
  exact ccmRational_tsum_reindex_of_support_subset_range g hg F hs

/-- The first CCM endpoint is exactly the physical weighted zero-mode
cancellation of every periodic trace packet. -/
theorem CCMRationalAdelicPureTensorPeriodicTracePacket.physicalZero
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b)
    (hzero : f 0 * phi.1 0 = 0) :
    P.weight (@ccmRationalPeriodicResidue
        P.period P.period_neZero 0) *
      ccmRationalPositiveDenominatorDilation
        f P.denominator P.denominator_pos 0 = 0 := by
  have hw0 := P.finiteCoefficient 0
  have hw0' : phi.1 0 = P.weight (@ccmRationalPeriodicResidue
      P.period P.period_neZero 0) := by
    simpa using hw0
  rw [ccmRationalPositiveDenominatorDilation_apply, mul_zero, hw0'.symm]
  simpa [mul_comm] using hzero

/-- Raw zero-evaluation of the adelic tensor is equivalent to the physical
packet cancellation. -/
theorem CCMRationalAdelicPureTensorPeriodicTracePacket.physicalZero_of_zeroEval
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b)
    (hzero : ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] phi) = 0) :
    P.weight (@ccmRationalPeriodicResidue
        P.period P.period_neZero 0) *
      ccmRationalPositiveDenominatorDilation
        f P.denominator P.denominator_pos 0 = 0 := by
  apply P.physicalZero
  simpa using hzero

/-- Under the first endpoint cancellation, the logarithmic genuine-unit orbit
trace is exactly the periodic weighted logarithmic trace of the packet. -/
theorem CCMRationalAdelicPureTensorPeriodicTracePacket.unitLogTrace_eq
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b)
    (hzero : f 0 * phi.1 0 = 0) :
    (fun t : ℝ => ∑' q : CCMRationalUnit,
      ccmRationalAdelicBruhatPureTensorOrbit
        f phi (Real.exp t) b (q : ℚ)) =
      @ccmRationalPeriodicWeightedLogTrace
        P.period P.period_neZero P.weight
        (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos) := by
  funext t
  calc
    (∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatPureTensorOrbit
          f phi (Real.exp t) b (q : ℚ)) =
        ∑' q : ℚ,
          ccmRationalAdelicBruhatPureTensorOrbit
            f phi (Real.exp t) b q :=
      (ccmRationalAdelicBruhatPureTensorOrbitSum_eq_unitOrbitSum
        f phi (Real.exp t) b hzero).symm
    _ = @ccmRationalPeriodicWeightedTrace
          P.period P.period_neZero P.weight
          (ccmRationalPositiveDenominatorDilation
            f P.denominator P.denominator_pos) (Real.exp t) :=
      P.trace_eq (Real.exp t)
    _ = @ccmRationalPeriodicWeightedLogTrace
          P.period P.period_neZero P.weight
          (ccmRationalPositiveDenominatorDilation
            f P.denominator P.denominator_pos) t := rfl

/-- With the two exact endpoint cancellations, the genuine `ℚˣ` pure
tensor trace has all-derivative, all-exponential-weight Meyer decay. -/
theorem CCMRationalAdelicPureTensorPeriodicTracePacket.unitLogTrace_strongLogDecay
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b)
    (hzero : f 0 * phi.1 0 = 0)
    (hdual :
      (∑ r : Fin P.period, P.weight r) *
        (𝓕 (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos)) 0 = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (fun t : ℝ => ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatPureTensorOrbit
          f phi (Real.exp t) b (q : ℚ)) := by
  letI : NeZero P.period := P.period_neZero
  rw [CCMRationalAdelicPureTensorPeriodicTracePacket.unitLogTrace_eq
    f phi b P hzero]
  apply ccmRationalPeriodicWeightedLogTrace_strongLogDecay
  · simpa only [ccmRationalPeriodicResidue_zero] using
      CCMRationalAdelicPureTensorPeriodicTracePacket.physicalZero
        f phi b P hzero
  · exact hdual

end RHTower
end GaloisForLFunctions
