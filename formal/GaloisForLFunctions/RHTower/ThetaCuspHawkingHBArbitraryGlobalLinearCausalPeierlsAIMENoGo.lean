import GaloisForLFunctions.RHTower.ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedEisensteinContinuumPhaseNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility
import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusPoissonReserve

/-!
# Arbitrary-global linear causal Peierls–AIME no-go

Reciprocity and retarded/advanced Schwarz exchange force the canonical same-fibre source response
of every arbitrary global complex-linear causal Peierls jump to be Schwarz-real. At a critical Xi
copy, exact unit BM incidence inside the full third-order AIME residue instead forces that response
to be the nonreal negative unit AIME numerator. Hardy's theorem supplies an unconditional critical
copy, killing universal incidence for this entire response class.

No diagonal, local, finite-range, bounded, support, or fibre-preservation condition is used.
Consequently arbitrary cross-fibre or cross-channel mixing cannot rescue a canonical linear causal
Peierls realization of the HB AIME cancellation arrow.

`[NEW] [HB ROUTE KILL] [ARBITRARY GLOBAL] [CAUSAL PEIERLS] [AIME PHASE] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Canonical same-fibre source response of a retarded-minus-advanced Peierls jump. -/
def d4HBGlobalCausalPeierlsSamePoleResponse
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (q : XiZeroCopy) : ℂ :=
  d4GaugeFixedTeukolskyPeierlsSourcePairing hbXiPeierlsPairing
    (hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv)
    (hbXiPeierlsPlusSource 1 q) (hbXiPeierlsMinusSource 1 q)

/-- Constant spectral remainder supplied by the canonical causal Peierls response at one fibre. -/
def d4HBGlobalCausalPeierlsSamePoleRemainder
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (q : XiZeroCopy) : ℂ → ℂ :=
  fun _ => d4HBGlobalCausalPeierlsSamePoleResponse Gret Gadv q

/-- Reciprocity and retarded/advanced Schwarz exchange make every canonical same-fibre causal
Peierls source response Schwarz-real, even for arbitrary global cross-fibre mixing. -/
theorem d4HBGlobalCausalPeierlsSamePoleResponse_schwarzReal
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hreciprocal : HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv)
    (hexchange : HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv)
    (q : XiZeroCopy) :
    (starRingEnd ℂ) (d4HBGlobalCausalPeierlsSamePoleResponse Gret Gadv q) =
      d4HBGlobalCausalPeierlsSamePoleResponse Gret Gadv q := by
  exact hbXiPeierlsGlobalPropagator_sourceResponse_schwarzReal
    (hbXiPeierlsRetardedAdvancedCausalJump Gret Gadv)
    (hbXiPeierlsRetardedAdvancedCausalJump_skew Gret Gadv hreciprocal)
    (hbXiPeierlsRetardedAdvancedCausalJump_channelSchwarzOdd Gret Gadv hexchange)
    1 q

/-- The canonical arbitrary-global causal Peierls same-pole response has zero imaginary part. -/
theorem d4HBGlobalCausalPeierlsSamePoleResponse_im_eq_zero
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hreciprocal : HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv)
    (hexchange : HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv)
    (q : XiZeroCopy) :
    (d4HBGlobalCausalPeierlsSamePoleResponse Gret Gadv q).im = 0 := by
  have hstar := d4HBGlobalCausalPeierlsSamePoleResponse_schwarzReal
    Gret Gadv hreciprocal hexchange q
  have him := congrArg Complex.im hstar
  rw [Complex.conj_im] at him
  linarith

/-- At any critical Xi fibre, arbitrary-global reciprocal and Schwarz-exchanged retarded/advanced
linear response cannot provide the nonreal same-pole counterterm required to cancel unit AIME. -/
theorem d4HBGlobalCausalPeierlsFullResidue_ne_unitBMTarget_of_criticalLine
    (n : ℕ)
    (Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier)
    (hreciprocal : HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv)
    (hexchange : HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv)
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4FullCrossBranchProjectedResidue 1
        (d4HBGlobalCausalPeierlsSamePoleRemainder Gret Gadv q)
        (xiSpectralPoint q) ≠
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro hincidence
  have hforced :=
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n 1 (d4HBGlobalCausalPeierlsSamePoleRemainder Gret Gadv q) q hline).1
      hincidence
  change d4HBGlobalCausalPeierlsSamePoleResponse Gret Gadv q =
    -d4FundamentalQNMCrossBranchAIMENumerator 1 (xiSpectralPoint q) at hforced
  have hresponseIm := d4HBGlobalCausalPeierlsSamePoleResponse_im_eq_zero
    Gret Gadv hreciprocal hexchange q
  have him := congrArg Complex.im hforced
  rw [hresponseIm, Complex.neg_im] at him
  exact d4FundamentalQNMCrossBranchAIMENumerator_one_im_ne_zero_of_re_eq_half q hline
    (by linarith)

/-- Closed route class: no arbitrary-global complex-linear reciprocal, Schwarz-exchanged
retarded/advanced Peierls pair can supply exact unit AIME cancellation on every Xi copy. -/
def D4HBArbitraryGlobalLinearCausalPeierlsAIMERouteKilled : Prop :=
  ∀ n : ℕ,
    ¬ ∃ Gret Gadv : HBXiPeierlsCarrier →ₗ[ℂ] HBXiPeierlsCarrier,
      HBXiPeierlsRetardedAdvancedReciprocal Gret Gadv ∧
        HBXiPeierlsRetardedToAdvancedSchwarzExchange Gret Gadv ∧
          ∀ q : XiZeroCopy,
            d4FullCrossBranchProjectedResidue 1
                (d4HBGlobalCausalPeierlsSamePoleRemainder Gret Gadv q)
                (xiSpectralPoint q) =
              d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q

/-- Premise-free certificate killing the arbitrary-global linear causal Peierls realization of the
HB AIME cancellation arrow. Cross-fibre and cross-channel mixing do not evade the obstruction. -/
theorem d4HBArbitraryGlobalLinearCausalPeierlsAIMERouteKilled :
    D4HBArbitraryGlobalLinearCausalPeierlsAIMERouteKilled := by
  intro n
  rintro ⟨Gret, Gadv, hreciprocal, hexchange, hincidence⟩
  let qCritical : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  let q : XiZeroCopy := qCritical.1
  have hline : (q.1 : ℂ).re = 1 / 2 := qCritical.2
  exact d4HBGlobalCausalPeierlsFullResidue_ne_unitBMTarget_of_criticalLine
    n Gret Gadv hreciprocal hexchange q hline (hincidence q)

end

end RHTower
