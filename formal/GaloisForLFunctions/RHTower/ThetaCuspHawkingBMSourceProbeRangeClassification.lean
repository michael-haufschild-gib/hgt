import GaloisForLFunctions.RHTower.ThetaCuspHawkingDiagonalPeierlsSourceIncidenceRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility
import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusPoissonReserve

/-!
# Exact range of the Birmingham--Mokhtari source probe

The unit complementary BM source is zero at every critical Xi copy. Pairing any returned
vector with this source therefore gives zero there, irrespective of how that vector was
constructed. Conversely every scalar profile vanishing on critical copies is realized by a
single weighted complex-linear skew Peierls propagator. Arbitrary nonlinear response and
copy-dependent vector selection do not enlarge this range.

The canonical realizing weight is the target divided by the squared source amplitude. It is
unique off the critical line and unrestricted on it. This is a range classification, not a
source-derived response law: the canonical realization uses the target profile.

The full nonzero-seed AIME incidence requires a nonzero remainder on critical copies, and the
first-live completed spin-two angular jet is also nonzero there. Neither can factor through
this source probe. A response outside the linear, reciprocal, or Schwarz-exchanged classes
still cannot recover a coefficient erased by the testing leg. Pairings on a different source
or on retained derivative data are outside this theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Scalar profile measured with the literal complementary unit BM source. The returned
vector may depend arbitrarily on the Xi copy. -/
def hbXiPeierlsSourceProbeProfile
    (returned : XiZeroCopy → HBXiPeierlsCarrier) (q : XiZeroCopy) : ℂ :=
  hbXiPeierlsPairing (returned q) (hbXiPeierlsMinusSource 1 q)

/-- The complementary testing leg erases every returned vector on a critical copy. -/
theorem hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine
    (returned : XiZeroCopy → HBXiPeierlsCarrier) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    hbXiPeierlsSourceProbeProfile returned q = 0 := by
  unfold hbXiPeierlsSourceProbeProfile
  rw [(hbXiPeierlsMinusSource_eq_zero_iff one_ne_zero q).2 hline]
  exact map_zero _

/-- The weight reconstructing the visible part of an arbitrary target profile. -/
def hbXiPeierlsSourceProbeRealizingWeight (target : XiZeroCopy → ℂ)
    (q : XiZeroCopy) : ℂ :=
  target q / (Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) : ℂ)

/-- The actual source norm is nonzero exactly away from the critical line. -/
theorem hbXiPeierlsUnitSourceNorm_ne_zero_iff (q : XiZeroCopy) :
    (Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) : ℂ) ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [Complex.ofReal_ne_zero, Ne, Complex.normSq_eq_zero,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q]

/-- Weighted skew propagation has the exact source-norm multiplier. -/
theorem hbXiPeierlsSourceProbeProfile_weighted
    (w : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    hbXiPeierlsSourceProbeProfile
        (fun r => hbXiPeierlsWeightedPropagator w (hbXiPeierlsPlusSource 1 r)) q =
      w q * Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) := by
  exact hbXiPeierlsWeighted_sourcePairing_eq w 1 q

/-- The canonical weight recovers every target away from the zero probe and erases exactly
its critical-copy values. This formula has no target-compatibility hypothesis. -/
theorem hbXiPeierlsSourceProbeRealizingWeight_profile
    (target : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    hbXiPeierlsSourceProbeProfile
        (fun r => hbXiPeierlsWeightedPropagator
          (hbXiPeierlsSourceProbeRealizingWeight target) (hbXiPeierlsPlusSource 1 r)) q =
      if (q.1 : ℂ).re = 1 / 2 then 0 else target q := by
  classical
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · rw [if_pos hline]
    exact hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine _ q hline
  · rw [if_neg hline, hbXiPeierlsSourceProbeProfile_weighted]
    exact div_mul_cancel₀ (target q) ((hbXiPeierlsUnitSourceNorm_ne_zero_iff q).2 hline)

/-- Exact image classification, including arbitrary nonlinear, discontinuous, and copy-dependent
returned vectors. -/
theorem exists_hbXiPeierlsSourceProbeProfile_iff
    (target : XiZeroCopy → ℂ) :
    (∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q, hbXiPeierlsSourceProbeProfile returned q = target q) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → target q = 0 := by
  constructor
  · rintro ⟨returned, hreturned⟩ q hline
    rw [← hreturned q]
    exact hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline
  · intro htarget
    refine ⟨fun q => hbXiPeierlsWeightedPropagator
      (hbXiPeierlsSourceProbeRealizingWeight target) (hbXiPeierlsPlusSource 1 q), ?_⟩
    intro q
    rw [hbXiPeierlsSourceProbeRealizingWeight_profile]
    split_ifs with hline
    · exact (htarget q hline).symm
    · rfl

/-- A single arbitrary map of the complete carrier realizes exactly the same profiles as
copy-dependent returned vectors. -/
theorem exists_hbXiPeierlsArbitraryResponseProfile_iff
    (target : XiZeroCopy → ℂ) :
    (∃ response : HBXiPeierlsCarrier → HBXiPeierlsCarrier,
      ∀ q, hbXiPeierlsSourceProbeProfile
        (fun r => response (hbXiPeierlsPlusSource 1 r)) q = target q) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → target q = 0 := by
  constructor
  · rintro ⟨response, hresponse⟩
    exact (exists_hbXiPeierlsSourceProbeProfile_iff target).1
      ⟨fun q => response (hbXiPeierlsPlusSource 1 q), hresponse⟩
  · intro htarget
    refine ⟨hbXiPeierlsWeightedPropagator (hbXiPeierlsSourceProbeRealizingWeight target), ?_⟩
    intro q
    rw [hbXiPeierlsSourceProbeRealizingWeight_profile]
    split_ifs with hline
    · exact (htarget q hline).symm
    · rfl

/-- Nonlinear response supplies no new scalar profile: one weighted complex-linear skew
propagator reproduces every one of its source-probe measurements simultaneously. -/
theorem hbXiPeierlsArbitraryResponseProfile_has_weightedSkewRealization
    (response : HBXiPeierlsCarrier → HBXiPeierlsCarrier) :
    ∃ w : XiZeroCopy → ℂ,
      (∀ f g : HBXiPeierlsCarrier,
        hbXiPeierlsPairing (hbXiPeierlsWeightedPropagator w f) g =
          -hbXiPeierlsPairing (hbXiPeierlsWeightedPropagator w g) f) ∧
      ∀ q, hbXiPeierlsSourceProbeProfile
          (fun r => hbXiPeierlsWeightedPropagator w (hbXiPeierlsPlusSource 1 r)) q =
        hbXiPeierlsSourceProbeProfile
          (fun r => response (hbXiPeierlsPlusSource 1 r)) q := by
  let target := hbXiPeierlsSourceProbeProfile
    (fun r => response (hbXiPeierlsPlusSource 1 r))
  refine ⟨hbXiPeierlsSourceProbeRealizingWeight target, ?_, ?_⟩
  · exact hbXiPeierlsWeightedSourcePairing_skew _
  · intro q
    rw [hbXiPeierlsSourceProbeRealizingWeight_profile]
    split_ifs with hline
    · exact (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine _ q hline).symm
    · rfl

/-- Two weighted propagators are indistinguishable by every unit source probe exactly when
their weights agree off the critical line. All critical-copy weights remain free. -/
theorem hbXiPeierlsSourceProbeProfile_weighted_eq_iff
    (w v : XiZeroCopy → ℂ) :
    (∀ q, hbXiPeierlsSourceProbeProfile
        (fun r => hbXiPeierlsWeightedPropagator w (hbXiPeierlsPlusSource 1 r)) q =
      hbXiPeierlsSourceProbeProfile
        (fun r => hbXiPeierlsWeightedPropagator v (hbXiPeierlsPlusSource 1 r)) q) ↔
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → w q = v q := by
  simp only [hbXiPeierlsSourceProbeProfile_weighted]
  constructor
  · intro h q hline
    exact mul_right_cancel₀ ((hbXiPeierlsUnitSourceNorm_ne_zero_iff q).2 hline) (h q)
  · intro h q
    by_cases hline : (q.1 : ℂ).re = 1 / 2
    · have ha := (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff
        one_ne_zero q).2 hline
      rw [ha]
      simp
    · rw [h q hline]

/-- Full AIME incidence fails at each critical copy for every returned vector family and
nonzero seed. No symmetry, linearity, regularity, or vacuum condition is used. -/
theorem d4FullCrossBranchProjectedResidue_sourceProbe_ne_unitBMTarget
    (n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0)
    (returned : XiZeroCopy → HBXiPeierlsCarrier) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    d4FullCrossBranchProjectedResidue amplitude
        (fun _ => hbXiPeierlsSourceProbeProfile returned q) (xiSpectralPoint q) ≠
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro hmatch
  have hnonzero := d4FullCrossBranch_samePoleSourceRemainder_ne_zero_of_unitBMTarget_of_criticalLine
    n hamplitude (fun _ => hbXiPeierlsSourceProbeProfile returned q) q hline hmatch
  exact hnonzero (hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q hline)

/-- Unconditional exclusion of universal full AIME incidence through the extinct source probe.
The returned vectors may be chosen independently at every copy. -/
theorem not_exists_hbXiPeierlsSourceProbe_fullAIMEIncidence :
    ∀ n : ℕ, ¬ ∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy,
        d4FullCrossBranchProjectedResidue 1
            (fun _ => hbXiPeierlsSourceProbeProfile returned q) (xiSpectralPoint q) =
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  intro n
  rintro ⟨returned, hmatch⟩
  let q : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  exact d4FullCrossBranchProjectedResidue_sourceProbe_ne_unitBMTarget
    n one_ne_zero returned q.1 q.2 (hmatch q.1)

/-- The nonzero first-live angular jet cannot be reconstructed through the old source probe,
even by an arbitrary copy-dependent response. It must be retained before this pairing. -/
theorem not_exists_hbXiPeierlsSourceProbe_firstLiveAngularJet :
    ¬ ∃ returned : XiZeroCopy → HBXiPeierlsCarrier,
      ∀ q : XiZeroCopy, hbXiPeierlsSourceProbeProfile returned q =
        d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q := by
  rintro ⟨returned, hmatch⟩
  let q : XiCriticalLineResolventCopy :=
    Classical.choice nonempty_xiCriticalLineResolventCopy_of_hardy
  apply d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet_ne_zero q.1
  rw [← hmatch q.1]
  exact hbXiPeierlsSourceProbeProfile_eq_zero_of_criticalLine returned q.1 q.2

end

end RHTower
