import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCanonicalMatchingNoGo

/-! Exact source-encoding boundary for the complete original QNM action. -/
open Complex
namespace RHTower
open D4BMJointSource D4BMOriginalCanonicalAction D4BMOriginalSourceResolvent
noncomputable section
set_option autoImplicit false

/-- The complete action retains the original quadratic source amplitude,
including every temporal, metric and forcing term. -/
theorem canonicalQNMValue_quadratic_amplitude (q : XiZeroCopy) (br side : Bool) (a : ℂ) :
    canonicalQNMValue q br side a = a^2*canonicalQNMValue q br side 1 := by
  rw [canonicalQNMValue_eq_source_periods,canonicalQNMValue_eq_source_periods]
  rw [physicalFundamentalSourceMoment_polynomial q br side a,
    physicalFundamentalSourceMoment_polynomial q br side 1]
  simp only [fundamentalSourceTortoiseMoment,fundamentalSourceForcingMoment,one_pow,mul_one]
  ring

/-- Exact fibres of the original complete action at fixed physical source data. -/
theorem canonicalQNMValue_amplitude_fibres (q : XiZeroCopy) (br side : Bool) (a b : ℂ) :
    canonicalQNMValue q br side a=canonicalQNMValue q br side b ↔
      canonicalQNMValue q br side 1=0 ∨ a^2=b^2 := by
  rw [canonicalQNMValue_quadratic_amplitude q br side a,
    canonicalQNMValue_quadratic_amplitude q br side b]
  by_cases h : canonicalQNMValue q br side 1=0
  · simp [h]
  · simp only [h,false_or]
    exact ⟨mul_right_cancel₀ h,fun he=>congrArg (fun z=>z*canonicalQNMValue q br side 1) he⟩

private theorem polarizedAmplitude_quadratic (q : XiZeroCopy) (a : ℂ) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude a q =
      a^2*d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q := by
  unfold d4BMXiSecondHarmonicPolarizedSourceAmplitude d4ThetaHawkingSelfDualQuadraticCarrierCoefficient
  ring

private theorem plusSource_coordinate (q : XiZeroCopy) (a : ℂ) :
    (hbXiPeierlsPlusSource a q).1 q=a^2*d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q := by
  simp only [hbXiPeierlsPlusSource,Finsupp.single_eq_same]
  exact polarizedAmplitude_quadratic q a

/-- At a critical copy, the literal carrier loses every source amplitude. -/
theorem hbXiPeierlsPlusSource_critical_amplitudes (q : XiZeroCopy)
    (hq : (q.1:ℂ).re=1/2) (a : ℂ) : hbXiPeierlsPlusSource a q=0 := by
  have h := (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).2 hq
  rw [hbXiPeierlsPlusSource,polarizedAmplitude_quadratic q a,h,mul_zero]
  simp only [Finsupp.single_zero,Prod.zero_eq_mk]

/-- Exact existence boundary for arbitrary nonlinear, discontinuous decoders
of the original source carrier. The decoder need not use a Peierls probe. -/
theorem exists_fullCanonical_source_decoder_iff (q : XiZeroCopy) (br side : Bool) :
    (∃ decode : HBXiPeierlsCarrier → ℂ,
      ∀ a : ℂ, decode (hbXiPeierlsPlusSource a q)=canonicalQNMValue q br side a) ↔
      ((q.1:ℂ).re=1/2 → canonicalQNMValue q br side 1=0) := by
  constructor
  · rintro ⟨decode,hd⟩ hq
    have h0 := hd 0
    have h1 := hd 1
    rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 0,
      canonicalQNMValue_quadratic_amplitude q br side 0] at h0
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_mul] at h0
    rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 1] at h1
    exact h1.symm.trans h0
  · intro h
    by_cases hq : (q.1:ℂ).re=1/2
    · refine ⟨fun _=>0,fun a=>?_⟩
      rw [canonicalQNMValue_quadratic_amplitude q br side a,h hq,mul_zero]
    · have hS : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q≠0 := by
        intro hz
        exact hq ((d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).1 hz)
      refine ⟨fun x=>x.1 q/d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q*
        canonicalQNMValue q br side 1,fun a=>?_⟩
      change (hbXiPeierlsPlusSource a q).1 q/d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q*
        canonicalQNMValue q br side 1=canonicalQNMValue q br side a
      rw [plusSource_coordinate,canonicalQNMValue_quadratic_amplitude q br side a]
      rw [mul_div_cancel_right₀ _ hS]

/-- Changing the output rule cannot reconstruct the full canonical action
from this encoding, even with a different arbitrary decoder for each copy. -/
theorem not_exists_fullCanonical_source_decoder :
    ¬∃ decode : XiZeroCopy → HBXiPeierlsCarrier → ℂ,
      ∀ (q : XiZeroCopy) (a : ℂ),
        decode q (hbXiPeierlsPlusSource a q)=canonicalQNMValue q true true a := by
  rintro ⟨decode,hd⟩
  obtain ⟨q,hq,hne⟩ := exists_critical_canonicalQNMValue_ne_zero
  exact hne ((exists_fullCanonical_source_decoder_iff q true true).1 ⟨decode q,hd q⟩ hq)

/-- The obstruction uses two nonzero physical amplitudes. Excluding the
vacuum or allowing singular behaviour there does not repair the matching. -/
theorem not_exists_fullCanonical_nonzero_source_decoder :
    ¬∃ decode : XiZeroCopy → HBXiPeierlsCarrier → ℂ,
      ∀ (q : XiZeroCopy) (a : ℂ), a≠0 →
        decode q (hbXiPeierlsPlusSource a q)=canonicalQNMValue q true true a := by
  rintro ⟨decode,hd⟩
  obtain ⟨q,hq,hne⟩ := exists_critical_canonicalQNMValue_ne_zero
  have h1 := hd q 1 one_ne_zero
  have h2 := hd q 2 (by norm_num)
  rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 1] at h1
  rw [hbXiPeierlsPlusSource_critical_amplitudes q hq 2,
    canonicalQNMValue_quadratic_amplitude q true true 2] at h2
  have he : canonicalQNMValue q true true 1=0 := by
    linear_combination (h1-h2)/3
  exact hne he

/-- Positive survivor: an actual erased critical fibre retains precisely the
squared amplitude in the complete physical action. -/
theorem exists_critical_fullCanonical_amplitude_fibre :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧ canonicalQNMValue q true true 1≠0 ∧
      (∀ a : ℂ, hbXiPeierlsPlusSource a q=0) ∧
      ∀ a b : ℂ, canonicalQNMValue q true true a=canonicalQNMValue q true true b ↔ a^2=b^2 := by
  obtain ⟨q,hq,hne⟩ := exists_critical_canonicalQNMValue_ne_zero
  refine ⟨q,hq,hne,hbXiPeierlsPlusSource_critical_amplitudes q hq,?_⟩
  intro a b
  rw [canonicalQNMValue_amplitude_fibres]
  simp only [hne,false_or]

end
end RHTower
