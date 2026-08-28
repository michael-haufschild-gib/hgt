import GaloisForLFunctions.RHTower.PrimeDepthBVWoldBarrelledSourceSelector

/-!
# Terminal classification of the barrelled Wold source certificate

The barrelled certificate interface has no independent arithmetic existence content. Banach--
Steinhaus already forces its centered coefficient to vanish, while on the zero fibre the zero
Banach-space orbit and zero readout satisfy every certificate field. Thus pointwise certificate
existence is exactly centered neutrality, and global Xi-labelled existence is exactly RH.
-/

namespace RHTower

noncomputable section

/-- Canonical zero-fibre certificate. It exposes that the certificate fields impose no further
source condition once the centered coefficient vanishes. -/
def primeDepthBVWoldZeroBarrelledSourceCertificate (sourceDepth : ℕ) :
    PrimeDepthBVWoldBarrelledSourceCertificate sourceDepth 0 where
  E := ℝ
  readout := fun _ => 0
  orbit := fun _ => 0
  orbit_tendsto_zero := tendsto_const_nhds
  readout_pointwise_bounded := by
    intro y
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp
  physical_matrix_coefficient := by
    intro n
    simp [primeDepthBVWoldSourceNormalCofinalCenteredTransport]

/-- **Pointwise terminal classification.** A barrelled source certificate exists exactly when its
centered Wold rate is already zero. -/
theorem nonempty_primeDepthBVWoldBarrelledSourceCertificate_iff
    (sourceDepth : ℕ) (a : ℝ) :
    Nonempty (PrimeDepthBVWoldBarrelledSourceCertificate sourceDepth a) ↔ a = 0 := by
  constructor
  · rintro ⟨cert⟩
    exact cert.centeredRate_eq_zero
  · rintro rfl
    exact ⟨primeDepthBVWoldZeroBarrelledSourceCertificate sourceDepth⟩

/-- The Xi-labelled certificate exists exactly on the critical line. -/
theorem nonempty_primeDepthBVWoldXiBarrelledSourceCertificate_iff
    (sourceDepth : ℕ) (rho : XiDivisorSupport) :
    Nonempty (PrimeDepthBVWoldXiBarrelledSourceCertificate sourceDepth rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [PrimeDepthBVWoldXiBarrelledSourceCertificate,
    nonempty_primeDepthBVWoldBarrelledSourceCertificate_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- **BW terminal no-go.** The proposed global barrelled-source producer is equivalent to RH, so
constructing an inhabitant cannot be an independent pre-divisor proof step. -/
theorem primeDepthBVWoldXiGlobalBarrelledSourceProducer_iff_riemannHypothesis
    (sourceDepth : ℕ) :
    PrimeDepthBVWoldXiGlobalBarrelledSourceProducer sourceDepth ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_globalBarrelledSourceProducer sourceDepth
  · intro hRH rho
    exact (nonempty_primeDepthBVWoldXiBarrelledSourceCertificate_iff
      sourceDepth rho).2 (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
