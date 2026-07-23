import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
import GaloisForLFunctions.RHTower.XiFiniteEvaluationReporter

/-!
# Exact data-processing boundary for finite Xi evaluation reporters

The abstract reporter data-processing theorem assumes that information is nonsingular before a
decoder and singular afterwards.  Completed-Xi jet freeness discharges the first hypothesis with
one concrete unisolvent sample packet at every finite resolution.

For that packet, decoded Gram singularity is classified exactly by a genuinely nonzero Xi jet
packet which is nonzero in the samples but erased by the decoder.  Consequently every compression
into fewer than `N` Hilbert dimensions loses such a packet from an `N`-jet sample block.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u

/-- **Exact Xi sample data-processing alternative.**  At every finite jet resolution there is one
packet of pairwise distinct sample points such that, for every Hilbert-valued linear decoder,
singularity of the decoded reporter Gram is equivalent to erasure of a genuinely nonzero Xi jet
packet which was visibly nonzero before decoding. -/
theorem exists_injective_xiFiniteEvaluationReporter_exactDataProcessingAlternative (N : ℕ) :
    ∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      ∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
        (finiteDerivativeReporterGram N xi
          (decode.comp (finiteEvaluationReporter points))).det = 0 ↔
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          decode (finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi)) = 0 := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hpreGram, hpreDetPos,
      _hpreInjective, _hpreKer, _hpreRank, _hpreInfo⟩ :=
    exists_injective_xiFiniteEvaluationReporterHilbertReconstruction N
  refine ⟨points, hinj, hpreGram, ?_⟩
  intro Y _ _ decode
  constructor
  · intro hpost
    obtain ⟨c, _hcpost, hcpre, hpacket, hreport, hdecode⟩ :=
      exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_gram_det_transition
        N xi (finiteEvaluationReporter points) decode hpreDetPos.ne' hpost
    have hc : c ≠ 0 := by
      intro hzero
      apply hcpre
      rw [hzero]
      exact Submodule.zero_mem _
    exact ⟨c, hc, hpacket, hreport, hdecode⟩
  · rintro ⟨c, hc, _hpacket, _hreport, hdecode⟩
    by_contra hdet
    have hinjective : Function.Injective
        (finiteDerivativeReporterMap N xi
          (decode.comp (finiteEvaluationReporter points))) :=
      (finiteDerivativeReporterGram_det_ne_zero_iff_injective
        N xi (decode.comp (finiteEvaluationReporter points))).mp hdet
    have hcmap : finiteDerivativeReporterMap N xi
        (decode.comp (finiteEvaluationReporter points)) c = 0 := by
      simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hdecode
    apply hc
    apply hinjective
    rw [hcmap, map_zero]

/-- **Strict Xi sample-compression loss.**  Every decoder from an `N`-sample faithful Xi reporter
into a Hilbert space of finrank below `N` erases a genuinely nonzero Xi jet packet which had a
nonzero sample vector.  The pre-decoding faithfulness and post-decoding singularity hypotheses are
both discharged. -/
theorem exists_injective_xiFiniteEvaluationReporter_strictCompressionBlindPacket (N : ℕ) :
    ∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      ∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          [FiniteDimensional ℂ Y]
          (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
        finrank ℂ Y < N →
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          decode (finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi)) = 0 := by
  obtain ⟨points, hinj, hpreGram, halternative⟩ :=
    exists_injective_xiFiniteEvaluationReporter_exactDataProcessingAlternative N
  refine ⟨points, hinj, hpreGram, ?_⟩
  intro Y _ _ _ decode hdim
  apply (halternative Y decode).mp
  exact finiteDerivativeReporterGram_det_eq_zero_of_finrank_lt
    N xi (decode.comp (finiteEvaluationReporter points)) hdim

end

end RHTower
