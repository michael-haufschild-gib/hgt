import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
import GaloisForLFunctions.RHTower.XiFiniteEvaluationReporter
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation

/-!
# One Xi evaluation packet for source discrimination and data processing

The source-discrimination and decoder-erasure theorems separately choose unisolvent Xi sample
packets.  Choosing the common finite-evaluation reconstruction once produces a stronger law: the
same packet is faithful to the completed-Xi jets, blind to a genuinely new logarithmic-derivative
direction, and universal for exact and strict decoder data-processing loss.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u

/-- **Joint Xi reporter source/data-processing law.**  At every finite resolution one sample
packet simultaneously discriminates `xi` from `logDeriv xi` and classifies every decoder loss by
erasure of a nonzero visible Xi jet packet.  Every decoder of smaller Hilbert dimension therefore
erases such a packet. -/
theorem exists_injective_xiEvaluationReporter_jointSourceDataProcessingUniversality (N : ℕ) :
    ∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      (∃ k : ℕ, k ≤ N ∧
        finiteDerivativeReporterConditionalInformation k (logDeriv xi)
            (finiteEvaluationReporter points) = 0 ∧
        finiteEvaluationReporter points (iteratedDeriv k (logDeriv xi)) ∈
          finiteDerivativeReporterPreviousSpace k (logDeriv xi)
            (finiteEvaluationReporter points) ∧
        iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
          (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi))) ∧
      (∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
        (finiteDerivativeReporterGram N xi
          (decode.comp (finiteEvaluationReporter points))).det = 0 ↔
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          decode (finiteEvaluationReporter points
            (finiteDerivativeReporterPacket c xi)) = 0) ∧
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
  obtain ⟨points, _dual, hinjective, _hdelta, _hrecovery, hpreGram, hpreDetPos,
      _hinjectiveMap, _hker, _hrank, _hinformation⟩ :=
    exists_injective_xiFiniteEvaluationReporterHilbertReconstruction N
  obtain ⟨k, hk, hzero, hreported, hsource⟩ :=
    exists_xiLogDeriv_finiteReporterConditionalInformation_collapse
      (finiteEvaluationReporter points)
  have hkN : k ≤ N := by simpa using hk
  have halternative :
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
    intro Y _ _ decode
    constructor
    · intro hpost
      obtain ⟨c, _hcpost, hcpre, hpacket, hreport, hdecode⟩ :=
        exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_gram_det_transition
          N xi (finiteEvaluationReporter points) decode hpreDetPos.ne' hpost
      have hc : c ≠ 0 := by
        intro hczero
        apply hcpre
        rw [hczero]
        exact Submodule.zero_mem _
      exact ⟨c, hc, hpacket, hreport, hdecode⟩
    · rintro ⟨c, hc, _hpacket, _hreport, hdecode⟩
      by_contra hdet
      have hinjectivePost : Function.Injective
          (finiteDerivativeReporterMap N xi
            (decode.comp (finiteEvaluationReporter points))) :=
        (finiteDerivativeReporterGram_det_ne_zero_iff_injective
          N xi (decode.comp (finiteEvaluationReporter points))).mp hdet
      have hcmap : finiteDerivativeReporterMap N xi
          (decode.comp (finiteEvaluationReporter points)) c = 0 := by
        simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hdecode
      apply hc
      apply hinjectivePost
      rw [hcmap, map_zero]
  have hstrict :
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
    intro Y _ _ _ decode hdim
    apply (halternative Y decode).mp
    exact finiteDerivativeReporterGram_det_eq_zero_of_finrank_lt
      N xi (decode.comp (finiteEvaluationReporter points)) hdim
  exact ⟨points, hinjective, hpreGram,
    ⟨k, hkN, hzero, hreported, hsource⟩, halternative, hstrict⟩

end

end RHTower
