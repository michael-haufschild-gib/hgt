import GaloisForLFunctions.RHTower.XiArbitraryJetCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiFiniteEvaluationReporterDataProcessing

/-!
# Cofinite completed-Xi evaluation reporters and data processing

The completed-Xi cofinite reconstruction theorem lets the literal evaluation reporter avoid any
prescribed finite subset of the complex plane.  The resulting packet retains exact dual recovery,
strict reporter information, injective coefficient readout, zero blind kernel, full visible rank,
and positive sequential information at every admitted derivative order.

The existing exact Hilbert-reporter data-processing boundary then applies to that same surviving
packet.  Decoded Gram singularity is exactly the appearance of a genuinely nonzero Xi jet packet
which was visible before decoding and erased afterward; every decoder into fewer than `N`
dimensions necessarily creates such a loss.
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry
open Module

noncomputable section

/-- **Deletion-robust Xi evaluation reporter reconstruction.**  After every finite deletion of the
complex sampling domain, one packet of exactly `N` surviving samples gives exact coefficient
recovery, strict information, faithful readout, full visible rank, and positive sequential
information throughout the initial Xi derivative block. -/
theorem xiCofiniteEvaluationReporterHilbertReconstruction (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin N → {z : ℂ // z ∉ F}) (dual : Fin N → Fin N → ℂ),
        Function.Injective points ∧
        (∀ (q r : Fin N),
          ∑ i, dual q i * iteratedDeriv (r : ℕ) xi (points i) =
            if q = r then 1 else 0) ∧
        (∀ (a : Fin N → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * iteratedDeriv (r : ℕ) xi (points i)) = a q) ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        0 < (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).det ∧
        Function.Injective
          (finiteDerivativeReporterMap N xi
            (finiteEvaluationReporter (fun i => (points i : ℂ)))) ∧
        LinearMap.ker
          (finiteDerivativeReporterMap N xi
            (finiteEvaluationReporter (fun i => (points i : ℂ)))) = ⊥ ∧
        finrank ℂ (LinearMap.range
          (finiteDerivativeReporterMap N xi
            (finiteEvaluationReporter (fun i => (points i : ℂ))))) = N ∧
        ∀ k : ℕ, k < N →
          0 < finiteDerivativeReporterConditionalInformation k xi
            (finiteEvaluationReporter (fun i => (points i : ℂ))) := by
  intro F hF
  obtain ⟨points, dual, hpoints, hdelta, hrecovery, hgram, _hdet⟩ :=
    exists_injective_xiDerivativeOrderCofiniteHilbertReconstruction
      (fun j : Fin N => (j : ℕ)) Fin.val_injective F hF
  let report :=
    finiteEvaluationReporter (fun i => (points i : ℂ))
  have hreportGram :
      (finiteDerivativeReporterGram N xi report).PosDef := by
    simpa [report, finiteDerivativeReporterGram_finiteEvaluationReporter,
      cofiniteEvaluationGram, cofiniteEvaluationColumn,
      finiteEvaluationGram, finiteEvaluationColumn,
      xiDerivativeOrderFamily] using! hgram
  have hreportDetPos :
      0 < (finiteDerivativeReporterGram N xi report).det :=
    hreportGram.det_pos
  have hreportInjective :
      Function.Injective (finiteDerivativeReporterMap N xi report) :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_injective
      N xi report).mp hreportDetPos.ne'
  have hker : LinearMap.ker
      (finiteDerivativeReporterMap N xi report) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hreportInjective
  have hrank : finrank ℂ (LinearMap.range
      (finiteDerivativeReporterMap N xi report)) = N := by
    simpa using LinearMap.finrank_range_of_inj hreportInjective
  have hinfo : ∀ k : ℕ, k < N →
      0 < finiteDerivativeReporterConditionalInformation k xi report :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_forall_conditionalInformation_pos
      N xi report).mp hreportDetPos.ne'
  exact ⟨points, dual, hpoints, hdelta, hrecovery, hreportGram,
    hreportDetPos, hreportInjective, hker, hrank, hinfo⟩

universe u

/-- **Cofinite Xi data-processing alternative.**  For every finite forbidden set, one surviving
faithful sample packet has the property that decoded Gram singularity is exactly erasure of a
genuinely nonzero Xi jet packet which was visible before decoding. -/
theorem xiCofiniteEvaluationReporter_exactDataProcessingAlternative (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        ∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
            (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
          (finiteDerivativeReporterGram N xi
            (decode.comp
              (finiteEvaluationReporter (fun i => (points i : ℂ))))).det = 0 ↔
          ∃ c : Fin N → ℂ,
            c ≠ 0 ∧
            finiteDerivativeReporterPacket c xi ≠ 0 ∧
            finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
            decode (finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c xi)) = 0 := by
  intro F hF
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hpreGram, hpreDetPos,
      _hpreInjective, _hpreKer, _hpreRank, _hpreInfo⟩ :=
    xiCofiniteEvaluationReporterHilbertReconstruction N F hF
  refine ⟨points, hinj, hpreGram, ?_⟩
  intro Y _ _ decode
  constructor
  · intro hpost
    obtain ⟨c, _hcpost, hcpre, hpacket, hreport, hdecode⟩ :=
      exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_gram_det_transition
        N xi (finiteEvaluationReporter (fun i => (points i : ℂ)))
          decode hpreDetPos.ne' hpost
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
          (decode.comp
            (finiteEvaluationReporter (fun i => (points i : ℂ))))) :=
      (finiteDerivativeReporterGram_det_ne_zero_iff_injective
        N xi
          (decode.comp
            (finiteEvaluationReporter (fun i => (points i : ℂ))))).mp hdet
    have hcmap : finiteDerivativeReporterMap N xi
        (decode.comp
          (finiteEvaluationReporter (fun i => (points i : ℂ)))) c = 0 := by
      simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hdecode
    apply hc
    apply hinjective
    rw [hcmap, map_zero]

/-- **Cofinite strict Xi compression loss.**  After every finite complex deletion, one faithful
surviving `N`-sample reporter exposes a genuinely nonzero visible Xi jet packet erased by every
decoder whose output finrank is below `N`. -/
theorem xiCofiniteEvaluationReporter_strictCompressionBlindPacket (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        ∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
            [FiniteDimensional ℂ Y]
            (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
          finrank ℂ Y < N →
          ∃ c : Fin N → ℂ,
            c ≠ 0 ∧
            finiteDerivativeReporterPacket c xi ≠ 0 ∧
            finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
            decode (finiteEvaluationReporter (fun i => (points i : ℂ))
              (finiteDerivativeReporterPacket c xi)) = 0 := by
  intro F hF
  obtain ⟨points, hinj, hpreGram, halternative⟩ :=
    xiCofiniteEvaluationReporter_exactDataProcessingAlternative N F hF
  refine ⟨points, hinj, hpreGram, ?_⟩
  intro Y _ _ _ decode hdim
  apply (halternative Y decode).mp
  exact finiteDerivativeReporterGram_det_eq_zero_of_finrank_lt
    N xi
      (decode.comp
        (finiteEvaluationReporter (fun i => (points i : ℂ)))) hdim

end

end RHTower
