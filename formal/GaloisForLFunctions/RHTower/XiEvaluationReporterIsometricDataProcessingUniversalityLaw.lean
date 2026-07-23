import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.RHTower.XiFiniteEvaluationReporterDataProcessing
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation

/-!
# Xi evaluation-reporter isometric data-processing universality

One unisolvent completed-Xi evaluation packet survives every isometric recoding with its positive
Gram geometry intact.  The same recoding preserves a genuinely new but reporter-blind `logDeriv
xi` direction and is recovered exactly by its Hilbert adjoint.  Every later linear decoder still
obeys the exact Xi packet-erasure alternative.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u v

/-- **Xi isometric source/data-processing law.**  At every finite resolution, one point packet
simultaneously has faithful Xi geometry, irrecoverable logarithmic-source information, exact
adjoint recovery of every isometric representation, and an exact downstream decoder-erasure
classification. -/
theorem exists_injective_xiEvaluationReporter_isometricDataProcessingUniversality (N : ℕ) :
    ∃ points : Fin N → ℂ,
      Function.Injective points ∧
      (finiteDerivativeReporterGram N xi
        (finiteEvaluationReporter points)).PosDef ∧
      ∀ (Z : Type u) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
          (encode : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] Z),
        (finiteDerivativeReporterGram N xi
          (encode.toLinearMap.comp (finiteEvaluationReporter points))).PosDef ∧
        (∃ k : ℕ, k ≤ N ∧
          finiteDerivativeReporterConditionalInformation k (logDeriv xi)
              (finiteEvaluationReporter points) = 0 ∧
          finiteDerivativeReporterConditionalInformation k (logDeriv xi)
              (encode.toLinearMap.comp (finiteEvaluationReporter points)) = 0 ∧
          iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
            (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi))) ∧
        encode.toContinuousLinearMap.adjoint.toLinearMap.comp
            (encode.toLinearMap.comp (finiteEvaluationReporter points)) =
          finiteEvaluationReporter points ∧
        ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
            (decode : Z →ₗ[ℂ] Y),
          (finiteDerivativeReporterGram N xi
            (decode.comp
              (encode.toLinearMap.comp (finiteEvaluationReporter points)))).det = 0 ↔
          ∃ c : Fin N → ℂ,
            c ≠ 0 ∧
            finiteDerivativeReporterPacket c xi ≠ 0 ∧
            finiteEvaluationReporter points
              (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
            encode (finiteEvaluationReporter points
              (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
            decode (encode (finiteEvaluationReporter points
              (finiteDerivativeReporterPacket c xi))) = 0 := by
  obtain ⟨points, hinjective, hXi, halternative⟩ :=
    exists_injective_xiFiniteEvaluationReporter_exactDataProcessingAlternative N
  refine ⟨points, hinjective, hXi, ?_⟩
  intro Z _ _ _ encode
  let report := finiteEvaluationReporter points
  have hencodedXi :
      (finiteDerivativeReporterGram N xi
        (encode.toLinearMap.comp report)).PosDef := by
    rw [finiteDerivativeReporterGram_postcomp_linearIsometry]
    exact hXi
  obtain ⟨k, hk, hzero, _hreported, hsource⟩ :=
    exists_xiLogDeriv_finiteReporterConditionalInformation_collapse report
  have hkN : k ≤ N := by simpa [report] using hk
  have hencodedZero :
      finiteDerivativeReporterConditionalInformation k (logDeriv xi)
          (encode.toLinearMap.comp report) = 0 := by
    rw [finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry,
      hzero]
  have hrecover :
      encode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (encode.toLinearMap.comp report) = report :=
    finiteDerivativeReporter_isometricAdjointRecovery report encode
  refine ⟨hencodedXi, ⟨k, hkN, hzero, hencodedZero, hsource⟩, hrecover, ?_⟩
  intro Y _ _ decode
  let totalDecode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y :=
    decode.comp encode.toLinearMap
  have hbase := halternative Y totalDecode
  constructor
  · intro hdet
    have hdet' :
        (finiteDerivativeReporterGram N xi
          (totalDecode.comp (finiteEvaluationReporter points))).det = 0 := by
      simpa only [totalDecode, LinearMap.comp_assoc] using hdet
    obtain ⟨c, hc, hpacket, hreport, herase⟩ := hbase.mp hdet'
    have hencoded : encode
        (finiteEvaluationReporter points (finiteDerivativeReporterPacket c xi)) ≠ 0 := by
      intro hzeroEncoded
      apply hreport
      exact encode.injective (by simpa using hzeroEncoded)
    refine ⟨c, hc, hpacket, hreport, hencoded, ?_⟩
    simpa only [totalDecode, LinearMap.comp_apply,
      LinearIsometry.coe_toLinearMap] using herase
  · rintro ⟨c, hc, hpacket, hreport, _hencoded, herase⟩
    have htotalErase : totalDecode
        (finiteEvaluationReporter points (finiteDerivativeReporterPacket c xi)) = 0 := by
      simpa only [totalDecode, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap] using herase
    have hdet' := hbase.mpr ⟨c, hc, hpacket, hreport, htotalErase⟩
    simpa only [totalDecode, LinearMap.comp_assoc] using hdet'

end

end RHTower
