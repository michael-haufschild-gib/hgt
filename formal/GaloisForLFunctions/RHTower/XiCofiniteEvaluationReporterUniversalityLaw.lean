import GaloisForLFunctions.RHTower.XiCofiniteEvaluationReporterDataProcessing
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation
import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery

/-!
# Cofinite Xi evaluation-reporter universality

One completed-Xi evaluation packet can now be chosen outside every prescribed finite complex set
while simultaneously retaining three previously separate phases: faithful Xi geometry,
source-sensitive blindness to a genuinely new logarithmic-derivative direction, and exact
classification of every decoder-created Xi packet loss.

The same packet is universal under isometric recoding.  Its Xi Gram geometry and logarithmic-source
collapse are unchanged, the Hilbert adjoint recovers the original reporter exactly, every later
decoder obeys the exact packet-erasure alternative, and every output of finrank below the sampling
resolution necessarily erases a genuinely nonzero packet visible both before and after encoding.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u v

/-- **Cofinite joint Xi source/data-processing universality.**  Outside every finite forbidden
set, one faithful Xi sample packet also detects the source-sensitive logarithmic-derivative
collapse, classifies all decoder-created losses, and forces loss under every subcritical
finite-dimensional decoder. -/
theorem xiCofiniteEvaluationReporter_jointSourceDataProcessingUniversality (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        (∃ k : ℕ, k ≤ N ∧
          finiteDerivativeReporterConditionalInformation k (logDeriv xi)
              (finiteEvaluationReporter (fun i => (points i : ℂ))) = 0 ∧
          finiteEvaluationReporter (fun i => (points i : ℂ))
              (iteratedDeriv k (logDeriv xi)) ∈
            finiteDerivativeReporterPreviousSpace k (logDeriv xi)
              (finiteEvaluationReporter (fun i => (points i : ℂ))) ∧
          iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
            (Set.range fun i : Fin k =>
              iteratedDeriv (i : ℕ) (logDeriv xi))) ∧
        (∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
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
              (finiteDerivativeReporterPacket c xi)) = 0) ∧
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
  obtain ⟨points, hinjective, hpreGram, halternative⟩ :=
    xiCofiniteEvaluationReporter_exactDataProcessingAlternative N F hF
  let report :=
    finiteEvaluationReporter (fun i => (points i : ℂ))
  obtain ⟨k, hk, hzero, hreported, hsource⟩ :=
    exists_xiLogDeriv_finiteReporterConditionalInformation_collapse report
  have hkN : k ≤ N := by
    simpa [report] using hk
  have hstrict :
      ∀ (Y : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          [FiniteDimensional ℂ Y]
          (decode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y),
        finrank ℂ Y < N →
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          decode (report (finiteDerivativeReporterPacket c xi)) = 0 := by
    intro Y _ _ _ decode hdim
    apply (halternative Y decode).mp
    exact finiteDerivativeReporterGram_det_eq_zero_of_finrank_lt
      N xi (decode.comp report) hdim
  exact ⟨points, hinjective, hpreGram,
    ⟨k, hkN, hzero, hreported, hsource⟩, halternative, hstrict⟩

/-- **Cofinite isometric Xi source/data-processing universality.**  The cofinite joint packet
survives every isometric representation with identical Xi information, identical logarithmic
source blindness, exact adjoint recovery, and exact downstream loss classification.  Every
subcritical finite-dimensional downstream channel necessarily erases a packet visible on both
sides of the isometric encoding. -/
theorem xiCofiniteEvaluationReporter_isometricDataProcessingUniversality (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter (fun i => (points i : ℂ)))).PosDef ∧
        ∀ (Z : Type u) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
            [CompleteSpace Z]
            (encode : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] Z),
          (finiteDerivativeReporterGram N xi
            (encode.toLinearMap.comp
              (finiteEvaluationReporter (fun i => (points i : ℂ))))).PosDef ∧
          (∃ k : ℕ, k ≤ N ∧
            finiteDerivativeReporterConditionalInformation k (logDeriv xi)
                (finiteEvaluationReporter (fun i => (points i : ℂ))) = 0 ∧
            finiteDerivativeReporterConditionalInformation k (logDeriv xi)
                (encode.toLinearMap.comp
                  (finiteEvaluationReporter
                    (fun i => (points i : ℂ)))) = 0 ∧
            iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
              (Set.range fun i : Fin k =>
                iteratedDeriv (i : ℕ) (logDeriv xi))) ∧
          encode.toContinuousLinearMap.adjoint.toLinearMap.comp
              (encode.toLinearMap.comp
                (finiteEvaluationReporter (fun i => (points i : ℂ)))) =
            finiteEvaluationReporter (fun i => (points i : ℂ)) ∧
          (∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              (decode : Z →ₗ[ℂ] Y),
            (finiteDerivativeReporterGram N xi
              (decode.comp
                (encode.toLinearMap.comp
                  (finiteEvaluationReporter
                    (fun i => (points i : ℂ)))))).det = 0 ↔
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              finiteEvaluationReporter (fun i => (points i : ℂ))
                (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (finiteEvaluationReporter (fun i => (points i : ℂ))
                (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode
                (finiteEvaluationReporter (fun i => (points i : ℂ))
                  (finiteDerivativeReporterPacket c xi))) = 0) ∧
          ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              [FiniteDimensional ℂ Y] (decode : Z →ₗ[ℂ] Y),
            finrank ℂ Y < N →
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              finiteEvaluationReporter (fun i => (points i : ℂ))
                (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (finiteEvaluationReporter (fun i => (points i : ℂ))
                (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode
                (finiteEvaluationReporter (fun i => (points i : ℂ))
                  (finiteDerivativeReporterPacket c xi))) = 0 := by
  intro F hF
  obtain ⟨points, hinjective, hXi, hcollapse, halternative, hstrict⟩ :=
    xiCofiniteEvaluationReporter_jointSourceDataProcessingUniversality N F hF
  refine ⟨points, hinjective, hXi, ?_⟩
  intro Z _ _ _ encode
  let report :=
    finiteEvaluationReporter (fun i => (points i : ℂ))
  have hencodedXi :
      (finiteDerivativeReporterGram N xi
        (encode.toLinearMap.comp report)).PosDef := by
    rw [finiteDerivativeReporterGram_postcomp_linearIsometry]
    exact hXi
  obtain ⟨k, hkN, hzero, _hreported, hsource⟩ := hcollapse
  have hencodedZero :
      finiteDerivativeReporterConditionalInformation k (logDeriv xi)
          (encode.toLinearMap.comp report) = 0 := by
    rw [finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry,
      hzero]
  have hrecover :
      encode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (encode.toLinearMap.comp report) = report :=
    finiteDerivativeReporter_isometricAdjointRecovery report encode
  have hexact :
      ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          (decode : Z →ₗ[ℂ] Y),
        (finiteDerivativeReporterGram N xi
          (decode.comp (encode.toLinearMap.comp report))).det = 0 ↔
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
          decode (encode (report
            (finiteDerivativeReporterPacket c xi))) = 0 := by
    intro Y _ _ decode
    let totalDecode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y :=
      decode.comp encode.toLinearMap
    have hbase := halternative Y totalDecode
    constructor
    · intro hdet
      have hdet' :
          (finiteDerivativeReporterGram N xi
            (totalDecode.comp report)).det = 0 := by
        simpa only [totalDecode, LinearMap.comp_assoc] using hdet
      obtain ⟨c, hc, hpacket, hreport, herase⟩ := hbase.mp hdet'
      have hencoded :
          encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 := by
        intro hzeroEncoded
        apply hreport
        exact encode.injective (by simpa using hzeroEncoded)
      refine ⟨c, hc, hpacket, hreport, hencoded, ?_⟩
      simpa only [totalDecode, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap] using herase
    · rintro ⟨c, hc, hpacket, hreport, _hencoded, herase⟩
      have htotalErase : totalDecode
          (report (finiteDerivativeReporterPacket c xi)) = 0 := by
        simpa only [totalDecode, LinearMap.comp_apply,
          LinearIsometry.coe_toLinearMap] using herase
      have hdet' := hbase.mpr ⟨c, hc, hpacket, hreport, htotalErase⟩
      simpa only [totalDecode, LinearMap.comp_assoc] using hdet'
  have hstrictEncoded :
      ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
          [FiniteDimensional ℂ Y] (decode : Z →ₗ[ℂ] Y),
        finrank ℂ Y < N →
        ∃ c : Fin N → ℂ,
          c ≠ 0 ∧
          finiteDerivativeReporterPacket c xi ≠ 0 ∧
          report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
          encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
          decode (encode (report
            (finiteDerivativeReporterPacket c xi))) = 0 := by
    intro Y _ _ _ decode hdim
    let totalDecode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y :=
      decode.comp encode.toLinearMap
    obtain ⟨c, hc, hpacket, hreport, herase⟩ :=
      hstrict Y totalDecode hdim
    have hencoded :
        encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 := by
      intro hzeroEncoded
      apply hreport
      exact encode.injective (by simpa using hzeroEncoded)
    refine ⟨c, hc, hpacket, hreport, hencoded, ?_⟩
    simpa only [totalDecode, LinearMap.comp_apply,
      LinearIsometry.coe_toLinearMap] using herase
  exact ⟨hencodedXi, ⟨k, hkN, hzero, hencodedZero, hsource⟩,
    hrecover, hexact, hstrictEncoded⟩

end

end RHTower
