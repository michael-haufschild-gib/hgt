import GaloisForLFunctions.RHTower.XiCofiniteEvaluationReporterUniversalityLaw
import GaloisForLFunctions.RHTower.XiLogDerivRecoverableBlindnessUniversalityLaw

/-!
# Xi cofinite bounded-recoverable reporter universality

Outside every finite forbidden sampling set, one finite Xi evaluation packet remains faithful
under every bounded recoding admitting bounded exact left recovery on that packet.  The same
recovery preserves the complete log-Xi blind coefficient space and a normalized nonzero blind
source packet.  Isometry is therefore unnecessary for the joint cofinite faithfulness/blindness
law.
-/

open scoped ComplexOrder InnerProductSpace

namespace RHTower

open GaloisForLFunctions
open HTGeometry
open Module

noncomputable section

universe u v

/-- **Xi cofinite bounded-recoverable reporter universality.**  After every finite deletion of
sampling points, one faithful Xi reporter stays faithful under arbitrary bounded exact-recoverable
recoding, while the log-Xi zero-information phase, visible rank, blind kernel, and a normalized
nonzero blind packet are unchanged. -/
theorem xiCofiniteEvaluationReporter_boundedRecoverableBlindnessUniversality
    (N : ℕ) :
    ∀ F : Set ℂ, F.Finite →
      ∃ points : Fin N → {z : ℂ // z ∉ F},
        Function.Injective points ∧
        let report := finiteEvaluationReporter (fun i => (points i : ℂ))
        (finiteDerivativeReporterGram N xi report).PosDef ∧
        ∀ (Z : Type u) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
            (encode : EuclideanSpace ℂ (Fin N) →L[ℂ] Z)
            (recover : Z →L[ℂ] EuclideanSpace ℂ (Fin N)),
          recover.toLinearMap.comp (encode.toLinearMap.comp report) = report →
          (finiteDerivativeReporterGram N xi
            (encode.toLinearMap.comp report)).PosDef ∧
          XiLogDerivRecoverableBlindnessCertificate report encode ∧
          (∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              (decode : Z →ₗ[ℂ] Y),
            (finiteDerivativeReporterGram N xi
              (decode.comp (encode.toLinearMap.comp report))).det = 0 ↔
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode
                (report (finiteDerivativeReporterPacket c xi))) = 0) ∧
          ∀ (Y : Type v) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
              [FiniteDimensional ℂ Y] (decode : Z →ₗ[ℂ] Y),
            finrank ℂ Y < N →
            ∃ c : Fin N → ℂ,
              c ≠ 0 ∧
              finiteDerivativeReporterPacket c xi ≠ 0 ∧
              report (finiteDerivativeReporterPacket c xi) ≠ 0 ∧
              encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 ∧
              decode (encode
                (report (finiteDerivativeReporterPacket c xi))) = 0 := by
  intro F hF
  obtain ⟨points, hinjective, hXi, _hcollapse, halternative, hstrict⟩ :=
    xiCofiniteEvaluationReporter_jointSourceDataProcessingUniversality.{v} N F hF
  refine ⟨points, hinjective, ?_⟩
  dsimp only
  let report := finiteEvaluationReporter (fun i => (points i : ℂ))
  have hXi' : (finiteDerivativeReporterGram N xi report).PosDef := by
    simpa only [report] using hXi
  refine ⟨hXi', ?_⟩
  intro Z _ _ encode recover hrecover
  have hpreInjective :
      Function.Injective (finiteDerivativeReporterMap N xi report) :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_injective
      N xi report).1 hXi'.det_pos.ne'
  have hprofile :=
    finiteDerivativeReporter_recoverableCapacityAndInformationProfile
      N xi report encode recover hrecover
  have hpostInjective :
      Function.Injective
        (finiteDerivativeReporterMap N xi (encode.toLinearMap.comp report)) := by
    apply LinearMap.ker_eq_bot.mp
    rw [hprofile.2.1]
    exact LinearMap.ker_eq_bot.mpr hpreInjective
  have hpostGram :
      (finiteDerivativeReporterGram N xi
        (encode.toLinearMap.comp report)).PosDef := by
    rw [finiteDerivativeReporterGram]
    exact Matrix.posDef_gram_of_linearIndependent
      ((linearIndependent_reportedDerivativeJets_iff_injective
        N xi (encode.toLinearMap.comp report)).2 hpostInjective)
  have hblind :=
    xiLogDerivReporter_recoverableBlindnessUniversality
      report encode recover hrecover
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
          decode (encode
            (report (finiteDerivativeReporterPacket c xi))) = 0 := by
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
        intro hzero
        apply hreport
        have hrecovered := LinearMap.congr_fun hrecover
          (finiteDerivativeReporterPacket c xi)
        have hzero' :
            encode ((finiteEvaluationReporter (fun i => (points i : ℂ)))
              (finiteDerivativeReporterPacket c xi)) = 0 := by
          simpa only [report] using hzero
        rw [← hrecovered]
        change recover (encode ((finiteEvaluationReporter
          (fun i => (points i : ℂ))) (finiteDerivativeReporterPacket c xi))) = 0
        rw [hzero']
        exact map_zero recover
      refine ⟨c, hc, hpacket, hreport, hencoded, ?_⟩
      simpa only [totalDecode, LinearMap.comp_apply] using herase
    · rintro ⟨c, hc, hpacket, hreport, _hencoded, herase⟩
      have htotalErase :
          totalDecode (report (finiteDerivativeReporterPacket c xi)) = 0 := by
        simpa only [totalDecode, LinearMap.comp_apply] using herase
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
          decode (encode
            (report (finiteDerivativeReporterPacket c xi))) = 0 := by
    intro Y _ _ _ decode hdim
    let totalDecode : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] Y :=
      decode.comp encode.toLinearMap
    obtain ⟨c, hc, hpacket, hreport, herase⟩ :=
      hstrict Y totalDecode hdim
    have hencoded :
        encode (report (finiteDerivativeReporterPacket c xi)) ≠ 0 := by
      intro hzero
      apply hreport
      have hrecovered := LinearMap.congr_fun hrecover
        (finiteDerivativeReporterPacket c xi)
      have hzero' :
          encode ((finiteEvaluationReporter (fun i => (points i : ℂ)))
            (finiteDerivativeReporterPacket c xi)) = 0 := by
        simpa only [report] using hzero
      rw [← hrecovered]
      change recover (encode ((finiteEvaluationReporter
        (fun i => (points i : ℂ))) (finiteDerivativeReporterPacket c xi))) = 0
      rw [hzero']
      exact map_zero recover
    refine ⟨c, hc, hpacket, hreport, hencoded, ?_⟩
    simpa only [totalDecode, LinearMap.comp_apply] using herase
  exact ⟨hpostGram, hblind, hexact, hstrictEncoded⟩

end

end RHTower
