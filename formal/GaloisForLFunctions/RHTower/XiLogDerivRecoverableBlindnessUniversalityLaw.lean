import GaloisForLFunctions.RHTower.XiLogDerivReporterBoundedRecovery
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation

/-!
# Recoverable Xi-reporter blindness universality

An arbitrary bounded recoding with a bounded left recovery can distort nonzero conditional
information, but it cannot change which Xi logarithmic-derivative innovations vanish.  At every
resolution it also preserves the complete blind coefficient space and visible rank.  Therefore
the unconditional finite-reporter collapse has one normalized, genuinely nonzero source packet
which is blind before and after every exactly recoverable bounded recoding.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- Complete invariant carried by an exactly recoverable bounded recoding of a finite Xi
logarithmic-derivative reporter. -/
def XiLogDerivRecoverableBlindnessCertificate
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) : Prop :=
  (∀ N,
    HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
        (decode.toLinearMap.comp report) = 0 ↔
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report = 0) ∧
  (∀ N,
    Module.finrank ℂ (LinearMap.range
        (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
          (decode.toLinearMap.comp report))) =
        Module.finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
    LinearMap.ker (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
        (decode.toLinearMap.comp report)) =
      LinearMap.ker
        (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
  ∃ (k : ℕ) (c : Fin (k + 1) → ℂ),
    k ≤ finrank ℂ Y ∧
    HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
    HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi)
        (decode.toLinearMap.comp report) = 0 ∧
    c (Fin.last k) = -1 ∧
    c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi) report) ∧
    c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi)
        (decode.toLinearMap.comp report)) ∧
    HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
    report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
    decode (report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi))) = 0 ∧
    iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
      (Set.range fun i : Fin k ↦ iteratedDeriv (i : ℕ) (logDeriv xi))

/-- **Recoverable-blindness universality law.**  Exact bounded recovery preserves the complete
zero-information phase, visible rank, blind coefficient space, and one normalized nonzero Xi
collapse packet.  Isometry is unnecessary. -/
theorem xiLogDerivReporter_recoverableBlindnessUniversality
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y)
    (decode : Y →L[ℂ] Z) (recover : Z →L[ℂ] Y)
    (hrecover : recover.toLinearMap.comp
        (decode.toLinearMap.comp report) = report) :
    XiLogDerivRecoverableBlindnessCertificate report decode := by
  have hzero : ∀ N,
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) = 0 ↔
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report = 0 := by
    intro N
    have hsandwich := xiLogDerivReporter_boundedRecovery_sandwich
      report decode recover hrecover N
    constructor
    · intro hpost
      have hle := hsandwich.2
      rw [hpost, mul_zero] at hle
      exact le_antisymm hle
        (HTGeometry.finiteDerivativeReporterConditionalInformation_nonneg
          N (logDeriv xi) report)
    · intro hpre
      have hle := hsandwich.1
      rw [hpre, mul_zero] at hle
      exact le_antisymm hle
        (HTGeometry.finiteDerivativeReporterConditionalInformation_nonneg
          N (logDeriv xi) (decode.toLinearMap.comp report))
  have hcapacity : ∀ N,
      Module.finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
            (decode.toLinearMap.comp report))) =
          Module.finrank ℂ (LinearMap.range
            (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
      LinearMap.ker (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
          (decode.toLinearMap.comp report)) =
        LinearMap.ker
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report) := by
    intro N
    have hprofile := xiLogDerivReporter_recoverableCapacityAndInformationProfile
      report decode recover hrecover N
    exact ⟨hprofile.1, hprofile.2.1⟩
  obtain ⟨k, c, hk, hkzero, hclast, hcker, hcne, hreport, hsource⟩ :=
    HTGeometry.exists_finiteDerivativeReporterConditionalInformation_normalizedBlindPacket_collapse
      xiLogDeriv_constantCoefficientDifferentiallyTranscendental report
  have hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi)
        (decode.toLinearMap.comp report)) := by
    rw [(hcapacity (k + 1)).2]
    exact hcker
  have hpostzero := (hzero k).2 hkzero
  have hdecode :
      decode (report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi))) = 0 := by
    rw [hreport]
    exact map_zero decode
  exact ⟨hzero, hcapacity, k, c, hk, hkzero, hpostzero, hclast, hcker, hcpost,
    hcne, hreport, hdecode, hsource⟩

end

end RHTower
