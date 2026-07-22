import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.RHTower.XiLogDerivFiniteSpectralDressing
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

/-!
# Isometric recovery does not repair Xi reporter blindness

An isometric downstream encoding preserves every finite Xi reporter information value and is
exactly decoded by its Hilbert adjoint.  Nevertheless, the unconditional finite-dimensional Xi
reporter collapse remains: perfect recovery returns the original reporter, including its blind
direction, rather than recovering the derivative information erased before the encoding.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- **Complete Xi isometric observability profile.**  At every jet resolution, isometric recoding
preserves Gram geometry, conditional information, visible coefficient rank, and the complete blind
coefficient subspace; one adjoint recovers the reporter uniformly across all resolutions. -/
theorem xiLogDerivReporter_isometricObservabilityProfile
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    (∀ N,
      HTGeometry.finiteDerivativeReporterGram N (logDeriv xi)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterGram N (logDeriv xi) report ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report ∧
      Module.finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
            (decode.toLinearMap.comp report))) =
        Module.finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
      LinearMap.ker (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi)
          (decode.toLinearMap.comp report)) =
        LinearMap.ker
          (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) ∧
    decode.toContinuousLinearMap.adjoint.toLinearMap.comp
        (decode.toLinearMap.comp report) = report := by
  constructor
  · intro N
    have h := HTGeometry.finiteDerivativeReporter_isometricObservabilityProfile
      N (logDeriv xi) report decode
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · exact HTGeometry.finiteDerivativeReporter_isometricAdjointRecovery report decode

/-- Isometric postprocessing preserves the complete Xi conditional-information tower and admits
the adjoint as an exact reporter recovery. -/
theorem xiLogDerivReporter_isometric_information_and_recovery
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    (∀ N,
      HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterConditionalInformation N (logDeriv xi) report) ∧
    decode.toContinuousLinearMap.adjoint.toLinearMap.comp
        (decode.toLinearMap.comp report) = report := by
  have h := xiLogDerivReporter_isometricObservabilityProfile report decode
  exact ⟨fun N => (h.1 N).2.1, h.2⟩

/-- **Perfectly recoverable reporter, irrecoverable source direction.**  At the unconditional Xi
collapse order, the isometric encoding has the same zero information and its adjoint recovers the
original reporter exactly, while the source derivative remains independent of all predecessors. -/
theorem exists_xiLogDeriv_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi)
        (decode.toLinearMap.comp report) = 0 ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  obtain ⟨k, hk, hzero, hpostzero, _, _, hrecover, hsource⟩ :=
    HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
      xiLogDeriv_constantCoefficientDifferentiallyTranscendental
      report decode
  exact ⟨k, hk, hzero, hpostzero, hrecover, hsource⟩

/-- **Exact Xi collapse packet under isometric recovery.**  At one unconditional Xi
logarithmic-derivative collapse order, the newest coefficient can be normalized to `-1` in a
genuinely nonzero source packet.  Original and encoded reporters annihilate that same packet and
have identical visible rank and blind kernel at its resolution. -/
theorem exists_xiLogDeriv_isometricReporterRecovery_exactBlindPacket_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ (k : ℕ) (c : Fin (k + 1) → ℂ),
      k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi)
          (decode.toLinearMap.comp report) = 0 ∧
      c (Fin.last k) = -1 ∧
      c ∈ LinearMap.ker
        (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi) report) ∧
      c ∈ LinearMap.ker (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi)
        (decode.toLinearMap.comp report)) ∧
      LinearMap.ker (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi)
          (decode.toLinearMap.comp report)) =
        LinearMap.ker
          (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi) report) ∧
      finrank ℂ (LinearMap.range (HTGeometry.finiteDerivativeReporterMap (k + 1)
          (logDeriv xi) (decode.toLinearMap.comp report))) =
        finrank ℂ (LinearMap.range
          (HTGeometry.finiteDerivativeReporterMap (k + 1) (logDeriv xi) report)) ∧
      HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi))) = 0 ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  exact HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_exactBlindPacket_collapse
    xiLogDeriv_constantCoefficientDifferentiallyTranscendental report decode

/-- **Perfect Xi recovery preserves singular information.**  Some bounded Xi logarithmic-
derivative Gram block is singular both before and after isometric recoding, even though the
encoded reporter is recovered exactly and the collapsed derivative remains new at the source. -/
theorem exists_xiLogDeriv_isometricReporterRecovery_singularGram_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      (HTGeometry.finiteDerivativeReporterGram (k + 1) (logDeriv xi) report).det = 0 ∧
      (HTGeometry.finiteDerivativeReporterGram (k + 1) (logDeriv xi)
        (decode.toLinearMap.comp report)).det = 0 ∧
      HTGeometry.finiteDerivativeReporterGram (k + 1) (logDeriv xi)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterGram (k + 1) (logDeriv xi) report ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  exact HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_singularGram_collapse
    xiLogDeriv_constantCoefficientDifferentiallyTranscendental report decode

/-- **Finite-Gibbs dressed Xi recovery boundary.**  Isometric postprocessing exactly recovers the
dressed reporter and preserves its zero-information witness, but cannot recover the same genuinely
new derivative direction erased before reporting. -/
theorem exists_xiLogDeriv_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  exact HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
    (xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy)
    report decode

/-- Finite Gibbs dressing likewise cannot remove simultaneous original/encoded Xi Gram
singularity under perfect isometric recovery. -/
theorem exists_xiLogDeriv_add_finiteGibbs_isometricReporterRecovery_singularGram_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      (HTGeometry.finiteDerivativeReporterGram (k + 1)
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report).det = 0 ∧
      (HTGeometry.finiteDerivativeReporterGram (k + 1)
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
        (decode.toLinearMap.comp report)).det = 0 ∧
      HTGeometry.finiteDerivativeReporterGram (k + 1)
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) =
        HTGeometry.finiteDerivativeReporterGram (k + 1)
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  exact HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_singularGram_collapse
    (xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy)
    report decode

end

end RHTower
