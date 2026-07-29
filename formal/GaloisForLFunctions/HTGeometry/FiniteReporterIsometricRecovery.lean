import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric recovery of finite derivative-clock reporters

General postprocessing can only decrease finite reporter information.  An isometric
postprocessor is the exact equality case: it preserves every reported-jet Gram matrix, and its
Hilbert adjoint recovers the original reporter on the nose.  Applying data processing once to the
isometric encoding and once to the recovered channel proves equality of every sequential
conditional-information value.

This is a finite-observation recovery theorem, not a temporal statement.  It separates two kinds
of loss: isometric recoding loses no reporter information, while any blindness already present in
the reporter remains present after perfect recovery.

Quantum-information provenance: preservation of an information metric under a sufficient channel
is the equality/recovery side of quantum data processing; see Gao--Li--Marvian--Rouze,
arXiv:2302.02341.  The present Hilbert-valued theorem is the exact isometric special case, with the
adjoint as recovery map.
-/

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

open GaloisForLFunctions

/-- Isometric postprocessing preserves the complete finite reported-jet Gram matrix. -/
theorem finiteDerivativeReporterGram_postcomp_linearIsometry
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    finiteDerivativeReporterGram N f (decode.toLinearMap.comp report) =
      finiteDerivativeReporterGram N f report := by
  ext i j
  simp [finiteDerivativeReporterGram, Matrix.gram_apply,
    LinearIsometry.inner_map_map]

/-- Hence every finite D-optimal determinant is exactly preserved. -/
theorem det_finiteDerivativeReporterGram_postcomp_linearIsometry
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    (finiteDerivativeReporterGram N f
        (decode.toLinearMap.comp report)).det =
      (finiteDerivativeReporterGram N f report).det := by
  rw [finiteDerivativeReporterGram_postcomp_linearIsometry]

/-- **Adjoint recovery.**  The Hilbert adjoint of an isometric postprocessor is an exact left
inverse on every reported observable. -/
theorem finiteDerivativeReporter_isometricAdjointRecovery
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    decode.toContinuousLinearMap.adjoint.toLinearMap.comp
        (decode.toLinearMap.comp report) = report := by
  ext g
  have h := congrArg
    (fun T : Y →L[ℂ] Y => T (report g)) decode.adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometry.coe_toContinuousLinearMap] using h

/-- Coefficient packets are recovered exactly after isometric reporter postprocessing. -/
theorem finiteDerivativeReporterMap_isometricAdjointRecovery
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z)
    (c : Fin N → ℂ) :
    decode.toContinuousLinearMap.adjoint
        (finiteDerivativeReporterMap N f (decode.toLinearMap.comp report) c) =
      finiteDerivativeReporterMap N f report c := by
  have hrecover := finiteDerivativeReporter_isometricAdjointRecovery report decode
  have h := congrArg
    (fun reporter : (ℂ → ℂ) →ₗ[ℂ] Y =>
      finiteDerivativeReporterMap N f reporter c) hrecover
  simpa [finiteDerivativeReporterMap_apply] using h

/-- **Exact conditional-information recovery.**  Every sequential innovation value is unchanged
by isometric recoding. -/
theorem finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) =
      finiteDerivativeReporterConditionalInformation N f report := by
  apply le_antisymm
  · exact finiteDerivativeReporterConditionalInformation_postcomp_le_of_norm_le_one
      N f report decode.toContinuousLinearMap decode.norm_toContinuousLinearMap_le
  · have hback := finiteDerivativeReporterConditionalInformation_postcomp_le_of_norm_le_one
      N f (decode.toLinearMap.comp report)
      decode.toContinuousLinearMap.adjoint
      (by simpa using decode.norm_toContinuousLinearMap_le)
    rw [finiteDerivativeReporter_isometricAdjointRecovery report decode] at hback
    exact hback

/-- **Complete isometric finite-reporter profile.**  Isometric recoding simultaneously preserves
the Gram geometry, every sequential innovation value, visible coefficient capacity, and the
entire blind coefficient subspace; its adjoint recovers the original reporter. -/
theorem finiteDerivativeReporter_isometricObservabilityProfile
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    finiteDerivativeReporterGram N f (decode.toLinearMap.comp report) =
        finiteDerivativeReporterGram N f report ∧
      finiteDerivativeReporterConditionalInformation N f
          (decode.toLinearMap.comp report) =
        finiteDerivativeReporterConditionalInformation N f report ∧
      Module.finrank ℂ (LinearMap.range
          (finiteDerivativeReporterMap N f (decode.toLinearMap.comp report))) =
        Module.finrank ℂ
          (LinearMap.range (finiteDerivativeReporterMap N f report)) ∧
      LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.toLinearMap.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report := by
  have hrecover := finiteDerivativeReporter_isometricAdjointRecovery report decode
  have hcapacity := finiteDerivativeReporterMap_postcomp_capacity_eq_of_recovery
    N f report decode.toLinearMap decode.toContinuousLinearMap.adjoint.toLinearMap hrecover
  exact ⟨finiteDerivativeReporterGram_postcomp_linearIsometry N f report decode,
    finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry N f report decode,
    hcapacity.1, hcapacity.2, hrecover⟩

/-- **Perfectly recoverable representation, irrecoverable source direction.**  For an infinite
derivative clock observed through a finite-dimensional reporter, an isometric downstream encoding
has the same collapse witness and is recovered exactly by its adjoint, while that derivative
direction remains independent before reporting. -/
theorem exists_finiteDerivativeReporter_isometricRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      finiteDerivativeReporterConditionalInformation k f report = 0 ∧
      finiteDerivativeReporterConditionalInformation k f
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k f) ∈
        finiteDerivativeReporterPreviousSpace k f report ∧
      decode (report (iteratedDeriv k f)) ∈
        finiteDerivativeReporterPreviousSpace k f (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  obtain ⟨k, hk, hzero, hpostzero, hreported, hpostreported, hsource⟩ :=
    exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
      hf report decode.toLinearMap
  exact ⟨k, hk, hzero, hpostzero, hreported, hpostreported,
    finiteDerivativeReporter_isometricAdjointRecovery report decode, hsource⟩

/-- **Exact isometric collapse packet and capacity law.**  At one bounded collapse order, a
normalized nonzero source packet is already blind before recoding and remains the same blind
packet afterward.  Isometric recoding preserves the complete coefficient kernel and visible rank
at that resolution, so it introduces no additional algebraic blindness. -/
theorem exists_finiteDerivativeReporter_isometricRecovery_exactBlindPacket_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ (k : ℕ) (c : Fin (k + 1) → ℂ),
      k ≤ Module.finrank ℂ Y ∧
      finiteDerivativeReporterConditionalInformation k f report = 0 ∧
      finiteDerivativeReporterConditionalInformation k f
          (decode.toLinearMap.comp report) = 0 ∧
      c (Fin.last k) = -1 ∧
      c ∈ LinearMap.ker (finiteDerivativeReporterMap (k + 1) f report) ∧
      c ∈ LinearMap.ker (finiteDerivativeReporterMap (k + 1) f
        (decode.toLinearMap.comp report)) ∧
      LinearMap.ker (finiteDerivativeReporterMap (k + 1) f
          (decode.toLinearMap.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap (k + 1) f report) ∧
      Module.finrank ℂ (LinearMap.range (finiteDerivativeReporterMap (k + 1) f
          (decode.toLinearMap.comp report))) =
        Module.finrank ℂ
          (LinearMap.range (finiteDerivativeReporterMap (k + 1) f report)) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) = 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  obtain ⟨k, c, hk, hzero, hclast, hc, hpacket, hreport, hsource⟩ :=
    exists_finiteDerivativeReporterConditionalInformation_normalizedBlindPacket_collapse
      hf report
  have hpostzero :
      finiteDerivativeReporterConditionalInformation k f
          (decode.toLinearMap.comp report) = 0 := by
    rw [finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry]
    exact hzero
  have hprofile := finiteDerivativeReporter_isometricObservabilityProfile
    (k + 1) f report decode
  have hcpost :
      c ∈ LinearMap.ker (finiteDerivativeReporterMap (k + 1) f
        (decode.toLinearMap.comp report)) := by
    rw [hprofile.2.2.2.1]
    exact hc
  have hdecode : decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
    rw [hreport, map_zero]
  exact ⟨k, c, hk, hzero, hpostzero, hclast, hc, hcpost,
    hprofile.2.2.2.1, hprofile.2.2.1, hpacket, hreport, hdecode,
    hprofile.2.2.2.2, hsource⟩

/-- **Perfect recovery preserves singular information.**  Every finite-dimensional reporter of
a genuine infinite derivative clock has a bounded resolution whose Gram information is singular
both before and after isometric recoding.  The two Gram matrices agree, the adjoint recovers the
reporter exactly, and the collapsed derivative remains genuinely new at the source. -/
theorem exists_finiteDerivativeReporter_isometricRecovery_singularGram_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      (finiteDerivativeReporterGram (k + 1) f report).det = 0 ∧
      (finiteDerivativeReporterGram (k + 1) f
        (decode.toLinearMap.comp report)).det = 0 ∧
      finiteDerivativeReporterGram (k + 1) f
          (decode.toLinearMap.comp report) =
        finiteDerivativeReporterGram (k + 1) f report ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  obtain ⟨k, c, hk, _hzero, _hpostzero, _hclast, _hc, _hcpost,
      _hker, _hrank, hpacket, hreport, _hdecode, hrecover, hsource⟩ :=
    exists_finiteDerivativeReporter_isometricRecovery_exactBlindPacket_collapse
      hf report decode
  have hdet : (finiteDerivativeReporterGram (k + 1) f report).det = 0 :=
    (finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket hf report).2
      ⟨c, hreport, hpacket⟩
  have hgram := finiteDerivativeReporterGram_postcomp_linearIsometry
    (k + 1) f report decode
  exact ⟨k, hk, hdet, by rw [hgram]; exact hdet, hgram, hrecover, hsource⟩

end

end HTGeometry
