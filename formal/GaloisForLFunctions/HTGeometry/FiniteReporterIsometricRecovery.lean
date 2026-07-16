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
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
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

end

end HTGeometry
