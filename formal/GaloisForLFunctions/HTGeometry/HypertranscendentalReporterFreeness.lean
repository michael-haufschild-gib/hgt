import GaloisForLFunctions.HTGeometry.HypertranscendentalFunctionJetFreeness
import GaloisForLFunctions.HTGeometry.FiniteSpectralDressingStability
import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
import GaloisForLFunctions.HTGeometry.FiniteReporterNetworkFusion
import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery

/-!
# Hypertranscendental reporter freeness

Function hypertranscendence already implies constant-coefficient differential transcendence.
This module discharges that intermediate premise once for the strongest finite-dictionary,
reporter-network, data-processing, and isometric-recovery interfaces.  Analytic source modules can
therefore connect an unconditional hypertranscendence theorem directly to these reporter laws.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Adding a finite Gibbs spectrum to a globally smooth hypertranscendental source preserves
constant-coefficient differential transcendence. -/
theorem Hypertranscendental.add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (hfSmooth : ContDiff ℂ (⊤ : ℕ∞) f)
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (f + HTGeometry.finiteComplexGibbsPartition energy) :=
  HTGeometry.constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition
    (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf)
    hfSmooth energy

/-- Every finite-dimensional function dictionary contains at most its dimension many derivative
functions of a hypertranscendental source. -/
theorem Hypertranscendental.iteratedDeriv_mem_finset_card_le_finrank
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n f ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  HTGeometry.iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf)
    s hmem

/-- Some derivative among orders at most the dictionary dimension escapes every finite-dimensional
function dictionary. -/
theorem Hypertranscendental.exists_iteratedDeriv_not_mem_le_finrank
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n f ∉ V :=
  HTGeometry.exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf)

/-- A finite reporter network on a hypertranscendental source is singular exactly when every
reporter erases one common nonzero derivative packet. -/
theorem Hypertranscendental.reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N f
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c f) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c f ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf

/-- Every finite-dimensional reporter of a hypertranscendental source has one bounded-order source
direction which remains genuinely new before reporting and redundant before and after decoding. -/
theorem Hypertranscendental.exists_finiteReporterConditionalInformation_dataProcessing_collapse
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k f report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k f
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k f) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k f report ∧
      decode (report (iteratedDeriv k f)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k f (decode.comp report) ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf

/-- Isometric postprocessing perfectly recovers a finite reporter representation but cannot restore
the same bounded-order source direction erased from a hypertranscendental derivative tower. -/
theorem Hypertranscendental.exists_isometricReporterRecovery_collapse
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k f report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k f
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k f) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k f report ∧
      decode (report (iteratedDeriv k f)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k f
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf

end

end GaloisForLFunctions
