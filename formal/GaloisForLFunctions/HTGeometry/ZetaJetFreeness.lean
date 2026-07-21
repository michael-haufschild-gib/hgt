import GaloisForLFunctions.HTGeometry.HypertranscendentalFunctionJetFreeness
import GaloisForLFunctions.HTGeometry.FiniteSpectralDressingStability
import GaloisForLFunctions.HTGeometry.JacobiThetaDefectMeromorphicOrder
import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
import GaloisForLFunctions.HTGeometry.FiniteReporterNetworkFusion
import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.RHTower.ZetaHypertranscendental
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The Riemann zeta derivative jets are algebraically independent

This leaf instantiates the generic free-jet consequence of function hypertranscendence with the
repository's unconditional theorem for the Riemann zeta function. It is the exact formal bridge
from the analytic zeta theorem to free-jet HT geometry. No horizon fixed-field claim is added.
-/

namespace GaloisForLFunctions

/-- Every finite initial family of Riemann-zeta derivative functions is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_riemannZeta_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) riemannZeta) :=
  hypertranscendental_riemannZeta.algebraicIndependent_initialJets n

/-- **Riemann-zeta free jets.** All derivative functions of `ζ` are algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_riemannZeta_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j riemannZeta) :=
  hypertranscendental_riemannZeta.algebraicIndependent_iteratedDeriv

/-- **Exact Riemann-zeta finite-dictionary jet capacity.**  A finite-dimensional function space
can contain at most its dimension many distinct derivative observables of `ζ`. -/
theorem riemannZeta_iteratedDeriv_mem_finset_card_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n riemannZeta ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  HTGeometry.iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      hypertranscendental_riemannZeta) s hmem

/-- Some Riemann-zeta derivative of order at most `finrank V` escapes every fixed
finite-dimensional observable dictionary `V`. -/
theorem exists_riemannZeta_iteratedDeriv_not_mem_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n riemannZeta ∉ V :=
  HTGeometry.exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      hypertranscendental_riemannZeta)

/-- **Unconditional finite-network zeta Gram alternative.**  Fused reporter information is
singular exactly when every member of the finite network erases one common genuinely nonzero
Riemann-zeta derivative packet. -/
theorem riemannZeta_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N riemannZeta
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a
          (HTGeometry.finiteDerivativeReporterPacket c riemannZeta) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c riemannZeta ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    hypertranscendental_riemannZeta

/-- **Riemann-zeta data-processing no-recovery law.**  Some derivative order no larger than the
reporter dimension is genuinely new at the zeta source but redundant both before and after every
downstream linear decoder. -/
theorem exists_riemannZeta_finiteReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k riemannZeta report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k riemannZeta
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k riemannZeta) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k riemannZeta report ∧
      decode (report (iteratedDeriv k riemannZeta)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k riemannZeta
          (decode.comp report) ∧
      iteratedDeriv k riemannZeta ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) riemannZeta) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    hypertranscendental_riemannZeta

/-- **Perfectly recoverable zeta reporter, irrecoverable source direction.**  An isometric
downstream encoding is exactly recovered by its adjoint but cannot restore the bounded-order zeta
derivative direction erased by the original finite reporter. -/
theorem exists_riemannZeta_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k riemannZeta report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k riemannZeta
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k riemannZeta) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k riemannZeta report ∧
      decode (report (iteratedDeriv k riemannZeta)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k riemannZeta
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k riemannZeta ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) riemannZeta) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    hypertranscendental_riemannZeta

/-- Every zeta coefficient direction newly erased by a decoder is a genuine nonzero derivative
packet which was visible before decoding. -/
theorem riemannZeta_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N riemannZeta (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N riemannZeta report)) :
    HTGeometry.finiteDerivativeReporterPacket c riemannZeta ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c riemannZeta) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c riemannZeta)) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      hypertranscendental_riemannZeta)
    report decode hcpost hcpre

/-! ## Finite Gibbs spectral dressing -/

/-- The Riemann zeta function is meromorphic at its pole `s = 1`.  This packages the existing
analytic residue unit as the local factorization `ζ(s) = (s - 1)⁻¹ G(s)`. -/
theorem meromorphicAt_riemannZeta_one :
    MeromorphicAt riemannZeta 1 := by
  have hsub : MeromorphicAt (fun z : ℂ => z - 1) 1 := by fun_prop
  have hmodel : MeromorphicAt
      (fun z : ℂ => (z - 1)⁻¹ * RHTower.zetaResidueUnit z) 1 :=
    hsub.inv.mul RHTower.zetaResidueUnit_analyticAt.meromorphicAt
  apply hmodel.congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : z ≠ 1 := by simpa using hz
  rw [RHTower.zetaResidueUnit, Function.update_of_ne hz1]
  field_simp [sub_ne_zero.mpr hz1]

/-- The pole of Riemann zeta at `s = 1` has exact meromorphic order `-1`. -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = ((-1 : ℤ) : WithTop ℤ) := by
  exact meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub
    meromorphicAt_riemannZeta_one (by norm_num) riemannZeta_residue_one

/-- Riemann zeta retains infinite constant-coefficient spectral complexity after addition of any
finite Gibbs partition response. -/
theorem riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) :=
  HTGeometry.constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
    meromorphicAt_riemannZeta_one meromorphicOrderAt_riemannZeta_one energy

/-- Fused reporter information for finite-Gibbs dressed Riemann zeta is singular exactly when all
reporters erase one common genuinely nonzero dressed-zeta derivative packet. -/
theorem riemannZeta_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact
    riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy

/-- Finite-Gibbs dressing preserves the Riemann-zeta same-witness data-processing collapse. -/
theorem exists_riemannZeta_add_finiteGibbs_finiteReporterConditionalInformation_dataProcessing_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) = 0 ∧
      report (iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) ∧
      iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact
    riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy

/-- An isometrically encoded finite-Gibbs dressed-zeta reporter is exactly recovered, while the
same bounded-order source direction erased before encoding remains genuinely new. -/
theorem exists_riemannZeta_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact
    riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy

/-- Every coefficient direction newly erased by a decoder for finite-Gibbs dressed zeta
synthesizes a genuine nonzero packet visible before decoding. -/
theorem riemannZeta_add_finiteGibbs_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (riemannZeta + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      energy)
    report decode hcpost hcpre

end GaloisForLFunctions
