import GaloisForLFunctions.HTGeometry.HypertranscendentalReporterFreeness
import GaloisForLFunctions.HTGeometry.JacobiThetaDefectMeromorphicOrder
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# Gamma and digamma derivative-jet freeness

Hölder's unconditional Gamma hypertranscendence theorem and the corresponding digamma theorem
discharge every premise of the generic free-jet and finite-reporter interfaces.  This module
publishes the resulting source-level capacity, network-singularity, data-processing, isometric
recovery, and newly-blind-packet capstones.
-/

namespace GaloisForLFunctions

/-- Every finite initial family of Gamma derivatives is algebraically independent over `ℂ`. -/
theorem algebraicIndependent_gamma_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.Gamma) :=
  hypertranscendental_gamma.algebraicIndependent_initialJets n

/-- All Gamma derivative functions are algebraically independent over `ℂ`. -/
theorem algebraicIndependent_gamma_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j Complex.Gamma) :=
  hypertranscendental_gamma.algebraicIndependent_iteratedDeriv

/-- A finite-dimensional function dictionary contains at most its dimension many Gamma derivative
functions. -/
theorem gamma_iteratedDeriv_mem_finset_card_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n Complex.Gamma ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  hypertranscendental_gamma.iteratedDeriv_mem_finset_card_le_finrank V s hmem

/-- Some Gamma derivative of order at most the dictionary dimension escapes every finite function
dictionary. -/
theorem exists_gamma_iteratedDeriv_not_mem_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n Complex.Gamma ∉ V :=
  hypertranscendental_gamma.exists_iteratedDeriv_not_mem_le_finrank V

/-- Fused Gamma reporter information is singular exactly when all reporters erase one common
nonzero Gamma derivative packet. -/
theorem gamma_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N Complex.Gamma
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a
          (HTGeometry.finiteDerivativeReporterPacket c Complex.Gamma) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c Complex.Gamma ≠ 0 :=
  hypertranscendental_gamma.reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    N report

/-- Some bounded-order Gamma direction is new at the source but redundant before and after every
downstream decoder. -/
theorem exists_gamma_finiteReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.Gamma report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.Gamma
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k Complex.Gamma) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.Gamma report ∧
      decode (report (iteratedDeriv k Complex.Gamma)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.Gamma
          (decode.comp report) ∧
      iteratedDeriv k Complex.Gamma ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) Complex.Gamma) :=
  hypertranscendental_gamma.exists_finiteReporterConditionalInformation_dataProcessing_collapse
    report decode

/-- Isometric encoding perfectly recovers a Gamma reporter representation but not the same erased
bounded-order source direction. -/
theorem exists_gamma_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.Gamma report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.Gamma
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k Complex.Gamma) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.Gamma report ∧
      decode (report (iteratedDeriv k Complex.Gamma)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.Gamma
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k Complex.Gamma ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) Complex.Gamma) :=
  hypertranscendental_gamma.exists_isometricReporterRecovery_collapse report decode

/-- Every Gamma coefficient direction newly erased by a decoder is a genuine nonzero packet which
was visible before decoding. -/
theorem gamma_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N Complex.Gamma (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N Complex.Gamma report)) :
    HTGeometry.finiteDerivativeReporterPacket c Complex.Gamma ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c Complex.Gamma) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c Complex.Gamma)) = 0 :=
  HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

/-! ## Digamma source -/

/-- Every finite initial family of digamma derivatives is algebraically independent over `ℂ`. -/
theorem algebraicIndependent_digamma_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma) :=
  hypertranscendental_digamma.algebraicIndependent_initialJets n

/-- All digamma derivative functions are algebraically independent over `ℂ`. -/
theorem algebraicIndependent_digamma_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j Complex.digamma) :=
  hypertranscendental_digamma.algebraicIndependent_iteratedDeriv

/-- A finite-dimensional function dictionary contains at most its dimension many digamma
derivative functions. -/
theorem digamma_iteratedDeriv_mem_finset_card_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n Complex.digamma ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  hypertranscendental_digamma.iteratedDeriv_mem_finset_card_le_finrank V s hmem

/-- Some digamma derivative of order at most the dictionary dimension escapes every finite
function dictionary. -/
theorem exists_digamma_iteratedDeriv_not_mem_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n Complex.digamma ∉ V :=
  hypertranscendental_digamma.exists_iteratedDeriv_not_mem_le_finrank V

/-- Fused digamma reporter information is singular exactly when all reporters erase one common
nonzero digamma derivative packet. -/
theorem digamma_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N Complex.digamma
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a
          (HTGeometry.finiteDerivativeReporterPacket c Complex.digamma) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c Complex.digamma ≠ 0 :=
  hypertranscendental_digamma.reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    N report

/-- Some bounded-order digamma direction is new at the source but redundant before and after every
downstream decoder. -/
theorem exists_digamma_finiteReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.digamma report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.digamma
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k Complex.digamma) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.digamma report ∧
      decode (report (iteratedDeriv k Complex.digamma)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.digamma
          (decode.comp report) ∧
      iteratedDeriv k Complex.digamma ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) Complex.digamma) :=
  hypertranscendental_digamma.exists_finiteReporterConditionalInformation_dataProcessing_collapse
    report decode

/-- Isometric encoding perfectly recovers a digamma reporter representation but not the same
erased bounded-order source direction. -/
theorem exists_digamma_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.digamma report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k Complex.digamma
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k Complex.digamma) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.digamma report ∧
      decode (report (iteratedDeriv k Complex.digamma)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k Complex.digamma
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k Complex.digamma ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) Complex.digamma) :=
  hypertranscendental_digamma.exists_isometricReporterRecovery_collapse report decode

/-- Every digamma coefficient direction newly erased by a decoder is a genuine nonzero packet
which was visible before decoding. -/
theorem digamma_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N Complex.digamma (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N Complex.digamma report)) :
    HTGeometry.finiteDerivativeReporterPacket c Complex.digamma ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c Complex.digamma) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c Complex.digamma)) = 0 :=
  HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

/-! ## Exact pole orders and finite Gibbs spectral dressing -/

/-- Every Gamma pole at a nonpositive integer has exact meromorphic order `-1`. -/
theorem meromorphicOrderAt_gamma_neg_nat (k : ℕ) :
    meromorphicOrderAt Complex.Gamma (-(k : ℂ)) = ((-1 : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub
    (c := (-1 : ℂ) ^ k / (k.factorial : ℂ))
    (Meromorphic.Gamma.meromorphicAt : MeromorphicAt Complex.Gamma (-(k : ℂ)))
    (div_ne_zero (pow_ne_zero k (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero k))
  simpa using gamma_residue k

/-- Every digamma pole at a nonpositive integer has exact meromorphic order `-1`. -/
theorem meromorphicOrderAt_digamma_neg_nat (k : ℕ) :
    meromorphicOrderAt Complex.digamma (-(k : ℂ)) = ((-1 : ℤ) : WithTop ℤ) := by
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (c := (-1 : ℂ))
    (Complex.meromorphic_digamma.meromorphicAt :
      MeromorphicAt Complex.digamma (-(k : ℂ))) (by norm_num)
  simpa using digamma_residue k

/-- Gamma retains infinite constant-coefficient spectral complexity after addition of any finite
Gibbs partition response. -/
theorem gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) :=
  HTGeometry.constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
    (Meromorphic.Gamma.meromorphicAt : MeromorphicAt Complex.Gamma 0)
    (by simpa using meromorphicOrderAt_gamma_neg_nat 0) energy

/-- Fused reporter information for finite-Gibbs dressed Gamma is singular exactly when all
reporters erase one common genuinely nonzero dressed-Gamma derivative packet. -/
theorem gamma_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Finite-Gibbs dressing preserves the Gamma same-witness data-processing collapse. -/
theorem exists_gamma_add_finiteGibbs_finiteReporterConditionalInformation_dataProcessing_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) = 0 ∧
      report (iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) ∧
      iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Isometric encoding exactly recovers a finite-Gibbs dressed-Gamma reporter but not the same
bounded-order source direction erased before encoding. -/
theorem exists_gamma_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Every coefficient direction newly erased by a decoder for finite-Gibbs dressed Gamma
synthesizes a genuine nonzero packet visible before decoding. -/
theorem gamma_add_finiteGibbs_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)
        (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (Complex.Gamma + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

/-- Digamma retains infinite constant-coefficient spectral complexity after addition of any finite
Gibbs partition response. -/
theorem digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) :=
  HTGeometry.constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
    (Complex.meromorphic_digamma.meromorphicAt : MeromorphicAt Complex.digamma 0)
    (by simpa using meromorphicOrderAt_digamma_neg_nat 0) energy

/-- Fused reporter information for finite-Gibbs dressed digamma is singular exactly when all
reporters erase one common genuinely nonzero dressed-digamma derivative packet. -/
theorem digamma_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Finite-Gibbs dressing preserves the digamma same-witness data-processing collapse. -/
theorem exists_digamma_add_finiteGibbs_finiteReporterConditionalInformation_dataProcessing_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) = 0 ∧
      report (iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) ∧
      iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Isometric encoding exactly recovers a finite-Gibbs dressed-digamma reporter but not the same
bounded-order source direction erased before encoding. -/
theorem exists_digamma_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k
          (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- Every coefficient direction newly erased by a decoder for finite-Gibbs dressed digamma
synthesizes a genuine nonzero packet visible before decoding. -/
theorem digamma_add_finiteGibbs_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)
        (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (Complex.digamma + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

end GaloisForLFunctions
