import GaloisForLFunctions.HTGeometry.DifferentialOrder
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.HTGeometry.FiniteReporterNetworkFusion
import GaloisForLFunctions.HTGeometry.HypertranscendentalPointJetFreeness
import GaloisForLFunctions.HTGeometry.HypertranscendentalReporterFreeness
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional

/-!
# Free derivative jets of the completed xi function

This leaf instantiates the generic jet consequences of function hypertranscendence with the
unconditional theorem for the completed Riemann xi function.  It records algebraic independence of
the derivative functions, algebraic independence after adjoining the point coordinate, isolation of
every nonzero differential-polynomial relation locus, and failure of differential algebraicity at
each finite order.

These are global function-theoretic consequences of xi hypertranscendence.  They contain no
zero-location or Riemann-hypothesis conclusion.
-/

namespace RHTower

open GaloisForLFunctions

/-- Every finite initial family of completed-xi derivative functions is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_xi_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi) :=
  xi_hypertranscendental.algebraicIndependent_initialJets n

/-- **Completed-xi free jets.** All derivative functions of xi are algebraically independent over
`ℂ`. -/
theorem algebraicIndependent_xi_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j xi) :=
  xi_hypertranscendental.algebraicIndependent_iteratedDeriv

/-- The point coordinate together with every finite initial completed-xi derivative jet is
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_xi_pointInitialJets (n : ℕ) :
    AlgebraicIndependent ℂ (pointJetFunctionTuple xi n) :=
  xi_hypertranscendental.algebraicIndependent_pointInitialJets n

/-- Every nonzero differential polynomial has an isolated vanishing locus on the completed-xi
jets. -/
theorem xi_jetEval_isolated {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    ∀ z₀, ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi z) P = 0) :=
  xi_hypertranscendental.jetEval_isolated xi_differentiable hP

/-- The completed xi function satisfies no algebraic differential equation of any prescribed
finite order. -/
theorem xi_not_differentiallyAlgebraicOfOrder (n : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder xi n :=
  xi_hypertranscendental.not_differentiallyAlgebraicOfOrder n

/-- **Exact Xi finite-dictionary jet capacity.**  Every finite set of completed-Xi derivative
observables captured by a finite-dimensional function space has cardinality at most that space's
dimension. -/
theorem xi_iteratedDeriv_mem_finset_card_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n xi ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  HTGeometry.iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      xi_hypertranscendental) s hmem

/-- Some completed-Xi derivative among orders at most `finrank V` escapes every fixed
finite-dimensional observable dictionary `V`. -/
theorem exists_xi_iteratedDeriv_not_mem_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n xi ∉ V :=
  HTGeometry.exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      xi_hypertranscendental)

/-- **Unconditional finite-network completed-Xi Gram alternative.**  Fused reporter information
is singular exactly when every reporter erases one common genuinely nonzero Xi derivative
packet. -/
theorem xi_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N xi
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c xi) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c xi ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- **Completed-Xi data-processing no-recovery law.**  Some derivative order no larger than the
reporter dimension is new at the Xi source but redundant both before and after every downstream
linear decoder. -/
theorem exists_xi_finiteReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k xi) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi report ∧
      decode (report (iteratedDeriv k xi)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi (decode.comp report) ∧
      iteratedDeriv k xi ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) xi) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- **Perfectly recoverable completed-Xi reporter, irrecoverable source direction.**  At one
bounded-order Xi collapse witness, an isometric encoding preserves zero information and its
adjoint recovers the reporter exactly, while the source derivative remains new. -/
theorem exists_xi_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k xi) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi report ∧
      decode (report (iteratedDeriv k xi)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k xi ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) xi) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- Every completed-Xi coefficient direction newly erased by a decoder is a genuine nonzero Xi
derivative packet which was visible before decoding. -/
theorem xi_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N xi (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N xi report)) :
    HTGeometry.finiteDerivativeReporterPacket c xi ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c xi) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c xi)) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      xi_hypertranscendental)
    report decode hcpost hcpre

/-! ## Finite Gibbs spectral dressing -/

/-- Completed Xi retains infinite constant-coefficient spectral complexity after addition of any
finite Gibbs partition response. -/
theorem xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (xi + HTGeometry.finiteComplexGibbsPartition energy) :=
  GaloisForLFunctions.Hypertranscendental.add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental xi_differentiable.contDiff energy

/-- Fused reporter information for finite-Gibbs dressed completed Xi is singular exactly when all
reporters erase one common genuinely nonzero dressed-Xi derivative packet. -/
theorem xi_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (xi + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- Finite-Gibbs dressing preserves the completed-Xi same-witness data-processing collapse. -/
theorem exists_xi_add_finiteGibbs_finiteReporterConditionalInformation_dataProcessing_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) = 0 ∧
      report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) ∧
      iteratedDeriv k (xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- An isometrically encoded finite-Gibbs dressed-Xi reporter is exactly recovered, while the same
bounded-order source direction erased before encoding remains genuinely new. -/
theorem exists_xi_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- Every coefficient direction newly erased by a decoder for finite-Gibbs dressed completed Xi
synthesizes a genuine nonzero packet visible before decoding. -/
theorem xi_add_finiteGibbs_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (xi + HTGeometry.finiteComplexGibbsPartition energy) (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (xi + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy)
    report decode hcpost hcpre

end RHTower
