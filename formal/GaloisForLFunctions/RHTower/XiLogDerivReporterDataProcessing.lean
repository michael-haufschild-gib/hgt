import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
import GaloisForLFunctions.RHTower.XiLogDerivFiniteSpectralDressing

/-!
# Data-processing stability of the Xi finite-reporter collapse

The finite-dimensional Xi reporter collapse survives every downstream linear quantum
measurement, coarse graining, or decoder at the same derivative order.  The source derivative is
still independent of its predecessors, while both the original and postprocessed panels assign
it zero conditional information.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- **Xi data-processing no-recovery law.**  A downstream linear operation cannot repair the
specific reporter-induced Xi derivative collapse. -/
theorem exists_xiLogDeriv_finiteReporterConditionalInformation_dataProcessing_collapse
    (zeroIndex : ℕ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k (logDeriv xi)
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k (logDeriv xi)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k (logDeriv xi) report ∧
      decode (report (iteratedDeriv k (logDeriv xi))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k (logDeriv xi)
          (decode.comp report) ∧
      iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) (logDeriv xi)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact HTGeometry.constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
    (meromorphicAt_logDeriv_xi (xiZeroPoint zeroIndex))
    (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero zeroIndex))

/-- A decoder-created blind Xi coefficient direction is a nonzero derivative packet which was
visible before decoding and is erased afterwards. -/
theorem xiLogDeriv_finiteDerivativeReporterMap_postcomp_newBlindPacket
    (zeroIndex : ℕ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) :
    HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (HTGeometry.constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
      (meromorphicAt_logDeriv_xi (xiZeroPoint zeroIndex))
      (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero zeroIndex)))
    report decode hcpost hcpre

/-- Finite Gibbs dressing does not turn a decoder-created blind coefficient direction into a
source relation: the dressed Xi packet is nonzero and visible before decoding. -/
theorem xiLogDeriv_add_finiteGibbs_postcomp_newBlindPacket
    (zeroIndex : ℕ) {α : Type*} [Fintype α] (energy : α → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
        (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    (xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      zeroIndex energy)
    report decode hcpost hcpre

end

end RHTower
