import GaloisForLFunctions.HTGeometry.FiniteReporterDataProcessing
import GaloisForLFunctions.RHTower.XiLogDerivReporterConditionalInformation

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
  obtain ⟨k, hk, hzero, hreported, hsource⟩ :=
    exists_xiLogDeriv_finiteReporterConditionalInformation_collapse zeroIndex report
  have hpostzero :=
    HTGeometry.finiteDerivativeReporterConditionalInformation_eq_zero_postcomp decode hzero
  have hpostreported :=
    (HTGeometry.finiteDerivativeReporterConditionalInformation_eq_zero_iff
      k (logDeriv xi) (decode.comp report)).mp hpostzero
  exact ⟨k, hk, hzero, hpostzero, hreported, hpostreported, hsource⟩

end

end RHTower
