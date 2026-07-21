import GaloisForLFunctions.HTGeometry.FiniteReporterNetworkFusion
import GaloisForLFunctions.RHTower.XiLogDerivReporterRankNullity

/-!
# Xi logarithmic-derivative reporter Gram/Fisher alternative

The finite reporter information matrix for the Xi logarithmic-derivative clock is singular exactly
when the reporter erases a genuinely nonzero finite derivative packet.  This is unconditional:
an actual Xi zero makes the logarithmic derivative constant-coefficient differentially
transcendental.  Finite Gibbs or finite-clock dressing preserves the same alternative.

The result is not an RH criterion.  It gives a positive finite-resolution design rule: a proposed
physics, genomic, or learned reporter is faithful on a chosen Xi jet truncation precisely when its
explicit Gram matrix is nonsingular.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- **Unconditional Xi Gram alternative.**  Singular finite reporter information is equivalent to
the existence of a genuinely nonzero erased Xi logarithmic-derivative packet. -/
theorem xiLogDeriv_reporterGram_det_eq_zero_iff_exists_blindPacket
    (N : ℕ)
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (HTGeometry.finiteDerivativeReporterGram N (logDeriv xi) report).det = 0 ↔
      ∃ c : Fin N → ℂ,
        report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
          HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket
  exact xiLogDeriv_constantCoefficientDifferentiallyTranscendental

/-- The exact singular-information/blind-packet alternative survives every finite Gibbs spectral
dressing of the Xi logarithmic derivative. -/
theorem xiLogDeriv_add_finiteGibbs_reporterGram_det_eq_zero_iff_exists_blindPacket
    (N : ℕ) {A Y : Type*} [Fintype A]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (energy : A → ℝ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (HTGeometry.finiteDerivativeReporterGram N
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report).det = 0 ↔
      ∃ c : Fin N → ℂ,
        report (HTGeometry.finiteDerivativeReporterPacket c
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) = 0 ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket
  exact xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

/-- **Unconditional finite-network Xi Gram alternative.**  A finite family of reporters has
singular fused information exactly when every member erases the same genuinely nonzero Xi
logarithmic-derivative packet. -/
theorem xiLogDeriv_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ)
    {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N (logDeriv xi)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a
          (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact xiLogDeriv_constantCoefficientDifferentiallyTranscendental

/-- Finite-network singularity for the Xi logarithmic derivative remains the exact existence of a
common nonzero blind packet after any finite Gibbs spectral dressing. -/
theorem xiLogDeriv_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

end

end RHTower
