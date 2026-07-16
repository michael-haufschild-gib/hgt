import GaloisForLFunctions.HTGeometry.FiniteReporterGramFisher
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
    (zeroIndex N : ℕ)
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    (HTGeometry.finiteDerivativeReporterGram N (logDeriv xi) report).det = 0 ↔
      ∃ c : Fin N → ℂ,
        report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0 ∧
          HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_det_eq_zero_iff_exists_blindPacket
  exact HTGeometry.constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
    (meromorphicAt_logDeriv_xi (xiZeroPoint zeroIndex))
    (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero zeroIndex))

/-- The exact singular-information/blind-packet alternative survives every finite Gibbs spectral
dressing of the Xi logarithmic derivative. -/
theorem xiLogDeriv_add_finiteGibbs_reporterGram_det_eq_zero_iff_exists_blindPacket
    (zeroIndex N : ℕ) {A Y : Type*} [Fintype A]
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
    zeroIndex energy

end

end RHTower
