import GaloisForLFunctions.HTGeometry.FiniteReporterBlindness
import GaloisForLFunctions.RHTower.XiLogDerivFiniteSpectralDressing

/-!
# Finite reporters cannot resolve the Xi logarithmic-derivative clock

The completed-zeta logarithmic derivative has infinite constant-coefficient differential
complexity because it has an actual simple pole.  The general finite-reporter theorem therefore
produces, for every finite-dimensional linear readout, a nonzero finite derivative packet that the
readout sends to zero.  This is unconditional and survives addition of any finite Gibbs/finite
spectral clock response.

The conclusion is an observability boundary, not an RH criterion: the hidden packet exists because
the derivative clock is infinite-rank, while its coefficients may depend on the chosen reporter.
It nonetheless rules out any proof architecture that expects one fixed finite reporter panel to
faithfully resolve the complete Xi logarithmic-derivative jet tower.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- Every finite-dimensional readout of the Xi logarithmic-derivative clock misses a nonzero finite
derivative packet.  No RH hypothesis is used. -/
theorem exists_xiLogDeriv_nonzero_finiteDerivativeReporterPacket_ker
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin (finrank ℂ Y + 1) → ℂ,
      (∃ i, c i ≠ 0) ∧
      HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c (logDeriv xi)) = 0 := by
  apply HTGeometry.exists_nonzero_finiteDerivativeReporterPacket_ker
  exact xiLogDeriv_constantCoefficientDifferentiallyTranscendental

/-- Finite Gibbs/finite-clock dressing does not repair finite-reporter blindness of the Xi
logarithmic derivative. -/
theorem exists_xiLogDeriv_add_finiteGibbs_nonzero_finiteDerivativeReporterPacket_ker
    {A Y : Type*} [Fintype A]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (energy : A → ℝ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin (finrank ℂ Y + 1) → ℂ,
      (∃ i, c i ≠ 0) ∧
      HTGeometry.finiteDerivativeReporterPacket c
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) = 0 := by
  apply HTGeometry.exists_nonzero_finiteDerivativeReporterPacket_ker
  exact xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    energy

end

end RHTower
