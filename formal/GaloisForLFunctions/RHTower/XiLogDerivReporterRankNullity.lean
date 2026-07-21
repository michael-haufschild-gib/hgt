import GaloisForLFunctions.RHTower.XiLogDerivFiniteReporterBlindness

/-!
# Exact visible/blind rank census for Xi logarithmic-derivative reporters

The finite-reporter no-go supplies one hidden derivative packet.  The rank--nullity relation from
finite genetic reporter panels and learned sensor maps is stronger: at every finite jet resolution,
it counts the complete visible and blind coefficient spaces.  For the Xi logarithmic derivative,
every nonzero blind coefficient direction is a genuinely nonzero function because an actual Xi zero
supplies a simple pole and hence infinite constant-coefficient derivative rank.

This is an observability census, not an RH criterion.  Its direct proof-search consequence is that
adding a finite Gibbs or finite-clock dressing cannot reduce the blind dimension except by increasing
the actual reporter rank.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions Module

/-- **Exact Xi reporter capacity law.**  At every finite jet resolution, visible and blind
coefficient directions add to the resolution, and the Xi logarithmic-derivative synthesis itself
has no coefficient aliases.  The latter is unconditional because one actual Xi zero supplies a
simple pole of the logarithmic derivative. -/
theorem xiLogDeriv_finiteDerivativeReporter_rank_nullity
    (N : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    finrank ℂ (LinearMap.range
        (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) +
          finrank ℂ (LinearMap.ker
            (HTGeometry.finiteDerivativeReporterMap N (logDeriv xi) report)) = N ∧
      Function.Injective
        (HTGeometry.finiteDerivativeJetSynthesis N (logDeriv xi)) := by
  constructor
  · exact HTGeometry.finiteDerivativeReporterMap_rank_nullity N (logDeriv xi) report
  · apply HTGeometry.finiteDerivativeJetSynthesis_injective
    exact xiLogDeriv_constantCoefficientDifferentiallyTranscendental

/-- Finite Gibbs/finite-clock dressing preserves the exact reporter capacity law and cannot create
coefficient aliases in any finite derivative packet. -/
theorem xiLogDeriv_add_finiteGibbs_finiteDerivativeReporter_rank_nullity
    (N : ℕ) {A Y : Type*} [Fintype A]
    [AddCommGroup Y] [Module ℂ Y]
    (energy : A → ℝ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    finrank ℂ (LinearMap.range
        (HTGeometry.finiteDerivativeReporterMap N
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report)) +
          finrank ℂ (LinearMap.ker
            (HTGeometry.finiteDerivativeReporterMap N
              (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report)) = N ∧
      Function.Injective
        (HTGeometry.finiteDerivativeJetSynthesis N
          (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  constructor
  · exact HTGeometry.finiteDerivativeReporterMap_rank_nullity N
      (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) report
  · exact HTGeometry.finiteDerivativeJetSynthesis_injective
      (xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
        energy)

end

end RHTower
