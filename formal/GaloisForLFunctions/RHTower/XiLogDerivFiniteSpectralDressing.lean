import GaloisForLFunctions.HTGeometry.FiniteSpectralDressingStability
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

/-!
# Finite spectral dressing cannot erase the Xi log-derivative clock

The completed-zeta logarithmic derivative has an actual simple pole at every chosen Xi divisor
point.  The general finite-spectral dressing theorem therefore applies without an RH premise:
adding any finite Gibbs/finite-clock partition response preserves infinite constant-coefficient
spectral complexity and cannot yield another finite Gibbs response.

This is a direct RHTower consumer of the general HTGeometry closure law.  It is a static statement
about the complete derivative-observation family, not a Hamiltonian time evolution.
-/

namespace RHTower

noncomputable section

/-- The Xi logarithmic derivative retains infinite constant-coefficient spectral complexity after
adding any finite-level Gibbs response. -/
theorem xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    (n : ℕ) {α : Type*} [Fintype α] (energy : α → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (logDeriv xi + HTGeometry.finiteComplexGibbsPartition energy) :=
  HTGeometry.constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
    (meromorphicAt_logDeriv_xi (xiZeroPoint n))
    (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero n)) energy

/-- No finite Gibbs dressing of the Xi logarithmic derivative can equal a finite Gibbs partition
function, for arbitrary finite dressing and target spectra. -/
theorem xiLogDeriv_add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition
    (n : ℕ) {α β : Type*} [Fintype α] [Fintype β]
    (dressing : α → ℝ) (target : β → ℝ) :
    logDeriv xi + HTGeometry.finiteComplexGibbsPartition dressing ≠
      HTGeometry.finiteComplexGibbsPartition target :=
  HTGeometry.add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition_of_simplePole
    (meromorphicAt_logDeriv_xi (xiZeroPoint n))
    (meromorphicOrderAt_logDeriv_xi_eq_neg_one (xiZeroPoint_eq_zero n)) dressing target

end

end RHTower
