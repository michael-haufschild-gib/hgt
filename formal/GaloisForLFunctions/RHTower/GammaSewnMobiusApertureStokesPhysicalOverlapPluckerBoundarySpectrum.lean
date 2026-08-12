import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerFaithfulness
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

/-!
# Boundary spectrum of the faithful physical-overlap Pluecker operator

P-G95 removes every normalizable zero mode, but compactness on the infinite physical lattice forces
zero to remain in continuous boundary spectrum.  The physical operator has normalized approximate
unit gauges, dense nonclosed proper range, and zero in its spectrum, while injectivity excludes zero
as an eigenvalue.

Thus local Stokes gauge was not destroyed: it moved from Hilbert kernel to spectral boundary.  Any
Gamma/polar resolvent identification must reproduce this singular boundary behavior and cannot use
a bounded inverse at zero.
-/

namespace RHTower.HedenmalmThetaSource
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

theorem gammaSewnCriticalPhysicalPluckerHilbert_not_finiteDimensional :
    ¬ FiniteDimensional ℂ GammaSewnCriticalPhysicalPluckerHilbert := by
  intro hfinite
  letI : FiniteDimensional ℂ GammaSewnCriticalPhysicalPluckerHilbert := hfinite
  have hon : Orthonormal ℂ
      (fun n : ℕ => gammaSewnCriticalPhysicalPluckerBasis (n, 0)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_gammaSewnCriticalPhysicalPluckerBasis]
    simp
  have hli := hon.linearIndependent
  have hcard := hli.lt_aleph0_of_finiteDimensional
  have hnot : ¬ (Cardinal.mk ℕ < Cardinal.aleph0) := by simp
  exact hnot hcard

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_hasApproximateUnitKernel :
    HasApproximateUnitKernel
      gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  exact compact_injective_hasApproximateUnitKernel
    gammaSewnCriticalPhysicalPluckerSpectralOperator
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isCompact
    gammaSewnCriticalPhysicalPluckerSpectralOperator_injective
    gammaSewnCriticalPhysicalPluckerHilbert_not_finiteDimensional

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_not_isClosed_range :
    ¬ IsClosed (Set.range gammaSewnCriticalPhysicalPluckerSpectralOperator) :=
  (hasApproximateUnitKernel_iff_not_isClosed_range
    gammaSewnCriticalPhysicalPluckerSpectralOperator
    gammaSewnCriticalPhysicalPluckerSpectralOperator_injective).1
      gammaSewnCriticalPhysicalPluckerSpectralOperator_hasApproximateUnitKernel

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_denseRange :
    DenseRange gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  exact denseRange_of_isSelfAdjoint_of_injective
    gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
    gammaSewnCriticalPhysicalPluckerSpectralOperator_injective

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_not_surjective :
    ¬ Function.Surjective gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  intro hsurj
  apply gammaSewnCriticalPhysicalPluckerSpectralOperator_not_isClosed_range
  rw [hsurj.range_eq]
  exact isClosed_univ

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_zero_mem_spectrum :
    (0 : ℂ) ∈ spectrum ℂ gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  rw [spectrum.zero_mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
  exact fun hbij =>
    gammaSewnCriticalPhysicalPluckerSpectralOperator_not_surjective hbij.2

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_zero_not_eigenvalue :
    ¬ ∃ x : GammaSewnCriticalPhysicalPluckerHilbert,
      x ≠ 0 ∧ gammaSewnCriticalPhysicalPluckerSpectralOperator x = 0 := by
  rintro ⟨x, hx, hzero⟩
  exact hx ((gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff x).1 hzero)

end RHTower.HedenmalmThetaSource
