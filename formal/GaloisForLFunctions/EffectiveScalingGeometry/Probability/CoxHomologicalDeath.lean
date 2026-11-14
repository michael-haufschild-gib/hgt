import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHomologyCoordinates

/-!
# Gamma–Cox detection of prime-height homological death

The squared surviving-coordinate energy vanishes precisely on actual boundaries.
The half-height cutoff criterion therefore becomes a consistent binary test of
homological death for any finite family of real cycles.
-/

open Filter Topology Finset
open RHTower
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.EffectiveScalingGeometry
noncomputable section

/-- Squared mass of the prime-face coefficients surviving the current cutoff. -/
def primeCriticalEnergy (k N : ℕ)
    (x : (primeCutoffShortComplex ℝ k N).g.hom.ker) : ℝ :=
  let v := (primeCycleCriticalProjection ℝ k N x).val
  ∑ s ∈ v.support, (v s) ^ 2

/-- Coordinate energy vanishes exactly at the half-height cutoff. -/
theorem primeCriticalEnergy_zero_iff (k N : ℕ)
    (x : (primeCutoffShortComplex ℝ k N).g.hom.ker) :
    primeCriticalEnergy k N x = 0 ↔ x.val.val ∈ primeChainCutoff ℝ (k + 1) (N / 2) := by
  rw [← primeCycleCriticalProjection_eq_zero_iff]
  constructor
  · intro h
    apply Subtype.ext
    apply Finsupp.ext
    intro s
    let v := (primeCycleCriticalProjection ℝ k N x).val
    change v s = 0
    by_cases hs : s ∈ v.support
    · have he := (sum_eq_zero_iff_of_nonneg (fun s _ => sq_nonneg (v s))).mp h s hs
      exact sq_eq_zero_iff.mp he
    · exact Finsupp.notMem_support_iff.mp hs
  · intro h
    simp [primeCriticalEnergy, h]

/-- The same scalar energy detects membership in the actual boundary range. -/
theorem primeCriticalEnergy_zero_iff_boundary (k N : ℕ)
    (x : (primeCutoffShortComplex ℝ k N).g.hom.ker) :
    primeCriticalEnergy k N x = 0 ↔
      x ∈ (primeCutoffShortComplex ℝ k N).moduleCatToCycles.range := by
  rw [primeCriticalEnergy_zero_iff, ← primeCycleCriticalProjection_eq_zero_iff,
    ← LinearMap.mem_ker, primeCycleCriticalProjection_ker]

/-- A single energy detector recognizes exact homological death. -/
theorem cox_homological_death (k N : ℕ)
    (x : (primeCutoffShortComplex ℝ k N).g.hom.ker) :
    Tendsto (fun K => detection K (primeCriticalEnergy k N x)) atTop
      (𝓝 (if x ∈ (primeCutoffShortComplex ℝ k N).moduleCatToCycles.range then 1 else 0)) := by
  simpa only [primeCriticalEnergy_zero_iff_boundary] using
    tendsto_detection (primeCriticalEnergy k N x)

/-- Every cycle in a finite family is classified simultaneously for death at the current height. -/
theorem cox_homological_death_family {ι : Type*} [Fintype ι] (k N : ℕ)
    (x : ι → (primeCutoffShortComplex ℝ k N).g.hom.ker) :
    Tendsto (fun K => (binaryLaw K (fun i => primeCriticalEnergy k N (x i))).real
      {b | b ≠ fun i => decide (x i ∈ (primeCutoffShortComplex ℝ k N).moduleCatToCycles.range)})
      atTop (𝓝 0) := by
  simpa only [zeroPattern, primeCriticalEnergy_zero_iff_boundary] using
    tendsto_binaryLaw_error (fun i => primeCriticalEnergy k N (x i))

end
end GaloisForLFunctions.EffectiveScalingGeometry

#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCriticalEnergy_zero_iff
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCriticalEnergy_zero_iff_boundary
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_homological_death
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_homological_death_family
