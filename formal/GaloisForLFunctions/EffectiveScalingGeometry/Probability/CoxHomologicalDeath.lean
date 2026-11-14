import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeAugmentedHomology

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

/-- Squared coordinate energy detects the zero finitely supported chain. -/
private theorem support_energy_zero_iff {α : Type*} (v : α →₀ ℝ) :
    (∑ s ∈ v.support, (v s) ^ 2) = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro s
    by_cases hs : s ∈ v.support
    · exact sq_eq_zero_iff.mp
        ((sum_eq_zero_iff_of_nonneg (fun s _ => sq_nonneg (v s))).mp h s hs)
    · exact Finsupp.notMem_support_iff.mp hs
  · rintro rfl
    simp

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
  change (∑ s ∈ (primeCycleCriticalProjection ℝ k N x).val.support,
    ((primeCycleCriticalProjection ℝ k N x).val s) ^ 2) = 0 ↔ _
  rw [support_energy_zero_iff]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

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
  exact tendsto_classification_error (fun i => primeCriticalEnergy k N (x i))
    (fun i => x i ∈ (primeCutoffShortComplex ℝ k N).moduleCatToCycles.range) fun i => by
    simp only [primeCriticalEnergy_zero_iff_boundary]

/-- Surviving empty-face energy for the augmented degree. -/
def primeZeroCriticalEnergy (N : ℕ)
    (x : (primeZeroShortComplex ℝ N).g.hom.ker) : ℝ :=
  let v := (primeZeroCriticalProjection ℝ N x).val
  ∑ s ∈ v.support, (v s) ^ 2

/-- The augmented energy vanishes precisely on actual empty-face boundaries. -/
theorem primeZeroCriticalEnergy_zero_iff_boundary (N : ℕ)
    (x : (primeZeroShortComplex ℝ N).g.hom.ker) :
    primeZeroCriticalEnergy N x = 0 ↔
      x ∈ (primeZeroShortComplex ℝ N).moduleCatToCycles.range := by
  rw [← primeZeroCriticalProjection_ker, LinearMap.mem_ker]
  change (∑ s ∈ (primeZeroCriticalProjection ℝ N x).val.support,
    ((primeZeroCriticalProjection ℝ N x).val s) ^ 2) = 0 ↔ _
  rw [support_energy_zero_iff]
  constructor
  · exact fun h => Subtype.ext h
  · exact fun h => congrArg Subtype.val h

/-- The augmented detector includes the exceptional empty-face persistence interval. -/
theorem cox_augmented_homological_death (N : ℕ)
    (x : (primeZeroShortComplex ℝ N).g.hom.ker) :
    Tendsto (fun K => detection K (primeZeroCriticalEnergy N x)) atTop
      (𝓝 (if x ∈ (primeZeroShortComplex ℝ N).moduleCatToCycles.range then 1 else 0)) := by
  simpa only [primeZeroCriticalEnergy_zero_iff_boundary] using
    tendsto_detection (primeZeroCriticalEnergy N x)

/-- Simultaneous boundary detection also holds in the augmented degree. -/
theorem cox_augmented_homological_death_family {ι : Type*} [Fintype ι] (N : ℕ)
    (x : ι → (primeZeroShortComplex ℝ N).g.hom.ker) :
    Tendsto (fun K => (binaryLaw K (fun i => primeZeroCriticalEnergy N (x i))).real
      {b | b ≠ fun i => decide (x i ∈ (primeZeroShortComplex ℝ N).moduleCatToCycles.range)})
      atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => primeZeroCriticalEnergy N (x i))
    (fun i => x i ∈ (primeZeroShortComplex ℝ N).moduleCatToCycles.range) fun i => by
    simp only [primeZeroCriticalEnergy_zero_iff_boundary]

end
end GaloisForLFunctions.EffectiveScalingGeometry

#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCriticalEnergy_zero_iff
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeCriticalEnergy_zero_iff_boundary
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_homological_death
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_homological_death_family
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.primeZeroCriticalEnergy_zero_iff_boundary
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_augmented_homological_death
#print axioms GaloisForLFunctions.EffectiveScalingGeometry.cox_augmented_homological_death_family
