import GaloisForLFunctions.HTGeometry.ScaleCompleteDyadicActionLaw
import GaloisForLFunctions.RHTower.ScalarRecurrenceTracelessCircuitSplit

open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **Scale-complete observer action** after removing the common identity-Choi
return channel. Dimension and replica order are positive by construction. -/
def staticChoiTracelessScaleCompleteActionMass
    (d : ℕ) (energy : Fin (d + 1) → ℝ)
    (target : EuclideanSpace ℂ
      (Fin (d + 1) × Fin (d + 1)))
    (r N : ℕ) : ℂ :=
  scaleCompleteComplexReplicaActionMass
    (staticChoiTracelessSpectralCoefficient energy target)
    energy (r + 1) N

/-- Every finite logarithmic-scale window is exactly the sum of physical
dyadic observer wavelets of the traceless Choi replica packet. -/
theorem staticChoiTracelessScaleCompleteActionMass_eq_wavelet_sum
    (d : ℕ) (energy : Fin (d + 1) → ℝ)
    (target : EuclideanSpace ℂ
      (Fin (d + 1) × Fin (d + 1)))
    (r N : ℕ) :
    staticChoiTracelessScaleCompleteActionMass d energy target r N =
      ∑ j ∈ Finset.range (2 * N),
        complexReplicaDyadicActionWavelet
          (staticChoiTracelessSpectralCoefficient energy target)
          energy (r + 1)
          ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) := by
  exact scaleCompleteComplexReplicaActionMass_eq_wavelet_sum
    (staticChoiTracelessSpectralCoefficient energy target)
    energy (r + 1) N

/-- **Traceless Choi scale-conservation law.** For every finite dimension,
every spectrum, every Choi target, and every positive replica order, the
complete multiscale observed action converges exactly to the negative exact
recurrence sector. There is no minimum spectral gap, terminal remainder, or
genericity assumption. -/
theorem tendsto_staticChoiTracelessScaleCompleteActionMass
    (d : ℕ) (energy : Fin (d + 1) → ℝ)
    (target : EuclideanSpace ℂ
      (Fin (d + 1) × Fin (d + 1)))
    (r : ℕ) :
    Tendsto
      (staticChoiTracelessScaleCompleteActionMass d energy target r)
      atTop
      (𝓝 (-complexReplicaGaussianCollisionPlateau
        (staticChoiTracelessSpectralCoefficient energy target)
        energy (r + 1))) := by
  let coefficient := staticChoiTracelessSpectralCoefficient energy target
  have hlimit := tendsto_scaleCompleteComplexReplicaActionMass
    coefficient energy (r + 1)
  have hcancel := staticChoiTracelessReplicaSectorMass_eq_neg_complement
    (Nat.succ_pos d) energy target (Nat.succ_pos r)
    (fun p q => replicaMultiplicityEnergy energy p =
      replicaMultiplicityEnergy energy q)
  have hnoncollision :
      complexReplicaSectorMass coefficient (r + 1)
          (fun p q => replicaMultiplicityEnergy energy p ≠
            replicaMultiplicityEnergy energy q) =
        -complexReplicaSectorMass coefficient (r + 1)
          (fun p q => replicaMultiplicityEnergy energy p =
            replicaMultiplicityEnergy energy q) := by
    have hneg := congrArg Neg.neg hcancel
    simpa [coefficient] using hneg.symm
  have hcollision :=
    complexReplicaGaussianCollisionPlateau_eq_sectorMass
      coefficient energy (r + 1)
  change Tendsto
    (scaleCompleteComplexReplicaActionMass coefficient energy (r + 1))
    atTop
    (𝓝 (-complexReplicaGaussianCollisionPlateau
      coefficient energy (r + 1)))
  rw [hcollision]
  rw [← hnoncollision]
  exact hlimit

end

end RHTower
