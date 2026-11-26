import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates.SubsetEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundaryEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.DrawConstraints
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PeriodicCuts

/-! # Gaussian tail of the squared energy at all periodic seams -/

open MeasureTheory ProbabilityTheory Finset Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- The exponential moment depends on the number of seams and their
bounded neighbourhood sizes, uniformly in the packet length. -/
theorem periodic_seam_tail (n L : ℕ) (B : ℝ) :
    let T := seamNeighbourhood (SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none)
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    exp (B/4)*μ.real {x | B≤energyOn T x} ≤ (sqrt 2)^(516*((n+2)/L+1)) := by
  intro T μ
  apply (GaussianCoordinates.gaussian_seam_square_tail T B).trans
  apply pow_le_pow_right₀ (by norm_num)
  have h := (seamNeighbourhood_card _).trans (Nat.mul_le_mul_left 43
    (SpectralGapMass.Bulk.PeriodicCuts.seam_card (n:=n) L))
  simpa only [←Nat.mul_assoc] using h

#print axioms periodic_seam_tail
end
end GaloisForLFunctions.HTGeometry.BlockDilations
