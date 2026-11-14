import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskOccupancySpectrum
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCuspHeightsOfAPointAreSparse

/-!
# Spectral lattice-count bounds control the occupancy spectrum

The attained maximum number of Eisenstein integers in a disk inherits the
explicit area and quadratic bounds used in the cubic cusp-height sieve.
This connects the disk-covering occupancy invariant to the existing
fundamental-domain counting estimates.
-/

noncomputable section
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open DiskOccupancy

/-- The maximal occupancy satisfies the explicit fundamental-domain area bound. -/
theorem max_disk_occupancy_area_le {r : ℝ} (hr : 0 ≤ r) :
    (maxCount r : ℝ) * (9 * Real.sqrt 3 / 2) ≤ Real.pi * (3 * r + periodRadius) ^ 2 := by
  obtain ⟨z, hz⟩ := maxCount_attained r
  rw [← hz]
  apply card_lattice_disc_le z hr (points z r)
  intro n hn
  have h := (mem_points z r n).mp hn
  simpa only [dist_eq_norm, norm_sub_rev] using h

/-- The same invariant obeys the quadratic majorant already used by the cusp sieve. -/
theorem max_disk_occupancy_quadratic_le {r : ℝ} (hr : 0 ≤ r) :
    (maxCount r : ℝ) ≤ latticeConst * (1 + r ^ 2) := by
  obtain ⟨z, hz⟩ := maxCount_attained r
  rw [← hz]
  apply card_lattice_disc_le' z hr (points z r)
  intro n hn
  have h := (mem_points z r n).mp hn
  simpa only [dist_eq_norm, norm_sub_rev] using h

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover

#print axioms GaloisForLFunctions.SpectralTheoryOfTheCubicCover.max_disk_occupancy_area_le
#print axioms GaloisForLFunctions.SpectralTheoryOfTheCubicCover.max_disk_occupancy_quadratic_le
