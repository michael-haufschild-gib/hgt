import GaloisForLFunctions.TransThresholdPairCorrelation.CauchyLocalMoments

/-!
# Cauchy moments of finite weighted configurations

Collecting sources by integer cell is an exact operation. The uniform lattice
moment estimate therefore controls arbitrary finite configurations through
the moments of their cell occupancies, including coincident sources.
-/

open Finset
open scoped BigOperators NNReal

namespace GaloisForLFunctions.TransThresholdPairCorrelation
noncomputable section
variable {ι : Type*}

/-- Total nonnegative source mass in an integer cell. -/
def cellOccupancy (s : Finset ι) (bin : ι → ℤ) (m : ι → ℝ≥0) (j : ℤ) : ℝ≥0 :=
  ∑ i ∈ s with bin i = j, m i

/-- Exact collection of a weighted observable by integer cells. -/
theorem sum_cellOccupancy_mul (s : Finset ι) (bin : ι → ℤ) (m : ι → ℝ≥0) (F : ℤ → ℝ) :
    (∑ j ∈ s.image bin, (cellOccupancy s bin m j : ℝ) * F j) =
      ∑ i ∈ s, (m i : ℝ) * F (bin i) := by
  calc
    _ = ∑ j ∈ s.image bin, ∑ i ∈ s with bin i = j, (m i : ℝ) * F (bin i) := by
      apply sum_congr rfl
      intro j _
      simp only [cellOccupancy, NNReal.coe_sum, sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem bin hi) _

/-- Correlation at a source equals correlation of the exact cell occupancies. -/
theorem cellCauchyDensity_occupancy (s : Finset ι) (bin : ι → ℤ) (m : ι → ℝ≥0) (j : ℤ) :
    cellCauchyDensity (s.image bin) (cellOccupancy s bin m) j =
      ∑ i ∈ s, (m i : ℝ) * cellCauchy j (bin i) := by
  simpa only [cellCauchyDensity, mul_comm] using sum_cellOccupancy_mul s bin m (cellCauchy j)

/-- Arbitrary multiplicities and coincident sources obey the same uniform moment estimate. -/
theorem configuration_cellCauchy_moment_le (s : Finset ι) (bin : ι → ℤ)
    (m : ι → ℝ≥0) (q : ℕ) :
    (∑ i ∈ s, (m i : ℝ) *
      (∑ k ∈ s, (m k : ℝ) * cellCauchy (bin i) (bin k)) ^ (q + 1)) ≤
      2 * cellCauchyMass ^ (q + 1) *
        ∑ j ∈ s.image bin, (cellOccupancy s bin m j : ℝ) ^ (q + 2) := by
  have h := cellCauchy_moment_le (s.image bin) (cellOccupancy s bin m) q
  rw [sum_cellOccupancy_mul s bin m
    (fun j => cellCauchyDensity (s.image bin) (cellOccupancy s bin m) j ^ (q + 1))] at h
  simpa only [cellCauchyDensity_occupancy] using h

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.configuration_cellCauchy_moment_le
