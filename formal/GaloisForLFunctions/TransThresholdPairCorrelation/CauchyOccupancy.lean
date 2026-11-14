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

/-- Passing to unit cells enlarges a Cauchy interaction by at most a factor of three. -/
theorem cauchy_le_cell (x y : ℝ) :
    1 / (1 + (x - y) ^ 2) ≤ 3 * cellCauchy ⌊x⌋ ⌊y⌋ := by
  have he : |(x - y) - ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ))| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [Int.floor_le x, Int.floor_le y,
      Int.lt_floor_add_one x, Int.lt_floor_add_one y]
  have hs := (sq_le_one_iff_abs_le_one _).2 he
  have hd : 1 + ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)) ^ 2 ≤ 3 * (1 + (x - y) ^ 2) := by
    nlinarith only [hs, sq_nonneg (2 * (x - y) - ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)))]
  unfold cellCauchy
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [one_mul] using hd

/-- Real source locations, including collisions, satisfy the local Cauchy moment bound.
The constant is independent of the number, position, and multiplicity of the sources. -/
theorem configuration_cauchy_moment_le (s : Finset ι) (x : ι → ℝ)
    (m : ι → ℝ≥0) (q : ℕ) :
    (∑ i ∈ s, (m i : ℝ) *
      (∑ k ∈ s, (m k : ℝ) / (1 + (x i - x k) ^ 2)) ^ (q + 1)) ≤
      2 * (3 * cellCauchyMass) ^ (q + 1) *
        ∑ j ∈ s.image (fun i => ⌊x i⌋),
          (cellOccupancy s (fun i => ⌊x i⌋) m j : ℝ) ^ (q + 2) := by
  let bin : ι → ℤ := fun i => ⌊x i⌋
  have hpoint (i : ι) :
      (∑ k ∈ s, (m k : ℝ) / (1 + (x i - x k) ^ 2)) ≤
        3 * ∑ k ∈ s, (m k : ℝ) * cellCauchy (bin i) (bin k) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    have h := mul_le_mul_of_nonneg_left (cauchy_le_cell (x i) (x k)) (m k).coe_nonneg
    simpa only [mul_one_div, mul_left_comm, bin] using h
  have hlocal := configuration_cellCauchy_moment_le s bin m q
  calc
    _ ≤ ∑ i ∈ s, (m i : ℝ) *
        (3 * ∑ k ∈ s, (m k : ℝ) * cellCauchy (bin i) (bin k)) ^ (q + 1) := by
      apply sum_le_sum
      intro i _
      have hn : (0 : ℝ) ≤ ∑ k ∈ s, (m k : ℝ) / (1 + (x i - x k) ^ 2) :=
        sum_nonneg fun k _ => div_nonneg (m k).coe_nonneg (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hn (hpoint i) _) (m i).coe_nonneg
    _ = 3 ^ (q + 1) * (∑ i ∈ s, (m i : ℝ) *
        (∑ k ∈ s, (m k : ℝ) * cellCauchy (bin i) (bin k)) ^ (q + 1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [mul_pow]
      ring
    _ ≤ 3 ^ (q + 1) * (2 * cellCauchyMass ^ (q + 1) *
        ∑ j ∈ s.image bin, (cellOccupancy s bin m j : ℝ) ^ (q + 2)) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by rw [mul_pow]; ring

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.configuration_cellCauchy_moment_le
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.configuration_cauchy_moment_le
