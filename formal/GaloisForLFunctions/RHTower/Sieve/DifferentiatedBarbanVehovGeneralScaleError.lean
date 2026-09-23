import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovStrongScaleError

/-!
# Differentiated Barban--Vehov errors at every admissible long scale

The continuous harmonic-log model controls the exact long lcm moments whenever every lcm fibre
lies below one eighth of the lower endpoint.  Since both divisor variables are at most `M`, the
single scale condition `8 * M^(2 : ℕ) ≤ L` supplies this uniformly.  The resulting errors are small on
every scale with `M^(2 : ℕ) = o(L)`, not only the previously isolated cubic scale.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Every lcm in the mollifier support lies below an admissible long lower scale. -/
theorem lcm_general_scale_le
    {L M q r : ℕ} (hscale : 8 * M ^ (2 : ℕ) ≤ L)
    (hq0 : 0 < q) (hr0 : 0 < r) (hq : q ≤ M) (hr : r ≤ M) :
    8 * Nat.lcm q r ≤ L := by
  have hlcm : Nat.lcm q r ≤ q * r := Nat.lcm_le_mul hq0 hr0
  have hqr : q * r ≤ M ^ (2 : ℕ) := by
    rw [pow_two]
    exact Nat.mul_le_mul hq hr
  exact (Nat.mul_le_mul_left 8 (hlcm.trans hqr)).trans hscale

/-- Uniform base-moment error at any long scale satisfying `8 M² ≤ L`. -/
theorem abs_barbanVehovFullLongBaseLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovFullLongBaseLcm L M -
        barbanVehovFullLongBaseContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongBaseLcm, barbanVehovFullLongBaseContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (3 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongHarmonicKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_general_scale_le hscale hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
              barbanVehovLongHarmonicKernelContinuous L (L * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (3 / (L : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM) (by positivity)

/-- Uniform base--derivative cross-moment error at any long scale satisfying `8 M² ≤ L`. -/
theorem abs_barbanVehovFullLongCrossLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovFullLongCrossLcm L M -
        barbanVehovFullLongCrossContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongCrossLcm, barbanVehovFullLongCrossContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongFirstLogKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_general_scale_le hscale hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2))| := by
                congr 1
                ring
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2| := by
                rw [abs_neg, abs_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM)
      positivity

/-- Uniform derivative-square moment error at any long scale satisfying `8 M² ≤ L`. -/
theorem abs_barbanVehovFullLongDerivativeLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovFullLongDerivativeLcm L M -
        barbanVehovFullLongDerivativeContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)) := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongDerivativeLcm, barbanVehovFullLongDerivativeContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernelContinuous L (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongSecondLogKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_general_scale_le hscale hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongSecondLogKernelContinuous L (L * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM)
      positivity

end

end RHTower.Sieve
