import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovContinuousKernels
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovLcmExpansion
import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def barbanVehovFullLongBaseContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernelContinuous L (L * M) p.1 p.2

def barbanVehovFullLongCrossContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelContinuous L (L * M) p.1 p.2

def barbanVehovFullLongDerivativeContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernelContinuous L (L * M) p.1 p.2

private theorem sum_product_abs_barbanVehovWeight_eq_sq (M : ℕ) :
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| =
      (∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q|) ^ (2 : ℕ) := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [abs_mul]

/-- Product `ℓ¹` mass bound for the two Barban--Vehov divisor variables. -/
theorem sum_product_abs_barbanVehovWeight_le
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) := by
  rw [sum_product_abs_barbanVehovWeight_eq_sq]
  have hs := sum_abs_barbanVehovWeight_le hM (le_refl M)
  have hs0 : 0 ≤ ∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have htarget0 : 0 ≤ (M : ℝ) * Real.log M := by
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hM))
  calc
    (∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q|) ^ (2 : ℕ) =
        (∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q|) *
          (∑ q ∈ Finset.Icc 1 M, |barbanVehovWeight M q|) := by rw [pow_two]
    _ ≤ ((M : ℝ) * Real.log M) * ((M : ℝ) * Real.log M) :=
      mul_le_mul hs hs hs0 htarget0
    _ = ((M : ℝ) * Real.log M) ^ (2 : ℕ) := by rw [pow_two]

private theorem lcm_strong_scale_le
    {M q r : ℕ} (hM : 8 ≤ M) (hq0 : 0 < q) (hr0 : 0 < r)
    (hq : q ≤ M) (hr : r ≤ M) :
    8 * Nat.lcm q r ≤ M ^ (3 : ℕ) := by
  have hlcm : Nat.lcm q r ≤ q * r := Nat.lcm_le_mul hq0 hr0
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hM hq) hr
  calc
    8 * Nat.lcm q r ≤ 8 * (q * r) := Nat.mul_le_mul_left 8 hlcm
    _ = (8 * q) * r := by ring
    _ ≤ (M * M) * M := hprod
    _ = M ^ (3 : ℕ) := by ring

theorem abs_barbanVehovFullLongBaseLcm_cube_sub_continuous_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongBaseLcm (M ^ (3 : ℕ)) M -
        barbanVehovFullLongBaseContinuous (M ^ (3 : ℕ)) M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
  have hM1 : 1 ≤ M := by omega
  have hLU : M ^ (3 : ℕ) ≤ M ^ (3 : ℕ) * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongBaseLcm, barbanVehovFullLongBaseContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (3 / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongHarmonicKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_strong_scale_le hM hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongHarmonicKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
              barbanVehovLongHarmonicKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (3 / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / ((M ^ (3 : ℕ) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM1) (by positivity)

theorem abs_barbanVehovFullLongCrossLcm_cube_sub_continuous_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongCrossLcm (M ^ (3 : ℕ)) M -
        barbanVehovFullLongCrossContinuous (M ^ (3 : ℕ)) M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
  have hM1 : 1 ≤ M := by omega
  have hLU : M ^ (3 : ℕ) ≤ M ^ (3 : ℕ) * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongCrossLcm, barbanVehovFullLongCrossContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongFirstLogKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_strong_scale_le hM hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2)| *
            |barbanVehovLongFirstLogKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongFirstLogKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| := by
                rw [abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (6 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM1)
      positivity

theorem abs_barbanVehovFullLongDerivativeLcm_cube_sub_continuous_le
    {M : ℕ} (hM : 8 ≤ M) :
    |barbanVehovFullLongDerivativeLcm (M ^ (3 : ℕ)) M -
        barbanVehovFullLongDerivativeContinuous (M ^ (3 : ℕ)) M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (12 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ^ (2 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
  have hM1 : 1 ≤ M := by omega
  have hLU : M ^ (3 : ℕ) ≤ M ^ (3 : ℕ) * M := Nat.le_mul_of_pos_right _ (by omega)
  rw [barbanVehovFullLongDerivativeLcm, barbanVehovFullLongDerivativeContinuous,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
          (12 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ^ (2 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk := abs_barbanVehovLongSecondLogKernel_sub_continuous_le
        hp1.1 hp2.1 (lcm_strong_scale_le hM hp1.1 hp2.1 hp1.2 hp2.2) hLU
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovLongSecondLogKernel (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2 -
              barbanVehovLongSecondLogKernelContinuous (M ^ (3 : ℕ)) (M ^ (3 : ℕ) * M) p.1 p.2| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
          (12 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ^ (2 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (12 * Real.log (M ^ (3 : ℕ) * M + 1 : ℕ) ^ (2 : ℕ) / ((M ^ (3 : ℕ) : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (sum_product_abs_barbanVehovWeight_le hM1)
      positivity

end

end RHTower.Sieve
