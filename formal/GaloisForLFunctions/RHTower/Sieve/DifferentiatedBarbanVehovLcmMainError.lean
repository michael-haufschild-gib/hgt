import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelAsymptotics

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def barbanVehovFullLongBaseMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernelMain L (L * M) p.1 p.2

def barbanVehovFullLongCrossMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2

def barbanVehovFullLongDerivativeMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernelMain L (L * M) p.1 p.2

def barbanVehovFullLongBaseKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      (40 / (Nat.lcm p.1 p.2 : ℝ))

def barbanVehovFullLongCrossKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 200) /
        (Nat.lcm p.1 p.2 : ℝ))

def barbanVehovFullLongDerivativeKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) *
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| +
        200 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) +
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 2000) /
        (Nat.lcm p.1 p.2 : ℝ))

theorem abs_barbanVehovFullLongBaseLcm_sub_main_le
    {L M : ℕ} (hM : 1 ≤ M) :
    |barbanVehovFullLongBaseLcm L M - barbanVehovFullLongBaseMain L M| ≤
      barbanVehovFullLongBaseKernelError M := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right L (by omega)
  rw [barbanVehovFullLongBaseLcm, barbanVehovFullLongBaseMain,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [barbanVehovFullLongBaseKernelError]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hq : 0 < p.1 := hp1.1
  have hr : 0 < p.2 := hp2.1
  have hk := abs_barbanVehovLongHarmonicKernel_sub_main_le hLU hq hr
  calc
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
        barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
      barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
        barbanVehovLongHarmonicKernelMain L (L * M) p.1 p.2| =
      |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
        |barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovLongHarmonicKernelMain L (L * M) p.1 p.2| := by
            rw [← abs_mul]
            congr 1
            ring
    _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
        (40 / (Nat.lcm p.1 p.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hk (abs_nonneg _)

theorem abs_barbanVehovFullLongCrossLcm_sub_main_le
    {L M : ℕ} (hM : 1 ≤ M) :
    |barbanVehovFullLongCrossLcm L M - barbanVehovFullLongCrossMain L M| ≤
      barbanVehovFullLongCrossKernelError M := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right L (by omega)
  rw [barbanVehovFullLongCrossLcm, barbanVehovFullLongCrossMain,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [barbanVehovFullLongCrossKernelError]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hq : 0 < p.1 := hp1.1
  have hr : 0 < p.2 := hp2.1
  have hk := abs_barbanVehovLongFirstLogKernel_sub_main_le hLU hq hr
  calc
    |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
        barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
      -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
        barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2| =
      |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
        |barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2| := by
            calc
              |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
                  barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
                -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
                  barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2| =
                |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
                  (barbanVehovLongFirstLogKernel L (L * M) p.1 p.2 -
                    barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2))| := by
                      congr 1
                      ring_nf
              _ = _ := by rw [abs_neg, abs_mul]
    _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
        ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 200) /
          (Nat.lcm p.1 p.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hk (abs_nonneg _)

theorem abs_barbanVehovFullLongDerivativeLcm_sub_main_le
    {L M : ℕ} (hM : 1 ≤ M) :
    |barbanVehovFullLongDerivativeLcm L M - barbanVehovFullLongDerivativeMain L M| ≤
      barbanVehovFullLongDerivativeKernelError M := by
  have hLU : L ≤ L * M := Nat.le_mul_of_pos_right L (by omega)
  rw [barbanVehovFullLongDerivativeLcm, barbanVehovFullLongDerivativeMain,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [barbanVehovFullLongDerivativeKernelError]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hq : 0 < p.1 := hp1.1
  have hr : 0 < p.2 := hp2.1
  have hk := abs_barbanVehovLongSecondLogKernel_sub_main_le hLU hq hr
  calc
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
        barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
      barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
        barbanVehovLongSecondLogKernelMain L (L * M) p.1 p.2| =
      |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
        |barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongSecondLogKernelMain L (L * M) p.1 p.2| := by
            rw [← abs_mul]
            congr 1
            ring
    _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) *
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| +
        200 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) +
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 2000) /
        (Nat.lcm p.1 p.2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hk (abs_nonneg _)

end

end RHTower.Sieve
