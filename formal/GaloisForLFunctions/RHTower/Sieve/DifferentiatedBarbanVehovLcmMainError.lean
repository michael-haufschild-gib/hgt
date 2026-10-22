import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovKernelAsymptotics

/-!
# Main terms and kernel errors for the long Barban–Vehov lcm forms

With Barban–Vehov weights `w_M(q) = μ(q) log(M/q)` for `q ≤ M`, the long base, cross and
differentiated moments are bilinear lcm forms `∑_{q, r ≤ M} w_M(q) w_M(r) K(q, r)`, where the
kernels are harmonic sums over multiples `k ∈ (L, LM]` of `lcm(q, r)` weighted by `1/k`,
`log(k/r)/k` or `log(k/q) log(k/r)/k`. Replacing each kernel by its integral-model main term (built
from `(log(B+1))^(m+1)/(m+1) - (log(A+1))^(m+1)/(m+1)` on the rescaled window) defines main forms;
this module bounds the difference between each exact form and its main form by an explicit
weighted sum of kernel errors of size `O(log-polynomial / lcm(q, r))`.

## Main results

- `abs_barbanVehovFullLongBaseLcm_sub_main_le`: base form error at most
  `∑ |w(q) w(r)| · 40 / lcm(q, r)`.
- `abs_barbanVehovFullLongCrossLcm_sub_main_le`: cross form error at most
  `∑ |w(q) w(r)| (40 |log(lcm/r)| + 200) / lcm(q, r)`.
- `abs_barbanVehovFullLongDerivativeLcm_sub_main_le`: differentiated form error at most
  `∑ |w(q) w(r)| (40 |log(lcm/q) log(lcm/r)| + 200 |log(lcm/q) + log(lcm/r)| + 2000) / lcm(q, r)`.

## Hypotheses

All results are unconditional explicit inequalities; they assume only `1 ≤ M`.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Main term of the long base lcm form: the Barban–Vehov bilinear form with the harmonic kernel
replaced by its integral model. -/
def barbanVehovFullLongBaseMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernelMain L (L * M) p.1 p.2

/-- Main term of the long cross lcm form, using the integral model of the first log kernel. -/
def barbanVehovFullLongCrossMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelMain L (L * M) p.1 p.2

/-- Main term of the long differentiated lcm form, using the integral model of the second log
kernel. -/
def barbanVehovFullLongDerivativeMain (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernelMain L (L * M) p.1 p.2

/-- Kernel error budget `∑_{q, r ≤ M} |w(q) w(r)| · 40 / lcm(q, r)` for the base form. -/
def barbanVehovFullLongBaseKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      (40 / (Nat.lcm p.1 p.2 : ℝ))

/-- Kernel error budget `∑ |w(q) w(r)| (40 |log(lcm/r)| + 200) / lcm(q, r)` for the cross form. -/
def barbanVehovFullLongCrossKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 200) /
        (Nat.lcm p.1 p.2 : ℝ))

/-- Kernel error budget for the differentiated form, with numerator
`40 |log(lcm/q) log(lcm/r)| + 200 |log(lcm/q) + log(lcm/r)| + 2000`. -/
def barbanVehovFullLongDerivativeKernelError (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
      ((40 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) *
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| +
        200 * |Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) +
          Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| + 2000) /
        (Nat.lcm p.1 p.2 : ℝ))

/-- For `1 ≤ M`, the exact long base lcm form differs from its main term by at most the base kernel
error budget. -/
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

/-- For `1 ≤ M`, the exact long cross lcm form differs from its main term by at most the cross
kernel error budget. -/
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

/-- For `1 ≤ M`, the exact long differentiated lcm form differs from its main term by at most the
differentiated kernel error budget. -/
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
