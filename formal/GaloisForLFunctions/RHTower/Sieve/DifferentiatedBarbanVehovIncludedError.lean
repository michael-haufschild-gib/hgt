import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedContinuous
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError

/-!
# Continuous approximation error for the included detector-head boundary

The included upper endpoint is `L * min(q,r)`.  The generic long-kernel estimates apply after the
exact endpoint rewrite, and the existing weighted finite-sum transfer supplies the three moment
errors without a new analytic argument.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

theorem abs_barbanVehovIncludedLongHarmonicKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongHarmonicKernel L (L * M) q r -
        barbanVehovLongHarmonicKernelContinuous L (L * min q r) q r| ≤
      3 / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  rw [barbanVehovIncludedLongHarmonicKernel_eq_minEndpoint hqM hrM]
  exact abs_barbanVehovLongHarmonicKernel_sub_continuous_le
    hq hr hscaleL hLmin

theorem abs_barbanVehovIncludedLongFirstLogKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongFirstLogKernel L (L * M) q r -
        barbanVehovLongFirstLogKernelContinuous L (L * min q r) q r| ≤
      6 * Real.log (L * M + 1 : ℕ) / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hminM : min q r ≤ M := (Nat.min_le_left q r).trans hqM
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have hU : L * min q r ≤ L * M := Nat.mul_le_mul_left L hminM
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  rw [barbanVehovIncludedLongFirstLogKernel_eq_minEndpoint hqM hrM]
  refine (abs_barbanVehovLongFirstLogKernel_sub_continuous_le
    hq hr hscaleL hLmin).trans ?_
  have hlog : Real.log (L * min q r + 1 : ℕ) ≤ Real.log (L * M + 1 : ℕ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hU 1)
  gcongr

theorem abs_barbanVehovIncludedLongSecondLogKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongSecondLogKernel L (L * M) q r -
        barbanVehovLongSecondLogKernelContinuous L (L * min q r) q r| ≤
      12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hminM : min q r ≤ M := (Nat.min_le_left q r).trans hqM
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have hU : L * min q r ≤ L * M := Nat.mul_le_mul_left L hminM
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  rw [barbanVehovIncludedLongSecondLogKernel_eq_minEndpoint hqM hrM]
  refine (abs_barbanVehovLongSecondLogKernel_sub_continuous_le
    hq hr hscaleL hLmin).trans ?_
  have hlog : Real.log (L * min q r + 1 : ℕ) ≤ Real.log (L * M + 1 : ℕ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hU 1)
  have hlog0 : 0 ≤ Real.log (L * min q r + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ L * min q r + 1 by omega))
  gcongr

theorem abs_barbanVehovIncludedLongBaseLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongBaseLcm L M -
        barbanVehovIncludedLongBaseContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) := by
  rw [barbanVehovIncludedLongBaseLcm,
    barbanVehovIncludedLongBaseContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovLongHarmonicKernelContinuous
            L (L * min p.1 p.2) p.1 p.2| ≤ 3 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongHarmonicKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongHarmonicKernelContinuous
      L (L * min p.1 p.2) p.1 p.2) hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

theorem abs_barbanVehovIncludedLongCrossLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongCrossLcm L M -
        barbanVehovIncludedLongCrossContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
  rw [barbanVehovIncludedLongCrossLcm,
    barbanVehovIncludedLongCrossContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongFirstLogKernelContinuous
            L (L * min p.1 p.2) p.1 p.2| ≤
        6 * Real.log (L * M + 1 : ℕ) / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongFirstLogKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2))
    (fun p => barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongFirstLogKernelContinuous
      L (L * min p.1 p.2) p.1 p.2) hpoint
  change |(∑ p ∈ s,
      -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
        barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2) -
      ∑ p ∈ s,
        -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
          barbanVehovLongFirstLogKernelContinuous
            L (L * min p.1 p.2) p.1 p.2| ≤ _
  calc
    _ ≤ (∑ p ∈ s,
          |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2)|) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := hraw
    _ = (∑ p ∈ s,
          |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      simp only [abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_product_abs_barbanVehovWeight_le hM) (by positivity)

theorem abs_barbanVehovIncludedLongDerivativeLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |barbanVehovIncludedLongDerivativeLcm L M -
        barbanVehovIncludedLongDerivativeContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) *
        (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)) := by
  rw [barbanVehovIncludedLongDerivativeLcm,
    barbanVehovIncludedLongDerivativeContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongSecondLogKernelContinuous
            L (L * min p.1 p.2) p.1 p.2| ≤
        12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongSecondLogKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongSecondLogKernelContinuous
      L (L * min p.1 p.2) p.1 p.2) hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

end

end RHTower.Sieve
