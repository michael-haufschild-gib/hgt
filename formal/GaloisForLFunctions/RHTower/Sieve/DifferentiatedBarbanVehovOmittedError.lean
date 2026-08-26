import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedContinuous
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleError

/-!
# Continuous approximation error for the omitted detector-head boundary

At every mollifier pair, the omitted lower endpoint `L * max(q,r)` is no smaller than `L` and no
larger than `L*M`. The corpus's harmonic-log endpoint estimates therefore apply uniformly under
the same admissible scale condition `8*M^2 ≤ L` as the full long energy.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Normalize an absolute approximation error by a common nonnegative denominator. -/
theorem abs_div_sub_div_le_of_abs_sub_le
    {a b E D : ℝ} (hD : 0 ≤ D) (h : |a - b| ≤ E) :
    |a / D - b / D| ≤ E / D := by
  rw [← sub_div, abs_div, abs_of_nonneg hD]
  exact div_le_div_of_nonneg_right h hD

/-- A uniform pointwise kernel error transfers through an arbitrary finite real weight. -/
theorem abs_sum_weight_mul_sub_le_of_pointwise
    {α : Type*} [DecidableEq α] (s : Finset α)
    (w f g : α → ℝ) {E : ℝ}
    (hfg : ∀ x ∈ s, |f x - g x| ≤ E) :
    |(∑ x ∈ s, w x * f x) - ∑ x ∈ s, w x * g x| ≤
      (∑ x ∈ s, |w x|) * E := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ x ∈ s, |w x * f x - w x * g x| ≤
        ∑ x ∈ s, |w x| * E := by
      apply Finset.sum_le_sum
      intro x hx
      rw [show w x * f x - w x * g x = w x * (f x - g x) by ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_left (hfg x hx) (abs_nonneg _)
    _ = (∑ x ∈ s, |w x|) * E := by rw [Finset.sum_mul]

/-- Pointwise base-kernel error at the omitted pair-dependent endpoint. -/
theorem abs_barbanVehovOmittedLongHarmonicKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongHarmonicKernel L (L * M) q r -
        barbanVehovLongHarmonicKernelContinuous
          (L * max q r) (L * M) q r| ≤
      3 / (L : ℝ) := by
  have hMpos : 0 < M := hq.trans_le hqM
  have hLpos : 0 < L := by nlinarith
  have hmax1 : 1 ≤ max q r :=
    (show 1 ≤ q from hq).trans (Nat.le_max_left _ _)
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  have hscaleMax : 8 * Nat.lcm q r ≤ L * max q r :=
    hscaleL.trans (by simpa using Nat.mul_le_mul_left L hmax1)
  have hk := abs_barbanVehovLongHarmonicKernel_sub_continuous_le
    hq hr hscaleMax hLmax
  rw [barbanVehovOmittedLongHarmonicKernel_eq_maxEndpoint
    L (L * M) q r hq]
  refine hk.trans ?_
  have hcast : (L : ℝ) ≤ (L * max q r : ℕ) := by
    exact_mod_cast (by simpa using Nat.mul_le_mul_left L hmax1)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hcast

/-- Pointwise first-log kernel error at the omitted pair-dependent endpoint. -/
theorem abs_barbanVehovOmittedLongFirstLogKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongFirstLogKernel L (L * M) q r -
        barbanVehovLongFirstLogKernelContinuous
          (L * max q r) (L * M) q r| ≤
      6 * Real.log (L * M + 1 : ℕ) / (L : ℝ) := by
  have hMpos : 0 < M := hq.trans_le hqM
  have hLpos : 0 < L := by nlinarith
  have hmax1 : 1 ≤ max q r :=
    (show 1 ≤ q from hq).trans (Nat.le_max_left _ _)
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  have hscaleMax : 8 * Nat.lcm q r ≤ L * max q r :=
    hscaleL.trans (by simpa using Nat.mul_le_mul_left L hmax1)
  have hk := abs_barbanVehovLongFirstLogKernel_sub_continuous_le
    hq hr hscaleMax hLmax
  rw [barbanVehovOmittedLongFirstLogKernel_eq_maxEndpoint
    L (L * M) q r hq]
  refine hk.trans ?_
  have hcast : (L : ℝ) ≤ (L * max q r : ℕ) := by
    exact_mod_cast (by simpa using Nat.mul_le_mul_left L hmax1)
  have hnum : 0 ≤ 6 * Real.log (L * M + 1 : ℕ) := by positivity
  exact div_le_div_of_nonneg_left hnum (by positivity) hcast

/-- Pointwise second-log kernel error at the omitted pair-dependent endpoint. -/
theorem abs_barbanVehovOmittedLongSecondLogKernel_sub_continuous_le
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongSecondLogKernel L (L * M) q r -
        barbanVehovLongSecondLogKernelContinuous
          (L * max q r) (L * M) q r| ≤
      12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ) := by
  have hMpos : 0 < M := hq.trans_le hqM
  have hLpos : 0 < L := by nlinarith
  have hmax1 : 1 ≤ max q r :=
    (show 1 ≤ q from hq).trans (Nat.le_max_left _ _)
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  have hscaleL := lcm_general_scale_le hscale hq hr hqM hrM
  have hscaleMax : 8 * Nat.lcm q r ≤ L * max q r :=
    hscaleL.trans (by simpa using Nat.mul_le_mul_left L hmax1)
  have hk := abs_barbanVehovLongSecondLogKernel_sub_continuous_le
    hq hr hscaleMax hLmax
  rw [barbanVehovOmittedLongSecondLogKernel_eq_maxEndpoint
    L (L * M) q r hq]
  refine hk.trans ?_
  have hcast : (L : ℝ) ≤ (L * max q r : ℕ) := by
    exact_mod_cast (by simpa using Nat.mul_le_mul_left L hmax1)
  have hnum : 0 ≤ 12 * Real.log (L * M + 1 : ℕ) ^ 2 := by positivity
  exact div_le_div_of_nonneg_left hnum (by positivity) hcast

/-- Uniform base-moment approximation error for the omitted head boundary. -/
theorem abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongBaseLcm L M -
        barbanVehovOmittedLongBaseContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ 2 * (3 / (L : ℝ)) := by
  rw [barbanVehovOmittedLongBaseLcm,
    barbanVehovOmittedLongBaseContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovLongHarmonicKernelContinuous
            (L * max p.1 p.2) (L * M) p.1 p.2| ≤
        3 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovOmittedLongHarmonicKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongHarmonicKernelContinuous
      (L * max p.1 p.2) (L * M) p.1 p.2) hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

/-- Uniform base--derivative approximation error for the omitted head boundary. -/
theorem abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongCrossLcm L M -
        barbanVehovOmittedLongCrossContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ 2 *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
  rw [barbanVehovOmittedLongCrossLcm,
    barbanVehovOmittedLongCrossContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongFirstLogKernelContinuous
            (L * max p.1 p.2) (L * M) p.1 p.2| ≤
        6 * Real.log (L * M + 1 : ℕ) / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovOmittedLongFirstLogKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2))
    (fun p => barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongFirstLogKernelContinuous
      (L * max p.1 p.2) (L * M) p.1 p.2) hpoint
  change |(∑ p ∈ s,
      -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
        barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2) -
      ∑ p ∈ s,
        -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
          barbanVehovLongFirstLogKernelContinuous
            (L * max p.1 p.2) (L * M) p.1 p.2| ≤ _
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

/-- Uniform derivative-square approximation error for the omitted head boundary. -/
theorem abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovOmittedLongDerivativeLcm L M -
        barbanVehovOmittedLongDerivativeContinuous L M| ≤
      ((M : ℝ) * Real.log M) ^ 2 *
        (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) := by
  rw [barbanVehovOmittedLongDerivativeLcm,
    barbanVehovOmittedLongDerivativeContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongSecondLogKernelContinuous
            (L * max p.1 p.2) (L * M) p.1 p.2| ≤
        12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovOmittedLongSecondLogKernel_sub_continuous_le
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongSecondLogKernelContinuous
      (L * max p.1 p.2) (L * M) p.1 p.2) hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

end

end RHTower.Sieve
