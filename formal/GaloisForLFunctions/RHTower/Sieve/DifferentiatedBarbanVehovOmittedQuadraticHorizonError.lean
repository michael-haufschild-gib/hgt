import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError

/-!
# Omitted long-energy errors at quadratic-horizon scale

Keeping the omitted sector's exact lower endpoint `L * max q r` exposes a reciprocal-max gain
lost by the uniform endpoint estimate. Consequently `8*M ≤ L`, rather than `8*M^2 ≤ L`, suffices
pointwise, and the aggregate coefficient budget is linear in `M` up to logarithms.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

theorem lcm_le_mul_max_of_le
    {M q r : ℕ} (hq0 : 0 < q) (hr0 : 0 < r) (hq : q ≤ M) :
    Nat.lcm q r ≤ M * max q r := by
  exact (Nat.lcm_le_mul hq0 hr0).trans
    (Nat.mul_le_mul hq (Nat.le_max_right q r))

theorem omitted_quadratic_scale_le
    {L M q r : ℕ} (hscale : 8 * M ≤ L)
    (hq0 : 0 < q) (hr0 : 0 < r) (hq : q ≤ M) :
    8 * Nat.lcm q r ≤ L * max q r := by
  calc
    8 * Nat.lcm q r ≤ 8 * (M * max q r) :=
      Nat.mul_le_mul_left 8 (lcm_le_mul_max_of_le hq0 hr0 hq)
    _ = (8 * M) * max q r := by ring
    _ ≤ L * max q r := Nat.mul_le_mul_right _ hscale

theorem abs_barbanVehovOmittedLongHarmonicKernel_sub_continuous_le_sharp
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongHarmonicKernel L (L * M) q r -
        barbanVehovLongHarmonicKernelContinuous
          (L * max q r) (L * M) q r| ≤
      3 / ((L * max q r : ℕ) : ℝ) := by
  have hmax1 : 1 ≤ max q r :=
    (show 1 ≤ q from hq).trans (Nat.le_max_left _ _)
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  rw [barbanVehovOmittedLongHarmonicKernel_eq_maxEndpoint
    L (L * M) q r hq]
  exact abs_barbanVehovLongHarmonicKernel_sub_continuous_le
    hq hr (omitted_quadratic_scale_le hscale hq hr hqM) hLmax

theorem abs_barbanVehovOmittedLongFirstLogKernel_sub_continuous_le_sharp
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongFirstLogKernel L (L * M) q r -
        barbanVehovLongFirstLogKernelContinuous
          (L * max q r) (L * M) q r| ≤
      6 * Real.log (L * M + 1 : ℕ) /
        ((L * max q r : ℕ) : ℝ) := by
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  rw [barbanVehovOmittedLongFirstLogKernel_eq_maxEndpoint
    L (L * M) q r hq]
  exact abs_barbanVehovLongFirstLogKernel_sub_continuous_le
    hq hr (omitted_quadratic_scale_le hscale hq hr hqM) hLmax

theorem abs_barbanVehovOmittedLongSecondLogKernel_sub_continuous_le_sharp
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongSecondLogKernel L (L * M) q r -
        barbanVehovLongSecondLogKernelContinuous
          (L * max q r) (L * M) q r| ≤
      12 * Real.log (L * M + 1 : ℕ) ^ 2 /
        ((L * max q r : ℕ) : ℝ) := by
  have hmaxM : max q r ≤ M := max_le hqM hrM
  have hLmax : L * max q r ≤ L * M := Nat.mul_le_mul_left L hmaxM
  rw [barbanVehovOmittedLongSecondLogKernel_eq_maxEndpoint
    L (L * M) q r hq]
  exact abs_barbanVehovLongSecondLogKernel_sub_continuous_le
    hq hr (omitted_quadratic_scale_le hscale hq hr hqM) hLmax

theorem abs_barbanVehovWeight_mul_div_max_le
    {M q r : ℕ} (hq : 0 < q) :
    |barbanVehovWeight M q * barbanVehovWeight M r| /
        ((max q r : ℕ) : ℝ) ≤
      (|barbanVehovWeight M q| / (q : ℝ)) *
        |barbanVehovWeight M r| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqmaxR : (q : ℝ) ≤ ((max q r : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left q r
  have hinv : 1 / (((max q r : ℕ) : ℝ)) ≤ 1 / (q : ℝ) := by
    exact one_div_le_one_div_of_le hqR hqmaxR
  rw [abs_mul]
  calc
    |barbanVehovWeight M q| * |barbanVehovWeight M r| /
        ((max q r : ℕ) : ℝ) =
      (1 / (((max q r : ℕ) : ℝ))) *
        (|barbanVehovWeight M q| * |barbanVehovWeight M r|) := by ring
    _ ≤ (1 / (q : ℝ)) *
        (|barbanVehovWeight M q| * |barbanVehovWeight M r|) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (|barbanVehovWeight M q| / (q : ℝ)) *
        |barbanVehovWeight M r| := by ring

theorem sum_abs_barbanVehovWeight_div_le
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ q ∈ Finset.Icc 1 M,
      |barbanVehovWeight M q| / (q : ℝ)) ≤
      Real.log M * (1 + Real.log M) := by
  calc
    (∑ q ∈ Finset.Icc 1 M,
        |barbanVehovWeight M q| / (q : ℝ)) ≤
      ∑ q ∈ Finset.Icc 1 M, Real.log M * (1 / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
        simpa [div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_right
            (abs_barbanVehovWeight_le (m := q) hM) hq0)
    _ = Real.log M * (∑ q ∈ Finset.Icc 1 M, 1 / (q : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log M * (1 + Real.log M) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log M)
        (Real.log_nonneg (by exact_mod_cast hM))

theorem sum_product_abs_barbanVehovWeight_div_max_le
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
        ((max p.1 p.2 : ℕ) : ℝ)) ≤
      (M : ℝ) * Real.log M ^ 2 * (1 + Real.log M) := by
  let S := Finset.Icc 1 M
  calc
    (∑ p ∈ S ×ˢ S,
      |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
        ((max p.1 p.2 : ℕ) : ℝ)) ≤
      ∑ p ∈ S ×ˢ S,
        (|barbanVehovWeight M p.1| / (p.1 : ℝ)) *
          |barbanVehovWeight M p.2| := by
        apply Finset.sum_le_sum
        intro p hp
        exact abs_barbanVehovWeight_mul_div_max_le
          (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
    _ = (∑ q ∈ S, |barbanVehovWeight M q| / (q : ℝ)) *
        (∑ r ∈ S, |barbanVehovWeight M r|) := by
      rw [Finset.sum_product]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
    _ ≤ (Real.log M * (1 + Real.log M)) *
        ((M : ℝ) * Real.log M) := by
      exact mul_le_mul (sum_abs_barbanVehovWeight_div_le hM)
        (sum_abs_barbanVehovWeight_le hM le_rfl)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast hM))
          (by positivity))
    _ = (M : ℝ) * Real.log M ^ 2 * (1 + Real.log M) := by ring

theorem abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le_quadratic
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongBaseLcm L M -
        barbanVehovOmittedLongBaseContinuous L M| ≤
      ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (3 / (L : ℝ)) := by
  rw [barbanVehovOmittedLongBaseLcm,
    barbanVehovOmittedLongBaseContinuous, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernelContinuous
              (L * max p.1 p.2) (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) * (3 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk :=
        abs_barbanVehovOmittedLongHarmonicKernel_sub_continuous_le_sharp
          hp1.1 hp2.1 hp1.2 hp2.2 hscale
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2 -
              barbanVehovLongHarmonicKernelContinuous
                (L * max p.1 p.2) (L * M) p.1 p.2| := by
              rw [← abs_mul]
              congr 1
              ring
        _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            (3 / ((L * max p.1 p.2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg _)
        _ = (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
              ((max p.1 p.2 : ℕ) : ℝ)) * (3 / (L : ℝ)) := by
          have hL : (L : ℝ) ≠ 0 := by
            exact_mod_cast (show L ≠ 0 by omega)
          have hmax : ((max p.1 p.2 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (show max p.1 p.2 ≠ 0 by omega)
          push_cast
          field_simp [hL, hmax]
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) * (3 / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (3 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_div_max_le hM) (by positivity)

theorem abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le_quadratic
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongCrossLcm L M -
        barbanVehovOmittedLongCrossContinuous L M| ≤
      ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
  rw [barbanVehovOmittedLongCrossLcm,
    barbanVehovOmittedLongCrossContinuous, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2 -
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            barbanVehovLongFirstLogKernelContinuous
              (L * max p.1 p.2) (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk :=
        abs_barbanVehovOmittedLongFirstLogKernel_sub_continuous_le_sharp
          hp1.1 hp2.1 hp1.2 hp2.2 hscale
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongFirstLogKernelContinuous
                (L * max p.1 p.2) (L * M) p.1 p.2| := by
              have heq :
                  -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
                        barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2 -
                      -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
                        barbanVehovLongFirstLogKernelContinuous
                          (L * max p.1 p.2) (L * M) p.1 p.2 =
                    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
                      (barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2 -
                        barbanVehovLongFirstLogKernelContinuous
                          (L * max p.1 p.2) (L * M) p.1 p.2)) := by ring
              rw [heq, abs_neg, abs_mul]
        _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            (6 * Real.log (L * M + 1 : ℕ) /
              ((L * max p.1 p.2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg _)
        _ = (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
              ((max p.1 p.2 : ℕ) : ℝ)) *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
          have hL : (L : ℝ) ≠ 0 := by
            exact_mod_cast (show L ≠ 0 by omega)
          have hmax : ((max p.1 p.2 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (show max p.1 p.2 ≠ 0 by omega)
          push_cast
          field_simp [hL, hmax]
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_div_max_le hM) (by positivity)

theorem abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le_quadratic
    {L M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ≤ L) :
    |barbanVehovOmittedLongDerivativeLcm L M -
        barbanVehovOmittedLongDerivativeContinuous L M| ≤
      ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) := by
  rw [barbanVehovOmittedLongDerivativeLcm,
    barbanVehovOmittedLongDerivativeContinuous, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernelContinuous
              (L * max p.1 p.2) (L * M) p.1 p.2| ≤
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_Icc] at hp1 hp2
      have hk :=
        abs_barbanVehovOmittedLongSecondLogKernel_sub_continuous_le_sharp
          hp1.1 hp2.1 hp1.2 hp2.2 hscale
      calc
        _ = |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            |barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2 -
              barbanVehovLongSecondLogKernelContinuous
                (L * max p.1 p.2) (L * M) p.1 p.2| := by
              rw [← abs_mul]
              congr 1
              ring
        _ ≤ |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 /
              ((L * max p.1 p.2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hk (abs_nonneg _)
        _ = (|barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
              ((max p.1 p.2 : ℕ) : ℝ)) *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) := by
          have hL : (L : ℝ) ≠ 0 := by
            exact_mod_cast (show L ≠ 0 by omega)
          have hmax : ((max p.1 p.2 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (show max p.1 p.2 ≠ 0 by omega)
          push_cast
          field_simp [hL, hmax]
    _ = (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        |barbanVehovWeight M p.1 * barbanVehovWeight M p.2| /
          ((max p.1 p.2 : ℕ) : ℝ)) *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ ((M : ℝ) * Real.log M ^ 2 * (1 + Real.log M)) *
        (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (sum_product_abs_barbanVehovWeight_div_max_le hM) (by positivity)

end
end RHTower.Sieve

