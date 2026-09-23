import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorOmittedLongMomentExpansion
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovLcmExpansion

/-!
# Exact lcm expansion of the omitted detector-head boundary

The omitted boundary condition is `L*q < k` in complementary-mollifier orientation. Expanding two
such divisor sums therefore adds exactly the pair of boundary inequalities to the existing lcm
fibres. This file packages the three resulting harmonic kernels and identifies them with the base,
mixed, and differentiated omitted-head moments.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Harmonic lcm kernel with both complementary divisors beyond the head cutoff. -/
def barbanVehovOmittedLongHarmonicKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if L * q < k ∧ L * r < k then 1 / (k : ℝ) else 0

/-- First complementary-divisor log moment on an omitted-boundary lcm fibre. -/
def barbanVehovOmittedLongFirstLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if L * q < k ∧ L * r < k then
      Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)
    else 0

/-- Second complementary-divisor log moment on an omitted-boundary lcm fibre. -/
def barbanVehovOmittedLongSecondLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if L * q < k ∧ L * r < k then
      Real.log (((k / q : ℕ) : ℝ)) *
        Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)
    else 0

/-- Exact lcm quadratic form for the omitted-head base moment. -/
def barbanVehovOmittedLongBaseLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2

/-- Exact lcm form for the omitted-head base/differentiated cross moment. -/
def barbanVehovOmittedLongCrossLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2

/-- Exact lcm form for the omitted-head differentiated square moment. -/
def barbanVehovOmittedLongDerivativeLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2

theorem levinsonCriticalDetectorOmittedLongBaseMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorOmittedLongBaseMoment L M =
      barbanVehovOmittedLongBaseLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorOmittedLongBaseMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovOmittedBaseCoeff L M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if L * p.1 < k ∧ L * p.2 < k then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovOmittedBaseCoeff, Finset.sum_filter]
    rw [sq, Finset.sum_mul_sum, Finset.sum_product, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : L * q < k <;> by_cases hrk : L * r < k <;>
      simp [hqk, hrk]
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if L * p.1 < k ∧ L * p.2 < k then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovOmittedLongHarmonicKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovOmittedLongHarmonicKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : L * p.1 < k ∧ L * p.2 < k <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovOmittedLongBaseLcm]

theorem levinsonCriticalDetectorOmittedLongCrossMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorOmittedLongCrossMoment L M =
      barbanVehovOmittedLongCrossLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorOmittedLongCrossMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovOmittedBaseCoeff L M k *
          barbanVehovOmittedDifferentiatedCoeff L M k / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if L * p.1 < k ∧ L * p.2 < k then
            -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
              Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovOmittedBaseCoeff,
      barbanVehovOmittedDifferentiatedCoeff]
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [mul_neg, Finset.sum_mul_sum, Finset.sum_product]
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : L * q < k <;> by_cases hrk : L * r < k <;>
      simp [hqk, hrk] <;> ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if L * p.1 < k ∧ L * p.2 < k then
            -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
              Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (-barbanVehovOmittedLongFirstLogKernel L (L * M) p.1 p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovOmittedLongFirstLogKernel, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : L * p.1 < k ∧ L * p.2 < k <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovOmittedLongCrossLcm]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem levinsonCriticalDetectorOmittedLongDerivativeMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorOmittedLongDerivativeMoment L M =
      barbanVehovOmittedLongDerivativeLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorOmittedLongDerivativeMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovOmittedDifferentiatedCoeff L M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if L * p.1 < k ∧ L * p.2 < k then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
              (Real.log (((k / p.1 : ℕ) : ℝ)) *
                Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovOmittedDifferentiatedCoeff, neg_sq]
    rw [Finset.sum_filter]
    rw [sq, Finset.sum_mul_sum, Finset.sum_product, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : L * q < k <;> by_cases hrk : L * r < k <;>
      simp [hqk, hrk] <;> ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if L * p.1 < k ∧ L * p.2 < k then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
              (Real.log (((k / p.1 : ℕ) : ℝ)) *
                Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovOmittedLongSecondLogKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovOmittedLongSecondLogKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : L * p.1 < k ∧ L * p.2 < k <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovOmittedLongDerivativeLcm]

end

end RHTower.Sieve
