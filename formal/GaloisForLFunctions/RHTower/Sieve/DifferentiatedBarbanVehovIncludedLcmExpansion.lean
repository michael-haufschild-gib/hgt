import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorIncludedLongMomentExpansion
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovLcmExpansion

/-!
# Exact lcm expansion of the included detector-head long range

Direct finite-convolution expansion retains complementary divisors satisfying `k ≤ L*q`.
Pair expansion therefore has upper endpoint `L * min(q,r)`, preserving cancellation that is lost
when full and omitted energies are bounded separately.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Harmonic lcm kernel with both complementary divisors retained by the finite head. -/
def barbanVehovIncludedLongHarmonicKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if k ≤ L * q ∧ k ≤ L * r then 1 / (k : ℝ) else 0

/-- First complementary-divisor log kernel retained by the finite head. -/
def barbanVehovIncludedLongFirstLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if k ≤ L * q ∧ k ≤ L * r then
      Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)
    else 0

/-- Second complementary-divisor log kernel retained by the finite head. -/
def barbanVehovIncludedLongSecondLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    if k ≤ L * q ∧ k ≤ L * r then
      Real.log (((k / q : ℕ) : ℝ)) *
        Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)
    else 0

/-- Exact included-head lcm quadratic form for the base moment. -/
def barbanVehovIncludedLongBaseLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2

/-- Exact included-head lcm form for the base/differentiated cross moment. -/
def barbanVehovIncludedLongCrossLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2

/-- Exact included-head lcm form for the differentiated-square moment. -/
def barbanVehovIncludedLongDerivativeLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2

theorem levinsonCriticalDetectorIncludedLongBaseMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorIncludedLongBaseMoment L M =
      barbanVehovIncludedLongBaseLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorIncludedLongBaseMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovIncludedBaseCoeff L M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovIncludedBaseCoeff, Finset.sum_filter]
    rw [sq, Finset.sum_mul_sum, Finset.sum_product, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : k ≤ L * q <;> by_cases hrk : k ≤ L * r <;>
      simp [hqk, hrk]
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovIncludedLongHarmonicKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k ≤ L * p.1 ∧ k ≤ L * p.2 <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovIncludedLongBaseLcm]

theorem levinsonCriticalDetectorIncludedLongCrossMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorIncludedLongCrossMoment L M =
      barbanVehovIncludedLongCrossLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorIncludedLongCrossMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovIncludedBaseCoeff L M k *
          barbanVehovIncludedDifferentiatedCoeff L M k / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
              Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovIncludedBaseCoeff,
      barbanVehovIncludedDifferentiatedCoeff]
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [mul_neg, Finset.sum_mul_sum, Finset.sum_product]
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : k ≤ L * q <;> by_cases hrk : k ≤ L * r <;>
      simp [hqk, hrk] <;> ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
              Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (-barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovIncludedLongFirstLogKernel, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k ≤ L * p.1 ∧ k ≤ L * p.2 <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovIncludedLongCrossLcm]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem levinsonCriticalDetectorIncludedLongDerivativeMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorIncludedLongDerivativeMoment L M =
      barbanVehovIncludedLongDerivativeLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorIncludedLongDerivativeMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovIncludedDifferentiatedCoeff L M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
              (Real.log (((k / p.1 : ℕ) : ℝ)) *
                Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ)
          else 0 := by
    intro k hk
    rw [barbanVehovIncludedDifferentiatedCoeff, neg_sq]
    rw [Finset.sum_filter]
    rw [sq, Finset.sum_mul_sum, Finset.sum_product, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hqk : k ≤ L * q <;> by_cases hrk : k ≤ L * r <;>
      simp [hqk, hrk] <;> ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter
            (fun k => Nat.lcm p.1 p.2 ∣ k),
          if k ≤ L * p.1 ∧ k ≤ L * p.2 then
            barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
              (Real.log (((k / p.1 : ℕ) : ℝ)) *
                Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ)
          else 0) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovIncludedLongSecondLogKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k ≤ L * p.1 ∧ k ≤ L * p.2 <;> simp [h] <;> ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovIncludedLongDerivativeLcm]

/-- A pair of included-head inequalities is exactly the minimum upper endpoint. -/
theorem sum_Ioc_lcm_if_le_mul_pair_eq_minEndpoint
    {R : Type*} [AddCommMonoid R] (F : ℕ → R)
    {L M q r : ℕ} (hqM : q ≤ M) (hrM : r ≤ M) :
    (∑ k ∈ (Finset.Ioc L (L * M)).filter (fun k => Nat.lcm q r ∣ k),
      if k ≤ L * q ∧ k ≤ L * r then F k else 0) =
      ∑ k ∈ (Finset.Ioc L (L * min q r)).filter (fun k => Nat.lcm q r ∣ k), F k := by
  classical
  let small := (Finset.Ioc L (L * min q r)).filter (fun k => Nat.lcm q r ∣ k)
  let big := (Finset.Ioc L (L * M)).filter (fun k => Nat.lcm q r ∣ k)
  have hminM : min q r ≤ M := by
    rcases le_total q r with hqr | hrq
    · simpa [min_eq_left hqr] using hqM
    · simpa [min_eq_right hrq] using hrM
  have hcond : ∀ k : ℕ,
      (k ≤ L * q ∧ k ≤ L * r) ↔ k ≤ L * min q r := by
    intro k
    rcases le_total q r with hqr | hrq
    · rw [min_eq_left hqr]
      constructor
      · exact fun h => h.1
      · intro hk
        exact ⟨hk, hk.trans (Nat.mul_le_mul_left L hqr)⟩
    · rw [min_eq_right hrq]
      constructor
      · exact fun h => h.2
      · intro hk
        exact ⟨hk.trans (Nat.mul_le_mul_left L hrq), hk⟩
  have hsub : small ⊆ big := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
    exact ⟨⟨hk.1.1, hk.1.2.trans (Nat.mul_le_mul_left L hminM)⟩, hk.2⟩
  have hzero : ∀ k ∈ big, k ∉ small →
      (if k ≤ L * q ∧ k ≤ L * r then F k else 0) = 0 := by
    intro k hkbig hknsmall
    have hncond : ¬(k ≤ L * q ∧ k ≤ L * r) := by
      intro hkcond
      apply hknsmall
      rw [Finset.mem_filter, Finset.mem_Ioc]
      rw [Finset.mem_filter, Finset.mem_Ioc] at hkbig
      exact ⟨⟨hkbig.1.1, (hcond k).mp hkcond⟩, hkbig.2⟩
    simp [hncond]
  have hrestrict :
      (∑ k ∈ small, if k ≤ L * q ∧ k ≤ L * r then F k else 0) =
        ∑ k ∈ big, if k ≤ L * q ∧ k ≤ L * r then F k else 0 :=
    Finset.sum_subset hsub hzero
  rw [show
      (∑ k ∈ big, if k ≤ L * q ∧ k ≤ L * r then F k else 0) =
        ∑ k ∈ small, if k ≤ L * q ∧ k ≤ L * r then F k else 0 from
      hrestrict.symm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkupper : k ≤ L * min q r := by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    exact hk.1.2
  simp [(hcond k).mpr hkupper]

theorem barbanVehovIncludedLongHarmonicKernel_eq_minEndpoint
    {L M q r : ℕ} (hqM : q ≤ M) (hrM : r ≤ M) :
    barbanVehovIncludedLongHarmonicKernel L (L * M) q r =
      barbanVehovLongHarmonicKernel L (L * min q r) q r := by
  exact sum_Ioc_lcm_if_le_mul_pair_eq_minEndpoint
    (fun k => 1 / (k : ℝ)) hqM hrM

theorem barbanVehovIncludedLongFirstLogKernel_eq_minEndpoint
    {L M q r : ℕ} (hqM : q ≤ M) (hrM : r ≤ M) :
    barbanVehovIncludedLongFirstLogKernel L (L * M) q r =
      barbanVehovLongFirstLogKernel L (L * min q r) q r := by
  exact sum_Ioc_lcm_if_le_mul_pair_eq_minEndpoint
    (fun k => Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)) hqM hrM

theorem barbanVehovIncludedLongSecondLogKernel_eq_minEndpoint
    {L M q r : ℕ} (hqM : q ≤ M) (hrM : r ≤ M) :
    barbanVehovIncludedLongSecondLogKernel L (L * M) q r =
      barbanVehovLongSecondLogKernel L (L * min q r) q r := by
  exact sum_Ioc_lcm_if_le_mul_pair_eq_minEndpoint
    (fun k => Real.log (((k / q : ℕ) : ℝ)) *
      Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)) hqM hrM

end

end RHTower.Sieve
