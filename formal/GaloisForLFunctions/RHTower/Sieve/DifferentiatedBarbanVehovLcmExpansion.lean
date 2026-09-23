import GaloisForLFunctions.RHTower.Sieve.BarbanVehovDifferentiatedConvolution

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Swap an outer positive interval with two divisor fibres. -/
theorem sum_Ioc_divisorPair_eq_lcmKernel
    {R : Type*} [AddCommMonoid R] {L U : ℕ} (hL : 0 < L)
    (F : ℕ → ℕ × ℕ → R) :
    (∑ k ∈ Finset.Ioc L U, ∑ p ∈ k.divisors ×ˢ k.divisors, F k p) =
      ∑ p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U),
        ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm p.1 p.2 ∣ k), F k p := by
  classical
  have hmem : ∀ (k : ℕ) (p : ℕ × ℕ),
      k ∈ Finset.Ioc L U ∧ p ∈ k.divisors ×ˢ k.divisors ↔
        k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm p.1 p.2 ∣ k) ∧
          p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U) := by
    intro k p
    constructor
    · rintro ⟨hk, hp⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hkpos : 0 < k := hL.trans (Finset.mem_Ioc.mp hk).1
      have hd1 : p.1 ∣ k := Nat.dvd_of_mem_divisors hp1
      have hd2 : p.2 ∣ k := Nat.dvd_of_mem_divisors hp2
      refine ⟨Finset.mem_filter.mpr ⟨hk, Nat.lcm_dvd hd1 hd2⟩,
        Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp1,
          (Nat.le_of_dvd hkpos hd1).trans (Finset.mem_Ioc.mp hk).2⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp2,
          (Nat.le_of_dvd hkpos hd2).trans (Finset.mem_Ioc.mp hk).2⟩
    · rintro ⟨hkf, hp⟩
      obtain ⟨hk, hlcm⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hk0 : k ≠ 0 := (hL.trans (Finset.mem_Ioc.mp hk).1).ne'
      refine ⟨hk, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_left _ _).trans hlcm, hk0⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_right _ _).trans hlcm, hk0⟩
  exact Finset.sum_comm' hmem

/-- Harmonic mass of multiples of an lcm on a long window. -/
def barbanVehovLongHarmonicKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k), 1 / (k : ℝ)

/-- First complementary-divisor log moment on an lcm fibre. -/
def barbanVehovLongFirstLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)

/-- Second complementary-divisor log moment on an lcm fibre. -/
def barbanVehovLongSecondLogKernel (L U q r : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ioc L U).filter (fun k => Nat.lcm q r ∣ k),
    Real.log (((k / q : ℕ) : ℝ)) * Real.log (((k / r : ℕ) : ℝ)) / (k : ℝ)

/-- A bilinear Barban--Vehov lcm form only sees the square of the weight support. -/
theorem sum_barbanVehovWeight_pair_support {M U : ℕ} (hMU : M ≤ U)
    (K : ℕ × ℕ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U),
      barbanVehovWeight M p.1 * barbanVehovWeight M p.2 * K p) =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 * K p := by
  classical
  have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 U := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1,
      (Finset.mem_Icc.mp hq).2.trans hMU⟩
  have hprod : (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) ⊆
      (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨hsub (Finset.mem_product.mp hp).1,
      hsub (Finset.mem_product.mp hp).2⟩
  have hvanish : ∀ p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U),
      p ∉ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) →
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 * K p = 0 := by
    intro p hp hpnot
    have hout : p.1 ∉ Finset.Icc 1 M ∨ p.2 ∉ Finset.Icc 1 M := by
      simpa only [Finset.mem_product, not_and_or] using hpnot
    rcases hout with hout | hout
    · have hpU := (Finset.mem_product.mp hp).1
      have hgt : M < p.1 := by
        have hp1 := (Finset.mem_Icc.mp hpU).1
        simpa [Finset.mem_Icc, hp1, not_le] using hout
      rw [barbanVehovWeight, if_neg (not_le.mpr hgt), zero_mul, zero_mul]
    · have hpU := (Finset.mem_product.mp hp).2
      have hgt : M < p.2 := by
        have hp1 := (Finset.mem_Icc.mp hpU).1
        simpa [Finset.mem_Icc, hp1, not_le] using hout
      have hz : barbanVehovWeight M p.2 = 0 := by
        rw [barbanVehovWeight, if_neg (not_le.mpr hgt)]
      rw [hz, mul_zero, zero_mul]
  exact (Finset.sum_subset hprod hvanish).symm

/-- Exact lcm quadratic form for the base long moment. -/
def barbanVehovFullLongBaseLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernel L (L * M) p.1 p.2

/-- Exact lcm form for the base/differentiated cross moment. -/
def barbanVehovFullLongCrossLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernel L (L * M) p.1 p.2

/-- Exact lcm form for the differentiated square moment. -/
def barbanVehovFullLongDerivativeLcm (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernel L (L * M) p.1 p.2

theorem levinsonCriticalDetectorFullLongBaseMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorFullLongBaseMoment L M =
      barbanVehovFullLongBaseLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorFullLongBaseMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovCoeff M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ) := by
    intro k hk
    rw [barbanVehovCoeff, sq, Finset.sum_mul_sum, Finset.sum_product,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter (fun k => Nat.lcm p.1 p.2 ∣ k),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 / (k : ℝ)) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongHarmonicKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovLongHarmonicKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovFullLongBaseLcm]

theorem levinsonCriticalDetectorFullLongCrossMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorFullLongCrossMoment L M =
      barbanVehovFullLongCrossLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorFullLongCrossMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovCoeff M k * barbanVehovDifferentiatedCoeff M k / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ) := by
    intro k hk
    rw [barbanVehovCoeff,
      barbanVehovDifferentiatedCoeff_eq_neg_sum_weight_logNatDiv
        (hLpos.trans (Finset.mem_Ioc.mp hk).1)]
    rw [mul_neg, Finset.sum_mul_sum, Finset.sum_product]
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter (fun k => Nat.lcm p.1 p.2 ∣ k),
          -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (-barbanVehovLongFirstLogKernel L (L * M) p.1 p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovLongFirstLogKernel, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrepack]
  rw [sum_barbanVehovWeight_pair_support hMprod]
  rw [barbanVehovFullLongCrossLcm]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem levinsonCriticalDetectorFullLongDerivativeMoment_eq_lcm
    {L M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    RHTower.levinsonCriticalDetectorFullLongDerivativeMoment L M =
      barbanVehovFullLongDerivativeLcm L M := by
  classical
  have hLpos : 0 < L := (Nat.zero_lt_of_lt hM).trans_le hML
  have hMprod : M ≤ L * M :=
    hML.trans (Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM))
  rw [RHTower.levinsonCriticalDetectorFullLongDerivativeMoment]
  have hexpand : ∀ k ∈ Finset.Ioc L (L * M),
      barbanVehovDifferentiatedCoeff M k ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (Real.log (((k / p.1 : ℕ) : ℝ)) *
              Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ) := by
    intro k hk
    rw [barbanVehovDifferentiatedCoeff_eq_neg_sum_weight_logNatDiv
      (hLpos.trans (Finset.mem_Ioc.mp hk).1)]
    rw [neg_sq, sq, Finset.sum_mul_sum, Finset.sum_product]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_divisorPair_eq_lcmKernel hLpos]
  have hrepack :
      (∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
        ∑ k ∈ (Finset.Ioc L (L * M)).filter (fun k => Nat.lcm p.1 p.2 ∣ k),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            (Real.log (((k / p.1 : ℕ) : ℝ)) *
              Real.log (((k / p.2 : ℕ) : ℝ))) / (k : ℝ)) =
        ∑ p ∈ (Finset.Icc 1 (L * M)) ×ˢ (Finset.Icc 1 (L * M)),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            barbanVehovLongSecondLogKernel L (L * M) p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [barbanVehovLongSecondLogKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrepack, sum_barbanVehovWeight_pair_support hMprod,
    barbanVehovFullLongDerivativeLcm]

end


end RHTower.Sieve
