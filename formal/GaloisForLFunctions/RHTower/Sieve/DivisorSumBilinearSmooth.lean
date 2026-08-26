import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquareSmooth

open Finset GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

theorem sum_mul_divisorSum_eq_lcm_bilinear
    (N : ℕ) (a b : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N,
        (∑ m ∈ k.divisors, a m) * (∑ n ∈ k.divisors, b n) =
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        a p.1 * b p.2 * ((N / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  classical
  have hexp : ∀ k ∈ Finset.Icc 1 N,
      (∑ m ∈ k.divisors, a m) * (∑ n ∈ k.divisors, b n) =
        ∑ p ∈ k.divisors ×ˢ k.divisors, a p.1 * b p.2 := by
    intro k _
    rw [Finset.sum_mul_sum, Finset.sum_product]
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (k : ℕ) (p : ℕ × ℕ),
      k ∈ Finset.Icc 1 N ∧ p ∈ k.divisors ×ˢ k.divisors
        ↔ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.lcm p.1 p.2 ∣ k)
            ∧ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    intro k p
    constructor
    · rintro ⟨hk, hp⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      have hd1 : p.1 ∣ k := Nat.dvd_of_mem_divisors hp1
      have hd2 : p.2 ∣ k := Nat.dvd_of_mem_divisors hp2
      have hk0 : 0 < k := hk1
      refine ⟨Finset.mem_filter.mpr ⟨hk, Nat.lcm_dvd hd1 hd2⟩,
        Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp1,
          le_trans (Nat.le_of_dvd hk0 hd1) hkN⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp2,
          le_trans (Nat.le_of_dvd hk0 hd2) hkN⟩
    · rintro ⟨hkf, hp⟩
      obtain ⟨hk, hlcm⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      have hk0 : k ≠ 0 := by omega
      refine ⟨hk, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_left _ _) hlcm, hk0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_lcm_right _ _) hlcm, hk0⟩
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp11, -⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hp21, -⟩ := Finset.mem_Icc.mp hp2
  have hlcmpos : 0 < Nat.lcm p.1 p.2 := Nat.pos_of_ne_zero (by
    intro h
    rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1 <;> omega)
  rw [Finset.sum_const, card_filter_dvd_Icc hlcmpos, nsmul_eq_mul]
  ring

theorem abs_sum_mul_divisorSum_sub_lcm_main_le
    (N : ℕ) (a b : ℕ → ℝ) :
    |(∑ k ∈ Finset.Icc 1 N,
        (∑ m ∈ k.divisors, a m) * (∑ n ∈ k.divisors, b n)) -
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        a p.1 * b p.2 * ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ))| ≤
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        |a p.1| * |b p.2| := by
  rw [sum_mul_divisorSum_eq_lcm_bilinear N a b, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp11, -⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hp21, -⟩ := Finset.mem_Icc.mp hp2
  have hlcmpos : 0 < Nat.lcm p.1 p.2 := Nat.pos_of_ne_zero (by
    intro h
    rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1 <;> omega)
  have hdiff : a p.1 * b p.2 * ((N / Nat.lcm p.1 p.2 : ℕ) : ℝ) -
      a p.1 * b p.2 * ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ)) =
    (a p.1 * b p.2) *
      (((N / Nat.lcm p.1 p.2 : ℕ) : ℝ) -
        (N : ℝ) / (Nat.lcm p.1 p.2 : ℝ)) := by ring
  rw [hdiff, abs_mul, abs_mul]
  exact mul_le_of_le_one_right (by positivity) (abs_natDiv_sub_div_le hlcmpos)

end RHTower.Sieve
