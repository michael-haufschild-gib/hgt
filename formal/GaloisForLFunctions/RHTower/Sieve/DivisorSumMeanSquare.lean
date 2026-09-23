import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# The mean square of a divisor sum as an lcm-weighted quadratic form

Expanding the square of a divisor sum and counting multiples turns
`∑_{k ≤ N} (∑_{m ∣ k} a m)²` into the quadratic form `∑_{m₁, m₂ ≤ N} a(m₁) a(m₂) ⌊N / [m₁,m₂]⌋`.
This is the first structural step of the Barban–Vehov / Graham mean square, and it is purely
combinatorial: no property of the coefficients is used.
-/

open Finset GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

theorem card_filter_dvd_Icc {d N : ℕ} (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun k => d ∣ k)).card = N / d := by
  classical
  rw [multiples_Icc hd N,
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd h)]
  simp

/-- **The divisor-sum mean square as an lcm quadratic form.** -/
theorem sum_sq_divisorSum_eq_lcm_quadratic (N : ℕ) (a : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, a m) ^ (2 : ℕ)
      = ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          a p.1 * a p.2 * ((N / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  classical
  have hexp : ∀ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, a m) ^ (2 : ℕ)
      = ∑ p ∈ k.divisors ×ˢ k.divisors, a p.1 * a p.2 := by
    intro k _
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
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
      refine ⟨Finset.mem_filter.mpr ⟨hk, Nat.lcm_dvd hd1 hd2⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
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

end RHTower.Sieve
