import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensityTwinCarriesTheConductorSeries

/-!
# The zero-density endpoint has positive Euler mass

A prime set with logarithmic mass `O((1 + log N)^α)`, `0 ≤ α < 1`, has positive Euler
mass: the positive Wirsing lower bound is linear in `log N`. Its conductor classification
therefore follows from the full positive-density resolvent. Together with the positive-κ
theorem, this closes the endpoint of the power-error regime `0 ≤ κ < 1/4`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- Sublinear power growth of prime logarithmic mass forces positive Euler density. -/
theorem primeSetHarmonicDensity_pos_of_logMass_sublinear (P : Set ℕ) {C α : ℝ}
    (hα : 0 ≤ α) (hα1 : α < 1)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n| ≤ C * (1 + Real.log n) ^ α) :
    0 < primeSetHarmonicDensity P := by
  obtain ⟨c, hc, N₀, hN₀⟩ :=
    exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip P (κ := 0) (by norm_num)
      hα (by simpa using hα1) (by simpa using hP)
  have hbound : ∀ᶠ N : ℕ in atTop, c / 2 ≤ harmonicCorrelation (primeSetFlip P) N := by
    filter_upwards [eventually_ge_atTop (max 3 N₀)] with N hN
    have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
    have hlog : 1 ≤ Real.log N := one_le_log_of_three_le hN3
    have hsum : c * Real.log N ≤ gaugeHarmonicSum (primeSetFlip P) N := by
      simpa only [mul_zero, sub_zero, Real.rpow_one] using hN₀ N ((le_max_right _ _).trans hN)
    have hHupper : gaugeHarmonicSum (fun _ => (1 : ℝ)) N ≤ 2 * Real.log N := by
      have h := (abs_le.mp (abs_harmonic_sub_log_le N)).2
      linarith only [h, hlog]
    rw [harmonicCorrelation, le_div_iff₀ (gaugeHarmonicSum_one_pos (by omega))]
    have hmul := mul_le_mul_of_nonneg_left hHupper (half_pos hc).le
    nlinarith only [hmul, hsum]
  exact (half_pos hc).trans_le
    (ge_of_tendsto (primeSetFlip_harmonicCorrelation_tendsto P) hbound)

/-- At positive Euler mass, a finite conductor packet exactly detects separation. -/
theorem hodgeSeparates_primeSetFlip_iff_packet_of_positive_mass (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) :
    HodgeSeparates (primeSetFlip P) ↔ ∃ s, 0 < s ∧ s < 2 * Real.log 2 ∧ ∃ S : Finset ℕ,
      (∀ m ∈ S, 2 ≤ m) ∧ 1 / s < ∑ m ∈ S, primeSetSpectralWeight P m /
        (ramanujanAdjunctionEnergy m - γ - s) := by
  constructor
  · intro hsep
    obtain ⟨s, hs, hs2, hpos⟩ := (hodgeSeparates_primeSetFlip_iff_secular_pos P hc).mp hsep
    have htail := summable_primeSetSecularTail P hc hs hs2
    have hgt : 1 / s < ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
      dsimp only [primeSetSecular] at hpos
      linarith only [hpos]
    obtain ⟨K, hK⟩ := (htail.hasSum.tendsto_sum_nat.eventually_const_lt hgt).exists
    refine ⟨s, hs, hs2, (range K).image (· + 2), ?_, ?_⟩
    · intro m hm
      obtain ⟨k, _, rfl⟩ := mem_image.mp hm
      omega
    · rwa [sum_image fun a _ b _ h => by omega]
  · rintro ⟨s, hs, hs2, S, hS, h⟩
    exact hodgeSeparates_primeSetFlip_of_packet P hs hs2 S hS h

/-- The finite-packet classification includes the zero-density endpoint with the same
power-error condition as in the positive-density-exponent regime. -/
theorem hodgeSeparates_primeSetFlip_iff_packet_of_nonneg_logDensity
    (P : Set ℕ) {κ C α : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < 1 / 4)
    (hα : 0 ≤ α) (hακ : α < 1 - 2 * κ)
    (hP : ∀ n, 1 ≤ n → |primeSetLogMass P n - κ * Real.log n| ≤ C * (1 + Real.log n) ^ α) :
    HodgeSeparates (primeSetFlip P) ↔ ∃ s, 0 < s ∧ s < 2 * Real.log 2 ∧ ∃ S : Finset ℕ,
      (∀ m ∈ S, 2 ≤ m) ∧ 1 / s < ∑ m ∈ S, primeSetSpectralWeight P m /
        (ramanujanAdjunctionEnergy m - γ - s) := by
  rcases hκ0.eq_or_lt with rfl | hκpos
  · exact hodgeSeparates_primeSetFlip_iff_packet_of_positive_mass P
      (primeSetHarmonicDensity_pos_of_logMass_sublinear P hα
        (by simpa using hακ) (by simpa using hP))
  · exact hodgeSeparates_primeSetFlip_iff_packet P hκpos hκ hα hακ hP

end GaloisForLFunctions.RenormalizedIntersectionTheory

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.primeSetHarmonicDensity_pos_of_logMass_sublinear
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.hodgeSeparates_primeSetFlip_iff_packet_of_nonneg_logDensity
