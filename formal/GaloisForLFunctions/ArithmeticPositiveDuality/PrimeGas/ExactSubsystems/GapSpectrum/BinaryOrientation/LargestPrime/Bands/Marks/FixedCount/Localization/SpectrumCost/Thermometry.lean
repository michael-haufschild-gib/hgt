import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.LocalCost

/-! # Inverse temperature from two measured neighborhood costs -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Filter Topology

/-- Infimum of the measured neighborhood exponents for an admissible spectrum. -/
def observedCost {c d : ℝ} {k : ℕ} (β : ℝ) (v : ↥(orderedBand c d k)) :=
  sInf (neighborhoodExponents c d β v.val)

theorem observedCost_eq {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (β : ℝ)
    (v : ↥(orderedBand c d k)) : observedCost β v = rate c d β v.val := by
  have hx := lt_add_of_pos_right (rate c d β v.val) zero_lt_one
  exact (local_rate hc hcd β hk v.property).csInf_eq
    ⟨_,fun _ hG hvG => open_lower hc hcd β hk hG v.property hvG _ hx⟩

/-- Subtracting two local costs cancels the pressure and isolates the additive energy difference. -/
theorem cost_difference {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (β : ℝ)
    (v w : ↥(orderedBand c d k)) :
    observedCost β v-observedCost β w = (β-1)*((∑ i, v.val i)-(∑ i, w.val i)) := by
  rw [observedCost_eq hc hcd hk,observedCost_eq hc hcd hk,rate,rate]
  ring

/-- Off criticality the total energy classifies indistinguishability by exponential cost. -/
theorem same_cost_iff {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) {β : ℝ} (hβ : β ≠ 1)
    (v w : ↥(orderedBand c d k)) :
    observedCost β v = observedCost β w ↔ (∑ i, v.val i) = ∑ i, w.val i := by
  rw [← sub_eq_zero,cost_difference hc hcd hk,mul_eq_zero,or_iff_right (sub_ne_zero.mpr hβ),sub_eq_zero]

/-- Any two admissible configurations of different total energy suffice for thermometry. -/
theorem temperature_from_costs {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k)
    (β : ℝ) (v w : ↥(orderedBand c d k)) (hE : (∑ i, v.val i) ≠ ∑ i, w.val i) :
    1+(observedCost β v-observedCost β w)/((∑ i, v.val i)-(∑ i, w.val i)) = β := by
  rw [cost_difference hc hcd hk,mul_div_cancel_right₀ _ (sub_ne_zero.mpr hE)]
  ring

/-- Choosing the two endpoint vectors gives a calibrated thermometer on every nontrivial band. -/
theorem endpoint_thermometry {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (β : ℝ) :
    1+(observedCost β ⟨fun _ : Fin k => d,constant_mem ⟨hcd.le,le_rfl⟩ k⟩-
       observedCost β ⟨fun _ : Fin k => c,constant_mem ⟨le_rfl,hcd.le⟩ k⟩)/(k*(d-c)) = β := by
  rw [cost_difference hc hcd hk]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_sub]
  rw [mul_div_cancel_right₀ _ (mul_pos (Nat.cast_pos.mpr hk) (sub_pos.mpr hcd)).ne']
  ring

/-- Equality of just the two endpoint neighborhood costs characterizes isometric splitting. -/
theorem split_isometric_iff_endpoint_costs {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
    observedCost (2*s.re) ⟨fun _ : Fin k => d,constant_mem ⟨hcd.le,le_rfl⟩ k⟩ =
    observedCost (2*s.re) ⟨fun _ : Fin k => c,constant_mem ⟨le_rfl,hcd.le⟩ k⟩ := by
  rw [split_isometric_iff]
  constructor
  · intro hs
    rw [show 2*s.re=1 by rw [hs]; ring,observedCost_eq hc hcd hk,observedCost_eq hc hcd hk,rate_one,rate_one]
  · intro he
    have H := endpoint_thermometry hc hcd hk (2*s.re)
    rw [he,sub_self,zero_div,add_zero] at H
    linarith only [H]

#print axioms observedCost_eq
#print axioms same_cost_iff
#print axioms temperature_from_costs
#print axioms endpoint_thermometry
#print axioms split_isometric_iff_endpoint_costs

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
