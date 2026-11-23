import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.SpectralBand

/-! # Unique spectra at the two relative endpoints -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

theorem relativeReading_hot (f : SpectralResponse) (r : ℕ) : relativeReading f (hotEdge r) = 0 := by
  simp [relativeReading,spectralDrop,hotEdge]

theorem relativeReading_cold (f : SpectralResponse) (r : ℕ) : relativeReading f (coldEdge r) = relativeHead f r :=
  (hasSum_edge_drop f r).tsum_eq

theorem relativeReading_bounds (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    relativeReading f b ∈ Icc 0 (relativeHead f r) :=
  ⟨tsum_nonneg (drop_nonneg f b),((summable_spectralDrop f b).tsum_le_tsum (drop_le_edge f b)
    (hasSum_edge_drop f r).summable).trans_eq (hasSum_edge_drop f r).tsum_eq⟩

private theorem term_zero_of_zero_sum {g : ℕ → ℝ} (hg : Summable g) (hn : ∀ n, 0 ≤ g n)
    (he : ∑' n, g n = 0) (n : ℕ) : g n = 0 := by
  by_contra h
  exact (hg.tsum_pos hn n (lt_of_le_of_ne (hn n) (Ne.symm h))).ne' he

/-- Strictly increasing detectors have the same unique zero-loss spectrum. -/
theorem relativeReading_zero_iff (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    relativeReading f b = 0 ↔ b = hotEdge r := by
  constructor
  · intro he
    funext n
    apply Subtype.ext
    have h := term_zero_of_zero_sum (summable_spectralDrop f b) (drop_nonneg f b) he n
    exact f.inc.injOn (band_in_unit b n) (occupation_in_unit n) (sub_eq_zero.mp h).symm
  · rintro rfl
    exact relativeReading_hot f r

/-- At the ceiling every occupation lies at the lower interlacing endpoint. -/
theorem relativeReading_head_iff (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    relativeReading f b = relativeHead f r ↔ b = coldEdge r := by
  constructor
  · intro he
    let g (n : ℕ) := spectralDrop f (coldEdge r) n-spectralDrop f b n
    have hs : Summable g := (hasSum_edge_drop f r).summable.sub (summable_spectralDrop f b)
    have hsum : ∑' n, g n = 0 := by
      rw [show (∑' n, g n) = relativeReading f (coldEdge r)-relativeReading f b from
        (hasSum_edge_drop f r).summable.tsum_sub (summable_spectralDrop f b),relativeReading_cold,he,sub_self]
    funext n
    apply Subtype.ext
    have h := term_zero_of_zero_sum hs (fun n => sub_nonneg.mpr (drop_le_edge f b n)) hsum n
    have eqn := sub_eq_zero.mp h
    exact f.inc.injOn (band_in_unit b n) (occupation_in_unit (n+r)) (sub_right_inj.mp eqn).symm
  · rintro rfl
    exact relativeReading_cold f r

theorem reading_interior_iff (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) :
    relativeReading f b ∈ Ioo 0 (relativeHead f r) ↔ b ≠ hotEdge r ∧ b ≠ coldEdge r := by
  obtain ⟨hl,hu⟩ := relativeReading_bounds f b
  constructor
  · rintro ⟨h₀,hH⟩
    exact ⟨fun e => h₀.ne' ((relativeReading_zero_iff f b).mpr e),fun e => hH.ne ((relativeReading_head_iff f b).mpr e)⟩
  · rintro ⟨h₀,hH⟩
    exact ⟨lt_of_le_of_ne hl (fun e => h₀ ((relativeReading_zero_iff f b).mp e.symm)),
      lt_of_le_of_ne hu (fun e => hH ((relativeReading_head_iff f b).mp e))⟩

#print axioms relativeReading_zero_iff
#print axioms relativeReading_head_iff
#print axioms reading_interior_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
