import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ExtremalSpectra

/-! # Detector-independent stability at both interlacing edges -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

private theorem tendsto_of_single_fiber {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {F : X → Y} (hF : Continuous F) {p : X}
    (hu : ∀ x, F x = F p → x = p) {b : ι → X} {l : Filter ι} (h : Tendsto (F ∘ b) l (𝓝 (F p))) :
    Tendsto b l (𝓝 p) := by
  apply tendsto_nhds.mpr
  intro U hU hp
  have hclosed : IsClosed (F '' Uᶜ) := (hU.isClosed_compl.isCompact.image hF).isClosed
  have hnot : F p ∈ (F '' Uᶜ)ᶜ := by
    rintro ⟨x,hx,he⟩
    exact hx (by rw [hu x he]; exact hp)
  filter_upwards [h (hclosed.isOpen_compl.mem_nhds hnot)] with i hi
  by_contra hn
  exact hi ⟨b i,hn,rfl⟩

/-- Vanishing relative cost is equivalent to convergence of all occupations to the unshifted spectrum. -/
theorem relativeReading_tendsto_zero_iff {r : ℕ} (f : SpectralResponse) {ι : Type*}
    (b : ι → SpectralBand r) (l : Filter ι) :
    Tendsto (relativeReading f ∘ b) l (𝓝 0) ↔ Tendsto b l (𝓝 (hotEdge r)) := by
  rw [← relativeReading_hot f r]
  constructor
  · intro h
    exact tendsto_of_single_fiber (continuous_relativeReading f r)
      (fun x hx => (relativeReading_zero_iff f x).mp (hx.trans (relativeReading_hot f r))) h
  · exact fun h => (continuous_relativeReading f r).continuousAt.tendsto.comp h

/-- Saturating the ceiling is equivalent to convergence of all occupations to the shifted spectrum. -/
theorem relativeReading_tendsto_head_iff {r : ℕ} (f : SpectralResponse) {ι : Type*}
    (b : ι → SpectralBand r) (l : Filter ι) :
    Tendsto (relativeReading f ∘ b) l (𝓝 (relativeHead f r)) ↔ Tendsto b l (𝓝 (coldEdge r)) := by
  rw [← relativeReading_cold f r]
  constructor
  · intro h
    exact tendsto_of_single_fiber (continuous_relativeReading f r)
      (fun x hx => (relativeReading_head_iff f x).mp (hx.trans (relativeReading_cold f r))) h
  · exact fun h => (continuous_relativeReading f r).continuousAt.tendsto.comp h

#print axioms relativeReading_tendsto_zero_iff
#print axioms relativeReading_tendsto_head_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
