import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ExtremalSpectra
import Mathlib.Topology.Order.IntermediateValue

/-! # Transfer between measurements on the same connected family of spectra

A detector spanning its strict interval identifies both extreme spectra
in the compact closure. Every other detector then spans its own interval.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Extremizing one response forces both endpoint spectra into the physical closure. -/
theorem edges_in_closure {r : ℕ} (S : Set (SpectralBand r)) (f : SpectralResponse)
    (hH : 0 < relativeHead f r) (hs : Ioo 0 (relativeHead f r) ⊆ relativeReading f '' S) :
    hotEdge r ∈ closure S ∧ coldEdge r ∈ closure S := by
  have hf := continuous_relativeReading f r
  have hclosed : IsClosed (relativeReading f '' closure S) := (isClosed_closure.isCompact.image hf).isClosed
  have hinc : Icc 0 (relativeHead f r) ⊆ relativeReading f '' closure S := by
    rw [← closure_Ioo hH.ne]
    exact closure_minimal (hs.trans (image_mono subset_closure)) hclosed
  obtain ⟨u,hu,he⟩ := hinc ⟨le_rfl,hH.le⟩
  obtain ⟨v,hv,he'⟩ := hinc ⟨hH.le,le_rfl⟩
  exact ⟨(relativeReading_zero_iff f u).mp he ▸ hu,(relativeReading_head_iff f v).mp he' ▸ hv⟩

/-- Both boundary limits and connectedness imply attainment of every strictly intermediate reading. -/
theorem open_interval_of_edges {r : ℕ} {S : Set (SpectralBand r)} (hs : IsPreconnected S)
    (hu : hotEdge r ∈ closure S) (hl : coldEdge r ∈ closure S) (f : SpectralResponse) :
    Ioo 0 (relativeHead f r) ⊆ relativeReading f '' S := by
  letI : NeBot (𝓝[S] (hotEdge r)) := mem_closure_iff_nhdsWithin_neBot.mp hu
  letI : NeBot (𝓝[S] (coldEdge r)) := mem_closure_iff_nhdsWithin_neBot.mp hl
  have hf := continuous_relativeReading f r
  have h₀ := hf.continuousWithinAt (x := hotEdge r) (s := S)
  have hH := hf.continuousWithinAt (x := coldEdge r) (s := S)
  have h := hs.intermediate_value_Ioo (show 𝓝[S] (hotEdge r) ≤ 𝓟 S from inf_le_right)
    (show 𝓝[S] (coldEdge r) ≤ 𝓟 S from inf_le_right) hf.continuousOn h₀.tendsto hH.tendsto
  simpa only [relativeReading_hot,relativeReading_cold] using h

#print axioms edges_in_closure
#print axioms open_interval_of_edges

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
