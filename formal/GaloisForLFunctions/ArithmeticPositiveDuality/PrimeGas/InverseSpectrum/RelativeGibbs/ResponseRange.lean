import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.LaneSpectra
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.EndpointTransfer
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FiniteRange

/-! # Exact relative range of all increasing continuous detectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private theorem lane_quadratic_covers (r : ℕ) :
    Ioo 0 (relativeHead quadraticResponse (r+1)) ⊆ relativeReading quadraticResponse '' laneSpectra (r+1) := by
  rw [quadratic_head]
  intro y hy
  let t := y/traceCeiling (r+1)
  have hc := traceCeiling_pos (Nat.succ_pos r)
  have ht : 0 < t := div_pos hy.1 hc
  have ht₁ : t < 1 := (div_lt_one hc).mpr hy.2
  have hex (j : Fin (r+1)) : ∃ v : MissingWave,
      lineLoss (extendModes (progression j) v.val) = t*occupationWeight j.val^2 := by
    have hp := sq_pos_of_pos (occupationWeight_pos j.val)
    exact progression_realizes j ⟨mul_pos ht hp,mul_lt_of_lt_one_left hp ht₁⟩
  choose u hu using hex
  refine ⟨laneSpectrum u,⟨u,rfl⟩,?_⟩
  have hsum : (∑ j : Fin (r+1), occupationWeight j.val^2) = traceCeiling (r+1) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => occupationWeight k^2) (r+1)
  rw [lane_quadratic]
  simp only [laneWaves,hu,← Finset.mul_sum,hsum]
  exact div_mul_cancel₀ _ hc.ne'

/-- Both interlacing edges are limits of actual conserving omission spectra. -/
theorem physical_spectral_edges (r : ℕ) :
    hotEdge (r+1) ∈ closure (laneSpectra (r+1)) ∧ coldEdge (r+1) ∈ closure (laneSpectra (r+1)) :=
  edges_in_closure _ quadraticResponse (by rw [quadratic_head]; exact traceCeiling_pos (Nat.succ_pos r))
    (lane_quadratic_covers r)

/-- Any strictly increasing continuous response has exactly its predicted open interval of losses. -/
theorem responseAtRank_succ (f : SpectralResponse) (r : ℕ) :
    responseAtRank f (r+1) = Ioo 0 (relativeHead f (r+1)) := by
  ext y
  constructor
  · rintro ⟨P,hd,hc,rfl⟩
    exact physical_reading_interior f P (Nat.succ_pos r) hd hc
  · intro hy
    obtain ⟨hu,hl⟩ := physical_spectral_edges r
    obtain ⟨_,⟨u,rfl⟩,he⟩ := open_interval_of_edges (laneSpectra_preconnected _) hu hl f hy
    exact he ▸ lane_reading_mem f u

theorem responseAtRank_zero (f : SpectralResponse) : responseAtRank f 0 = {0} := by
  have h (b : SpectralBand 0) : relativeReading f b = 0 := by
    obtain ⟨hl,hu⟩ := relativeReading_bounds f b
    exact le_antisymm (by simpa only [relativeHead,Finset.range_zero,Finset.sum_empty] using hu) hl
  ext y
  constructor
  · rintro ⟨P,hd,hc,rfl⟩
    exact h _
  · rintro rfl
    obtain ⟨P,hd,hc,_⟩ := (show (0:ℝ) ∈ lossesAtRank 0 by simpa only [lossesAtRank_zero] using (mem_singleton (0:ℝ)))
    exact ⟨P,hd,hc,h _⟩

#print axioms physical_spectral_edges
#print axioms responseAtRank_succ
#print axioms responseAtRank_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
