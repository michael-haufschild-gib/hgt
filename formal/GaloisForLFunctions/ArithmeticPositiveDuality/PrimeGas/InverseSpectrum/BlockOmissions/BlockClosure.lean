import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockDiagonal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.PhysicalLimits

/-! # Every consecutive block deletion is a limit of physical spectra at the same rank -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Exact rank is maintained while the missing directions tend to the prescribed finite block. -/
theorem blockSpectrum_mem_closure (N r : ℕ) : blockSpectrum N r ∈ closure (physicalSpectra r) := by
  obtain ⟨v,hv⟩ := exists_missingWave_tendsto (modeWave 1)
  let f := skipLabel 0 N
  let u (n : ℕ) (_ : Fin r) := v n
  let W (n : ℕ) (i : Fin r) := extendModes f (laneWaves (u n) i)
  let V (i : Fin r) := modeWave (blockLabel N r i)
  have hn (n : ℕ) (i : Fin r) : W n i ≠ 0 := by
    intro h
    have he := (extendModes f).injective (h.trans (map_zero _).symm)
    exact missingWave_ne_zero (v n) ((extendModes (progression i)).injective (he.trans (map_zero _).symm))
  have ho (n : ℕ) (i j : Fin r) (h : i ≠ j) : inner ℂ (W n i) (W n j) = 0 := by
    change inner ℂ (extendModes f _) (extendModes f _) = 0
    rw [(extendModes f).inner_map_map]
    exact extendModes_orthogonal (progression_separate h) _ _
  have hV (i : Fin r) : V i ≠ 0 := norm_ne_zero_iff.mp ((modeWave_norm _).trans_ne one_ne_zero)
  have hO (i j : Fin r) (h : i ≠ j) : inner ℂ (V i) (V j) = 0 := by
    have hne : blockLabel N r i ≠ blockLabel N r j := (blockLabel N r).injective.ne h
    simp [V,modeWave,lp.inner_single_left,lp.single_apply,Pi.single_eq_of_ne hne]
  have ht (i : Fin r) : Tendsto (fun n => W n i) atTop (𝓝 (V i)) := by
    have he : extendModes f (extendModes (progression i) (modeWave 1)) = V i := by
      rw [show extendModes (progression i) (modeWave 1) = modeWave (progression i 1) from
        _root_.RHTower.lpScalarInjection_single _ _ _ _,progression_one]
      rw [show extendModes f (modeWave (number i.val)) = modeWave (f (number i.val)) from
        _root_.RHTower.lpScalarInjection_single _ _ _ _]
      change modeWave (skipLabel 0 N (number i.val)) = modeWave (number (N+i.val))
      simp only [skipLabel_number,skipIndex,Nat.not_lt_zero,if_false,Nat.add_comm i.val]
    rw [← he]
    exact ((extendModes f).continuous.tendsto _).comp (((extendModes (progression i)).continuous.tendsto _).comp hv)
  exact mem_closure_physicalSpectra_of_squares (fun n => missingDimension_family (hn n) (ho n))
    (fun n => extended_lanes_conserve f (skipLabel_increases 0 N) (u n))
    (tendsto_family_square hn ho hV hO ht) _ (block_square_approxNumber N r)

/-- Universal closed relations for physical spectra extend simultaneously to the full gas and each block deletion. -/
theorem hot_block_mem_closed_of_physical (r N : ℕ) {S : Set (SpectralBand (r+1) × SpectralBand (r+1))}
    (hs : IsClosed S) (h : ∀ b ∈ physicalSpectra (r+1), ∀ c ∈ physicalSpectra (r+1), (b,c) ∈ S) :
    (hotEdge (r+1),blockSpectrum N (r+1)) ∈ S := by
  have hh := closure_mono (laneSpectra_subset_physicalSpectra (r+1)) (physical_spectral_edges r).1
  have hc : (hotEdge (r+1),blockSpectrum N (r+1)) ∈ closure (physicalSpectra (r+1) ×ˢ physicalSpectra (r+1)) := by
    rw [closure_prod_eq]
    exact ⟨hh,blockSpectrum_mem_closure N (r+1)⟩
  have hsub : physicalSpectra (r+1) ×ˢ physicalSpectra (r+1) ⊆ S := by
    rintro ⟨b,c⟩ ⟨hb,hc'⟩
    exact h b hb c hc'
  exact closure_minimal hsub hs hc

#print axioms blockSpectrum_mem_closure
#print axioms hot_block_mem_closed_of_physical

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
