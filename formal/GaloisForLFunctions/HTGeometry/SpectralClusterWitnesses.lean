import GaloisForLFunctions.HTGeometry.FiniteSpectralClusterUniformLocalityLaw

/-!
# Spectrally clustered matrices exist

Clustering asks that every real spectral point sit within one tolerance of a prescribed energy.
It holds outright whenever the spectrum is contained in the energy range, and in particular for
every real scalar matrix at its own energy — the spectrum of a scalar being that scalar.  It is
also monotone in the tolerance, which is the form the plateau separation argument consumes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A spectrum inside the energy range is clustered at every positive tolerance.** -/
theorem spectrallyClusteredAround_of_subset_range {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    (hδ : 0 < δ) {A : Matrix (Fin n) (Fin n) ℂ} (h : spectrum ℝ A ⊆ Set.range energy) :
    SpectrallyClusteredAround energy δ A := by
  intro x hx
  obtain ⟨k, hk⟩ := h hx
  refine ⟨k, ?_⟩
  rw [hk, sub_self, abs_zero]
  exact hδ

/-- Clustering is monotone in the tolerance. -/
theorem SpectrallyClusteredAround.mono {n : ℕ} {energy : Fin n → ℝ} {δ δ' : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ} (h : SpectrallyClusteredAround energy δ A) (hδ : δ ≤ δ') :
    SpectrallyClusteredAround energy δ' A := by
  intro x hx
  obtain ⟨k, hk⟩ := h x hx
  exact ⟨k, lt_of_lt_of_le hk hδ⟩

/-- **Every real scalar matrix is clustered at its own energy.** -/
theorem spectrallyClusteredAround_algebraMap {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    SpectrallyClusteredAround (fun _ : Fin n => c) δ
      (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) c) := by
  refine spectrallyClusteredAround_of_subset_range hδ ?_
  rw [spectrum.scalar_eq]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, hx.symm⟩

/-- The zero matrix is clustered at the zero energy. -/
theorem spectrallyClusteredAround_zero {n : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ) :
    SpectrallyClusteredAround (fun _ : Fin n => (0 : ℝ)) δ 0 := by
  refine spectrallyClusteredAround_of_subset_range hδ ?_
  rw [spectrum.zero_eq]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, hx.symm⟩

end GaloisForLFunctions.HTGeometry
