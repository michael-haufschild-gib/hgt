import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.PlateauOnset.FirstEpisode
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NearHilbertOnset

/-! # A genuine first expensive interval at error one tenth on the frozen chain -/

open Set MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
open AccuracyScales.TenthPlateau
noncomputable section

/-- Throughout the near-Hilbert onset range, the earliest strict exit
starts a whole open expensive interval. Its first affordable endpoint
is attained at the very same gate budget and physical tolerance. -/
theorem gaussian_first_complete_plateau_episode :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Square (Bits N)) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ s : ℕ, D / 2 ^ (3 * N.sqrt) ≤ s → s ≤ D / (7 * (N + 1)) →
        let τ := tenthPlateauOnset H s
        (D:ℝ)/(2:ℝ)^(14*N.sqrt)<τ ∧
        (∀ t∈Icc 0 τ, orbitCircuitDistance H s t≤1/10) ∧ orbitCircuitDistance H s τ=1/10 ∧
        ∃ v>τ, orbitCircuitDistance H s v=1/10 ∧
          IsLeast {t | τ<t ∧ orbitCircuitDistance H s t≤1/10} v ∧
          ∀ t∈Ioo τ v, 1/10<orbitCircuitDistance H s t := by
  obtain ⟨_,h⟩ := gaussian_tenth_error_exact_onset_and_near_hilbert_core
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro N D H s hlo hhi τ
  obtain ⟨htime,_,hpre,he,hpos⟩ := hk.2.2.1 s hlo hhi
  refine ⟨htime,fun t ht => (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hpre t ht),he,?_⟩
  apply first_episode_end H s (by norm_num) τ
  intro b hb
  let δ := (b-τ)/2
  have hδ : 0<δ := half_pos (sub_pos.mpr hb)
  have hp := hpos δ hδ
  have hn : ((SharpOccupation.visitSet H s (1/10))ᶜ ∩ Icc τ (τ+δ)).Nonempty := by
    by_contra! h
    rw [h] at hp
    simp at hp
  obtain ⟨t,ht,ht'⟩ := hn
  have hhigh : 1/10<orbitCircuitDistance H s t := lt_of_not_ge (fun hb =>
    ht ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hb))
  have hne : τ≠t := fun h => hhigh.ne' ((congrArg (orbitCircuitDistance H s) h.symm).trans he)
  exact ⟨t,⟨lt_of_le_of_ne ht'.1 hne,by dsimp only [δ] at ht'; linarith only [ht'.2,hb]⟩,hhigh⟩

#print axioms gaussian_first_complete_plateau_episode
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
