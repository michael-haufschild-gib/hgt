import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.ForestRatios
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Simultaneous extremality for every forest of physical eigenvalue differences -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

private theorem forest_null {n L D : ℕ} [NeZero L] (hn : 0<n) {P : Fin L → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (hS : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    {leaf root : Fin (n+1) → Fin D} (hi : Function.Injective leaf) (hd : ∀ i j, root i ≠ leaf j) :
    volume {x ∈ simpleEnsembleLocus hP |
      KleinbockMargulis.VWA (forestRatio leaf root (sortedEnsembleSpectrum hP x))} = 0 := by
  let U := simpleEnsembleLocus hP
  let bad := {x | KleinbockMargulis.VWA (forestRatio leaf root (sortedEnsembleSpectrum hP x))}
  let B (p : {p : (Fin L → ℝ) × ℝ // 0<p.2 ∧ Metric.ball p.1 p.2 ⊆ U}) := Metric.ball p.val.1 p.val.2
  obtain ⟨T,hT,he⟩ := TopologicalSpace.isOpen_iUnion_countable B (fun _ => Metric.isOpen_ball)
  have cover (x) (hx : x∈U) : x ∈ ⋃ p∈T, B p := by
    rw [he]
    obtain ⟨r,hr,hh⟩ := Metric.isOpen_iff.mp (isOpen_simpleEnsembleLocus hP) x hx
    exact mem_iUnion.mpr ⟨⟨(x,r),hr,hh⟩,Metric.mem_ball_self hr⟩
  refine measure_mono_null (t:=⋃ p∈T, B p ∩ bad) ?_ ?_
  · rintro x ⟨hx,hb⟩
    obtain ⟨p,hp,hB⟩ := mem_iUnion₂.mp (cover x hx)
    exact mem_iUnion₂.mpr ⟨p,hp,hB,hb⟩
  · rw [measure_biUnion_null_iff hT]
    exact fun p _ => forest_chart hn hP hS hi hd Metric.isOpen_ball Metric.isPreconnected_ball
      ⟨p.val.1,Metric.mem_ball_self p.property.1⟩ p.property.2

private theorem sorted_forest (k n : ℕ) (leaf root : Fin (n+1) → Fin (2^(k+3))) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, 0<n → Function.Injective leaf → (∀ i j, root i ≠ leaf j) →
      let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      ¬KleinbockMargulis.VWA (forestRatio leaf root (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) θ)) := by
  by_cases h : 0<n ∧ Function.Injective leaf ∧ ∀ i j, root i ≠ leaf j
  · let hP := chainPauliFin_isHermitian (k+3)
    have hh := forest_null h.1 hP (chainPauliFin_spectrumEscapesRealRelations k) h.2.1 h.2.2
    have hv : ∀ᵐ x ∂volume, ¬(x ∈ simpleEnsembleLocus hP ∧
        KleinbockMargulis.VWA (forestRatio leaf root (sortedEnsembleSpectrum hP x))) :=
      ae_iff.mpr (by simpa only [not_not] using hh)
    have hs : ∀ᵐ x ∂volume, MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP x).eigenvalues :=
      ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)
    let p := Fintype.card (ChainLabel (k+3))
    have hac : centredProductGaussian (Fin p) 1 ≪ volume := by
      simpa [centredProductGaussian] using productGaussian_absolutelyContinuous p one_ne_zero (fun _ => 0)
    have good := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (hac.ae_le (hs.and hv))
    filter_upwards [good] with ω hω _ _ _
    exact fun hw => hω.2 ⟨hω.1.injective,hw⟩
  · filter_upwards with ω hn hi hd
    exact (h ⟨hn,hi,hd⟩).elim

/-- A single Gaussian draw works simultaneously for all rare-return residue
partitions: roots can repeat, while every leaf is distinct and is never a root. -/
theorem gaussian_forest_ratios :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k n : ℕ,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ leaf root : Fin (n+1) → (Fin (k+3) → Bool), 0<n → Function.Injective leaf →
        (∀ i j, root i ≠ leaf j) → ¬KleinbockMargulis.VWA (forestRatio leaf root E) := by
  have h (k n : ℕ) := ae_all_iff.mpr fun leaf => ae_all_iff.mpr (sorted_forest k n leaf)
  filter_upwards [ae_all_iff.mpr (fun k => ae_all_iff.mpr (h k)),
    gaussian_path_all_prefixes_maximally_projective] with ω hh hspec k n
  intro E leaf root hn hi hd
  obtain ⟨e,he⟩ := SpectralJets.physical_sorted_order k ω (hspec k).injective
  have hv := hh k n (e ∘ leaf) (e ∘ root) hn (e.injective.comp hi) (fun i j h => hd i j (e.injective h))
  have hE : E = sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
      (fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)) ∘ e := funext he
  rw [hE]
  exact hv

#print axioms gaussian_forest_ratios
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
