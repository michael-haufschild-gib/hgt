import GaloisForLFunctions.RHTower.CHMDSpectralGraphCompletion

/-!
# Spectral completion with the critical component fixed

The entire signed radical belongs to the spectral graph core. Orthogonal
reduction preserves that core, so spectral approximation may retain the
critical component exactly and takes place within the reduced graph when the
target is reduced.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem radical_source_mem_massCriticalSpace {p : SourceGraph} (hp : p ∈ signedRadical) :
    sourceMap p ∈ massCriticalSpace := by
  have hr : resolvent ((2 : ℝ) • sourceMap p) = sourceMap p := by
    have h := resolvent_preimage_of_sourcePair (p := p) (b := 0)
      (fun q => by rw [hp q, inner_zero_left])
    simpa only [add_zero] using h
  have h := congrArg (fun w : MassSpace => (1/2 : ℝ) • w) hr
  rw [map_smul, smul_smul] at h
  norm_num at h
  exact (mem_massCriticalSpace _).mpr h

theorem signedRadical_le_spectralGraphCore : signedRadical ≤ spectralGraphCore := by
  intro p hp
  exact massCriticalSpace_le_spectralOperatorCore (radical_source_mem_massCriticalSpace hp)

theorem criticalProjection_mem_spectralGraphCore (p : SourceGraph) :
    criticalProjection p ∈ spectralGraphCore :=
  signedRadical_le_spectralGraphCore (criticalProjection_mem p)

theorem reducedSource_mem_spectralGraphCore {p : SourceGraph} (hp : p ∈ spectralGraphCore) :
    reducedSource p ∈ spectralGraphCore :=
  spectralGraphCore.sub_mem hp (criticalProjection_mem_spectralGraphCore p)

/-- The full critical component can remain fixed throughout spectral synthesis. -/
theorem exists_spectral_graph_approximation_fixed_critical (p : SourceGraph) :
    ∃ q : ℕ → SourceGraph, (∀ n, q n ∈ spectralGraphCore) ∧
      (∀ n, q n - p ∈ signedRadicalᗮ) ∧ Tendsto q atTop (𝓝 p) := by
  obtain ⟨q, hq, ht⟩ := mem_closure_iff_seq_limit.mp (dense_spectralGraphCore p)
  let v : ℕ → SourceGraph := fun n => criticalProjection p + reducedSource (q n)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n
    exact spectralGraphCore.add_mem (criticalProjection_mem_spectralGraphCore p)
      (reducedSource_mem_spectralGraphCore (hq n))
  · intro n
    have he : v n - p = reducedSource (q n) - reducedSource p := by
      change criticalProjection p + (q n - criticalProjection (q n)) - p =
        (q n - criticalProjection (q n)) - (p - criticalProjection p)
      abel
    rw [he]
    exact signedRadicalᗮ.sub_mem (reducedSource_mem _) (reducedSource_mem _)
  · have he : criticalProjection p + reducedSource p = p := by
      change criticalProjection p + (p - criticalProjection p) = p
      abel
    have h : Tendsto v atTop (𝓝 (criticalProjection p + reducedSource p)) :=
      tendsto_const_nhds.add ((reducedSource.continuous.tendsto p).comp ht)
    simpa only [he] using h

/-- Reduced graph vectors admit spectral approximants in the same reduced
space, with convergence of their actual signed arithmetic energies. -/
theorem exists_reduced_spectral_graph_approximation {p : SourceGraph}
    (hp : p ∈ signedRadicalᗮ) :
    ∃ q : ℕ → SourceGraph, (∀ n, q n ∈ spectralGraphCore ∧ q n ∈ signedRadicalᗮ) ∧
      Tendsto q atTop (𝓝 p) ∧
      Tendsto (fun n => sourceEnergy (q n)) atTop (𝓝 (sourceEnergy p)) := by
  obtain ⟨q, hq, ho, ht⟩ := exists_spectral_graph_approximation_fixed_critical p
  refine ⟨q, fun n => ⟨hq n, ?_⟩, ht, (continuous_sourceEnergy.tendsto p).comp ht⟩
  have h := signedRadicalᗮ.add_mem (ho n) hp
  simpa using h

end RHTower.CHMDDoobGraph
