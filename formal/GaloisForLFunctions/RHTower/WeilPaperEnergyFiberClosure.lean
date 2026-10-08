import GaloisForLFunctions.RHTower.WeilPaperEnergyFiberContractions
import GaloisForLFunctions.RHTower.WeilPaperSymmetricEnergyLimits

/-!
# Exact energy levels accumulate on every lower-energy native law

The exact-loss construction is intrinsic to the native law space. Consequently
every attained level has the whole sublevel in its closure. At the same time,
every strict high-energy region is dense. Both statements hold inside the
real-test, inversion-symmetric image with its own weak topology.
-/

open Filter Set Topology
open scoped NNReal
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- Exact prescribed energy losses expressed directly on native laws. -/
theorem exists_nativePoint_tendsto_exact_energy
    (μ : Set.range spectralRepresentingMeasure) (δ : ℝ≥0) :
    ∃ ν : ℕ → Set.range spectralRepresentingMeasure, Tendsto ν atTop (𝓝 μ) ∧
      ∀ n, paperNativeSpectralEnergy (ν n) = paperNativeSpectralEnergy μ + δ := by
  rcases μ with ⟨μ, a, rfl⟩
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_exact_energy a δ
  refine ⟨fun n => ⟨spectralRepresentingMeasure (c n), Set.mem_range_self _⟩,
    tendsto_subtype_rng.mpr hc, ?_⟩
  intro n
  simpa only [paperNativeSpectralEnergy_apply] using he n

/-- Divergent energy sequences expressed directly on native laws. -/
theorem exists_nativePoint_tendsto_energy_atTop
    (μ : Set.range spectralRepresentingMeasure) :
    ∃ ν : ℕ → Set.range spectralRepresentingMeasure, Tendsto ν atTop (𝓝 μ) ∧
      Tendsto (fun n => paperNativeSpectralEnergy (ν n)) atTop atTop := by
  rcases μ with ⟨μ, a, rfl⟩
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_energy_atTop a
  refine ⟨fun n => ⟨spectralRepresentingMeasure (c n), Set.mem_range_self _⟩,
    tendsto_subtype_rng.mpr hc, ?_⟩
  simpa only [paperNativeSpectralEnergy_apply] using he

/-- Every lower-energy native law lies in the closure of a given exact energy level. -/
theorem native_energy_sublevel_subset_closure_fiber (a : Set.range spectralRepresentingMeasure) :
    {μ | paperNativeSpectralEnergy μ ≤ paperNativeSpectralEnergy a} ⊆
      closure (PaperNativeEnergyFiber a) := by
  intro μ hμ
  let δ : ℝ≥0 := ⟨paperNativeSpectralEnergy a - paperNativeSpectralEnergy μ, sub_nonneg.mpr hμ⟩
  obtain ⟨ν, hν, he⟩ := exists_nativePoint_tendsto_exact_energy μ δ
  apply mem_closure_of_tendsto hν
  apply Filter.Eventually.of_forall
  intro n
  change paperNativeSpectralEnergy (ν n) = paperNativeSpectralEnergy a
  rw [he]
  change paperNativeSpectralEnergy μ +
    (paperNativeSpectralEnergy a - paperNativeSpectralEnergy μ) = paperNativeSpectralEnergy a
  ring

/-- The same downward accumulation occurs inside the symmetric real-test image. -/
theorem symmetric_energy_sublevel_subset_closure_fiber (a : Set.range paperNativeRealification) :
    {μ : Set.range paperNativeRealification |
      paperNativeSpectralEnergy μ.1 ≤ paperNativeSpectralEnergy a.1} ⊆
        closure (PaperSymmetricNativeEnergyFiber a) := by
  intro μ hμ
  let δ : ℝ≥0 := ⟨paperNativeSpectralEnergy a.1 - paperNativeSpectralEnergy μ.1, sub_nonneg.mpr hμ⟩
  obtain ⟨ν, hν, he⟩ := exists_symmetricNativePoint_tendsto_exact_energy μ δ
  apply mem_closure_of_tendsto hν
  apply Filter.Eventually.of_forall
  intro n
  change paperNativeSpectralEnergy (ν n).1 = paperNativeSpectralEnergy a.1
  rw [he]
  change paperNativeSpectralEnergy μ.1 +
    (paperNativeSpectralEnergy a.1 - paperNativeSpectralEnergy μ.1) = paperNativeSpectralEnergy a.1
  ring

/-- Native laws above any prescribed finite energy threshold are weakly dense. -/
theorem dense_native_energy_superlevel (r : ℝ) :
    Dense {μ : Set.range spectralRepresentingMeasure | r < paperNativeSpectralEnergy μ} := by
  intro μ
  obtain ⟨ν, hν, he⟩ := exists_nativePoint_tendsto_energy_atTop μ
  exact mem_closure_of_tendsto hν (he.eventually_gt_atTop r)

/-- Arbitrarily high energy remains dense after imposing real tests and spectral symmetry. -/
theorem dense_symmetric_native_energy_superlevel (r : ℝ) :
    Dense {μ : Set.range paperNativeRealification | r < paperNativeSpectralEnergy μ.1} := by
  intro μ
  obtain ⟨ν, hν, he⟩ := exists_symmetricNativePoint_tendsto_energy_atTop μ
  exact mem_closure_of_tendsto hν (he.eventually_gt_atTop r)

end RHTower.WeilWorkPBAP
