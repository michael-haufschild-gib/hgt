import GaloisForLFunctions.RHTower.CHMDSpectralOperatorCore

/-!
# Full energy-graph completion of finite spectral sources

Every completed arithmetic graph vector is a limit of finite-sample graph
vectors plus Riesz lifts of finite-sample mass vectors. Convergence holds in
the full graph norm, retaining the archimedean term and every prime jump.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def rieszLiftCLM : MassSpace →L[ℝ] SourceGraph :=
  rieszLinear.mkContinuous 1 (by
    intro w
    rw [one_mul]
    change ‖rieszLift w‖ ≤ ‖w‖
    have h : ‖rieszLift w‖ ^ 2 ≤ ‖w‖ * ‖rieszLift w‖ := by
      calc
        _ = ⟪w, resolvent w⟫_ℝ := graph_norm_sq_rieszLift w
        _ ≤ ‖w‖ * ‖resolvent w‖ := real_inner_le_norm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_source_le_graph _) (norm_nonneg _)
    nlinarith [norm_nonneg w, norm_nonneg (rieszLift w)])

theorem rieszLiftCLM_apply (w : MassSpace) : rieszLiftCLM w = rieszLift w := rfl

def spectralGraphCore : Submodule ℝ SourceGraph :=
  spectralOperatorCore.comap sourceMap.toLinearMap

theorem spectralGraphCore_realization {p : SourceGraph} (hp : p ∈ spectralGraphCore) :
    ∃ (S T : Finset zetaZeroConfig.carrier) (u v : MassSpace),
      FiniteMassSampleSupport S u ∧ FiniteMassSampleSupport T v ∧
      p = finiteSampleGraphLift S u + rieszLift v := by
  change sourceMap p ∈ spectralOperatorCore at hp
  obtain ⟨u, ⟨S, hu⟩, r, ⟨v, ⟨T, hv⟩, rfl⟩, hs⟩ := Submodule.mem_sup.mp hp
  refine ⟨S, T, u, v, hu, hv, ?_⟩
  apply source_projection_injective
  change sourceMap p = sourceMap (finiteSampleGraphLift S u + rieszLift v)
  rw [map_add, finiteSampleGraphLift_source hu]
  exact hs.symm

/-- The finite spectral construction is dense in the full arithmetic energy graph. -/
theorem dense_spectralGraphCore : Dense (spectralGraphCore : Set SourceGraph) := by
  have hsub : Set.range rieszLift ⊆ closure (spectralGraphCore : Set SourceGraph) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨b, hb, ht⟩ := exists_spectral_forcing_approximation z
    have hg : Tendsto (fun n => rieszLift (massCriticalProjection z + b n)) atTop
        (𝓝 (rieszLift z)) :=
      (rieszLiftCLM.continuous.tendsto z).comp ht
    apply mem_closure_of_tendsto hg
    refine Eventually.of_forall fun n => ?_
    change resolvent (massCriticalProjection z + b n) ∈ spectralOperatorCore
    rw [map_add]
    exact spectralOperatorCore.add_mem
      (resolvent_critical_mem_spectralOperatorCore (massCriticalProjection_mem z))
      (resolvent_sampling_mem_spectralOperatorCore (hb n))
  have h := closure_minimal hsub isClosed_closure
  rw [dense_range_rieszLift.closure_eq] at h
  intro p
  exact h (mem_univ p)

theorem spectralGraphCore_closure : spectralGraphCore.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp dense_spectralGraphCore

/-- Actual finite-sample sources and one Riesz lift synthesize every completed
graph vector; the supports may increase along the approximating sequence. -/
theorem exists_finite_spectral_graph_synthesis (p : SourceGraph) :
    ∃ (S T : ℕ → Finset zetaZeroConfig.carrier) (u v : ℕ → MassSpace),
      (∀ n, FiniteMassSampleSupport (S n) (u n) ∧ FiniteMassSampleSupport (T n) (v n)) ∧
      Tendsto (fun n => finiteSampleGraphLift (S n) (u n) + rieszLift (v n)) atTop (𝓝 p) := by
  obtain ⟨q, hq, ht⟩ := mem_closure_iff_seq_limit.mp (dense_spectralGraphCore p)
  choose S T u v hu hv he using fun n => spectralGraphCore_realization (hq n)
  refine ⟨S, T, u, v, fun n => ⟨hu n, hv n⟩, ?_⟩
  exact ht.congr he

/-- The same synthesis converges in the original signed arithmetic energy,
including its polar correction. -/
theorem exists_finite_spectral_energy_synthesis (p : SourceGraph) :
    ∃ q : ℕ → SourceGraph, (∀ n, q n ∈ spectralGraphCore) ∧
      Tendsto q atTop (𝓝 p) ∧
      Tendsto (fun n => sourceEnergy (q n)) atTop (𝓝 (sourceEnergy p)) := by
  obtain ⟨q, hq, ht⟩ := mem_closure_iff_seq_limit.mp (dense_spectralGraphCore p)
  exact ⟨q, hq, ht, (continuous_sourceEnergy.tendsto p).comp ht⟩

end RHTower.CHMDDoobGraph
