import GaloisForLFunctions.RHTower.CHMDStationaryLocalSmoothCore

/-!
# Compact smooth operator cores for both actual CHMD generators

Spatial operator localization followed by the proved local theta-domain
transfer and convolution regularization gives compact C2 graph approximants.
The closure is the full maximal operator graph, for both the stationary
pullback and the actual arithmetic generator. No extra domain hypothesis is
assumed, and form density is not substituted for operator density.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

theorem stationaryGenerator_compact_smooth_graph_closure :
    closure {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} =
      (stationaryGenerator.graph : Set (MassSpace × MassSpace)) := by
  apply Set.Subset.antisymm
  · exact stationaryGenerator_isClosed.closure_subset_iff.mpr fun _ h => h.1
  · have hl : {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
        ∃ f : ℝ → ℝ, HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} ⊆
        closure {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
          ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} := by
      rintro z ⟨hz, hc⟩
      obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' stationaryGenerator).mp hz
      obtain ⟨k, hk⟩ := exists_massCutoff_fixed (u : MassSpace) hc
      have h := localStationarySmooth_tendsto k u hk
      apply mem_closure_of_tendsto (h.1.prodMk_nhds h.2)
      exact Eventually.of_forall fun n =>
        ⟨stationaryGenerator.mem_graph (localStationarySmooth k u hk n),
          localStationarySmooth_compact_contDiff k u hk n⟩
    intro z hz
    have hz' : z ∈ closure {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
        ∃ f : ℝ → ℝ, HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} := by
      rw [stationaryGenerator_compact_graph_closure]
      exact hz
    exact closure_minimal hl isClosed_closure hz'

/-- Every maximal-domain vector has compact C2 approximants in the actual stationary graph norm. -/
theorem stationaryGenerator_compact_smooth_core :
    ∀ u : stationaryGenerator.domain, ∃ v : ℕ → stationaryGenerator.domain,
      (∀ n, ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (v n : MassSpace) =ᵐ[massMeasure] f) ∧
      Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => stationaryGenerator (v n)) atTop (𝓝 (stationaryGenerator u)) := by
  intro u
  have hu : ((u : MassSpace), stationaryGenerator u) ∈
      closure {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
        ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} := by
    rw [stationaryGenerator_compact_smooth_graph_closure]
    exact stationaryGenerator.mem_graph u
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose v hv using fun n => (LinearPMap.mem_graph_iff' stationaryGenerator).mp (hz n).1
  have ht' : Tendsto (fun n => ((v n : MassSpace), stationaryGenerator (v n))) atTop
      (𝓝 ((u : MassSpace), stationaryGenerator u)) := ht.congr fun n => (hv n).symm
  refine ⟨v, fun n => ?_, ht'.fst, ht'.snd⟩
  have h := (hz n).2
  rw [← hv n] at h
  exact h

/-- The bounded ground perturbation transfers the same compact C2 core to the arithmetic generator. -/
theorem arithmeticGenerator_compact_smooth_core :
    ∀ u : arithmeticGenerator.domain, ∃ v : ℕ → arithmeticGenerator.domain,
      (∀ n, ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (v n : MassSpace) =ᵐ[massMeasure] f) ∧
      Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => arithmeticGenerator (v n)) atTop (𝓝 (arithmeticGenerator u)) := by
  intro u
  let us : stationaryGenerator.domain :=
    ⟨(u : MassSpace), arithmeticGenerator_domain_eq_stationary ▸ u.property⟩
  obtain ⟨v, hv, hs, hg⟩ := stationaryGenerator_compact_smooth_core us
  refine ⟨fun n => stationaryToArithmetic (v n), hv, hs, ?_⟩
  have h := hg.add ((groundPerturbation.continuous.tendsto (u : MassSpace)).comp hs)
  have he : arithmeticGenerator u = stationaryGenerator us + groundPerturbation u :=
    arithmeticGenerator_eq_stationary_add u
  have hn : ∀ n, arithmeticGenerator (stationaryToArithmetic (v n)) =
      stationaryGenerator (v n) + groundPerturbation (v n) :=
    fun n => arithmeticGenerator_eq_stationary_add (stationaryToArithmetic (v n))
  simpa only [he, hn, Function.comp_def] using h

theorem arithmeticGenerator_compact_smooth_graph_closure :
    closure {z : MassSpace × MassSpace | z ∈ arithmeticGenerator.graph ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} =
      (arithmeticGenerator.graph : Set (MassSpace × MassSpace)) := by
  apply Set.Subset.antisymm
  · exact arithmeticGenerator_isClosed.closure_subset_iff.mpr fun _ h => h.1
  · intro z hz
    obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' arithmeticGenerator).mp hz
    obtain ⟨v, hv, hs, hg⟩ := arithmeticGenerator_compact_smooth_core u
    apply mem_closure_of_tendsto (hs.prodMk_nhds hg)
    exact Eventually.of_forall fun n => ⟨arithmeticGenerator.mem_graph (v n), hv n⟩

end RHTower.CHMDDoobGraph
