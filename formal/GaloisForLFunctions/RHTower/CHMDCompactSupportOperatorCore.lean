import GaloisForLFunctions.RHTower.CHMDOperatorCutoffCommutator

/-!
# Compactly supported cores for the actual CHMD generators

Every vector in the maximal operator domain admits explicit compactly
supported cutoffs converging together with its generator image. There is no
boundedness, smoothness, or weak-domain admission premise on the source.
This closes spatial localization; smoothing within a compact set is separate.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

theorem rieszLift_cutoff (n : ℕ) (w : MassSpace) :
    rieszLift (massCutoff n w + fullCutoffCommutator n (resolvent w)) =
      fullCutoff n (rieszLift w) := by
  apply rieszLift_unique
  intro q
  have h := fullCutoff_pairing n (rieszLift w) q
  rw [inner_rieszLift] at h
  have hq : (fullCutoff n q).val.fst = massCutoff n q.val.fst := fullCutoff_source n q
  rw [hq, ← massCutoff_symmetric] at h
  change ⟪fullCutoff n (rieszLift w), q⟫_ℝ - ⟪massCutoff n w, q.val.fst⟫_ℝ =
    ⟪fullCutoffCommutator n (resolvent w), q.val.fst⟫_ℝ at h
  rw [inner_add_left]
  linarith

theorem resolvent_cutoff (n : ℕ) (w : MassSpace) :
    resolvent (massCutoff n w + fullCutoffCommutator n (resolvent w)) =
      massCutoff n (resolvent w) := by
  have h := congrArg sourceMap (rieszLift_cutoff n w)
  rw [fullCutoff_source] at h
  exact h

theorem arithmeticGenerator_identity (u : arithmeticGenerator.domain) :
    resolvent ((u : MassSpace) + arithmeticGenerator u) = u :=
  generatorOfResolvent_identity resolvent resolvent_injective u

theorem massCutoff_mem_arithmeticGenerator_domain (n : ℕ) (u : arithmeticGenerator.domain) :
    massCutoff n u ∈ arithmeticGenerator.domain := by
  refine ⟨massCutoff n ((u : MassSpace) + arithmeticGenerator u) +
    fullCutoffCommutator n u, ?_⟩
  have h := resolvent_cutoff n ((u : MassSpace) + arithmeticGenerator u)
  rwa [arithmeticGenerator_identity] at h

def arithmeticGeneratorCutoff (n : ℕ) (u : arithmeticGenerator.domain) : arithmeticGenerator.domain :=
  ⟨massCutoff n u, massCutoff_mem_arithmeticGenerator_domain n u⟩

theorem arithmeticGeneratorCutoff_apply (n : ℕ) (u : arithmeticGenerator.domain) :
    arithmeticGenerator (arithmeticGeneratorCutoff n u) =
      massCutoff n (arithmeticGenerator u) + fullCutoffCommutator n u := by
  have h1 := arithmeticGenerator_identity (arithmeticGeneratorCutoff n u)
  have h2 := resolvent_cutoff n ((u : MassSpace) + arithmeticGenerator u)
  rw [arithmeticGenerator_identity] at h2
  have h := resolvent_injective (h1.trans h2.symm)
  change massCutoff n u + arithmeticGenerator (arithmeticGeneratorCutoff n u) =
    massCutoff n ((u : MassSpace) + arithmeticGenerator u) + fullCutoffCommutator n u at h
  rw [map_add, add_assoc] at h
  exact add_left_cancel h

theorem arithmeticGeneratorCutoff_tendsto (u : arithmeticGenerator.domain) :
    Tendsto (fun n => (arithmeticGeneratorCutoff n u : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => arithmeticGenerator (arithmeticGeneratorCutoff n u)) atTop
        (𝓝 (arithmeticGenerator u)) := by
  refine ⟨massCutoff_tendsto u, ?_⟩
  simp_rw [arithmeticGeneratorCutoff_apply]
  simpa only [add_zero] using
    (massCutoff_tendsto (arithmeticGenerator u)).add (fullCutoffCommutator_tendsto u)

theorem arithmeticGeneratorCutoff_compact (n : ℕ) (u : arithmeticGenerator.domain) :
    ∃ f : ℝ → ℝ, HasCompactSupport f ∧
      (arithmeticGeneratorCutoff n u : MassSpace) =ᵐ[massMeasure] f :=
  ⟨fun x => cutoff n x * (u : MassSpace) x, (cutoff_hasCompactSupport n).mul_right,
    massCutoff_ae n u⟩

/-- **Compact-support operator-core approximation on the full maximal domain.** -/
theorem arithmeticGenerator_compact_support_core :
    ∀ u : arithmeticGenerator.domain, ∃ v : ℕ → arithmeticGenerator.domain,
      (∀ n, ∃ f : ℝ → ℝ, HasCompactSupport f ∧ (v n : MassSpace) =ᵐ[massMeasure] f) ∧
      Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => arithmeticGenerator (v n)) atTop (𝓝 (arithmeticGenerator u)) := by
  intro u
  exact ⟨fun n => arithmeticGeneratorCutoff n u, fun n => arithmeticGeneratorCutoff_compact n u,
    arithmeticGeneratorCutoff_tendsto u⟩

def stationaryToArithmetic (u : stationaryGenerator.domain) : arithmeticGenerator.domain :=
  ⟨u, arithmeticGenerator_domain_eq_stationary.symm ▸ u.property⟩

def stationaryGeneratorCutoff (n : ℕ) (u : stationaryGenerator.domain) : stationaryGenerator.domain :=
  ⟨arithmeticGeneratorCutoff n (stationaryToArithmetic u),
    arithmeticGenerator_domain_eq_stationary ▸
      (arithmeticGeneratorCutoff n (stationaryToArithmetic u)).property⟩

theorem stationaryGeneratorCutoff_apply (n : ℕ) (u : stationaryGenerator.domain) :
    stationaryGenerator (stationaryGeneratorCutoff n u) =
      arithmeticGenerator (arithmeticGeneratorCutoff n (stationaryToArithmetic u)) -
        groundPerturbation (massCutoff n u) := by
  have h := arithmeticGenerator_eq_stationary_add
    (arithmeticGeneratorCutoff n (stationaryToArithmetic u))
  change arithmeticGenerator (arithmeticGeneratorCutoff n (stationaryToArithmetic u)) =
    stationaryGenerator (stationaryGeneratorCutoff n u) + groundPerturbation (massCutoff n u) at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem stationaryGeneratorCutoff_tendsto (u : stationaryGenerator.domain) :
    Tendsto (fun n => (stationaryGeneratorCutoff n u : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => stationaryGenerator (stationaryGeneratorCutoff n u)) atTop
        (𝓝 (stationaryGenerator u)) := by
  refine ⟨massCutoff_tendsto u, ?_⟩
  simp_rw [stationaryGeneratorCutoff_apply]
  have h := (arithmeticGeneratorCutoff_tendsto (stationaryToArithmetic u)).2.sub
    ((groundPerturbation.continuous.tendsto (u : MassSpace)).comp (massCutoff_tendsto u))
  have he : arithmeticGenerator (stationaryToArithmetic u) - groundPerturbation u =
      stationaryGenerator u := by
    have hh := arithmeticGenerator_eq_stationary_add (stationaryToArithmetic u)
    change arithmeticGenerator (stationaryToArithmetic u) =
      stationaryGenerator u + groundPerturbation u at hh
    exact sub_eq_iff_eq_add.mpr hh
  exact he ▸ h

/-- The stationary pullback has the same compact-support core property. -/
theorem stationaryGenerator_compact_support_core :
    ∀ u : stationaryGenerator.domain, ∃ v : ℕ → stationaryGenerator.domain,
      (∀ n, ∃ f : ℝ → ℝ, HasCompactSupport f ∧ (v n : MassSpace) =ᵐ[massMeasure] f) ∧
      Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => stationaryGenerator (v n)) atTop (𝓝 (stationaryGenerator u)) := by
  intro u
  refine ⟨fun n => stationaryGeneratorCutoff n u, ?_, stationaryGeneratorCutoff_tendsto u⟩
  intro n
  exact arithmeticGeneratorCutoff_compact n (stationaryToArithmetic u)

/-- The closure of the compactly supported part is the full arithmetic operator graph. -/
theorem arithmeticGenerator_compact_graph_closure :
    closure {z : MassSpace × MassSpace | z ∈ arithmeticGenerator.graph ∧
      ∃ f : ℝ → ℝ, HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} =
      (arithmeticGenerator.graph : Set (MassSpace × MassSpace)) := by
  apply Set.Subset.antisymm
  · exact arithmeticGenerator_isClosed.closure_subset_iff.mpr fun _ h => h.1
  · intro z hz
    obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' arithmeticGenerator).mp hz
    have h := arithmeticGeneratorCutoff_tendsto u
    apply mem_closure_of_tendsto (h.1.prodMk_nhds h.2)
    exact Eventually.of_forall fun n =>
      ⟨arithmeticGenerator.mem_graph (arithmeticGeneratorCutoff n u),
        arithmeticGeneratorCutoff_compact n u⟩

/-- The same graph closure holds for the actual stationary pullback generator. -/
theorem stationaryGenerator_compact_graph_closure :
    closure {z : MassSpace × MassSpace | z ∈ stationaryGenerator.graph ∧
      ∃ f : ℝ → ℝ, HasCompactSupport f ∧ z.1 =ᵐ[massMeasure] f} =
      (stationaryGenerator.graph : Set (MassSpace × MassSpace)) := by
  apply Set.Subset.antisymm
  · exact stationaryGenerator_isClosed.closure_subset_iff.mpr fun _ h => h.1
  · intro z hz
    obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' stationaryGenerator).mp hz
    have h := stationaryGeneratorCutoff_tendsto u
    apply mem_closure_of_tendsto (h.1.prodMk_nhds h.2)
    exact Eventually.of_forall fun n =>
      ⟨stationaryGenerator.mem_graph (stationaryGeneratorCutoff n u),
        arithmeticGeneratorCutoff_compact n (stationaryToArithmetic u)⟩

end RHTower.CHMDDoobGraph
