import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaCesaroSource

/-!
# A common literal finite-packet core for Gamma source families

For every family of positive Gamma parameters, closure of the joint
finite-packet graph in the product topology equals the simultaneous
cancelled-equation graph. Thus passing to further apertures requires no new
core or domain assumption. For finite families this is graph-norm closure.
The common approximants use the original source coefficients in every leg.
-/

open Filter Topology
open scoped BigOperators ENNReal
set_option autoImplicit false

noncomputable section
namespace RHTower

private abbrev H := SuzukiCausalDepthGammaTraceL2
private abbrev Index := SuzukiCausalDepthGammaTraceIndex

/-- Joint closure of the same literal source packet, evaluated at each parameter. -/
def suzukiGammaJointClosedGraph {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) : Submodule ℂ (H × (J → H)) :=
  (Submodule.span ℂ (Set.range fun i : Index =>
    (lp.single 2 i (1 : ℂ), fun j => suzukiGammaTwoLegFullColumn (h j) (a j) i))).topologicalClosure

/-- The simultaneous maximal equations share one input and retain each output. -/
def suzukiGammaJointEquationGraph {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) : Submodule ℂ (H × (J → H)) where
  carrier := {z | ∀ j, (z.1, z.2 j) ∈ suzukiGammaSourceEquationGraph (h j) (a j)}
  zero_mem' := fun j => (suzukiGammaSourceEquationGraph (h j) (a j)).zero_mem
  add_mem' := fun hz hw j => (suzukiGammaSourceEquationGraph (h j) (a j)).add_mem (hz j) (hw j)
  smul_mem' := fun c _ hz j => (suzukiGammaSourceEquationGraph (h j) (a j)).smul_mem c (hz j)

theorem suzukiGammaJointEquationGraph_isClosed {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) :
    IsClosed (suzukiGammaJointEquationGraph h a : Set (H × (J → H))) := by
  change IsClosed {z : H × (J → H) |
    ∀ j, (z.1, z.2 j) ∈ suzukiGammaSourceEquationGraph (h j) (a j)}
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro j
  exact (suzukiGammaSourceEquationGraph_isClosed (h j) (a j)).preimage
    (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))

theorem suzukiGammaJointClosedGraph_le_equationGraph {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) :
    suzukiGammaJointClosedGraph h a ≤ suzukiGammaJointEquationGraph h a := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩ j
    exact suzukiGammaTwoLegFullColumn_mem_equationGraph (h j) (a j) i
  · exact suzukiGammaJointEquationGraph_isClosed h a

/-- Radial cancellation completes one common finite input packet in all legs. -/
theorem suzukiGammaRegularizedSynthesis_mem_jointClosedGraph {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) (n : ℕ) (u : H) :
    (suzukiGammaSourceRegularization n u,
      fun j => suzukiGammaRegularizedSynthesis (h j) (a j) n u) ∈
        suzukiGammaJointClosedGraph h a := by
  let F : H →L[ℂ] H × (J → H) := (suzukiGammaSourceRegularization n).prod
    (ContinuousLinearMap.pi fun j => suzukiGammaRegularizedSynthesis (h j) (a j) n)
  have hsingle (i : Index) : F (lp.single 2 i (1 : ℂ)) ∈
      suzukiGammaJointClosedGraph h a := by
    have hi : (lp.single 2 i (1 : ℂ), fun j => suzukiGammaTwoLegFullColumn (h j) (a j) i) ∈
        suzukiGammaJointClosedGraph h a :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
    have he : F (lp.single 2 i (1 : ℂ)) = (1 - suzukiGammaSourcePowerSymbol n i) •
        (lp.single 2 i (1 : ℂ), fun j => suzukiGammaTwoLegFullColumn (h j) (a j) i) := by
      apply Prod.ext
      · exact suzukiGammaSourceRegularization_single n i
      · funext j
        exact suzukiGammaRegularizedSynthesis_single (h j) (a j) n i
    rw [he]
    exact (suzukiGammaJointClosedGraph h a).smul_mem _ hi
  have ht := F.continuous.tendsto u |>.comp
    (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) u)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  filter_upwards with s
  change F (∑ i ∈ s, lp.single 2 i (u i)) ∈ suzukiGammaJointClosedGraph h a
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  have hi := (suzukiGammaJointClosedGraph h a).smul_mem (u i) (hsingle i)
  simpa only [← map_smul, ← lp.single_smul, smul_eq_mul, mul_one] using hi

/-- Averaging preserves membership in the same literal joint source closure. -/
theorem suzukiGammaCesaroSynthesis_mem_jointClosedGraph {J : Type*}
    (h a : J → Set.Ioi (0 : ℝ)) (N : ℕ) (u : H) :
    (suzukiGammaCesaroSource N u, fun j => suzukiGammaCesaroSynthesis (h j) (a j) N u) ∈
      suzukiGammaJointClosedGraph h a := by
  have hs : (∑ n ∈ Finset.range N, (suzukiGammaSourceRegularization n u,
      fun j => suzukiGammaRegularizedSynthesis (h j) (a j) n u)) ∈
        suzukiGammaJointClosedGraph h a := by
    apply Submodule.sum_mem
    intro n _
    exact suzukiGammaRegularizedSynthesis_mem_jointClosedGraph h a n u
  have he : (suzukiGammaCesaroSource N u, fun j => suzukiGammaCesaroSynthesis (h j) (a j) N u) =
      algebraMap ℝ ℂ ((N : ℝ)⁻¹) • ∑ n ∈ Finset.range N,
        (suzukiGammaSourceRegularization n u, fun j => suzukiGammaRegularizedSynthesis (h j) (a j) n u) := by
    rw [IsScalarTower.algebraMap_smul]
    apply Prod.ext
    · simp [suzukiGammaCesaroSource_apply, Prod.fst_sum]
    · funext j
      simp [suzukiGammaCesaroSynthesis_apply, Prod.snd_sum, Finset.sum_apply]
  rw [he]
  exact (suzukiGammaJointClosedGraph h a).smul_mem (algebraMap ℝ ℂ ((N : ℝ)⁻¹)) hs

/-- **Common literal finite-packet core for every Gamma parameter family.**
Taking the actual source closure commutes with imposing all these parameter
equations on the same input. Closure uses the product graph topology, hence
the usual simultaneous graph norm for every finite family. No common-core
hypothesis is required. -/
theorem suzukiGammaJointClosedGraph_eq_equationGraph
    {J : Type*} (h a : J → Set.Ioi (0 : ℝ)) :
    suzukiGammaJointClosedGraph h a = suzukiGammaJointEquationGraph h a := by
  apply le_antisymm (suzukiGammaJointClosedGraph_le_equationGraph h a)
  rintro ⟨u, v⟩ huv
  have hu := tendsto_suzukiGammaCesaroSource u
  have hv : Tendsto (fun N j => suzukiGammaCesaroSynthesis (h j) (a j) N u)
      atTop (𝓝 v) :=
    tendsto_pi_nhds.mpr fun j => tendsto_suzukiGammaCesaroSynthesis (h j) (a j) (huv j)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hu.prodMk_nhds hv)
  exact Filter.Eventually.of_forall fun N =>
    suzukiGammaCesaroSynthesis_mem_jointClosedGraph h a N u

/-- The literal Gamma source packets are a common core across the entire
positive parameter plane, with no hypotheses. -/
theorem suzukiGammaUniversalSourceCore :
    suzukiGammaJointClosedGraph
      (fun p : Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ) => p.1) (fun p => p.2) =
    suzukiGammaJointEquationGraph
      (fun p : Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ) => p.1) (fun p => p.2) :=
  suzukiGammaJointClosedGraph_eq_equationGraph _ _

end RHTower
