import GaloisForLFunctions.RHTower.CHMDAlgebraicSpectralInverse

/-!
# Spectral reconstruction of the maximal arithmetic operator

Finite-sample mass vectors and their images under one application of the
arithmetic resolvent form an operator core. The approximation converges both
in mass and after application of the maximal generator. The full critical
component is retained, without a closed-range or cardinal-series assumption.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def finiteSampleSpace : Submodule ℝ MassSpace where
  carrier w := ∃ S : Finset zetaZeroConfig.carrier, FiniteMassSampleSupport S w
  zero_mem' := ⟨∅, FiniteMassSampleSupport.zero ∅⟩
  add_mem' := by
    rintro u v ⟨S, hu⟩ ⟨T, hv⟩
    classical
    exact ⟨S ∪ T, hu.add hv⟩
  smul_mem' := by
    rintro c w ⟨S, hw⟩
    exact ⟨S, hw.smul c⟩

theorem finiteSampleSpace_le_domain : finiteSampleSpace ≤ arithmeticGenerator.domain := by
  rintro w ⟨S, hw⟩
  exact finite_samples_mem_arithmetic_domain hw

theorem massCriticalSpace_le_finiteSampleSpace : massCriticalSpace ≤ finiteSampleSpace := by
  intro w hw
  have hs := mass_silent_of_resolvent_half ((mem_massCriticalSpace _).mp hw)
  refine ⟨∅, fun ρ _ => ?_⟩
  have hz := CHMDStage16.XiC_gammaOf_eq_zero ρ
  exact ⟨hs.1 _ hz, hs.1 _ (by rw [XiC_even, hz])⟩

/-- Finite-sample sources together with one actual resolvent image. -/
def spectralOperatorCore : Submodule ℝ MassSpace :=
  finiteSampleSpace ⊔ finiteSampleSpace.map (resolvent : MassSpace →ₗ[ℝ] MassSpace)

theorem finiteSampleSpace_le_spectralOperatorCore : finiteSampleSpace ≤ spectralOperatorCore :=
  le_sup_left

theorem resolvent_finiteSampleSpace_mem {w : MassSpace} (hw : w ∈ finiteSampleSpace) :
    resolvent w ∈ spectralOperatorCore :=
  (show finiteSampleSpace.map (resolvent : MassSpace →ₗ[ℝ] MassSpace) ≤
    spectralOperatorCore from le_sup_right) ⟨w, hw, rfl⟩

theorem massCriticalSpace_le_spectralOperatorCore : massCriticalSpace ≤ spectralOperatorCore :=
  massCriticalSpace_le_finiteSampleSpace.trans finiteSampleSpace_le_spectralOperatorCore

theorem spectralOperatorCore_le_domain : spectralOperatorCore ≤ arithmeticGenerator.domain := by
  apply sup_le finiteSampleSpace_le_domain
  rintro w ⟨v, _, hv⟩
  exact ⟨v, hv⟩

theorem resolvent_critical_mem_spectralOperatorCore {w : MassSpace}
    (hw : w ∈ massCriticalSpace) : resolvent w ∈ spectralOperatorCore := by
  rw [(mem_massCriticalSpace _).mp hw]
  exact spectralOperatorCore.smul_mem _ (massCriticalSpace_le_spectralOperatorCore hw)

/-- Algebraic inversion puts every resolvent-smoothed sampling kernel in the
spectral core, with only one resolvent application to a finite-sample vector. -/
theorem resolvent_sampling_mem_spectralOperatorCore {b : MassSpace}
    (hb : b ∈ massSamplingSpan) : resolvent b ∈ spectralOperatorCore := by
  rw [← finiteSampleImageSpace_eq_samplingSpan] at hb
  obtain ⟨S, w, hw, hr⟩ := hb
  have hw' : w ∈ finiteSampleSpace := ⟨S, hw⟩
  have he : resolvent b = w - (2 : ℝ) • resolvent w := by
    have h := hr
    rw [map_add, map_smul] at h
    calc
      _ = ((2 : ℝ) • resolvent w + resolvent b) - (2 : ℝ) • resolvent w := by module
      _ = _ := by rw [h]
  rw [he]
  exact spectralOperatorCore.sub_mem (finiteSampleSpace_le_spectralOperatorCore hw')
    (spectralOperatorCore.smul_mem _ (resolvent_finiteSampleSpace_mem hw'))

theorem exists_sampling_approximation (z : MassSpace) :
    ∃ b : ℕ → MassSpace, (∀ n, b n ∈ massSamplingSpan) ∧
      Tendsto b atTop (𝓝 (massReducedSource z)) := by
  have hr : massReducedSource z ∈ closure (massSamplingSpan : Set MassSpace) := by
    change massReducedSource z ∈ massSamplingSpan.topologicalClosure
    rw [massSamplingSpan_closure]
    exact massReducedSource_mem z
  exact mem_closure_iff_seq_limit.mp hr

/-- The forcing approximation preserves the complete critical component. -/
theorem exists_spectral_forcing_approximation (z : MassSpace) :
    ∃ b : ℕ → MassSpace, (∀ n, b n ∈ massSamplingSpan) ∧
      Tendsto (fun n => massCriticalProjection z + b n) atTop (𝓝 z) := by
  obtain ⟨b, hb, ht⟩ := exists_sampling_approximation z
  have he : massCriticalProjection z + massReducedSource z = z := by
    change massCriticalProjection z + (z - massCriticalProjection z) = z
    abel
  refine ⟨b, hb, ?_⟩
  simpa only [he] using
    (tendsto_const_nhds.add ht : Tendsto (fun n => massCriticalProjection z + b n) atTop
      (𝓝 (massCriticalProjection z + massReducedSource z)))

/-- Every actual maximal-domain vector is approximated in operator graph norm
by finite-sample vectors plus one arithmetic-resolvent image. -/
theorem arithmeticGenerator_spectral_core (u : arithmeticGenerator.domain) :
    ∃ v : ℕ → arithmeticGenerator.domain,
      (∀ n, (v n : MassSpace) ∈ spectralOperatorCore) ∧
      Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
      Tendsto (fun n => arithmeticGenerator (v n)) atTop (𝓝 (arithmeticGenerator u)) := by
  let z : MassSpace := (u : MassSpace) + arithmeticGenerator u
  obtain ⟨b, hb, ht⟩ := exists_spectral_forcing_approximation z
  let v : ℕ → arithmeticGenerator.domain := fun n =>
    ⟨resolvent (massCriticalProjection z + b n), ⟨massCriticalProjection z + b n, rfl⟩⟩
  have hr : resolvent z = (u : MassSpace) := arithmeticGenerator_identity u
  have hv : Tendsto (fun n => (v n : MassSpace)) atTop (𝓝 (resolvent z)) :=
    (resolvent.continuous.tendsto z).comp ht
  refine ⟨v, ?_, hr ▸ hv, ?_⟩
  · intro n
    change resolvent (massCriticalProjection z + b n) ∈ spectralOperatorCore
    rw [map_add]
    exact spectralOperatorCore.add_mem
      (resolvent_critical_mem_spectralOperatorCore (massCriticalProjection_mem z))
      (resolvent_sampling_mem_spectralOperatorCore (hb n))
  · have hn : ∀ n, arithmeticGenerator (v n) =
        massCriticalProjection z + b n - (v n : MassSpace) :=
      fun n => arithmeticGenerator_resolvent _
    have he : z - resolvent z = arithmeticGenerator u := by
      rw [hr]
      change (u : MassSpace) + arithmeticGenerator u - (u : MassSpace) = _
      abel
    simpa only [hn, he] using ht.sub hv

/-- The closure is the full maximal operator graph, including every critical mode. -/
theorem arithmeticGenerator_spectral_graph_closure :
    closure {z : MassSpace × MassSpace | z ∈ arithmeticGenerator.graph ∧
      z.1 ∈ spectralOperatorCore} =
      (arithmeticGenerator.graph : Set (MassSpace × MassSpace)) := by
  apply Set.Subset.antisymm
  · exact arithmeticGenerator_isClosed.closure_subset_iff.mpr fun _ h => h.1
  · intro z hz
    obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' arithmeticGenerator).mp hz
    obtain ⟨v, hv, hs, hg⟩ := arithmeticGenerator_spectral_core u
    apply mem_closure_of_tendsto (hs.prodMk_nhds hg)
    exact Eventually.of_forall fun n => ⟨arithmeticGenerator.mem_graph (v n), hv n⟩

end RHTower.CHMDDoobGraph
