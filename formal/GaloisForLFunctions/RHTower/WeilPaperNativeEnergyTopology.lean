import GaloisForLFunctions.RHTower.WeilPaperSpectralEnergyInstability
import GaloisForLFunctions.RHTower.WeilPaperTorusSpectralClassification

/-!
# Native full energy is a unique, nowhere-continuous function of the law

The complete representing probability determines full energy exactly. This gives
an intrinsic function on the actual native image, independently of which finite
mixture represents a point. Vanishing high-energy admixtures show that this
intrinsic function is discontinuous at every native law in the weak topology.
-/

open MeasureTheory Filter Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Full energy as a function of the actual native representing law. -/
def paperNativeSpectralEnergy (μ : Set.range spectralRepresentingMeasure) : ℝ :=
  energy (Classical.choose μ.2).1.1

/-- The choice of finite-mixture representative does not affect intrinsic energy. -/
@[simp] theorem paperNativeSpectralEnergy_apply (c : ComplexNullMixture) :
    paperNativeSpectralEnergy ⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩ =
      energy c.1.1 :=
  energy_eq_of_spectralRepresentingMeasure_eq _ c (Classical.choose_spec (Set.mem_range_self c))

/-- There is exactly one function of the native law realizing every native full energy. -/
theorem existsUnique_native_full_energy :
    ∃! F : Set.range spectralRepresentingMeasure → ℝ,
      ∀ c : ComplexNullMixture,
        F ⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩ = energy c.1.1 := by
  refine ⟨paperNativeSpectralEnergy, paperNativeSpectralEnergy_apply, ?_⟩
  intro F hF
  funext μ
  rcases μ with ⟨μ, a, rfl⟩
  exact (hF a).trans (paperNativeSpectralEnergy_apply a).symm

/-- Intrinsic full energy is nowhere continuous on its actual native domain. -/
theorem not_continuousAt_paperNativeSpectralEnergy
    (μ : Set.range spectralRepresentingMeasure) :
    ¬ ContinuousAt paperNativeSpectralEnergy μ := by
  rcases μ with ⟨μ, a, rfl⟩
  intro h
  obtain ⟨c, hc, he⟩ := exists_spectralRepresentingMeasure_tendsto_energy_atTop a
  let a' : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure a, Set.mem_range_self a⟩
  let c' (n : ℕ) : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure (c n), Set.mem_range_self (c n)⟩
  have hc' : Tendsto c' atTop (𝓝 a') := tendsto_subtype_rng.mpr hc
  have hlim : Tendsto (fun n => energy (c n).1.1) atTop (𝓝 (energy a.1.1)) := by
    simpa only [Function.comp_def, c', a', paperNativeSpectralEnergy_apply] using h.tendsto.comp hc'
  exact not_tendsto_nhds_of_tendsto_atTop he _ hlim

end RHTower.WeilWorkPBAP
