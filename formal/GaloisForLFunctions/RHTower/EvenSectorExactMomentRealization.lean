import GaloisForLFunctions.RHTower.EvenSectorCompactBoundaryRigidity
import GaloisForLFunctions.RHTower.EvenSectorPositiveBlindEnergy

/-!
# Exact single-source realization of all arithmetic and energy moments

Every actual nonnegative finite mixture of compact C² Weil sources has the
same whole arithmetic trace and the same literal archimedean energy as one
compact smooth even pole-free source. The equality concerns actual sources,
without closure, an error term, or an assumed sign of the Weil functional.

Compact boundary rigidity supplies strict descent, a positive blind bump
fills the energy difference, and exact smooth scalarization removes the
resulting finite mixture.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped NNReal
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

private theorem zero_moments_of_zero_active_sources (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (hz : ¬ ∃ f, 0 < c f ∧ f.1 ≠ 0) :
    linearCombination ℝ logVector c = 0 ∧ fullMixtureEnergy c = 0 := by
  have hsource (f : WeilTestFn) (hf : f ∈ c.support) : f.1 = 0 := by
    by_contra h
    exact hz ⟨f, lt_of_le_of_ne (hc f) (Finsupp.mem_support_iff.mp hf).symm, h⟩
  have htrace (f : WeilTestFn) (hf : f ∈ c.support) : logVector f = 0 := by
    ext j
    simp [logVector_apply, logValue, hsource f hf, EF.weilTest]
  have henergy (f : WeilTestFn) (hf : f ∈ c.support) :
      weilArchRe (EF.weilTest f.1 f.1) = 0 := by
    simp [hsource f hf, EF.weilTest, weilArchRe, paperFT]
  constructor
  · rw [linearCombination_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun f hf => by rw [htrace f hf, smul_zero]
  · rw [fullMixtureEnergy, linearCombination_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun f hf => by rw [henergy f hf, smul_zero]

theorem exists_single_smooth_exact_moments (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) :
    ∃ f : SmoothEvenPolarTestFn,
      logVector f.1.1 = linearCombination ℝ logVector c ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) = fullMixtureEnergy c := by
  by_cases hne : ∃ f, 0 < c f ∧ f.1 ≠ 0
  · obtain ⟨d, hd, hdt, hde⟩ := exists_full_mixture_strict_descent c hc hne
    have hε : 0 < (fullMixtureEnergy c - fullMixtureEnergy d) / 2 := by linarith
    obtain ⟨f, hft, hfe⟩ := exists_single_smooth_fibre_recovery d hd hε
    have hbelow : weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) ≤ fullMixtureEnergy c := by
      linarith
    obtain ⟨g, hgt, hge⟩ := exists_smooth_source_energy_raise f hbelow
    exact ⟨g, hgt.trans (hft.trans hdt), hge⟩
  · obtain ⟨ht, he⟩ := zero_moments_of_zero_active_sources c hc hne
    obtain ⟨f, _, hft, hfe⟩ := exists_smooth_scalarization_moments 0 (fun _ => le_rfl)
    refine ⟨f, ?_, ?_⟩
    · simpa only [map_zero, ht] using hft
    · simpa only [map_zero, he] using hfe

/-- **Exact EWU moment realization, unconditionally.** Any actual finite
nonnegative C² mixture has one smooth compact even pole-free source with
exactly its entire arithmetic trace and exactly its actual energy. -/
theorem full_mixture_single_smooth_exact_moments (c : WeilTestFn →₀ ℝ≥0) :
    ∃ f : SmoothEvenPolarTestFn,
      logVector f.1.1 = linearCombination ℝ logVector (nonnegativeRealCoefficients c) ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) =
        fullMixtureEnergy (nonnegativeRealCoefficients c) :=
  exists_single_smooth_exact_moments _ (nonnegativeRealCoefficients_nonneg c)

/-- Actual energies of single smooth even pole-free sources in one whole trace fibre. -/
def singleSmoothEnergyFibre (v : LogIndex →₀ ℝ) : Set ℝ :=
  {E | ∃ f : SmoothEvenPolarTestFn, logVector f.1.1 = v ∧
    weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) = E}

/-- **The actual fibre equality.** No completion or epigraph is needed to
remove positive convexification, arbitrary C² sources, or the parity and pole restrictions. -/
theorem singleSmooth_energy_fibre_eq (v : LogIndex →₀ ℝ) :
    singleSmoothEnergyFibre v = nodeFibre v := by
  classical
  ext E
  constructor
  · rintro ⟨f, ht, he⟩
    refine ⟨Finsupp.single f.1.1 1, ?_, ?_, ?_⟩
    · intro g
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    · simpa only [nodeVector_single_test] using ht
    · simpa only [nodeArchEnergy_single_test] using he
  · rintro ⟨c, hc, ht, he⟩
    obtain ⟨f, hft, hfe⟩ := exists_single_smooth_exact_moments c hc
    exact ⟨f, hft.trans ht, hfe.trans he⟩

end RHTower.EvenSector
