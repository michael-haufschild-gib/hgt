import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import GaloisForLFunctions.RHTower.PhotonicRotatingCylinderMaterialOverlap
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Sharp material interfaces do not act on all tempered distributions

The source's cylinder indicator is a bounded `L²` multiplier. In a local
normal coordinate at its interface, no continuous action on the *whole*
tempered-distribution space can agree with its point-mass action on both
sides. This rules out a global distributional extension of that material
operator; it does not rule out a restricted-domain Maxwell transmission
relation or the full rotating-cylinder model.
-/

open SchwartzMap

namespace RHTower

private theorem continuous_point_mass :
    Continuous (fun x : ℝ => (TemperedDistribution.delta x : 𝓢'(ℝ, ℂ))) := by
  apply PointwiseConvergenceCLM.continuous_of_continuous_eval
  intro f
  simpa only [TemperedDistribution.delta_apply] using f.continuous

private theorem point_mass_zero_ne_zero :
    (TemperedDistribution.delta (0 : ℝ) : 𝓢'(ℝ, ℂ)) ≠ 0 := by
  intro h
  have hval := congrArg
    (fun u : 𝓢'(ℝ, ℂ) => u GaloisForLFunctions.gaussianSchwartz) h
  simp [GaloisForLFunctions.gaussianSchwartz_apply,
    GaloisForLFunctions.gaussReal] at hval

/-- The literal sharp cutoff, viewed in a normal coordinate, has no
continuous action on all tempered distributions even when its action is
prescribed only on point masses strictly away from the interface. -/
theorem ptr_no_continuous_indicator_extension :
    ¬ ∃ T : 𝓢'(ℝ, ℂ) → 𝓢'(ℝ, ℂ), Continuous T ∧
      (∀ x : ℝ, x < 0 → T (TemperedDistribution.delta x) = 0) ∧
      (∀ x : ℝ, 0 < x →
        T (TemperedDistribution.delta x) = TemperedDistribution.delta x) := by
  rintro ⟨T, hT, hneg, hpos⟩
  let f : ℝ → 𝓢'(ℝ, ℂ) := fun x => T (TemperedDistribution.delta x)
  have hf : Continuous f := hT.comp continuous_point_mass
  have hzero : f 0 = 0 := by
    have hc : IsClosed {x : ℝ | f x = 0} := isClosed_singleton.preimage hf
    have hs : Set.Iio (0 : ℝ) ⊆ {x : ℝ | f x = 0} := by
      intro x hx
      exact hneg x hx
    have hcl := closure_minimal hs hc
    have hm : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
      rw [closure_Iio]
      simp
    exact hcl hm
  have hone : f 0 = TemperedDistribution.delta 0 := by
    have hc : IsClosed {x : ℝ | f x = TemperedDistribution.delta x} :=
      isClosed_eq hf continuous_point_mass
    have hs : Set.Ioi (0 : ℝ) ⊆
        {x : ℝ | f x = TemperedDistribution.delta x} := by
      intro x hx
      exact hpos x hx
    have hcl := closure_minimal hs hc
    have hm : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
      rw [closure_Ioi]
      simp
    exact hcl hm
  exact point_mass_zero_ne_zero (hone.symm.trans hzero)

/-- Source-specific version using the same indicator symbol as the `L²`
material-overlap theorem, on the local half-space normal chart. -/
theorem ptrCylinderSymbol_no_continuous_distribution_action :
    ¬ ∃ T : 𝓢'(ℝ, ℂ) → 𝓢'(ℝ, ℂ), Continuous T ∧
      ∀ x : ℝ, x ≠ 0 →
        T (TemperedDistribution.delta x) =
          ptrCylinderSymbol (Set.Ioi (0 : ℝ)) x • TemperedDistribution.delta x := by
  rintro ⟨T, hT, hpoint⟩
  apply ptr_no_continuous_indicator_extension
  refine ⟨T, hT, ?_, ?_⟩
  · intro x hx
    have hne : x ≠ 0 := ne_of_lt hx
    rw [hpoint x hne]
    simp [ptrCylinderSymbol, not_lt.mpr (le_of_lt hx)]
  · intro x hx
    have hne : x ≠ 0 := ne_of_gt hx
    rw [hpoint x hne]
    simp [ptrCylinderSymbol, hx]

end RHTower
