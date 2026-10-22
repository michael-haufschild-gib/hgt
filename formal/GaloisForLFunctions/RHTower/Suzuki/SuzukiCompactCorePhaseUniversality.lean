import GaloisForLFunctions.HTGeometry.NestedExhaustionPhaseUniversality

/-!
# Suzuki compact-core phase universality

Suzuki's finite-aperture differential operators have one-dimensional deficiency spaces, but the
compact-test graph exhaustion has a different asymptotic regime whenever its two shifted ranges
are dense: global deficiency is zero.  In that regime every contractive finite boundary block
vanishes strongly, so no extension-angle convergence or phase lock is required.

The theorems here are the exact bounded Cayley surface used by the Suzuki compact-core audit.  The
analytic source step proving density of both global shifted ranges is deliberately explicit as a
hypothesis; under RH it follows on paper from invariant-core essential self-adjointness of the
unitary translation generator.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology Submodule GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Preorder ι]

/-- Dense compact-core shifted ranges make finite Suzuki deficiency projections vanish strongly. -/
theorem tendsto_suzukiCompactCoreDeficiencyProjection_zero
    (HS M : ι → Submodule ℂ E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤) (x : E) :
    Tendsto (fun i => (HS i ⊓ (M i)ᗮ).starProjection x) atTop (𝓝 0) :=
  tendsto_deficiency_starProjection_zero HS M hHS hM hle hdenseHS hdenseM x

/-- **Suzuki phase universality.**  Every finite extension-angle schedule has the same strong
Cayley limit once the compact-core shifted ranges exhaust the global Hilbert space. -/
theorem tendsto_suzukiApertureCayley_allBoundarySchedules
    (HS M : ι → Submodule ℂ E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤)
    (V : E →L[ℂ] E) {W : ι → E →L[ℂ] E} (hW : ∀ i, ‖W i‖ ≤ 1) (x : E) :
    Tendsto (fun i => cayleyAssembly V (W i) (M i).starProjection
      (HS i ⊓ (M i)ᗮ).starProjection x) atTop (𝓝 (V x)) :=
  tendsto_cayleyAssembly_of_dense_nested_ranges HS M hHS hM hle
    hdenseHS hdenseM V hW x

/-- The phase-universal Suzuki Cayley limit gives generalized strong resolvent convergence for
every extension-angle schedule. -/
theorem tendsto_suzukiApertureResolvent_allBoundarySchedules
    (HS M : ι → Submodule ℂ E)
    [∀ i, (HS i).HasOrthogonalProjection] [∀ i, (M i).HasOrthogonalProjection]
    [∀ i, (HS i ⊓ (M i)ᗮ).HasOrthogonalProjection]
    [(⨆ i, HS i).topologicalClosure.HasOrthogonalProjection]
    [(⨆ i, M i).topologicalClosure.HasOrthogonalProjection]
    [((⨆ i, M i).topologicalClosure)ᗮ.HasOrthogonalProjection]
    (hHS : Monotone HS) (hM : Monotone M) (hle : ∀ i, M i ≤ HS i)
    (hdenseHS : (⨆ i, HS i).topologicalClosure = ⊤)
    (hdenseM : (⨆ i, M i).topologicalClosure = ⊤)
    (V : E →L[ℂ] E) {W : ι → E →L[ℂ] E} (hW : ∀ i, ‖W i‖ ≤ 1)
    (c : ℂ) (x : E) :
    Tendsto (fun i => (c • ((HS i).starProjection -
      cayleyAssembly V (W i) (M i).starProjection
        (HS i ⊓ (M i)ᗮ).starProjection)) x) atTop
      (𝓝 (cayleyResolvent c V x)) :=
  tendsto_cayleyResolvent_of_dense_nested_ranges HS M hHS hM hle
    hdenseHS hdenseM V hW c x

end

end GaloisForLFunctions.RHTower
