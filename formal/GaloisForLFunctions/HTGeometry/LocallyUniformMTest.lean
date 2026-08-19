import GaloisForLFunctions.HTGeometry.PeriodicHalfPlaneVanishing

/-!
# A locally uniform Weierstrass M-test

`tendstoUniformlyOn_tsum` is the M-test for a bound that is uniform on the whole set.  Locally
normal convergence only asks for such a bound near each point, and that is what one has for the
series defining the orbit limit of a Gamma monomial, where the dominating constant depends on the
distance to the boundary of the half plane.

The corpus has several bespoke local-normal-convergence bridges but no general one; this is it.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **Locally uniform M-test.**  A summable bound valid near each point gives local normal
convergence. -/
theorem summableLocallyUniformlyOn_of_locally_bounded {ι : Type*} {f : ι → ℂ → ℂ} {U : Set ℂ}
    (h : ∀ x ∈ U, ∃ t ∈ 𝓝[U] x, ∃ u : ι → ℝ, Summable u ∧ ∀ n, ∀ y ∈ t, ‖f n y‖ ≤ u n) :
    SummableLocallyUniformlyOn f U := by
  refine ⟨fun x => ∑' n, f n x, ?_⟩
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  intro v hv x hx
  obtain ⟨t, ht, u, hu, hb⟩ := h x hx
  refine ⟨t, ht, ?_⟩
  exact tendstoUniformlyOn_tsum hu (fun n y hy => hb n y hy) v hv

end

end GaloisForLFunctions.HTGeometry
