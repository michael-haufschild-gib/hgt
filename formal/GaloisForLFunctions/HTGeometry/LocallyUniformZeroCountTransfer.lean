import GaloisForLFunctions.HTGeometry.ZeroDivisorCount

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Compact-open convergence of holomorphic functions preserves full multiplicity count in
every disc whose boundary is zero-free for the limit. -/
theorem eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
    {α : Type*} {p : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ a, Differentiable ℂ (F a)) (hf : Differentiable ℂ f)
    (huniform : TendstoLocallyUniformly F f p)
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ a in p, zeroSumBall (F a) c r = zeroSumBall f c r := by
  obtain ⟨ε, hε, hstable⟩ := exists_eps_zeroSumBall_eq hr hrR
    isOpen_univ (by simp) hf.differentiableOn hne
  have hcompact : IsCompact (closedBall c R) := isCompact_closedBall c R
  have hconv : TendstoUniformlyOn F f p (closedBall c R) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcompact).mp
      huniform.tendstoLocallyUniformlyOn
  have hclose : ∀ᶠ a in p, ∀ z ∈ closedBall c R, ‖F a z - f z‖ ≤ ε := by
    have hlt := (Metric.tendstoUniformlyOn_iff.mp hconv) ε hε
    filter_upwards [hlt] with a ha
    intro z hz
    have := ha z hz
    simpa only [dist_eq_norm, norm_sub_rev] using this.le
  filter_upwards [hclose] with a ha
  exact (hstable (F a) (hF a).differentiableOn ha).2

end GaloisForLFunctions.HTGeometry
