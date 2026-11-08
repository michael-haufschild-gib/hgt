import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative
import GaloisForLFunctions.HTGeometry.DirichletStripAlmostPeriodic
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# Zeros of almost periodic functions recur with bounded gaps

**Theorem** (`zeros_recur_of_isStripAlmostPeriodicOn`, Bohr). Let `F` be holomorphic on a closed
vertical strip `|Re z − σ| ≤ r` and almost periodic there: for every `ε` the `ε`-almost periods form
a relatively dense set. Then every isolated zero `ρ` inside the strip recurs with bounded gaps: for
every `ε > 0` there is `L` such that every height interval of length `L` contains `τ` with a zero of
`F` within `ε` of `ρ + iτ`. In particular the zeros of `F` in the strip are transported to every
height (`zero_transport_of_isStripAlmostPeriodicOn`), which is the abscissa law there.

**Dirichlet series** (`zero_transport_of_dirichlet`). This applies to every Dirichlet series that its
partial sums approximate uniformly on closed strips (`isStripAlmostPeriodic_dirichlet`), e.g. on the
half-plane of absolute convergence: a finite top layer of zeros can sit only where the Dirichlet
series is not almost periodic.

The rational one-off of the corpus (`overRegularZeta`) tends to `1` along every vertical line
(`tendsto_overRegularZeta_im_atTop`), so it is almost periodic at large height, and it violates the
abscissa law (`criticalLineFirewall`). Almost periodicity at large height is not enough: the law
needs it uniformly in height, which is what periodicity gives on curves and what `ζ` lacks in the
critical strip.
-/

open Complex Set Filter Topology Metric

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

/-- **Zeros persist under small perturbation, locally.** If `F ρ = 0`, `|F| ≥ m` on the circle of
radius `r` about `ρ`, `g` is holomorphic on the closed disc and `|g − F| < m/2` there, then `g`
vanishes in the open disc. -/
theorem exists_zero_of_near_on {F g : ℂ → ℂ} {ρ : ℂ} {r m : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall ρ r)) (hρ : F ρ = 0)
    (hm : ∀ z ∈ sphere ρ r, m ≤ ‖F z‖)
    (hclose : ∀ z ∈ closedBall ρ r, ‖g z - F z‖ < m / 2) : ∃ z ∈ ball ρ r, g z = 0 := by
  by_contra hno
  push Not at hno
  have hm0 : 0 < m := by
    have := hclose ρ (mem_closedBall_self hr.le)
    rw [hρ, sub_zero] at this
    linarith [norm_nonneg (g ρ)]
  have hsph : ∀ z ∈ sphere ρ r, m / 2 < ‖g z‖ := fun z hz => by
    have h1 := hm z hz
    have h2 := hclose z (sphere_subset_closedBall hz)
    have h3 : ‖F z‖ ≤ ‖g z‖ + ‖g z - F z‖ := by
      calc ‖F z‖ = ‖g z - (g z - F z)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hne : ∀ z ∈ closedBall ρ r, g z ≠ 0 := fun z hz => by
    rcases eq_or_lt_of_le (mem_closedBall.mp hz) with h | h
    · have := hsph z (mem_sphere.mpr h)
      intro h0; rw [h0, norm_zero] at this; linarith
    · exact hno z (mem_ball.mpr h)
  have hcl : closure (ball ρ r) = closedBall ρ r := closure_ball ρ hr.ne'
  have hd : DiffContOnCl ℂ (fun z => (g z)⁻¹) (ball ρ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]
    exact hg.inv hne
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (C := 2 / m) (fun z hz => by
      rw [frontier_ball ρ hr.ne'] at hz
      have := hsph z hz
      rw [norm_inv]
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      linarith) (subset_closure (mem_ball_self hr))
  have hρg : ‖g ρ‖ < m / 2 := by
    have := hclose ρ (mem_closedBall_self hr.le)
    rwa [hρ, sub_zero] at this
  have hgρ : 0 < ‖g ρ‖ := norm_pos_iff.mpr (hne ρ (mem_closedBall_self hr.le))
  rw [norm_inv, inv_le_comm₀ hgρ (by positivity), inv_div] at hmax
  linarith

/-- **Zeros of a strip almost periodic function recur with bounded gaps.** -/
theorem zeros_recur_of_isStripAlmostPeriodicOn {F : ℂ → ℂ} {σ r : ℝ}
    (hap : IsStripAlmostPeriodicOn F σ r)
    (hdiff : ∀ z : ℂ, |z.re - σ| ≤ r → DifferentiableAt ℂ F z)
    {ρ : ℂ} (hρ : F ρ = 0) (hρr : |ρ.re - σ| < r) (hiso : ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), ∃ z ∈ ball (ρ + (τ : ℂ) * I) ε, F z = 0 := by
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ > 0, ∀ z ∈ ball ρ δ, z ≠ ρ → F z ≠ 0 := by
    obtain ⟨U, hU, hUF⟩ := (eventually_nhdsWithin_iff.mp hiso).exists_mem
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    exact ⟨δ, hδ, fun z hz hzρ => hUF z (hball hz) hzρ⟩
  set r' : ℝ := min (ε / 2) (min (δ / 2) ((r - |ρ.re - σ|) / 2)) with hr'
  have hr'ε : r' ≤ ε / 2 := min_le_left _ _
  have hr'δ : r' ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr'r : r' ≤ (r - |ρ.re - σ|) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hr'0 : 0 < r' := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  -- the closed disc lies in the strip
  have hstrip : ∀ z ∈ closedBall ρ r', |z.re - σ| ≤ r := by
    intro z hz
    have h1 : |z.re - ρ.re| ≤ r' := by
      have := abs_re_le_norm (z - ρ)
      rw [sub_re] at this
      exact this.trans (mem_closedBall_iff_norm.mp hz)
    calc |z.re - σ| = |(z.re - ρ.re) + (ρ.re - σ)| := by ring_nf
      _ ≤ |z.re - ρ.re| + |ρ.re - σ| := abs_add_le _ _
      _ ≤ r := by linarith
  -- a positive lower bound of `|F|` on the circle
  have hcont : ContinuousOn (fun z => ‖F z‖) (sphere ρ r') := fun z hz =>
    ((hdiff z (hstrip z (sphere_subset_closedBall hz))).continuousAt.norm).continuousWithinAt
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere ρ r').exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr'0.le) hcont
  set m := ‖F z₀‖ with hmdef
  have hm0 : 0 < m := by
    refine norm_pos_iff.mpr (hδF z₀ ?_ ?_)
    · rw [mem_ball, dist_eq_norm]
      rw [mem_sphere, dist_eq_norm] at hz₀
      linarith
    · intro h
      rw [h, mem_sphere, dist_self] at hz₀
      linarith
  have hm : ∀ z ∈ sphere ρ r', m ≤ ‖F z‖ := fun z hz => hmin hz
  obtain ⟨L, hL, hrel⟩ := hap (m / 4) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hτF⟩ := hrel a
  have hg : DifferentiableOn ℂ (fun z => F (z + (τ : ℂ) * I)) (closedBall ρ r') := by
    intro z hz
    have hz' : |(z + (τ : ℂ) * I).re - σ| ≤ r := by
      simpa using hstrip z hz
    exact ((hdiff _ hz').comp z ((differentiableAt_id).add_const _)).differentiableWithinAt
  obtain ⟨w, hw, hFw⟩ := exists_zero_of_near_on hr'0 hg hρ hm fun z hz => by
    have := hτF z (hstrip z hz)
    linarith
  refine ⟨τ, hτ, w + (τ : ℂ) * I, ?_, hFw⟩
  rw [mem_ball, dist_eq_norm, show w + (τ : ℂ) * I - (ρ + (τ : ℂ) * I) = w - ρ by ring]
  rw [mem_ball, dist_eq_norm] at hw
  linarith

/-- **Zero transport.** Every isolated zero inside the strip has zeros within `ε` of its real part
at every height. -/
theorem zero_transport_of_isStripAlmostPeriodicOn {F : ℂ → ℂ} {σ r : ℝ}
    (hap : IsStripAlmostPeriodicOn F σ r)
    (hdiff : ∀ z : ℂ, |z.re - σ| ≤ r → DifferentiableAt ℂ F z)
    {ρ : ℂ} (hρ : F ρ = 0) (hρr : |ρ.re - σ| < r) (hiso : ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ z : ℂ, F z = 0 ∧ |z.re - ρ.re| < ε ∧ T < z.im := by
  obtain ⟨L, -, hrec⟩ := zeros_recur_of_isStripAlmostPeriodicOn hap hdiff hρ hρr hiso hε
  obtain ⟨τ, hτ, z, hz, hFz⟩ := hrec (T + |ρ.im| + ε)
  refine ⟨z, hFz, ?_, ?_⟩
  · have := abs_re_le_norm (z - (ρ + (τ : ℂ) * I))
    rw [mem_ball, dist_eq_norm] at hz
    simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at this
    simp at this
    linarith
  · have := abs_im_le_norm (z - (ρ + (τ : ℂ) * I))
    rw [mem_ball, dist_eq_norm] at hz
    simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im] at this
    simp at this
    have h1 := (abs_lt.mp (lt_of_le_of_lt this hz)).1
    linarith [neg_abs_le ρ.im, hτ.1]

/-- **Dirichlet series obey the abscissa law where their partial sums converge uniformly.** -/
theorem zero_transport_of_dirichlet {σ R : ℝ} (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ)
    (hconv : ∀ r : ℝ, r < R → ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ z ∈ closedStrip σ r,
      ‖D z - ∑ k ∈ Finset.range n, a k * Complex.exp (-(lam k : ℂ) * z)‖ ≤ ε)
    {r : ℝ} (hrR : r < R) (hdiff : ∀ z : ℂ, |z.re - σ| ≤ r → DifferentiableAt ℂ D z)
    {ρ : ℂ} (hρ : D ρ = 0) (hρr : |ρ.re - σ| < r) (hiso : ∀ᶠ z in 𝓝[≠] ρ, D z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ z : ℂ, D z = 0 ∧ |z.re - ρ.re| < ε ∧ T < z.im :=
  zero_transport_of_isStripAlmostPeriodicOn
    (isStripAlmostPeriodic_dirichlet a lam D hconv r hrR) hdiff hρ hρr hiso hε T

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
