/-
# Local Kellogg–Warschawski boundary extension of the exterior Böttcher map

The sole deep input of the reflection route (`Q62ReflectionTransport.lean`) is the boundary
regularity of the exterior Böttcher branch `β = bottcherCoord c₁` at a smooth Julia arc: that
`β ∘ γ` (with `γ` the local inverse of the biholomorphic branch `φ` carrying the arc to the unit
circle) is continuous up to the circle.  This is **Kellogg–Warschawski** — a conformal map onto a
domain with an analytic boundary arc extends across it.  Because the arc `Λ = γ(unit circle)` is
real-analytic (image of the circle under the holomorphic `γ`), the extension is provable directly by
the **odd reflection of the Green potential**, and mathlib now has the enabling harmonic-function
theory.

The proof here is the load-bearing half — the "modulus regularity ⟹ full-map regularity" upgrade:

* `|β ∘ γ| = exp(u)` on the outer side, where `u = log‖β∘γ‖` is harmonic (`AnalyticAt.harmonicAt_log_norm`);
* the odd reflection of `u` across the circle is harmonic on the whole ball (the hypothesis `hu` —
  the Green-potential harmonic extension; this is the standard harmonic reflection across an analytic
  arc, whose only genuine content is the Green boundary regularity `u → 0` at the circle);
* its harmonic conjugate (`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, mathlib) gives `Φ` analytic
  on the ball with `Re Φ = u`;
* on the connected outer lune (`isPreconnected_ball_inter_exterior`), `(β∘γ)/exp(Φ)` is holomorphic
  with modulus one, hence a unimodular constant `κ` (`eqOn_const_of_norm_const`), so
  `β∘γ = κ·exp(Φ)`;
* `κ·exp(Φ)` is analytic on the *whole* ball — the analytic continuation of `β∘γ` across the circle.
  Pulling back by `φ` and using `‖φ‖ > 1` on the basin gives the continuation of `β` across the
  frontier point `z₀`, i.e. `ContinuesAcross β (filledJulia c₁)ᶜ z₀` — the natural-boundary target.

This reduces the smooth-piece rigidity gatekeeper's boundary input to exactly the *harmonic
extension of the Green potential* (`hu`), turning the argument's argument-continuity — the subtle part
KW is really about — into a theorem.  The residual `hu` is the harmonic reflection of `log‖β∘γ‖`
across the analytic arc, standard and reducing further to the Green boundary regularity `u → 0`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import GaloisForLFunctions.Bottcher.Q62ReflectionTransport
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction
import GaloisForLFunctions.Bottcher.HarmonicReflectionCircle
import Mathlib.Analysis.Complex.Harmonic.Analytic

open Complex Set Filter Topology InnerProductSpace

namespace Bottcher

/-- **Local Kellogg–Warschawski boundary extension (via the Green-potential harmonic reflection).**
At a frontier point `z₀` where the branch `φ` is a local biholomorphism onto the unit circle
(`AnalyticAt φ z₀`, `‖φ z₀‖ = 1`, local inverse `γ`), with `β ∘ γ` holomorphic and nonzero on the
outer side of a ball around `w₀ = φ z₀` and `‖β∘γ‖ = exp(u)` there for a function `u` that extends
harmonically across the circle to the whole ball, the exterior Böttcher branch `β` continues
analytically across `z₀`: `ContinuesAcross β (filledJulia c₁)ᶜ z₀`.  The continuation is
`(κ · exp ∘ Φ) ∘ φ`, where `Φ` is the analytic completion of `u` and `κ` the unimodular constant
matching `β∘γ` to `κ·exp(Φ)` on the connected outer lune. -/
theorem continuesAcross_of_greenPotential_harmonic_extension
    {c₁ : ℂ} {β φ γ : ℂ → ℂ} {u : ℂ → ℝ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hw₀ : ‖φ z₀‖ = 1)
    (hφAt : AnalyticAt ℂ φ z₀)
    (hγφ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖)
    (hβγhol : DifferentiableOn ℂ (fun w => β (γ w))
      (Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}))
    (hβγne : ∀ w ∈ Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}, β (γ w) ≠ 0)
    (hu : HarmonicOnNhd u (Metric.ball (φ z₀) r))
    (hueq : ∀ w ∈ Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}, u w = Real.log ‖β (γ w)‖) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  classical
  set w₀ : ℂ := φ z₀ with hw₀def
  obtain ⟨Φ, hΦan, hΦre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  set r' : ℝ := min r (1/2) with hr'def
  have hr'pos : 0 < r' := lt_min hr (by norm_num)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'half : r' ≤ 1/2 := min_le_right _ _
  set V : Set ℂ := Metric.ball w₀ r' ∩ {w : ℂ | 1 < ‖w‖} with hVdef
  have hVsub : V ⊆ Metric.ball w₀ r ∩ {w : ℂ | 1 < ‖w‖} :=
    fun w hw => ⟨Metric.ball_subset_ball hr'r hw.1, hw.2⟩
  have hVsubball : V ⊆ Metric.ball w₀ r := fun w hw => Metric.ball_subset_ball hr'r hw.1
  have hVc : IsPreconnected V := isPreconnected_ball_inter_exterior hw₀ hr'pos hr'half
  have hVo : IsOpen V := Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)
  -- witness point in V
  set wstar : ℂ := w₀ * ((1 + r'/2 : ℝ) : ℂ) with hwstardef
  have hwstarV : wstar ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, hwstardef,
        show w₀ * ((1 + r'/2 : ℝ) : ℂ) - w₀ = w₀ * ((r'/2 : ℝ) : ℂ) by push_cast; ring,
        norm_mul, hw₀, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · show 1 < ‖wstar‖
      rw [hwstardef, norm_mul, hw₀, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
  -- modulus identities on V
  have hnormBG : ∀ w ∈ V, ‖β (γ w)‖ = Real.exp (u w) := fun w hw => by
    have hpos : (0:ℝ) < ‖β (γ w)‖ := norm_pos_iff.mpr (hβγne w (hVsub hw))
    rw [hueq w (hVsub hw), Real.exp_log hpos]
  have hnormExp : ∀ w ∈ V, ‖Complex.exp (Φ w)‖ = Real.exp (u w) := fun w hw => by
    have hre : (Φ w).re = u w := hΦre (hVsubball hw)
    rw [Complex.norm_exp, hre]
  -- q = βγ / expΦ is holomorphic with modulus 1, hence constant
  have hexpDiff : DifferentiableOn ℂ (fun w => Complex.exp (Φ w)) V :=
    ((hΦan.mono hVsubball).differentiableOn).cexp
  have hqhol : DifferentiableOn ℂ (fun w => β (γ w) / Complex.exp (Φ w)) V :=
    (hβγhol.mono hVsub).div hexpDiff (fun w _ => Complex.exp_ne_zero _)
  have hqnorm : ∀ w ∈ V, ‖β (γ w) / Complex.exp (Φ w)‖ = 1 := fun w hw => by
    rw [norm_div, hnormBG w hw, hnormExp w hw, div_self (Real.exp_pos _).ne']
  have hqconst : Set.EqOn (fun w => β (γ w) / Complex.exp (Φ w))
      (fun _ => (fun w => β (γ w) / Complex.exp (Φ w)) wstar) V :=
    eqOn_const_of_norm_const hVc hVo hqhol hwstarV
      (fun w hw => by rw [hqnorm w hw, hqnorm wstar hwstarV])
  set κ : ℂ := β (γ wstar) / Complex.exp (Φ wstar) with hκdef
  have hBGeq : ∀ w ∈ V, β (γ w) = κ * Complex.exp (Φ w) := fun w hw => by
    have hq := hqconst hw
    simp only at hq
    rw [← hκdef] at hq
    exact (div_eq_iff (Complex.exp_ne_zero _)).mp hq
  -- Θ = κ exp Φ, analytic, continues βγ across the circle
  set Θ : ℂ → ℂ := fun w => κ * Complex.exp (Φ w) with hΘdef
  have hΘan : AnalyticOnNhd ℂ Θ (Metric.ball w₀ r) :=
    analyticOnNhd_const.mul hΦan.cexp
  have hΘw₀ : AnalyticAt ℂ Θ w₀ := hΘan w₀ (Metric.mem_ball_self hr)
  have hfAn : AnalyticAt ℂ (fun z => Θ (φ z)) z₀ := hΘw₀.comp hφAt
  -- agreement with β on the basin side
  have hφball : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, φ z ∈ Metric.ball w₀ r' := by
    have hpre : φ ⁻¹' (Metric.ball w₀ r') ∈ 𝓝 z₀ :=
      hφAt.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds w₀ hr'pos)
    exact nhdsWithin_le_nhds hpre
  have hagree : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, Θ (φ z) = β z := by
    filter_upwards [hbasin, hγφ, hφball] with z hz1 hz2 hz3
    have hφzV : φ z ∈ V := ⟨hz3, hz1⟩
    show Θ (φ z) = β z
    rw [hΘdef]
    simp only
    rw [← hBGeq (φ z) hφzV, hz2]
  exact ⟨fun z => Θ (φ z), hfAn, hagree⟩

/-- **Local Kellogg–Warschawski extension from Green boundary regularity alone.**  The `hu`
hypothesis of `continuesAcross_of_greenPotential_harmonic_extension` is now discharged by the harmonic
Schwarz reflection across the unit circle (`harmonicOnNhd_reflectCircle`): the extended potential is the
*odd reflection* `reflectCircle (log‖β∘γ‖)`, harmonic on a ball straddling the circle.  What remains is
exactly the **Green boundary regularity** of the exterior Böttcher map — the outer potential
`u₀ = log‖β∘γ‖` is harmonic on the exterior side, continuous up to the arc, and **vanishes on the arc**
(`hzero`, i.e. `‖β∘γ‖ → 1`).  Under those data (plus the local-biholomorphism / basin-side geometry),
the branch `β` continues analytically across the frontier point `z₀`. -/
theorem continuesAcross_of_greenBoundaryRegularity
    {c₁ : ℂ} {β φ γ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/2) (hw₀ : ‖φ z₀‖ = 1)
    (hφAt : AnalyticAt ℂ φ z₀)
    (hγφ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖)
    (hβγhol : DifferentiableOn ℂ (fun w => β (γ w))
      (Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}))
    (hβγne : ∀ w ∈ Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}, β (γ w) ≠ 0)
    (hharm : ∀ w ∈ Metric.ball (φ z₀) r, 1 < ‖w‖ →
      InnerProductSpace.HarmonicAt (fun v => Real.log ‖β (γ v)‖) w)
    (hcont : ContinuousOn (fun v => Real.log ‖β (γ v)‖)
      ({w : ℂ | 1 ≤ ‖w‖} ∩ Metric.ball (φ z₀) r))
    (hzero : ∀ w ∈ Metric.ball (φ z₀) r, ‖w‖ = 1 → Real.log ‖β (γ w)‖ = 0) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨r₁, hr₁0, hr₁r, hharmRefl⟩ :=
    harmonicOnNhd_reflectCircle hr hr1 hw₀ hharm hcont hzero
  refine continuesAcross_of_greenPotential_harmonic_extension hr₁0 hw₀ hφAt hγφ hbasin
    (hβγhol.mono (fun w hw => ⟨Metric.ball_subset_ball hr₁r hw.1, hw.2⟩))
    (fun w hw => hβγne w ⟨Metric.ball_subset_ball hr₁r hw.1, hw.2⟩) hharmRefl ?_
  intro w hw
  rw [reflectCircle_outer (le_of_lt hw.2)]

end Bottcher
