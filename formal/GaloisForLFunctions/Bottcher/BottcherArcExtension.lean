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
Schwarz reflection across the unit circle (`harmonicOnNhd_reflectCircle`): the extension is the *odd
reflection* `reflectCircle u₀`, harmonic on a ball straddling the circle.  What remains is exactly the
**Green boundary regularity** of the exterior Böttcher map, packaged as an *extended potential* `u₀`:
harmonic on the exterior side, agreeing there with `log‖β∘γ‖` (`houter`), continuous up to the arc
(`hcont`), and **vanishing on the arc** (`hzero`, i.e. `‖β∘γ‖ → 1`).  Note `u₀` is a genuine extension:
on the arc `β∘γ` is not defined (its argument is a Julia point), so the boundary value `0` is the Green
*limit*, not the pointwise `log‖β∘γ‖`.  Under those data (plus the local-biholomorphism / basin
geometry), the branch `β` continues analytically across the frontier point `z₀`. -/
theorem continuesAcross_of_greenBoundaryRegularity
    {c₁ : ℂ} {β φ γ : ℂ → ℂ} {u₀ : ℂ → ℝ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/2) (hw₀ : ‖φ z₀‖ = 1)
    (hφAt : AnalyticAt ℂ φ z₀)
    (hγφ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖)
    (hβγhol : DifferentiableOn ℂ (fun w => β (γ w))
      (Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}))
    (hβγne : ∀ w ∈ Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}, β (γ w) ≠ 0)
    (hharm : ∀ w ∈ Metric.ball (φ z₀) r, 1 < ‖w‖ → InnerProductSpace.HarmonicAt u₀ w)
    (hcont : ContinuousOn u₀ ({w : ℂ | 1 ≤ ‖w‖} ∩ Metric.ball (φ z₀) r))
    (hzero : ∀ w ∈ Metric.ball (φ z₀) r, ‖w‖ = 1 → u₀ w = 0)
    (houter : ∀ w ∈ Metric.ball (φ z₀) r, 1 < ‖w‖ → u₀ w = Real.log ‖β (γ w)‖) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨r₁, hr₁0, hr₁r, hharmRefl⟩ :=
    harmonicOnNhd_reflectCircle hr hr1 hw₀ hharm hcont hzero
  refine continuesAcross_of_greenPotential_harmonic_extension hr₁0 hw₀ hφAt hγφ hbasin
    (hβγhol.mono (fun w hw => ⟨Metric.ball_subset_ball hr₁r hw.1, hw.2⟩))
    (fun w hw => hβγne w ⟨Metric.ball_subset_ball hr₁r hw.1, hw.2⟩) hharmRefl ?_
  intro w hw
  rw [reflectCircle_outer (le_of_lt hw.2)]
  exact houter w (Metric.ball_subset_ball hr₁r hw.1) hw.2

/-- **KW extension across a smooth Julia arc — the isolated geometric input.**  Taking the extended
potential to be the *global* dynamical Green function `u₀ = greenFunctionDyn c₁ ∘ γ` (`= 0` on `K_{c₁}`,
`= greenLimit` on the basin), the two potential-theoretic boundary inputs are already discharged by the
tree: `continuous_greenFunctionDyn` gives continuity up to the arc for free, and
`greenFunctionDyn_eq_zero_iff` gives vanishing wherever `γ` lands in `K_{c₁}`.  The harmonic input comes
from `harmonicOnNhd_greenLimit_basin`, and outer agreement `log‖β∘γ‖ = greenFunctionDyn ∘ γ` is the
**global** Böttcher modulus `hβmod` (`‖β‖ = exp(green)` on the whole basin — `norm_eq_exp_green_basin`),
valid at the *frontier* arc (not just the far escape region).  The holomorphy/nonvanishing of `β∘γ` are
derived from `β` analytic-nonvanishing on the basin.  What is left is exactly the **geometric** content
of the smooth piece: `γ` maps the exterior side into the basin (`hγbasin`) and the arc `{‖w‖ = 1}` into
the filled Julia set (`hγarc`) — i.e. the branch `φ` carries the smooth Julia arc to the unit circle.
Under those data, `β` continues analytically across `z₀`. -/
theorem continuesAcross_of_smoothJuliaArc
    {c₁ : ℂ} {β φ γ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/2) (hw₀ : ‖φ z₀‖ = 1)
    (hφAt : AnalyticAt ℂ φ z₀)
    (hγφ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγAn : ∀ w ∈ Metric.ball (φ z₀) r, AnalyticAt ℂ γ w)
    (hγbasin : ∀ w ∈ Metric.ball (φ z₀) r, 1 < ‖w‖ → γ w ∈ (filledJulia c₁)ᶜ)
    (hγarc : ∀ w ∈ Metric.ball (φ z₀) r, ‖w‖ = 1 → γ w ∈ filledJulia c₁) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  have hγcont : ContinuousOn γ (Metric.ball (φ z₀) r) :=
    fun w hw => (hγAn w hw).continuousAt.continuousWithinAt
  -- `β ∘ γ` holomorphic and nonvanishing on the exterior side (from `β` on the basin)
  have hβγhol : DifferentiableOn ℂ (fun w => β (γ w))
      (Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}) := fun w hw =>
    ((hβan (γ w) (hγbasin w hw.1 hw.2)).comp (hγAn w hw.1)).differentiableAt.differentiableWithinAt
  have hβγne : ∀ w ∈ Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}, β (γ w) ≠ 0 := fun w hw =>
    norm_ne_zero_iff.mp (by rw [hβmod (γ w) (hγbasin w hw.1 hw.2)]; exact (Real.exp_pos _).ne')
  refine continuesAcross_of_greenBoundaryRegularity (u₀ := fun w => greenFunctionDyn c₁ (γ w))
    hr hr1 hw₀ hφAt hγφ hbasin hβγhol hβγne ?_ ?_ ?_ ?_
  · -- `greenFunctionDyn ∘ γ` is harmonic on the exterior side
    intro w hw hnorm
    have hbasinw := hγbasin w hw hnorm
    have hglHarm : InnerProductSpace.HarmonicAt (fun v => greenLimit c₁ (γ v)) w :=
      harmonicAt_comp_analytic (harmonicOnNhd_greenLimit_basin c₁ (γ w) hbasinw) (hγAn w hw)
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hglHarm
    have hopen : IsOpen (Metric.ball (φ z₀) r ∩ {w : ℂ | 1 < ‖w‖}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const continuous_norm)
    filter_upwards [hopen.mem_nhds ⟨hw, hnorm⟩] with v hv
    rw [greenFunctionDyn, if_neg (hγbasin v hv.1 hv.2)]
  · -- continuity up to the arc — from global continuity of `greenFunctionDyn`
    exact (continuous_greenFunctionDyn c₁).comp_continuousOn (hγcont.mono inter_subset_right)
  · -- vanishing on the arc — `γ` lands in `K_{c₁}`
    intro w hw hnorm
    show greenFunctionDyn c₁ (γ w) = 0
    exact (greenFunctionDyn_eq_zero_iff c₁ (γ w)).mpr (hγarc w hw hnorm)
  · -- outer agreement `greenFunctionDyn ∘ γ = log‖β∘γ‖` (global Böttcher modulus)
    intro w hw hnorm
    show greenFunctionDyn c₁ (γ w) = Real.log ‖β (γ w)‖
    rw [hβmod (γ w) (hγbasin w hw hnorm), Real.log_exp]

/-- **Böttcher continuation across a smooth arc from the two `z`-space side facts.**  At a non-critical
frontier arc point `z₀` (`deriv φ z₀ ≠ 0`, `‖φ z₀‖ = 1`), the modulus-one locus of `φ` is a local
separator.  Given only that the exterior germ `{‖φ‖ > 1}` lies in the basin (`hOutBasin`) and the
interior germ `{‖φ‖ < 1}` in the filled set (`hInFilled`), the modulus-one arc itself is forced into
`J₁` — every `{‖φ‖ = 1}` point has basin on one side and interior on the other, hence is a frontier
point (formalised as a closure/`NeBot` limit).  Constructing the local inverse `γ = φ⁻¹` and feeding
`continuesAcross_of_smoothJuliaArc`, `β` continues analytically across `z₀`.  This reduces the geometry
to the two atomic **which-side** facts, discharging the local-inverse construction and the
arc-is-frontier separation. -/
theorem continuesAcross_of_smoothArcSides
    {c₁ : ℂ} {β φ : ℂ → ℂ} {z₀ : ℂ}
    (hφAt : AnalyticAt ℂ φ z₀) (hd0 : deriv φ z₀ ≠ 0) (hmod : ‖φ z₀‖ = 1)
    (hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖)
    (hOutBasin : ∀ᶠ z in 𝓝 z₀, 1 < ‖φ z‖ → z ∈ (filledJulia c₁)ᶜ)
    (hInFilled : ∀ᶠ z in 𝓝 z₀, ‖φ z‖ < 1 → z ∈ filledJulia c₁)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  obtain ⟨γ, hγAn0, hγleft, hγright⟩ := exists_localInverse_of_continuation hφAt hd0
  have hγz₀ : γ (φ z₀) = z₀ := hγleft.self_of_nhds
  have htend : Tendsto γ (𝓝 (φ z₀)) (𝓝 z₀) := by
    have h : Tendsto γ (𝓝 (φ z₀)) (𝓝 (γ (φ z₀))) := hγAn0.continuousAt
    rwa [hγz₀] at h
  have hOut' : ∀ᶠ w in 𝓝 (φ z₀), 1 < ‖φ (γ w)‖ → γ w ∈ (filledJulia c₁)ᶜ := htend.eventually hOutBasin
  have hIn' : ∀ᶠ w in 𝓝 (φ z₀), ‖φ (γ w)‖ < 1 → γ w ∈ filledJulia c₁ := htend.eventually hInFilled
  have hev : ∀ᶠ w in 𝓝 (φ z₀), AnalyticAt ℂ γ w ∧ φ (γ w) = w ∧
      (1 < ‖φ (γ w)‖ → γ w ∈ (filledJulia c₁)ᶜ) ∧ (‖φ (γ w)‖ < 1 → γ w ∈ filledJulia c₁) :=
    hγAn0.eventually_analyticAt |>.and <| hγright.and <| hOut'.and hIn'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set r : ℝ := min ε (1/2) with hrdef
  have hball' : ∀ w ∈ Metric.ball (φ z₀) r, AnalyticAt ℂ γ w ∧ φ (γ w) = w ∧
      (1 < ‖φ (γ w)‖ → γ w ∈ (filledJulia c₁)ᶜ) ∧ (‖φ (γ w)‖ < 1 → γ w ∈ filledJulia c₁) :=
    fun w hw => hball (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  refine continuesAcross_of_smoothJuliaArc (lt_min hε (by norm_num)) (min_le_right _ _) hmod hφAt
    (nhdsWithin_le_nhds hγleft) hbasin hβan hβmod (fun w hw => (hball' w hw).1) ?_ ?_
  · -- exterior side maps into the basin
    intro w hw hnorm
    obtain ⟨_, hφγ, hout, _⟩ := hball' w hw
    exact hout (by rw [hφγ]; exact hnorm)
  · -- arc maps into `J₁`: `γ w` is a limit of `{‖φ‖ < 1}` points, all in the (closed) filled set
    intro w hw hnorm
    have hnebot : (𝓝[Metric.ball (0:ℂ) 1] w).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [closure_ball (0:ℂ) (by norm_num)]
      simp [Metric.mem_closedBall, hnorm]
    have hcw : Tendsto γ (𝓝[Metric.ball (0:ℂ) 1] w) (𝓝 (γ w)) :=
      (hball' w hw).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ w' in 𝓝[Metric.ball (0:ℂ) 1] w, γ w' ∈ filledJulia c₁ := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw)] with w' hw'disk hw'ball
      obtain ⟨_, hφγ, _, hin⟩ := hball' w' hw'ball
      refine hin ?_
      rw [hφγ]
      have := Metric.mem_ball.mp hw'disk
      rwa [dist_zero_right] at this
    have := mem_closure_of_tendsto hcw hmem
    rwa [(isClosed_filledJulia c₁).closure_eq] at this

/-- **Böttcher continuation across a smooth arc from the basin-branch identification.**  The whole
geometry is discharged from a single input: on the basin side of a neighbourhood of a non-critical
frontier point `z₀`, the arc branch `φ` *equals the Böttcher branch* `β` (`hgβ`).  Then the global
modulus makes `‖φ‖ = ‖β‖ = exp(green) > 1` strictly on the basin (so `{‖φ‖ < 1}` avoids the basin —
`hInFilled`), `‖φ‖ = 1` on the frontier arc (`norm_continuation_eq_one_on_frontier`), and the exterior
germ `{‖φ‖ > 1}` — a *connected* set (image of `ball ∩ exterior` under the local inverse `γ`) meeting
the basin and avoiding `J₁` — lies wholly in the basin (`IsPreconnected.subset_left_of_subset_union`),
giving `hOutBasin`.  `continuesAcross_of_smoothArcSides` then produces the continuation.  This reduces
the smooth-piece boundary content to the **root-matching** `φ = β` on the basin. -/
theorem continuesAcross_of_basinBranch
    {c₁ : ℂ} {β φ : ℂ → ℂ} {z₀ : ℂ}
    (hφAt : AnalyticAt ℂ φ z₀) (hd0 : deriv φ z₀ ≠ 0) (hmod : ‖φ z₀‖ = 1)
    (hz₀front : z₀ ∈ frontier (filledJulia c₁))
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c₁)ᶜ → φ z = β z)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) :
    U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀ := by
  classical
  have hgreenpos : ∀ z ∈ (filledJulia c₁)ᶜ, 0 < greenFunctionDyn c₁ z := by
    intro z hz
    rcases (greenFunctionDyn_nonneg c₁ z).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c₁ z).mp h.symm) hz
  obtain ⟨δ₀, hδ₀, hballz⟩ :=
    Metric.eventually_nhds_iff.mp (hgβ.and hφAt.eventually_analyticAt)
  have hφ1front : ∀ z' ∈ Metric.ball z₀ δ₀, z' ∈ frontier (filledJulia c₁) → ‖φ z'‖ = 1 := by
    intro z' hz'U hz'f
    refine norm_continuation_eq_one_on_frontier hβmod Metric.isOpen_ball
      (fun z hz => (hballz (Metric.mem_ball.mp hz)).2) (fun z hz => ?_) hz'U hz'f
    exact (hballz (Metric.mem_ball.mp hz.1)).1 hz.2
  obtain ⟨γ, hγAn0, hγleft, hγright⟩ := exists_localInverse_of_continuation hφAt hd0
  have hγz₀ : γ (φ z₀) = z₀ := hγleft.self_of_nhds
  have hγtend : Tendsto γ (𝓝 (φ z₀)) (𝓝 z₀) := by
    have h : Tendsto γ (𝓝 (φ z₀)) (𝓝 (γ (φ z₀))) := hγAn0.continuousAt
    rwa [hγz₀] at h
  have hγpre : ∀ᶠ w in 𝓝 (φ z₀), γ w ∈ Metric.ball z₀ δ₀ := hγtend (Metric.ball_mem_nhds z₀ hδ₀)
  obtain ⟨ε₀, hε₀, hballw⟩ :=
    Metric.eventually_nhds_iff.mp (hγAn0.eventually_analyticAt.and (hγright.and hγpre))
  set ε : ℝ := min ε₀ (1/2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε2 : ε ≤ 1/2 := min_le_right _ _
  have hballw' : ∀ w ∈ Metric.ball (φ z₀) ε,
      AnalyticAt ℂ γ w ∧ φ (γ w) = w ∧ γ w ∈ Metric.ball z₀ δ₀ :=
    fun w hw => hballw (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  set W : Set ℂ := Metric.ball (φ z₀) ε ∩ {w : ℂ | 1 < ‖w‖} with hWdef
  have hWconn : IsPreconnected W := isPreconnected_ball_inter_exterior hmod hε hε2
  set s : Set ℂ := γ '' W with hsdef
  have hsconn : IsPreconnected s :=
    hWconn.image γ (fun w hw => (hballw' w hw.1).1.continuousAt.continuousWithinAt)
  have hdecomp : ∀ z, z ∉ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₁)ᶜ ∪ interior (filledJulia c₁) := by
    intro z hz
    by_cases hzK : z ∈ filledJulia c₁
    · exact Or.inr (by by_contra hint; exact hz ⟨subset_closure hzK, hint⟩)
    · exact Or.inl hzK
  have hsdisj : s ⊆ (filledJulia c₁)ᶜ ∪ interior (filledJulia c₁) := by
    rintro p ⟨w, hwW, rfl⟩
    apply hdecomp
    intro hpf
    have hp1 : ‖φ (γ w)‖ = 1 := hφ1front (γ w) (hballw' w hwW.1).2.2 hpf
    rw [(hballw' w hwW.1).2.1] at hp1
    have h2 : 1 < ‖w‖ := hwW.2
    rw [hp1] at h2
    exact lt_irrefl 1 h2
  have hdisjuv : Disjoint ((filledJulia c₁)ᶜ) (interior (filledJulia c₁)) := by
    rw [Set.disjoint_iff]; intro z ⟨h1, h2⟩; exact h1 (interior_subset h2)
  have hbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖ := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hδ₀), self_mem_nhdsWithin]
      with z hzU hzKc
    rw [(hballz (Metric.mem_ball.mp hzU)).1 hzKc, hβmod z hzKc]
    exact Real.one_lt_exp_iff.mpr (hgreenpos z hzKc)
  have hnebot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure (by rwa [frontier_compl]))
  have hwit : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀,
      1 < ‖φ z‖ ∧ φ z ∈ Metric.ball (φ z₀) ε ∧ γ (φ z) = z ∧ z ∈ (filledJulia c₁)ᶜ := by
    filter_upwards [hbasin,
      nhdsWithin_le_nhds (hφAt.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (φ z₀) hε)),
      nhdsWithin_le_nhds hγleft, self_mem_nhdsWithin] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨zb, hzb1, hzbball, hzbleft, hzbKc⟩ := hwit.exists
  have hsmeet : (s ∩ (filledJulia c₁)ᶜ).Nonempty :=
    ⟨zb, ⟨φ zb, ⟨hzbball, hzb1⟩, hzbleft⟩, hzbKc⟩
  have hsK : s ⊆ (filledJulia c₁)ᶜ :=
    hsconn.subset_left_of_subset_union ((isClosed_filledJulia c₁).isOpen_compl) isOpen_interior
      hdisjuv hsdisj hsmeet
  have hOutBasin : ∀ᶠ z in 𝓝 z₀, 1 < ‖φ z‖ → z ∈ (filledJulia c₁)ᶜ := by
    filter_upwards [hφAt.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (φ z₀) hε), hγleft]
      with z hzball hzleft hznorm
    exact hsK ⟨φ z, ⟨hzball, hznorm⟩, hzleft⟩
  have hInFilled : ∀ᶠ z in 𝓝 z₀, ‖φ z‖ < 1 → z ∈ filledJulia c₁ := by
    filter_upwards [hgβ] with z hgβz hlt
    by_contra hzK
    rw [hgβz hzK, hβmod z hzK] at hlt
    have := Real.one_le_exp (greenFunctionDyn_nonneg c₁ z)
    linarith
  exact continuesAcross_of_smoothArcSides hφAt hd0 hmod hbasin hOutBasin hInFilled hβan hβmod

/-- **The smooth-arc geometric datum — the harmonic-reflection replacement of `ArcReflectionData`.**
For a non-constant analytic `φ` with modulus one on a relatively-open frontier piece `P`, there is a
frontier arc point `z₀` and a local inverse `γ` of `φ` carrying the exterior side `{‖w‖ > 1}` into the
basin and the arc `{‖w‖ = 1}` into the filled Julia set.  Unlike `ArcReflectionData`, this datum asks
for **no pre-existing reflected extension** of `β`: the continuation is *constructed* by the harmonic
Schwarz reflection of the Green potential (`continuesAcross_of_smoothJuliaArc`).  Its only content is
the geometry of the smooth piece — `φ` is a local biholomorphism carrying the smooth Julia arc to the
unit circle. -/
def GreenArcData (c₁ : ℂ) : Prop :=
  ∀ (φ : ℂ → ℂ) (Ω P : Set ℂ), IsOpen Ω → IsPreconnected Ω → AnalyticOnNhd ℂ φ Ω →
    (∃ z' ∈ Ω, deriv φ z' ≠ 0) → P ⊆ Ω → P ⊆ frontier (filledJulia c₁) →
    (∃ Uop, IsOpen Uop ∧ (Uop ∩ P).Nonempty) → (∀ z ∈ P, ‖φ z‖ = 1) →
    ∃ (z₀ : ℂ) (γ : ℂ → ℂ) (r : ℝ), z₀ ∈ frontier (filledJulia c₁) ∧ 0 < r ∧ r ≤ 1 / 2 ∧
      ‖φ z₀‖ = 1 ∧ AnalyticAt ℂ φ z₀ ∧
      (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, γ (φ z) = z) ∧
      (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖) ∧
      (∀ w ∈ Metric.ball (φ z₀) r, AnalyticAt ℂ γ w) ∧
      (∀ w ∈ Metric.ball (φ z₀) r, 1 < ‖w‖ → γ w ∈ (filledJulia c₁)ᶜ) ∧
      (∀ w ∈ Metric.ball (φ z₀) r, ‖w‖ = 1 → γ w ∈ filledJulia c₁)

/-- **`ReflectionCore` ⟸ `GreenArcData` — the harmonic route.**  Given the smooth-arc geometry
(`GreenArcData`) and the global Böttcher modulus `hβmod` (`‖β‖ = exp(green)` on the basin, carried by
every branch produced by the tree's colimit construction), `ReflectionCore c₁ β` holds: the
continuation across the arc is the harmonic reflection of the Green potential
(`continuesAcross_of_smoothJuliaArc`).  This lands the entire harmonic Schwarz-reflection stack on the
reflection-core input of the general both-connected gatekeeper — non-circular, requiring no
holomorphic-extension hypothesis, only the geometry of the smooth piece and the basin-wide modulus. -/
theorem reflectionCore_of_greenArcData {c₁ : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hdata : GreenArcData c₁) : ReflectionCore c₁ β := by
  intro φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  obtain ⟨z₀, γ, r, hz₀front, hr, hr1, hmod, hφAt, hγφ, hbasin, hγAn, hγbasin, hγarc⟩ :=
    hdata φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  exact ⟨z₀, hz₀front,
    continuesAcross_of_smoothJuliaArc hr hr1 hmod hφAt hγφ hbasin hβan hβmod hγAn hγbasin hγarc⟩

/-- **Smooth-piece rigidity from the smooth-arc geometry alone (harmonic route).**  Composing the
reflection-core reduction with the harmonic Schwarz-reflection stack: for connected
`c₁ ∈ mandelbrot ∖ {0,-2}`, the smooth-arc geometric datum `GreenArcData c₁` (a local biholomorphism
carrying the smooth Julia arc to the unit circle at some frontier piece point) yields
`SmoothPieceRigidity c₁ c₂`.  The branch's modulus `hβmod` and analyticity `hβan` are supplied by the
tree's colimit branch (`hnb_of_mem_mandelbrot_connected`, threaded through
`smoothPieceRigidity_of_reflectionCore`); the continuation across the arc is the harmonic reflection of
the Green potential, contradicting the natural boundary.  This reduces the general both-connected
gatekeeper (#118) to exactly the smooth-piece **geometry** `GreenArcData` — no analytic input remains. -/
theorem smoothPieceRigidity_of_greenArcData {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hdata : GreenArcData c₁) :
    SmoothPieceRigidity c₁ c₂ :=
  smoothPieceRigidity_of_reflectionCore hc₁M hc₁0 hc₁2 hconn₁
    (fun _β hβan _hβesc hβmod => reflectionCore_of_greenArcData hβan hβmod hdata)

/-- **The smooth-arc selection datum — the geometric core, in `z`-space.**  For a non-constant
analytic `φ` with modulus one on a relatively-open frontier piece, there is a *non-critical* arc point
`z₀` (`deriv φ z₀ ≠ 0`) at which the modulus-one locus is the local separator between the basin and the
interior: the basin side has `‖φ‖ > 1` (`hbasin`), the whole `{‖φ‖ > 1}` germ lies in the basin
(`hlevelOut`), and the whole `{‖φ‖ = 1}` germ lies in the filled Julia set (`hlevelArc`).  This is the
residual geometry of the smooth piece (Montel blow-up ⟹ the Julia piece is a real-analytic arc carrying
`φ` to the unit circle with the basin on the exterior side); it references only `φ` and the level sets,
not the local inverse. -/
def SmoothArcSelection (c₁ : ℂ) : Prop :=
  ∀ (φ : ℂ → ℂ) (Ω P : Set ℂ), IsOpen Ω → IsPreconnected Ω → AnalyticOnNhd ℂ φ Ω →
    (∃ z' ∈ Ω, deriv φ z' ≠ 0) → P ⊆ Ω → P ⊆ frontier (filledJulia c₁) →
    (∃ Uop, IsOpen Uop ∧ (Uop ∩ P).Nonempty) → (∀ z ∈ P, ‖φ z‖ = 1) →
    ∃ z₀ ∈ frontier (filledJulia c₁), AnalyticAt ℂ φ z₀ ∧ deriv φ z₀ ≠ 0 ∧ ‖φ z₀‖ = 1 ∧
      (∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, 1 < ‖φ z‖) ∧
      (∀ᶠ z in 𝓝 z₀, 1 < ‖φ z‖ → z ∈ (filledJulia c₁)ᶜ) ∧
      (∀ᶠ z in 𝓝 z₀, ‖φ z‖ = 1 → z ∈ filledJulia c₁)

/-- **`GreenArcData` ⟸ `SmoothArcSelection` — the local-inverse scaffolding.**  Given a non-critical
arc point with the level-set orientation (`SmoothArcSelection`), the local analytic inverse
`γ = φ⁻¹` (`exists_localInverse_of_continuation`) transports the orientation to the geometric datum
`GreenArcData`: on a small disk `ball (φ z₀) r`, `φ(γ w) = w` turns `1 < ‖w‖` into `γ w` in the basin
and `‖w‖ = 1` into `γ w` in the filled Julia set, and `γ` is analytic there.  This isolates the entire
remaining content of the both-connected gatekeeper's boundary half to the `z`-space geometry
`SmoothArcSelection` — all the local-inverse analysis is discharged here. -/
theorem greenArcData_of_smoothArcSelection {c₁ : ℂ} (hsel : SmoothArcSelection c₁) :
    GreenArcData c₁ := by
  intro φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  obtain ⟨z₀, hz₀front, hφAt, hd0, hmod, hbasin, hlevelOut, hlevelArc⟩ :=
    hsel φ Ω P hΩo hΩc hφ hnc hPΩ hPfront hUP hmodP
  obtain ⟨γ, hγAn0, hγleft, hγright⟩ := exists_localInverse_of_continuation hφAt hd0
  have hγz₀ : γ (φ z₀) = z₀ := hγleft.self_of_nhds
  have htend : Tendsto γ (𝓝 (φ z₀)) (𝓝 z₀) := by
    have h : Tendsto γ (𝓝 (φ z₀)) (𝓝 (γ (φ z₀))) := hγAn0.continuousAt
    rwa [hγz₀] at h
  -- gather the eventually-facts on a common disk around `φ z₀`
  have hev : ∀ᶠ w in 𝓝 (φ z₀), AnalyticAt ℂ γ w ∧ φ (γ w) = w ∧
      (1 < ‖φ (γ w)‖ → γ w ∈ (filledJulia c₁)ᶜ) ∧ (‖φ (γ w)‖ = 1 → γ w ∈ filledJulia c₁) :=
    hγAn0.eventually_analyticAt |>.and <| hγright.and <|
      (htend.eventually hlevelOut).and (htend.eventually hlevelArc)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨z₀, γ, min ε (1/2), hz₀front, lt_min hε (by norm_num), min_le_right _ _, hmod, hφAt, ?_,
    hbasin, ?_, ?_, ?_⟩
  · exact nhdsWithin_le_nhds hγleft
  · intro w hw
    exact (hball (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))).1
  · intro w hw hnorm
    obtain ⟨_, hφγ, hout, _⟩ := hball (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
    exact hout (by rw [hφγ]; exact hnorm)
  · intro w hw hnorm
    obtain ⟨_, hφγ, _, harc⟩ := hball (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
    exact harc (by rw [hφγ]; exact hnorm)

/-- **Smooth-piece rigidity from the `z`-space arc geometry (full harmonic route).**  The composition
of the whole harmonic Schwarz-reflection stack: for connected `c₁ ∈ mandelbrot ∖ {0,-2}`, the smooth-arc
selection datum `SmoothArcSelection c₁` — a non-critical frontier arc point at which the `‖φ‖ = 1` level
set separates the basin (`‖φ‖ > 1`) from the interior — yields `SmoothPieceRigidity c₁ c₂`.  This is the
tightest reduction of the both-connected gatekeeper's boundary half: every analytic ingredient (Dirichlet
problem, harmonic max principle, line and circle Koebe reflection, Green boundary regularity, the global
Böttcher modulus, and the local-inverse construction) is discharged, leaving only the level-set geometry
of the smooth piece. -/
theorem smoothPieceRigidity_of_smoothArcSelection {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hsel : SmoothArcSelection c₁) :
    SmoothPieceRigidity c₁ c₂ :=
  smoothPieceRigidity_of_greenArcData hc₁M hc₁0 hc₁2 hconn₁
    (greenArcData_of_smoothArcSelection hsel)

end Bottcher
