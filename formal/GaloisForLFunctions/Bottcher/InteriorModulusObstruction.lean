/-
# Interior-nonempty natural-boundary: the open-nodal-set dichotomy branch (toward #118)

Toward `hnb` for interior-NONEMPTY connected `c₁` (hyperbolic-component parameters), the discharge of
`ComponentSideNoncontinuabilityOnJulia` splits on the nodal set `{u = 0}` of `u := log‖g‖`, where `g`
is a hypothetical analytic continuation of the Böttcher branch across a frontier point. This file
supplies the EASY branch of that dichotomy: if `‖g‖ ≡ 1` on a nonempty open set, then `g` is constant,
contradicting `g = φ_{c₁}` being nonconstant on the basin side (`‖φ‖ = exp(G) > 1`). The hard branch
(the nodal arc is real-analytic ⟹ `J_{c₁}` locally analytic ⟹ `c₁ ∈ {0,-2}` via the proven even-FE
`c_mem_of_even_holo_ball`) is handled separately.

Axiom-clean; pure complex analysis (strong maximum modulus + identity theorem).
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Convex.PathConnected
import GaloisForLFunctions.Bottcher.DendriteContinuesAcross
import GaloisForLFunctions.Bottcher.ArcContinuation
import GaloisForLFunctions.Bottcher.ZeroSet
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect
import GaloisForLFunctions.Bottcher.FrontierPerfectGeneral
import GaloisForLFunctions.Bottcher.BoundaryArcCovering

open Complex Metric Set Topology Filter

namespace Bottcher

/-- **The exterior lune at a circle point is connected (unit-circle base case).** For `0 < ε ≤ 1/2`
the region `ball 1 ε ∩ {|w| > 1}` (a lune straddling the unit circle at `w = 1`) is preconnected: it
is star-convex with respect to the outward point `p = 1 + ε/2`. The star-convexity inequality —
`|(1-t)·p + t·q| > 1` for `q` in the lune — is the three-nonnegative-terms decomposition
`|w|² - 1 = a²(|p|²-1) + 2ab(Re(p̄q)-1) + b²(|q|²-1)`, whose cross term is nonnegative because the
lune constraint `|q|>1 ∧ |q-1|<ε` forces `Re(p̄q) = (1+ε/2)·Re(q) ≥ 1` when `ε ≤ 1/2`. Base for the
frontier-separation discharge of interior-nonempty `hnb` (#118): the local level-set geometry of a
Böttcher continuation near a Julia frontier point, with no quasidisk/nodal-set theory. -/
theorem isPreconnected_ball_one_inter_exterior {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1/2) :
    IsPreconnected (Metric.ball (1:ℂ) ε ∩ {w : ℂ | 1 < ‖w‖}) := by
  set S := Metric.ball (1:ℂ) ε ∩ {w : ℂ | 1 < ‖w‖} with hS
  set p : ℂ := ((1 + ε/2 : ℝ) : ℂ) with hp
  have hp_re : p.re = 1 + ε/2 := by rw [hp, Complex.ofReal_re]
  have hp_im : p.im = 0 := by rw [hp, Complex.ofReal_im]
  have hball_conv : Convex ℝ (Metric.ball (1:ℂ) ε) := convex_ball _ _
  have hpmem : p ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have hpe : p - 1 = ((ε/2 : ℝ) : ℂ) := by rw [hp]; push_cast; ring
      rw [hpe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    · show 1 < ‖p‖
      rw [hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hstar : StarConvex ℝ p S := by
    rw [starConvex_iff_segment_subset]
    intro q hq
    obtain ⟨hqball, hqext⟩ := hq
    have hqe : (1:ℝ) < ‖q‖ := hqext
    have hqball' : q ∈ Metric.ball (1:ℂ) ε := hqball
    rw [Metric.mem_ball, Complex.dist_eq] at hqball
    have hq3 : 1 < q.re^2 + q.im^2 := by
      have h1 : (1:ℝ) < ‖q‖^2 := by nlinarith [norm_nonneg q, hqe]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1; nlinarith [h1]
    have hq2 : (q.re - 1)^2 + q.im^2 < ε^2 := by
      have h1 : ‖q - 1‖^2 < ε^2 := by nlinarith [norm_nonneg (q-1), hqball]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h1
      nlinarith [h1]
    have hx : 1 - ε^2/2 < q.re := by nlinarith [hq2, hq3]
    have hsx : 1 ≤ (1 + ε/2) * q.re := by
      have hpos1 : (0:ℝ) < 1 + ε/2 := by linarith
      have hpos2 : (0:ℝ) < q.re - (1 - ε^2/2) := by linarith
      nlinarith [mul_pos hpos1 hpos2, hε, hε2, mul_nonneg hε.le (sq_nonneg ε)]
    have hs21 : (0:ℝ) < (1 + ε/2)^2 - 1 := by nlinarith [hε, sq_nonneg ε]
    intro w hw
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    refine ⟨?_, ?_⟩
    · exact hball_conv hpmem.1 hqball' ha hb hab
    · show 1 < ‖a • p + b • q‖
      have hwre : (a • p + b • q).re = a * (1 + ε/2) + b * q.re := by
        simp only [Complex.add_re, Complex.smul_re, hp_re, smul_eq_mul]
      have hwim : (a • p + b • q).im = b * q.im := by
        simp only [Complex.add_im, Complex.smul_im, hp_im, smul_eq_mul, mul_zero, zero_add]
      have hnorm2 : 1 < ‖a • p + b • q‖^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]
        rcases eq_or_lt_of_le hb with hb0 | hbpos
        · have ha1 : a = 1 := by linarith
          subst ha1
          have hb0' : b = 0 := by linarith
          subst hb0'
          nlinarith [hε, hε2]
        · have hbQ : 0 < b^2 * (q.re^2 + q.im^2 - 1) := by
            apply mul_pos (by positivity) (by linarith [hq3])
          have hA : 0 ≤ a^2 * ((1+ε/2)^2 - 1) := mul_nonneg (sq_nonneg a) hs21.le
          have hM : 0 ≤ 2 * a * b * ((1+ε/2) * q.re - 1) :=
            mul_nonneg (by positivity) (by linarith [hsx])
          nlinarith [hbQ, hA, hM, hab]
      nlinarith [norm_nonneg (a • p + b • q), hnorm2]
  exact (hstar.isPathConnected hpmem).isConnected.isPreconnected

/-- **The exterior lune at any unit-circle point is connected.** For `w₀` on the unit circle
(`‖w₀‖ = 1`) and `0 < ε ≤ 1/2`, the lune `ball w₀ ε ∩ {|w| > 1}` is preconnected. Reduces to the
base case `w₀ = 1` by the rotation `μ(z) = w₀·z`, an isometry (since `‖w₀‖ = 1`) that carries
`ball 1 ε ∩ {|w|>1}` onto `ball w₀ ε ∩ {|w|>1}`; preconnectedness is preserved by the continuous
image. This is the exact connectivity input for the frontier-separation discharge of
interior-nonempty `hnb` (#118): near the boundary value `w₀ = β z₀` (`‖w₀‖ = 1`), the exterior side
of a Böttcher continuation is connected, so it lands wholly in the basin. -/
theorem isPreconnected_ball_inter_exterior {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1/2) :
    IsPreconnected (Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖}) := by
  have hw₀0 : w₀ ≠ 0 := by intro h; rw [h] at hw₀; simp at hw₀
  set μ : ℂ → ℂ := fun z => w₀ * z with hμ
  have hcont : Continuous μ := continuous_const.mul continuous_id
  have hset : Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖}
      = μ '' (Metric.ball (1:ℂ) ε ∩ {w : ℂ | 1 < ‖w‖}) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_ball, Complex.dist_eq,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hb, he⟩
      refine ⟨w₀⁻¹ * w, ⟨?_, ?_⟩, ?_⟩
      · rw [show w₀⁻¹ * w - 1 = w₀⁻¹ * (w - w₀) by rw [mul_sub, inv_mul_cancel₀ hw₀0],
          norm_mul, norm_inv, hw₀]
        simpa using hb
      · rw [norm_mul, norm_inv, hw₀]; simpa using he
      · show w₀ * (w₀⁻¹ * w) = w
        rw [← mul_assoc, mul_inv_cancel₀ hw₀0, one_mul]
    · rintro ⟨z, ⟨hb, he⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show ‖w₀ * z - w₀‖ < ε
        rw [show w₀ * z - w₀ = w₀ * (z - 1) by ring, norm_mul, hw₀, one_mul]; exact hb
      · show 1 < ‖w₀ * z‖
        rw [norm_mul, hw₀, one_mul]; exact he
  rw [hset]
  exact (isPreconnected_ball_one_inter_exterior hε hε2).image μ hcont.continuousOn

/-- **Identity-theorem propagation on the exterior lune.** If a local inverse `γ` (analytic on
`ball w₀ ε`) and the global inverse `ψ` (analytic on the exterior) agree on a neighborhood of one
exterior point `w₁` of the lune `ball w₀ ε ∩ {|w|>1}`, then they agree on the whole exterior side
near `w₀`: `γ w = ψ w` for all exterior `w` near `w₀`. The lune is preconnected
(`isPreconnected_ball_inter_exterior`), `γ` and `ψ` are analytic on it, so the identity theorem
spreads the single-neighborhood agreement across the entire lune. This is the step that converts the
*local* biholomorphic-inverse geometry into the `hγψ` hypothesis consumed by
`continuesAcross_h_of_localInverse` — discharging the frontier-separation input of interior-nonempty
`hnb` (#118) once the seed agreement (from the basin side) is supplied. -/
theorem eqOn_lune_of_seed {γ ψ : ℂ → ℂ} {w₀ w₁ : ℂ} {ε : ℝ}
    (hw₀ : ‖w₀‖ = 1) (hε : 0 < ε) (hε2 : ε ≤ 1/2)
    (hγAn : AnalyticOnNhd ℂ γ (Metric.ball w₀ ε))
    (hψAn : ∀ w ∈ Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖}, AnalyticAt ℂ ψ w)
    (hw₁ : w₁ ∈ Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖})
    (hseed : γ =ᶠ[𝓝 w₁] ψ) :
    ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w = ψ w := by
  set V := Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖} with hV
  have hγV : AnalyticOnNhd ℂ γ V := fun w hw => hγAn w hw.1
  have hψV : AnalyticOnNhd ℂ ψ V := fun w hw => hψAn w hw
  have hVc : IsPreconnected V := isPreconnected_ball_inter_exterior hw₀ hε hε2
  have hEq : Set.EqOn γ ψ V := hγV.eqOn_of_preconnected_of_eventuallyEq hψV hVc hw₁ hseed
  filter_upwards [Metric.ball_mem_nhds w₀ hε] with w hw hwext
  exact hEq ⟨hw, hwext⟩

/-- **The basin side supplies the seed agreement `γ = ψ`.** From a Böttcher continuation `g` across a
frontier point `z₀` (`g z₀ = w₀`), with local inverse `γ` analytic on `ball w₀ ε` and the standard
model data, there is an exterior point `w₁` in the lune `ball w₀ ε ∩ {|w|>1}` and a whole neighborhood
of `w₁` on which `γ = ψ`. Construction: pick a basin point `z₁` near `z₀` (the frontier point makes the
basin accumulate, `nhdsWithin_compl_filledJulia_neBot_of_frontier`) in the domains of all the local
relations; set `w₁ = g z₁ = β z₁`, which lies in the lune (`‖w₁‖ = exp(G_c z₁) > 1`, and `w₁` near
`w₀` by continuity of `g`). Near `w₁`, `γ w ∈ basin` (continuity, `γ w₁ = z₁`) and `g (γ w) = w`, so
`β (γ w) = w`, hence `ψ w = ψ (β (γ w)) = γ w`. This is the seed consumed by `eqOn_lune_of_seed`;
together they discharge the frontier-separation input of interior-nonempty `hnb` (#118) with no
quasidisk topology — the connectivity of the exterior lune does the work that `FrontierSeparation`
was standing in for. -/
theorem eventuallyEq_gamma_psi_seed
    {c : ℂ} {β ψ g γ : ℂ → ℂ} {z₀ w₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀) (hw₀ : g z₀ = w₀)
    (hγAn : AnalyticOnNhd ℂ γ (Metric.ball w₀ ε))
    (hγg : ∀ᶠ z in 𝓝 z₀, γ (g z) = z)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c)ᶜ → g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z) :
    ∃ w₁, w₁ ∈ Metric.ball w₀ ε ∩ {w : ℂ | 1 < ‖w‖} ∧ γ =ᶠ[𝓝 w₁] ψ := by
  haveI hne : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  have hgcont : ContinuousAt g z₀ := hgAt.continuousAt
  obtain ⟨O₀, hO₀sub, hO₀op, hw₀O₀⟩ := _root_.mem_nhds_iff.mp hgγ
  obtain ⟨Oβ, hOβsub, hOβop, hz₀Oβ⟩ := _root_.mem_nhds_iff.mp hgβ
  have hgO₀ : ∀ᶠ z in 𝓝 z₀, g z ∈ O₀ :=
    hgcont (hw₀ ▸ hO₀op.mem_nhds hw₀O₀)
  have hgball : ∀ᶠ z in 𝓝 z₀, g z ∈ Metric.ball w₀ ε :=
    hgcont (hw₀ ▸ Metric.ball_mem_nhds w₀ hε)
  have key : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀,
      z ∈ (filledJulia c)ᶜ ∧ γ (g z) = z ∧ z ∈ Oβ ∧ g z ∈ O₀ ∧ g z ∈ Metric.ball w₀ ε := by
    filter_upwards [self_mem_nhdsWithin, hγg.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (hOβop.mem_nhds hz₀Oβ),
      hgO₀.filter_mono nhdsWithin_le_nhds, hgball.filter_mono nhdsWithin_le_nhds]
      with z hzc hzγg hzOβ hzO₀ hzball
    exact ⟨hzc, hzγg, hzOβ, hzO₀, hzball⟩
  obtain ⟨z₁, hz₁c, hz₁γg, hz₁Oβ, hz₁O₀, hz₁ball⟩ := key.exists
  have hz₁β : g z₁ = β z₁ := hOβsub hz₁Oβ hz₁c
  have hmod1 : 1 < ‖g z₁‖ := by
    rw [hz₁β, hβmod z₁ hz₁c]
    have hG : 0 < greenFunctionDyn c z₁ := by
      rcases (greenFunctionDyn_nonneg c z₁).lt_or_eq with h | h
      · exact h
      · exact absurd ((greenFunctionDyn_eq_zero_iff c z₁).mp h.symm) hz₁c
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hG
  refine ⟨g z₁, ⟨hz₁ball, hmod1⟩, ?_⟩
  have hγc : ContinuousAt γ (g z₁) := (hγAn (g z₁) hz₁ball).continuousAt
  have h1 : ∀ᶠ w in 𝓝 (g z₁), g (γ w) = w := by
    filter_upwards [hO₀op.mem_nhds hz₁O₀] with w hw using hO₀sub hw
  have h2 : ∀ᶠ w in 𝓝 (g z₁), γ w ∈ (filledJulia c)ᶜ := by
    have hmem : (filledJulia c)ᶜ ∈ 𝓝 (γ (g z₁)) := by
      rw [hz₁γg]; exact (isClosed_filledJulia c).isOpen_compl.mem_nhds hz₁c
    exact hγc hmem
  have h3 : ∀ᶠ w in 𝓝 (g z₁), γ w ∈ Oβ := by
    have hmem : Oβ ∈ 𝓝 (γ (g z₁)) := by rw [hz₁γg]; exact hOβop.mem_nhds hz₁Oβ
    exact hγc hmem
  filter_upwards [h1, h2, h3] with w hgγw hγwc hγwβ
  have hβγw : β (γ w) = w := by rw [← hOβsub hγwβ hγwc]; exact hgγw
  have hkey : ψ (β (γ w)) = γ w := hψβ (γ w) hγwc
  rw [hβγw] at hkey
  exact hkey.symm

/-- **`γ = ψ` on the exterior near a frontier point — unconditionally.** From a Böttcher continuation
`g` across a frontier point `z₀` with a local inverse `γ` (analytic on `ball w₀ ε`, `w₀ = g z₀` on the
unit circle) and the standard model data (`ψ` analytic on the exterior, `ψ ∘ β = id`, the Böttcher
modulus), the local inverse agrees with the global inverse on the whole exterior side:
`γ w = ψ w` for exterior `w` near `w₀`. Composes the basin-side seed
(`eventuallyEq_gamma_psi_seed`) with the lune identity-theorem propagation (`eqOn_lune_of_seed`).
**No `FrontierSeparation` hypothesis** — this is exactly the input `continuesAcross_h_of_localInverse`
needs, so it eliminates the genuinely-topological assumption previously carried through the
interior-nonempty `hnb` bridge (#118): the connectivity of the exterior lune replaces it. -/
theorem hγψ_of_continuation
    {c : ℂ} {β ψ g γ : ℂ → ℂ} {z₀ w₀ : ℂ} {ε : ℝ}
    (hw₀norm : ‖w₀‖ = 1) (hε : 0 < ε) (hε2 : ε ≤ 1/2)
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀) (hw₀ : g z₀ = w₀)
    (hγAn : AnalyticOnNhd ℂ γ (Metric.ball w₀ ε))
    (hγg : ∀ᶠ z in 𝓝 z₀, γ (g z) = z)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c)ᶜ → g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hψAn : ∀ w, 1 < ‖w‖ → AnalyticAt ℂ ψ w) :
    ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w = ψ w := by
  obtain ⟨w₁, hw₁mem, hseed⟩ :=
    eventuallyEq_gamma_psi_seed hε hfront hgAt hw₀ hγAn hγg hgγ hgβ hβmod hψβ
  exact eqOn_lune_of_seed hw₀norm hε hε2 hγAn (fun w hw => hψAn w hw.2) hw₁mem hseed

/-- **Constant modulus forces constant.** An analytic (`DifferentiableOn ℂ`) function whose modulus is
constant on a preconnected open set is itself constant there — the strong maximum modulus principle
read through a trivial `IsMaxOn`. -/
theorem eqOn_const_of_norm_const {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (hc : c ∈ U)
    (hconst : ∀ z ∈ U, ‖f z‖ = ‖f c‖) : Set.EqOn f (fun _ => f c) U := by
  apply eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hf hc
  intro z hz
  exact le_of_eq (hconst z hz)

/-- **The open-nodal-set obstruction.** If `g` is analytic on a preconnected open set `U`, its modulus
is `1` on a nonempty open subset `V ⊆ U`, and `‖g‖ ≠ 1` at some point of `U`, then `False`. On a ball
inside `V` the modulus is constant, so `g` is locally constant; the identity theorem spreads the
constant to all of `U`, forcing `‖g‖ ≡ 1` on `U` — contradicting the witness. This is the `u ≡ 0`
branch of the nodal-set dichotomy for the interior-nonempty natural boundary (#118): a hypothetical
continuation `g` of `φ_{c₁}` cannot have `‖g‖ ≡ 1` on an open piece of `interior K_{c₁}` while equaling
the nonconstant `φ_{c₁}` on the basin side. -/
theorem false_of_norm_one_on_open_of_norm_ne
    {g : ℂ → ℂ} {U V : Set ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hVU : V ⊆ U) (hVo : IsOpen V) {v₀ : ℂ} (hv₀ : v₀ ∈ V)
    (hV1 : ∀ z ∈ V, ‖g z‖ = 1)
    {z₁ : ℂ} (hz₁U : z₁ ∈ U) (hz₁ : ‖g z₁‖ ≠ 1) : False := by
  have hgv₀ : ‖g v₀‖ = 1 := hV1 v₀ hv₀
  have hv₀U : v₀ ∈ U := hVU hv₀
  -- a ball around `v₀` inside `V`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo v₀ hv₀
  have hBU : ball v₀ ε ⊆ U := hball.trans hVU
  -- `g` is constant `g v₀` on that ball (constant modulus + strong max modulus)
  have hgconstB : Set.EqOn g (fun _ => g v₀) (ball v₀ ε) := by
    apply eqOn_const_of_norm_const (convex_ball v₀ ε).isPreconnected isOpen_ball
      (hg.mono hBU) (mem_ball_self hε)
    intro z hz
    rw [hV1 z (hball hz), hgv₀]
  -- spread the constant to all of `U` by the identity theorem
  have hgA : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hUo
  have hconstA : AnalyticOnNhd ℂ (fun _ : ℂ => g v₀) U := analyticOnNhd_const
  have hev : g =ᶠ[𝓝 v₀] (fun _ => g v₀) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hgconstB hz
  have hEqU : Set.EqOn g (fun _ => g v₀) U :=
    hgA.eqOn_of_preconnected_of_eventuallyEq hconstA hUc hv₀U hev
  exact hz₁ (by rw [hEqU hz₁U]; exact hgv₀)

/-- **A continuation across a frontier point has modulus one.** If `β` carries the Böttcher modulus
`‖β z‖ = exp(G_c z)` on the basin `(filledJulia c)ᶜ` and `g` is an analytic continuation of `β` across
a frontier point `z₀` (`g` analytic at `z₀`, `g = β` on a basin-side neighborhood), then
`‖g z₀‖ = 1`: the frontier is the unit-modulus level `G_c = 0`. Unconditional foundational brick for
the interior-nonempty natural boundary (#118): whatever `g` does inside `K`, its modulus at the
frontier point is pinned to `1`. -/
theorem norm_continuation_eq_one_at_frontier {c z₀ : ℂ} {β g : ℂ → ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀)
    (hgEq : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀, g w = β w) :
    ‖g z₀‖ = 1 := by
  haveI hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  -- on the basin side, `‖g‖ = exp(G_c)`
  have hmod : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀,
      ‖g w‖ = Real.exp (greenFunctionDyn c w) := by
    filter_upwards [hgEq, self_mem_nhdsWithin] with w hw hwc
    rw [hw, hβmod w hwc]
  -- `‖g ·‖ → ‖g z₀‖` by continuity of the continuation
  have h1 : Tendsto (fun w => ‖g w‖) (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 ‖g z₀‖) :=
    (hgAt.continuousAt.norm).continuousWithinAt.tendsto
  -- `exp(G_c ·) → exp(G_c z₀)` and `‖g ·‖` shares that limit
  have h2 : Tendsto (fun w => Real.exp (greenFunctionDyn c w))
      (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 (Real.exp (greenFunctionDyn c z₀))) :=
    ((Real.continuous_exp.comp (continuous_greenFunctionDyn c)).continuousAt).continuousWithinAt.tendsto
  have h3 : Tendsto (fun w => ‖g w‖) (𝓝[(filledJulia c)ᶜ] z₀)
      (𝓝 (Real.exp (greenFunctionDyn c z₀))) := h2.congr' (Filter.EventuallyEq.symm hmod)
  have hgz0 : greenFunctionDyn c z₀ = 0 :=
    (greenFunctionDyn_eq_zero_iff c z₀).mpr (mem_filledJulia_of_frontier hfront)
  have heq := tendsto_nhds_unique h1 h3
  rw [heq, hgz0, Real.exp_zero]

/-- **The Böttcher-wired `u ≡ 0` obstruction.** Let `g` be an analytic continuation of the Böttcher
branch `β` on a preconnected open `U` containing a frontier point `z₀` (with `g = β` on the basin part
of `U`). If `‖g‖ ≡ 1` on some nonempty open `V ⊆ U`, then `False`. The basin side of `U` supplies a
witness `z₁` with `‖g z₁‖ = exp(G_c z₁) > 1`, and `false_of_norm_one_on_open_of_norm_ne` closes it.
This is the `u ≡ 0` branch of the interior-nonempty natural-boundary dichotomy (#118) in the concrete
Böttcher setting: a continuation cannot have modulus `1` on an open piece of `interior K_{c₁}`. -/
theorem false_of_continuation_norm_one_on_open {c z₀ : ℂ} {β g : ℂ → ℂ} {U V : Set ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hz₀U : z₀ ∈ U)
    (hg : DifferentiableOn ℂ g U)
    (hgβ : ∀ z ∈ U ∩ (filledJulia c)ᶜ, g z = β z)
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hVU : V ⊆ U) (hVo : IsOpen V) {v₀ : ℂ} (hv₀ : v₀ ∈ V)
    (hV1 : ∀ z ∈ V, ‖g z‖ = 1) : False := by
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  -- a basin point of `U` near `z₀`
  obtain ⟨z₁, hz₁U, hz₁Kc⟩ : ∃ z₁, z₁ ∈ U ∧ z₁ ∈ (filledJulia c)ᶜ := by
    obtain ⟨z, hz⟩ := hNeBot.nonempty_of_mem
      (inter_mem (mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hz₀U)) self_mem_nhdsWithin)
    exact ⟨z, hz.1, hz.2⟩
  -- there `‖g‖ = exp(G_c) > 1`, so `‖g‖ ≠ 1`
  have hGpos : 0 < greenFunctionDyn c z₁ := by
    rcases (greenFunctionDyn_nonneg c z₁).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z₁).mp h.symm) hz₁Kc
  have hgz₁ : ‖g z₁‖ = Real.exp (greenFunctionDyn c z₁) := by
    rw [hgβ z₁ ⟨hz₁U, hz₁Kc⟩, hβmod z₁ hz₁Kc]
  have hz₁ne : ‖g z₁‖ ≠ 1 := by
    rw [hgz₁]
    have : (1 : ℝ) < Real.exp (greenFunctionDyn c z₁) := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hGpos
    exact ne_of_gt this
  exact false_of_norm_one_on_open_of_norm_ne hUc hUo hg hVU hVo hv₀ hV1 hz₁U hz₁ne

/-- **A continuation exceeds unit modulus on the basin side.** If `g = β` on the basin part of `U` and
`β` carries the Böttcher modulus, then `1 < ‖g z‖` for every basin point `z ∈ U ∩ (filledJulia c)ᶜ`
(there `‖g z‖ = exp(G_c z)` with `G_c z > 0`). Paired with `norm_continuation_eq_one_at_frontier`
(`‖g z₀‖ = 1` at the frontier), this says the continuation maps the basin side strictly outside the
unit circle and the frontier point onto it — the transversal-crossing datum for the biholomorphic-arc
route to the interior-nonempty natural boundary (#118). -/
theorem norm_continuation_gt_one_of_mem_basin {c : ℂ} {β g : ℂ → ℂ} {U : Set ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hgβ : ∀ z ∈ U ∩ (filledJulia c)ᶜ, g z = β z)
    {z : ℂ} (hzU : z ∈ U) (hzKc : z ∈ (filledJulia c)ᶜ) : 1 < ‖g z‖ := by
  rw [hgβ z ⟨hzU, hzKc⟩, hβmod z hzKc]
  have hGpos : 0 < greenFunctionDyn c z := by
    rcases (greenFunctionDyn_nonneg c z).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z).mp h.symm) hzKc
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hGpos

/-- **A continuation maps the whole frontier arc into the unit circle.** If `g` is analytic on an open
`U`, equals the Böttcher branch `β` on the basin part of `U`, and `β` carries the modulus, then
`‖g z'‖ = 1` at EVERY frontier point `z' ∈ frontier (filledJulia c) ∩ U` — each such point is a
frontier point where `g` is a continuation, so `norm_continuation_eq_one_at_frontier` pins its modulus.
Thus `g` sends `frontier K ∩ U` into `{|w| = 1}`: the "frontier arc ⊆ g⁻¹(unit circle)" datum that,
with local injectivity of `g`, makes the Julia arc real-analytic (the biholomorphic-arc route to the
interior-nonempty natural boundary, #118). -/
theorem norm_continuation_eq_one_on_frontier {c : ℂ} {β g : ℂ → ℂ} {U : Set ℂ}
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hUo : IsOpen U) (hg : ∀ z ∈ U, AnalyticAt ℂ g z)
    (hgβ : ∀ z ∈ U ∩ (filledJulia c)ᶜ, g z = β z)
    {z' : ℂ} (hz'U : z' ∈ U) (hz'front : z' ∈ frontier (filledJulia c)) : ‖g z'‖ = 1 := by
  refine norm_continuation_eq_one_at_frontier hβmod hz'front (hg z' hz'U) ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hz'U), self_mem_nhdsWithin]
    with w hwU hwKc
  exact hgβ w ⟨hwU, hwKc⟩

/-- **Local analytic inverse of a continuation.** An analytic `g` with nonzero derivative at `z₀` has a
local analytic inverse `γ` at `g z₀`: `γ` analytic at `g z₀`, `γ ∘ g = id` near `z₀`, `g ∘ γ = id` near
`g z₀`. The frontier-point generalization of `exists_localInverse_global_branch_of_deriv_ne_zero`: for a
continuation `g` of the Böttcher branch across a frontier point `z₀` with `deriv g z₀ ≠ 0`, this gives a
local inverse extending `ψ` across the unit circle at `w₀ = g z₀` — the first step of the `β`-to-`h`
bridge (`h t = t·ψ(1/t)`) for the interior-nonempty natural boundary (#118). -/
theorem exists_localInverse_of_continuation {g : ℂ → ℂ} {z₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0) :
    ∃ γ : ℂ → ℂ, AnalyticAt ℂ γ (g z₀) ∧
      (∀ᶠ z in 𝓝 z₀, γ (g z) = z) ∧ (∀ᶠ w in 𝓝 (g z₀), g (γ w) = w) := by
  have hsd : HasStrictDerivAt g (deriv g z₀) z₀ := hgAt.hasStrictDerivAt
  exact ⟨hsd.localInverse _ _ _ hd0, hgAt.analyticAt_localInverse hd0,
    hsd.eventually_left_inverse hd0, hsd.eventually_right_inverse hd0⟩

/-- **The local inverse of a continuation extends the global inverse `ψ`.** Parametrizing by the basin
point `z` (not the value `w`) dodges the boundary-correspondence subtlety: on the basin near `z₀`, where
`g = β` and both `γ` (local inverse of `g`) and `ψ` (global inverse of `β`) are left inverses,
`γ (β z) = γ (g z) = z = ψ (β z)`. So `γ` and `ψ` agree on the exterior neighborhood `{β z : z ∈ Kᶜ
near z₀}` — i.e. `γ` continues `ψ` across the unit circle at `w₀ = β z₀`. Bridge step 2 for the
interior-nonempty natural boundary (#118), stated abstractly in the inverse data. -/
theorem localInverse_eqOn_psi_of_continuation {β ψ γ g : ℂ → ℂ} {z₀ : ℂ} {K : Set ℂ}
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ Kᶜ → g z = β z)
    (hγg : ∀ᶠ z in 𝓝 z₀, γ (g z) = z)
    (hψβ : ∀ z ∈ Kᶜ, ψ (β z) = z) :
    ∀ᶠ z in 𝓝 z₀, z ∈ Kᶜ → γ (β z) = ψ (β z) := by
  filter_upwards [hgβ, hγg] with z hgz hγz hzKc
  calc γ (β z) = γ (g z) := by rw [hgz hzKc]
    _ = z := hγz
    _ = ψ (β z) := (hψβ z hzKc).symm

/-- **Bridge step 3: the disk model continues across `t₀ = 1/w₀`.** Given the local inverse `γ`
analytic at `w₀` (step 1) agreeing with the global inverse `ψ` on the exterior near `w₀` (step 2), and
the basin bridge `h t = t·ψ(1/t)` on the punctured disk, the disk model `h` continues holomorphically
across the boundary point `t₀` with `t₀·w₀ = 1`. The witness is `G t = t·γ(1/t)`, analytic at `t₀`
(composition of `γ` with `t ↦ 1/t`) and equal to `h` on the inner side (there `1/t` is exterior and near
`w₀`, so `γ(1/t) = ψ(1/t)`). This is the pointwise half of the `β`-to-`h` bridge for the
interior-nonempty natural boundary (#118); the doubling-orbit propagation to a full arc, then
`natural_boundary_of_even_fe`, close it. -/
theorem continuesAcross_h_of_localInverse {h ψ γ : ℂ → ℂ} {t₀ w₀ : ℂ}
    (htw : t₀ * w₀ = 1)
    (hγAn : AnalyticAt ℂ γ w₀)
    (hγψ : ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w = ψ w)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ContinuesAcross h t₀ := by
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp at htw
  have hinv_eq : (1 : ℂ) / t₀ = w₀ := by
    rw [div_eq_iff ht₀0, mul_comm]; exact htw.symm
  set G : ℂ → ℂ := fun t => t * γ (1 / t) with hGdef
  -- `G` is analytic at `t₀`
  have hinvAn : AnalyticAt ℂ (fun t : ℂ => 1 / t) t₀ := by
    simpa only [one_div] using analyticAt_id.inv ht₀0
  have hγAn' : AnalyticAt ℂ γ (1 / t₀) := by rw [hinv_eq]; exact hγAn
  have hγcompAn : AnalyticAt ℂ (fun t : ℂ => γ (1 / t)) t₀ := hγAn'.comp hinvAn
  have hGAn : AnalyticAt ℂ G t₀ := analyticAt_id.mul hγcompAn
  -- `1/t → w₀` as `t → t₀`
  have hc : Tendsto (fun t : ℂ => 1 / t) (𝓝 t₀) (𝓝 w₀) := by
    have hcont : ContinuousAt (fun t : ℂ => 1 / t) t₀ :=
      (continuousAt_const : ContinuousAt (fun _ : ℂ => (1 : ℂ)) t₀).div continuousAt_id ht₀0
    have h := hcont.tendsto
    simp only at h
    rwa [hinv_eq] at h
  have hne0 : ∀ᶠ t : ℂ in 𝓝 t₀, t ≠ 0 := isOpen_compl_singleton.eventually_mem ht₀0
  -- eventual package near `t₀`
  have key : ∀ᶠ t in 𝓝 t₀,
      AnalyticAt ℂ G t ∧ t ≠ 0 ∧ (1 < ‖(1 : ℂ) / t‖ → γ (1 / t) = ψ (1 / t)) := by
    filter_upwards [hGAn.eventually_analyticAt, hne0, hc.eventually hγψ]
      with t ht1 ht2 ht3 using ⟨ht1, ht2, ht3⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp key
  refine ⟨Metric.ball t₀ ρ, Metric.isOpen_ball, Metric.mem_ball_self hρ, G, ?_, ?_⟩
  · intro t htU
    exact (hball (Metric.mem_ball.mp htU)).1.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨htU, ht𝔻⟩ := ht
    have hk := hball (Metric.mem_ball.mp htU)
    have ht0 : t ≠ 0 := hk.2.1
    have ht1 : ‖t‖ < 1 := by simpa using Metric.mem_ball.mp ht𝔻
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hnorminv : 1 < ‖(1 : ℂ) / t‖ := by
      rw [norm_div, norm_one, lt_div_iff₀ htpos, one_mul]; exact ht1
    have hγψt : γ (1 / t) = ψ (1 / t) := hk.2.2 hnorminv
    show G t = h t
    rw [hGdef]
    simp only
    rw [hγψt, ← hbridge t ht0 ht1]

/-- **Nonvanishing derivative propagates to a neighborhood.** If `g` is analytic at `z₀` with
`deriv g z₀ ≠ 0`, then `deriv g z ≠ 0` for all `z` near `z₀` (`deriv g` is analytic, hence continuous).
So a continuation of the Böttcher branch with nonzero derivative at one frontier point is a local
biholomorphism on a whole frontier arc — letting bridge step 3 (`continuesAcross_h_of_localInverse`)
apply at every point of the arc, not just `z₀`, en route to the arc-continuation that
`natural_boundary_of_even_fe` refutes (#118). -/
theorem eventually_deriv_ne_zero {g : ℂ → ℂ} {z₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, deriv g z ≠ 0 :=
  hgAt.deriv.continuousAt.eventually_ne hd0

/-- **Single-point `h`-continuation from a `β`-continuation, modulo the frontier separation.** Assembles
the `β`-to-`h` bridge: given a local inverse `γ` of the continuation at `w₀ = β z₀` (`γ` analytic,
`γ w₀ = z₀`, right inverse `g ∘ γ = id`), the model data (`g = β` on the basin near `z₀`, `ψ = β⁻¹` on
the basin, the disk bridge `h t = t·ψ(1/t)`), AND the frontier SEPARATION input `hsep` (`γ` maps the
exterior side `{|w|>1}` near `w₀` into the basin `Kᶜ`), the disk model `h` continues across `t₀ = 1/w₀`.
The separation is the one genuinely-topological remaining input for interior-nonempty `hnb` (#118) — it
encodes that the (quasidisk) Julia boundary locally separates basin from interior, with `β` respecting
it; everything else here is discharged. The derivation of step-3's `γ = ψ` hypothesis:
`γ w = ψ(β(γ w)) = ψ w` on the exterior side, using `g(γ w) = w`, `g = β` on the basin, `ψ ∘ β = id`. -/
theorem continuesAcross_h_of_separation
    {β ψ h g γ : ℂ → ℂ} {z₀ t₀ w₀ : ℂ} {K : Set ℂ}
    (htw : t₀ * w₀ = 1)
    (hγAn : AnalyticAt ℂ γ w₀) (hγw₀ : γ w₀ = z₀)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ Kᶜ → g z = β z)
    (hψβ : ∀ z ∈ Kᶜ, ψ (β z) = z)
    (hsep : ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w ∈ Kᶜ)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ContinuesAcross h t₀ := by
  have hγtend : Tendsto γ (𝓝 w₀) (𝓝 z₀) := by
    have := hγAn.continuousAt.tendsto
    rwa [hγw₀] at this
  have hγψ : ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w = ψ w := by
    filter_upwards [hgγ, hsep, hγtend.eventually hgβ] with w hgγw hsepw hgβw hw1
    have hγwK : γ w ∈ Kᶜ := hsepw hw1
    have hβγ : β (γ w) = w := by rw [← hgβw hγwK]; exact hgγw
    calc γ w = ψ (β (γ w)) := (hψβ (γ w) hγwK).symm
      _ = ψ w := by rw [hβγ]
  exact continuesAcross_h_of_localInverse htw hγAn hγψ hbridge

/-- **Local-inverse package from a raw `β`-continuation.** Extracts, from an analytic continuation `g`
of `β` across a frontier point (with `deriv g z₀ ≠ 0`, agreeing with `β` on a basin-side neighborhood),
exactly the local-inverse data that `continuesAcross_h_of_separation` consumes: a `γ` analytic at
`g z₀`, with `γ (g z₀) = z₀`, right inverse `g ∘ γ = id` near `g z₀`, and the `g = β`-on-basin fact in
`𝓝`-form. Connects the abstract bridge capstone to the concrete `ContinuesAcross β (filledJulia c)ᶜ z₀`
input for interior-nonempty `hnb` (#118). -/
theorem localInverse_package_of_continuation {β g : ℂ → ℂ} {z₀ : ℂ} {K : Set ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0)
    (hgEq : ∀ᶠ w in 𝓝[Kᶜ] z₀, g w = β w) :
    ∃ γ : ℂ → ℂ, AnalyticAt ℂ γ (g z₀) ∧ γ (g z₀) = z₀ ∧
      (∀ᶠ w in 𝓝 (g z₀), g (γ w) = w) ∧
      (∀ᶠ z in 𝓝 z₀, z ∈ Kᶜ → g z = β z) := by
  obtain ⟨γ, hγAn, hleft, hright⟩ := exists_localInverse_of_continuation hgAt hd0
  exact ⟨γ, hγAn, hleft.self_of_nhds, hright, (eventually_nhdsWithin_iff).mp hgEq⟩

/-- **Frontier separation (the named remaining topological input for interior-nonempty `hnb`).** A
continuation `g` of the Böttcher branch *locally separates* at the frontier point `z₀` if, near `z₀`,
`‖g z‖ > 1` forces `z` into the basin `(filledJulia c)ᶜ`. Equivalently `‖g‖ ≤ 1` on the interior-`K`
side (the part the modulus bricks do not control): the (quasidisk) Julia boundary locally separates
basin from interior, with `g` respecting the orientation. This is the one genuinely-topological
obligation isolated after the analytic `β`-to-`h` bridge (#118), shared with the #124 collar/Jordan
epic; it is NOT derivable from the modulus lemmas alone. -/
def FrontierSeparation (c : ℂ) (g : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ᶠ z in 𝓝 z₀, 1 < ‖g z‖ → z ∈ (filledJulia c)ᶜ

/-- **`FrontierSeparation` produces the local inverse's exterior-to-basin property.** Pulling the
`z`-space separation back along the local inverse `γ` (continuous, `γ w₀ = z₀`, right inverse
`g ∘ γ = id`): for exterior `w` near `w₀`, `‖g (γ w)‖ = ‖w‖ > 1`, so `γ w` lands in the basin. This is
the `hsep` hypothesis that `continuesAcross_h_of_separation` consumes. -/
theorem hsep_of_frontierSeparation {c : ℂ} {g γ : ℂ → ℂ} {z₀ w₀ : ℂ}
    (hγw₀ : γ w₀ = z₀) (hγc : ContinuousAt γ w₀)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hsep : FrontierSeparation c g z₀) :
    ∀ᶠ w in 𝓝 w₀, 1 < ‖w‖ → γ w ∈ (filledJulia c)ᶜ := by
  have hγtend : Tendsto γ (𝓝 w₀) (𝓝 z₀) := by rw [← hγw₀]; exact hγc.tendsto
  filter_upwards [hgγ, hγtend.eventually hsep] with w hgγw hsepw hw1
  exact hsepw (by rw [hgγw]; exact hw1)

/-- **Interior-nonempty single-point `hnb` bridge, on the named `FrontierSeparation` interface.** The
disk model `h` continues across `t₀ = 1/w₀` given the local-inverse data (`γ` analytic at `w₀`,
`γ w₀ = z₀`, right inverse), the model data (`g = β` on the basin, `ψ = β⁻¹`, the disk bridge), and the
one topological input `FrontierSeparation c g z₀`. Combines `hsep_of_frontierSeparation` with
`continuesAcross_h_of_separation`. -/
theorem continuesAcross_h_of_frontierSeparation
    {c : ℂ} {β ψ h g γ : ℂ → ℂ} {z₀ t₀ w₀ : ℂ}
    (htw : t₀ * w₀ = 1)
    (hγAn : AnalyticAt ℂ γ w₀) (hγw₀ : γ w₀ = z₀)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c)ᶜ → g z = β z)
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hsep : FrontierSeparation c g z₀)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ContinuesAcross h t₀ :=
  continuesAcross_h_of_separation htw hγAn hγw₀ hgγ hgβ hψβ
    (hsep_of_frontierSeparation hγw₀ hγAn.continuousAt hgγ hsep) hbridge

/-- **Interior-nonempty single-point `hnb` bridge, from a raw `β`-continuation (consolidation).** The
full `β`-to-`h` bridge in one statement: given an analytic continuation `g` of the Böttcher branch
across a frontier point `z₀` (`deriv g z₀ ≠ 0`, `g = β` on the basin side), the model data
(`ψ = β⁻¹` on the basin, the disk bridge `h t = t·ψ(1/t)`), and the frontier separation
`FrontierSeparation c g z₀`, the disk model `h` continues across `t₀ = 1/(g z₀)`. Composes
`localInverse_package_of_continuation` (steps 1 + plumbing) with
`continuesAcross_h_of_frontierSeparation` (steps 2–3 + separation). All that separates this from a full
interior-nonempty `hnb` discharge (#118) is `FrontierSeparation` (the quasidisk topology), the arc
assembly over the frontier arc, and `natural_boundary_of_even_fe`. -/
theorem continuesAcross_h_of_beta_continuation
    {c : ℂ} {β ψ h g : ℂ → ℂ} {z₀ t₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0)
    (hgEq : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀, g w = β w)
    (htw : t₀ * g z₀ = 1)
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hsep : FrontierSeparation c g z₀)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ContinuesAcross h t₀ := by
  obtain ⟨γ, hγAn, hγw₀, hgγ, hgβ⟩ := localInverse_package_of_continuation hgAt hd0 hgEq
  exact continuesAcross_h_of_frontierSeparation htw hγAn hγw₀ hgγ hgβ hψβ hsep hbridge

/-- **The `deriv = 0` edge is avoidable: a good frontier point exists.** If the (connected) Julia
frontier is perfect and `deriv g` is analytic on a preconnected open `Ω` meeting the frontier at `z₀`,
and `deriv g` is not identically zero on `Ω`, then some frontier point `z' ∈ Ω` has `deriv g z' ≠ 0`.
The zeros of `deriv g` are countable (`analyticOnNhd_zeros_countable`) while the frontier is uncountable
in every region (`countableAvoidance_frontier_open_of_perfect_frontier`), so the analytic bridge — which
needs `deriv g ≠ 0` — applies at a good frontier point, discharging the `deriv = 0` edge case for
interior-nonempty `hnb` (#118). -/
theorem exists_frontier_deriv_ne_zero {c : ℂ} {g : ℂ → ℂ} {Ω : Set ℂ} {z₀ w₀ : ℂ}
    (hfront : Perfect (frontier (filledJulia c)))
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hg : AnalyticOnNhd ℂ (deriv g) Ω)
    (hz₀front : z₀ ∈ frontier (filledJulia c)) (hz₀Ω : z₀ ∈ Ω)
    (hw₀Ω : w₀ ∈ Ω) (hderiv_w₀ : deriv g w₀ ≠ 0) :
    ∃ z' ∈ frontier (filledJulia c), z' ∈ Ω ∧ deriv g z' ≠ 0 := by
  have hcount : {z ∈ Ω | deriv g z = 0}.Countable :=
    analyticOnNhd_zeros_countable hg hΩc hw₀Ω hderiv_w₀
  obtain ⟨z', hz'front, hz'Ω, hz'nT⟩ :=
    countableAvoidance_frontier_open_of_perfect_frontier hfront hΩo hz₀front hz₀Ω
      {z ∈ Ω | deriv g z = 0} hcount
  exact ⟨z', hz'front, hz'Ω, fun h0 => hz'nT ⟨hz'Ω, h0⟩⟩

/-- **The `deriv = 0` edge is avoidable, connected case (self-contained).** For a connected filled
Julia set the frontier is perfect (`perfect_frontier_filledJulia_of_preconnected`, no empty-interior
hypothesis — in particular for interior-nonempty main-cardioid `c`), so a good frontier point with
`deriv g ≠ 0` exists whenever `deriv g` is analytic and not identically zero near `z₀`. This is the
`deriv = 0` edge case of interior-nonempty `hnb` (#118) discharged directly from `IsPreconnected
(filledJulia c)` — the exact hypothesis of the both-connected setting. -/
theorem exists_frontier_deriv_ne_zero_of_connected {c : ℂ} {g : ℂ → ℂ} {Ω : Set ℂ} {z₀ w₀ : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hg : AnalyticOnNhd ℂ (deriv g) Ω)
    (hz₀front : z₀ ∈ frontier (filledJulia c)) (hz₀Ω : z₀ ∈ Ω)
    (hw₀Ω : w₀ ∈ Ω) (hderiv_w₀ : deriv g w₀ ≠ 0) :
    ∃ z' ∈ frontier (filledJulia c), z' ∈ Ω ∧ deriv g z' ≠ 0 :=
  exists_frontier_deriv_ne_zero (perfect_frontier_filledJulia_of_preconnected hconn)
    hΩo hΩc hg hz₀front hz₀Ω hw₀Ω hderiv_w₀

/-- **Interior-nonempty single-point `hnb` bridge — with NO frontier-separation assumption.** The
`FrontierSeparation`-free capstone: from a Böttcher continuation `g` across a frontier point `z₀`
(`w₀ = g z₀` on the unit circle) with local inverse `γ` (analytic on `ball w₀ ε`) and the connected
Böttcher model data (`ψ` analytic on the exterior, `ψ ∘ β = id`, the modulus, the disk bridge
`h t = t·ψ(1/t)`), the disk model `h` continues holomorphically across `t₀ = 1/w₀`. Where
`continuesAcross_h_of_beta_continuation` carried the extra topological input `FrontierSeparation`,
this version discharges it internally: `hγψ_of_continuation` proves `γ = ψ` on the entire exterior
side using only the connectivity of the exterior lune (`isPreconnected_ball_inter_exterior`) and the
identity theorem, then `continuesAcross_h_of_localInverse` closes it. Contradicting
`natural_boundary_of_even_fe` for `c ∉ {0,-2}`, this is the interior-nonempty half of `hnb` (#118)
modulo wiring the connected Böttcher package (`ψ`, `hβmod`, `hψβ`, `hbridge`) and the reduction to
`deriv g z₀ ≠ 0` (`exists_frontier_deriv_ne_zero_of_connected` + `exists_localInverse_of_continuation`). -/
theorem continuesAcross_h_of_continuation_unconditional
    {c : ℂ} {β ψ h g γ : ℂ → ℂ} {z₀ w₀ t₀ : ℂ} {ε : ℝ}
    (hw₀norm : ‖w₀‖ = 1) (hε : 0 < ε) (hε2 : ε ≤ 1/2)
    (hfront : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀) (hw₀ : g z₀ = w₀)
    (hγAn : AnalyticOnNhd ℂ γ (Metric.ball w₀ ε))
    (hγg : ∀ᶠ z in 𝓝 z₀, γ (g z) = z)
    (hgγ : ∀ᶠ w in 𝓝 w₀, g (γ w) = w)
    (hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c)ᶜ → g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hψAn : ∀ w, 1 < ‖w‖ → AnalyticAt ℂ ψ w)
    (htw : t₀ * w₀ = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    ContinuesAcross h t₀ := by
  have hγψ := hγψ_of_continuation hw₀norm hε hε2 hfront hgAt hw₀ hγAn hγg hgγ hgβ hβmod hψβ hψAn
  have hγAt : AnalyticAt ℂ γ w₀ := hγAn w₀ (Metric.mem_ball_self hε)
  exact continuesAcross_h_of_localInverse htw hγAt hγψ hbridge

/-- **A single `ContinuesAcross` upgrades to a whole boundary arc — for free.** `ContinuesAcross h t₀`
carries an *open* witness set `U ∋ t₀` with a holomorphic extension `G` agreeing with `h` on the inner
side; every point of `U` (in particular every circle point in a small ball around `t₀`) inherits the
same witness. So `ContinuesAcross h t₀` yields `ContinuesAcross h ζ` for all circle `ζ` near `t₀` — the
exact arc-continuation hypothesis that `natural_boundary_of_even_fe` refutes. This removes the
"arc assembly" obligation that earlier appeared to need frontier local-connectivity: the openness of
the continuation domain already delivers the arc from one point (#118). -/
theorem arc_of_continuesAcross {h : ℂ → ℂ} {t₀ : ℂ} (hcont : ContinuesAcross h t₀) :
    ∃ r > 0, ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ∈ Metric.ball t₀ r → ContinuesAcross h ζ := by
  obtain ⟨U, hUopen, ht₀U, G, hGd, hGh⟩ := hcont
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen t₀ ht₀U
  exact ⟨r, hr, fun ζ _ hζ => ⟨U, hUopen, hrU hζ, G, hGd, hGh⟩⟩

/-- **`deriv ≠ 0` continuation ⟹ False (connected Böttcher package).** For `c ∉ {0,-2}`, a Böttcher
continuation `g` across a frontier point `z₀` with `deriv g z₀ ≠ 0` and the connected Böttcher +
even-FE disk-model package forces `False`: the `FrontierSeparation`-free bridge
(`continuesAcross_h_of_continuation_unconditional`) makes `h` continue across `t₀ = 1/(g z₀)` (a circle
point, `‖g z₀‖ = 1` at the frontier), `arc_of_continuesAcross` upgrades that to a boundary arc, and
`natural_boundary_of_even_fe` refutes it. The `deriv ≠ 0` core of interior-nonempty `hnb` (#118), with
NO quasidisk topology — only the local inverse and the exterior-lune connectivity. -/
theorem false_of_continuation_deriv_ne_zero_package
    {c z₀ : ℂ} {β ψ h g : ℂ → ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hz₀front : z₀ ∈ frontier (filledJulia c))
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0)
    (hgβnhds : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀, g w = β w)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψan : AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hh0 : h 0 = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    False := by
  have hw₀norm : ‖g z₀‖ = 1 := norm_continuation_eq_one_at_frontier hβmod hz₀front hgAt hgβnhds
  have hw₀ne : g z₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw₀norm; norm_num at hw₀norm
  obtain ⟨γ, hγAn, hleft, hright⟩ := exists_localInverse_of_continuation hgAt hd0
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.eventually_nhds_iff.mp hγAn.eventually_analyticAt
  set ε : ℝ := min ε₀ (1/2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hε2 : ε ≤ 1/2 := min_le_right _ _
  have hγAnOn : AnalyticOnNhd ℂ γ (Metric.ball (g z₀) ε) := fun w hw =>
    hball₀ (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _))
  have hgβ : ∀ᶠ z in 𝓝 z₀, z ∈ (filledJulia c)ᶜ → g z = β z := (eventually_nhdsWithin_iff).mp hgβnhds
  have hψAn : ∀ w, 1 < ‖w‖ → AnalyticAt ℂ ψ w := fun w hw => hψan w hw
  set t₀ : ℂ := 1 / g z₀ with ht₀def
  have htw : t₀ * g z₀ = 1 := by rw [ht₀def, one_div, inv_mul_cancel₀ hw₀ne]
  have ht₀norm : ‖t₀‖ = 1 := by rw [ht₀def, norm_div, norm_one, hw₀norm, div_one]
  have hcont : ContinuesAcross h t₀ :=
    continuesAcross_h_of_continuation_unconditional hw₀norm hε hε2 hz₀front hgAt rfl hγAnOn
      hleft hright hgβ hβmod hψβ hψAn htw hbridge
  obtain ⟨r, hr, harc⟩ := arc_of_continuesAcross hcont
  exact natural_boundary_of_even_fe hc0 hc2 ht₀norm hr hhd hhe hfe hh0 harc

/-- **Neighborhood-continuation ⟹ False (connected Böttcher package) — the interior-nonempty `hnb`
reduction.** For `c ∉ {0,-2}` with a connected filled Julia set, an analytic continuation `g` of the
Böttcher branch `β` on a preconnected open `Ω` meeting the frontier at `z₀` (`g = β` on the basin part
of `Ω`), together with the connected package, forces `False`. Dichotomy on `deriv g`:
- some `w₀ ∈ Ω` has `deriv g w₀ ≠ 0` ⟹ a good frontier point `z' ∈ Ω` exists
  (`exists_frontier_deriv_ne_zero_of_connected`; the continuation `g` continues `β` at *every* frontier
  point of `Ω`), and `false_of_continuation_deriv_ne_zero_package` closes it;
- `deriv g ≡ 0` on `Ω` ⟹ `g` is constant (`IsOpen.is_const_of_deriv_eq_zero`), so `‖g‖ ≡ 1` on `Ω`
  (its frontier value), and `false_of_continuation_norm_one_on_open` closes it.
Note this needs no interior-nonempty hypothesis — it is the natural-boundary `hnb` for *every*
connected `c ∉ {0,-2}`, subsuming the empty-interior case. What remains to reach the crux
`¬ ContinuesAcross β Kᶜ z₀` is only (i) adapting the abstract continuation predicate to the explicit
`(g, Ω)` data and (ii) instantiating the package from `exists_full_disk_model_of_mem_mandelbrot`
(#118). -/
theorem false_of_continuation_connected_package
    {c z₀ : ℂ} {β ψ h g : ℂ → ℂ} {Ω : Set ℂ}
    (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hconn : IsPreconnected (filledJulia c))
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hz₀Ω : z₀ ∈ Ω)
    (hz₀front : z₀ ∈ frontier (filledJulia c))
    (hgAn : AnalyticOnNhd ℂ g Ω)
    (hgβ : ∀ z ∈ Ω ∩ (filledJulia c)ᶜ, g z = β z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψan : AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hh0 : h 0 = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) :
    False := by
  have hgβnhds0 : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z₀, g w = β w := by
    filter_upwards [nhdsWithin_le_nhds (hΩo.mem_nhds hz₀Ω), self_mem_nhdsWithin]
      with w hwΩ hwc using hgβ w ⟨hwΩ, hwc⟩
  have hw₀norm : ‖g z₀‖ = 1 :=
    norm_continuation_eq_one_at_frontier hβmod hz₀front (hgAn z₀ hz₀Ω) hgβnhds0
  by_cases hex : ∃ w ∈ Ω, deriv g w ≠ 0
  · obtain ⟨w₀, hw₀Ω, hderiv_w₀⟩ := hex
    obtain ⟨z', hz'front, hz'Ω, hz'deriv⟩ :=
      exists_frontier_deriv_ne_zero_of_connected hconn hΩo hΩc hgAn.deriv hz₀front hz₀Ω hw₀Ω hderiv_w₀
    have hgβnhds' : ∀ᶠ w in 𝓝[(filledJulia c)ᶜ] z', g w = β w := by
      filter_upwards [nhdsWithin_le_nhds (hΩo.mem_nhds hz'Ω), self_mem_nhdsWithin]
        with w hwΩ hwc using hgβ w ⟨hwΩ, hwc⟩
    exact false_of_continuation_deriv_ne_zero_package hc0 hc2 hz'front (hgAn z' hz'Ω) hz'deriv
      hgβnhds' hβmod hψan hψβ hhd hhe hfe hh0 hbridge
  · have hex' : ∀ w ∈ Ω, deriv g w = 0 := fun w hw =>
      not_not.mp (fun hne => hex ⟨w, hw, hne⟩)
    have hconst : ∀ z ∈ Ω, g z = g z₀ := fun z hz =>
      hΩo.is_const_of_deriv_eq_zero hΩc hgAn.differentiableOn
        (fun x hx => hex' x hx) hz hz₀Ω
    have hnorm1 : ∀ z ∈ Ω, ‖g z‖ = 1 := fun z hz => by rw [hconst z hz]; exact hw₀norm
    exact false_of_continuation_norm_one_on_open hβmod hΩc hΩo hz₀Ω hgAn.differentiableOn hgβ
      hz₀front (subset_refl Ω) hΩo hz₀Ω hnorm1

end Bottcher
