/-
# Region-Cauchy for `λ` (toward the global preimage count → `λ̄` injective)

`ModularLambdaArgumentPrinciple.modularLambda_argument_principle` gives the *local* count: around any
`w`-preimage `τ₀ ∈ ℍ`, `∮_{C(τ₀,R)} λ'/(λ−w) = 2πi`. The injectivity of `λ̄ : ℍ/Γ(2) → ℂ∖{0,1}` (the
deep crux #28b, hence the three-value-Montel lift #30, hence Fatou density, hence the hRigid dynamical
input) needs the *global* count `∮_{∂F} λ'/(λ−w) = 2πi · #{preimages in F}` — obtained by homotoping the
fundamental-domain boundary to small circles around the finitely many preimages, where the log-derivative
1-form is closed (holomorphic).

This file builds the analytic substrate of that count: the integrand `τ ↦ λ'(τ)/(λ(τ)−w)` is holomorphic
on the punctured upper half-plane `{Im τ > 0} ∖ λ⁻¹(w)` — exactly the region on which the form is closed,
which mathlib's homotopy-invariance of curve integrals
(`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`) consumes.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaArgumentPrinciple
import GaloisForLFunctions.Bottcher.BoundaryArcWinding
import GaloisForLFunctions.Bottcher.ThetaWronskian
import GaloisForLFunctions.Bottcher.CuspLimits
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional

open Complex Filter Topology Set Real

namespace Bottcher

/-- **Holomorphy of the argument-principle integrand (pointwise).** `τ ↦ λ'(τ)/(λ(τ)−w)` is analytic at
every `τ₀ ∈ ℍ` with `λ(τ₀) ≠ w`. The log-derivative integrand whose contour integral counts the
`w`-preimages of `λ`. -/
theorem analyticAt_modularLambda_logDeriv_sub {τ₀ w : ℂ} (hτ₀ : 0 < τ₀.im)
    (hne : modularLambda τ₀ ≠ w) :
    AnalyticAt ℂ (fun τ => deriv modularLambda τ / (modularLambda τ - w)) τ₀ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ modularLambda {z : ℂ | 0 < z.im} :=
    fun z hz => (differentiableAt_modularLambda_of_im_pos hz).differentiableWithinAt
  have hlaman : AnalyticOnNhd ℂ modularLambda {z : ℂ | 0 < z.im} := hdiff.analyticOnNhd hopen
  have hlam : AnalyticAt ℂ modularLambda τ₀ := hlaman τ₀ hτ₀
  have hlamd : AnalyticAt ℂ (deriv modularLambda) τ₀ := (hlaman.deriv) τ₀ hτ₀
  have hden : AnalyticAt ℂ (fun τ => modularLambda τ - w) τ₀ := hlam.sub analyticAt_const
  exact hlamd.div hden (by simpa [sub_ne_zero] using hne)

/-- **Holomorphy of the integrand on the punctured upper half-plane.** `τ ↦ λ'(τ)/(λ(τ)−w)` is analytic
on all of `{Im τ > 0} ∖ λ⁻¹(w)` — the region on which the log-derivative 1-form is closed, on which the
fundamental-domain boundary is homotoped to the preimage circles for the global argument-principle count. -/
theorem analyticOnNhd_modularLambda_logDeriv_sub (w : ℂ) :
    AnalyticOnNhd ℂ (fun τ => deriv modularLambda τ / (modularLambda τ - w))
      ({z : ℂ | 0 < z.im} ∩ {z : ℂ | modularLambda z ≠ w}) := by
  intro τ₀ hτ₀
  exact analyticAt_modularLambda_logDeriv_sub hτ₀.1 hτ₀.2

/-- **Full imaginary-axis arc winding endpoint value.** For `w ∉ ℝ`, the `Y₂→∞`-limited winding of the
imaginary-axis arc, `(0−w)/(λ(iY₁)−w)`, tends as `Y₁→0⁺` to `(0−w)/(1−w)` — the cusp-`0`-to-cusp-`∞` value
of the `Re=0` side of the ideal-triangle fundamental domain `(0,1,∞)` (`λ(i∞)=0`, `λ(0)=1`). One of the
three full boundary-arc contributions whose product is the total boundary winding `exp(∮_{∂F})` of the
argument-principle count. -/
theorem imAxis_winding_cusps {w : ℂ} (hw : w.im ≠ 0) :
    Tendsto (fun Y₁ : ℝ => (0 - w) / (modularLambda ((Y₁:ℂ)*Complex.I) - w)) (𝓝[>] 0)
      (𝓝 ((0 - w) / (1 - w))) := by
  have hw1 : (1 : ℂ) - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; apply hw; rw [← h]; simp
  have hden : Tendsto (fun Y₁ : ℝ => modularLambda ((Y₁:ℂ)*Complex.I) - w) (𝓝[>] 0) (𝓝 (1 - w)) :=
    tendsto_modularLambda_imAxis_nhdsGT.sub_const w
  exact tendsto_const_nhds.div hden hw1

/-- **`λ(1+it) → 0` at the cusp `i∞`** (any approach with `Im → ∞`). -/
theorem tendsto_modularLambda_reOne_atTop :
    Tendsto (fun t : ℝ => modularLambda (1 + (t:ℂ)*Complex.I)) atTop (𝓝 0) := by
  apply tendsto_modularLambda_atImInfty.comp
  rw [tendsto_comap_iff]
  have h : (Complex.im ∘ fun t : ℝ => 1 + (t:ℂ)*Complex.I) = fun t : ℝ => t := by
    funext t
    simp [Complex.add_im, Complex.mul_im]
  rw [h]; exact tendsto_id

/-- **`Re=1` arc winding, `Y₂→∞`.** As the upper truncation height `Y₂→∞` (cusp `i∞`, where `λ→0`), the
`Re=1`-arc winding `exp(∫_{Y₁}^{Y₂} …)` converges to `(0−w)/(λ(1+iY₁)−w)`. The cusp-`∞` endpoint of the
`Re=1` side of the ideal-triangle boundary (mirror of `imAxis_winding_atTop`). The other endpoint (`Y₁→0`)
is the cusp `1` where `λ→∞`, so the full `Re=1` arc integral diverges — the boundary count must truncate
this corner, which is why the global winding is computed on the truncated contour, not as a product of
full-arc values. -/
theorem reOne_winding_atTop {w : ℂ} (hw : w.im ≠ 0) {Y₁ : ℝ} (hY₁ : 0 < Y₁) :
    Tendsto (fun Y₂ : ℝ => Complex.exp (∫ t in Y₁..Y₂,
        (Complex.I * deriv modularLambda (1 + (t:ℂ)*Complex.I))
          / (modularLambda (1 + (t:ℂ)*Complex.I) - w)))
      atTop (𝓝 ((0 - w) / (modularLambda (1 + (Y₁:ℂ)*Complex.I) - w))) := by
  have hden : modularLambda (1 + (Y₁:ℂ)*Complex.I) - w ≠ 0 := by
    intro h0; apply hw
    have h1 : modularLambda (1 + (Y₁:ℂ)*Complex.I) = w := sub_eq_zero.mp h0
    rw [← h1]; exact modularLambda_re_one_real
  have hratio : Tendsto (fun Y₂ : ℝ =>
      (modularLambda (1 + (Y₂:ℂ)*Complex.I) - w) / (modularLambda (1 + (Y₁:ℂ)*Complex.I) - w))
      atTop (𝓝 ((0 - w) / (modularLambda (1 + (Y₁:ℂ)*Complex.I) - w))) :=
    ((tendsto_modularLambda_reOne_atTop.sub_const w)).div_const _
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y₂ hY₂
  exact (reOne_winding hw hY₁ hY₂).symm

/-- **`λ' → 0` at the cusp `i∞`** (any approach with `Im → ∞`). From the unconditional closed form
`λ' = πi·θ₂⁴θ₄⁴/θ₃⁴` and the theta cusp limits `θ₂→0`, `θ₃,θ₄→1`. The uniform (in `Re`) derivative decay
that makes the top-segment (`Im=Y`) truncation contribution vanish in the argument-principle boundary
count — combined with `tendsto_modularLambda_atImInfty` (`λ→0`), the integrand `λ'/(λ−w) → 0/(−w) = 0`
uniformly on horizontal segments as the truncation height `Y → ∞`. -/
theorem tendsto_deriv_modularLambda_atImInfty :
    Tendsto (deriv modularLambda) (comap Complex.im atTop) (𝓝 0) := by
  have hev : (deriv modularLambda) =ᶠ[comap Complex.im atTop]
      (fun τ => (π : ℂ) * I * thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 4) := by
    filter_upwards [(eventually_gt_atTop (0:ℝ)).comap Complex.im] with τ hτ
    exact deriv_modularLambda_eq' hτ
  rw [tendsto_congr' hev]
  have hnum : Tendsto (fun τ => (π : ℂ) * I * thetaTwo τ ^ 4 * thetaFour τ ^ 4)
      (comap Complex.im atTop) (𝓝 ((π : ℂ) * I * 0 ^ 4 * 1 ^ 4)) :=
    (tendsto_const_nhds.mul (tendsto_thetaTwo_atImInfty.pow 4)).mul (tendsto_thetaFour_atImInfty.pow 4)
  have hden : Tendsto (fun τ => thetaThree τ ^ 4) (comap Complex.im atTop) (𝓝 ((1 : ℂ) ^ 4)) :=
    tendsto_thetaThree_atImInfty.pow 4
  have h := hnum.div hden (by norm_num)
  simpa using h

/-- **Top-segment (cusp-`∞` truncation) winding vanishes.** The horizontal segment `τ = t + iY`,
`t ∈ [0,1]`, at truncation height `Y`: its winding integral `∫₀¹ λ'(t+iY)/(λ(t+iY)−w) dt → 0` as `Y→∞`,
because both `λ→0` and `λ'→0` uniformly there (`comap im atTop`), so the integrand `→ 0/(−w)=0` uniformly
on `[0,1]`. This is the piece of the truncated argument-principle contour that lets the cusp-`∞` corner be
ignored in the limit `Y→∞` — so the global boundary winding `∮_{∂F}` is the limit of the three long arcs
plus the (vanishing) top truncation. -/
theorem topSegment_winding_atTop {w : ℂ} (hw : w.im ≠ 0) :
    Tendsto (fun Y : ℝ => ∫ t in (0:ℝ)..1,
        deriv modularLambda ((t:ℂ) + (Y:ℂ)*Complex.I)
          / (modularLambda ((t:ℂ) + (Y:ℂ)*Complex.I) - w))
      atTop (𝓝 0) := by
  have hw0 : (0:ℂ) - w ≠ 0 := by
    rw [zero_sub, neg_ne_zero]; intro h; apply hw; rw [h]; simp
  set h : ℂ → ℂ := fun τ => deriv modularLambda τ / (modularLambda τ - w) with hh
  have hcusp : Tendsto h (comap Complex.im atTop) (𝓝 0) := by
    have ht : Tendsto h (comap Complex.im atTop) (𝓝 ((0:ℂ) / ((0:ℂ) - w))) :=
      tendsto_deriv_modularLambda_atImInfty.div
        (tendsto_modularLambda_atImInfty.sub_const w) hw0
    simpa using ht
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hev : ∀ᶠ y in atTop, ∀ τ : ℂ, τ.im = y → ‖h τ‖ < ε / 2 := by
    have hball : ∀ᶠ τ in comap Complex.im atTop, h τ ∈ Metric.ball (0:ℂ) (ε/2) :=
      hcusp (Metric.ball_mem_nhds 0 hε2)
    rw [Filter.eventually_comap] at hball
    filter_upwards [hball] with y hy τ hτ
    have := hy τ hτ
    simpa [Metric.mem_ball, dist_eq_norm] using this
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨max M 1, fun Y hY => ?_⟩
  have hYM : M ≤ Y := le_trans (le_max_left _ _) hY
  rw [dist_eq_norm, sub_zero]
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖h ((t:ℂ) + (Y:ℂ)*Complex.I)‖ ≤ ε / 2 := by
    intro t _
    have him : ((t:ℂ) + (Y:ℂ)*Complex.I).im = Y := by
      simp [Complex.add_im, Complex.mul_im]
    exact le_of_lt (hM Y hYM _ him)
  have hle : ‖∫ t in (0:ℝ)..1, h ((t:ℂ) + (Y:ℂ)*Complex.I)‖ ≤ ε / 2 * |(1:ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hfin : ‖∫ t in (0:ℝ)..1, h ((t:ℂ) + (Y:ℂ)*Complex.I)‖ ≤ ε / 2 := by simpa using hle
  linarith [hfin]

/-- **`‖λ‖ → ∞` at the cusp `1`** (`λ(1+iy) → ∞` as `y → 0⁺`). Via the `T`-relation
`λ(τ+1) = λ(τ)/(λ(τ)−1)` (`modularLambda_T_eq'`) and `λ(iy) → 1` at the cusp `0`: the numerator `→ 1`,
the denominator `‖λ(iy)−1‖ → 0` (and `> 0` since `λ` omits the value `1`), so the ratio blows up. This is
the third cusp value `λ(1)=∞`, completing the cusp behavior `λ → {0,1,∞}` at the three cusps `∞,0,1` — the
input to the properness of `λ̄ : ℍ/Γ(2) → ℂ∖{0,1}` (whence `λ` is a covering, giving the three-value-Montel
lift `#30`). -/
theorem tendsto_norm_modularLambda_reOne_nhdsZero :
    Tendsto (fun y : ℝ => ‖modularLambda (1 + (y:ℂ)*Complex.I)‖) (𝓝[>] 0) atTop := by
  have heq : (fun y : ℝ => ‖modularLambda (1 + (y:ℂ)*Complex.I)‖) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ‖modularLambda ((y:ℂ)*Complex.I)‖
        / ‖modularLambda ((y:ℂ)*Complex.I) - 1‖) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyim : 0 < ((y:ℂ)*Complex.I).im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero]
      exact hy
    have hT : modularLambda (1 + (y:ℂ)*Complex.I)
        = modularLambda ((y:ℂ)*Complex.I) / (modularLambda ((y:ℂ)*Complex.I) - 1) := by
      rw [show 1 + (y:ℂ)*Complex.I = (y:ℂ)*Complex.I + 1 from by ring]
      exact modularLambda_T_eq' hyim
    rw [hT, norm_div]
  rw [tendsto_congr' heq]
  have hnum : Tendsto (fun y : ℝ => ‖modularLambda ((y:ℂ)*Complex.I)‖) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_modularLambda_imAxis_nhdsGT.norm
  have hden0 : Tendsto (fun y : ℝ => ‖modularLambda ((y:ℂ)*Complex.I) - 1‖) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_modularLambda_imAxis_nhdsGT.sub_const 1).norm
    simpa using this
  have hdenpos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < ‖modularLambda ((y:ℂ)*Complex.I) - 1‖ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyim : 0 < ((y:ℂ)*Complex.I).im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, add_zero]
      exact hy
    have hne : modularLambda ((y:ℂ)*Complex.I) ≠ 1 := (modularLambda_omits_zero_one' hyim).2
    rwa [norm_pos_iff, sub_ne_zero]
  have hden : Tendsto (fun y : ℝ => ‖modularLambda ((y:ℂ)*Complex.I) - 1‖) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hden0 hdenpos
  have hdeninv : Tendsto (fun y : ℝ => ‖modularLambda ((y:ℂ)*Complex.I) - 1‖⁻¹) (𝓝[>] 0) atTop :=
    hden.inv_tendsto_nhdsGT_zero
  have hmul := hnum.pos_mul_atTop (by norm_num : (0:ℝ) < 1) hdeninv
  refine hmul.congr (fun y => ?_)
  rw [div_eq_mul_inv]

end Bottcher
