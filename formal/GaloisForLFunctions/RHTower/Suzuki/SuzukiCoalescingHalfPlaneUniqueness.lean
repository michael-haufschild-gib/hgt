import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import GaloisForLFunctions.HTGeometry.ReciprocalLogDerivZero

/-!
# One imaginary interval closes the half-plane endpoint

A locally bounded family of source quotients on the upper half-plane, each with nonnegative real
part, that converges on a set of frequencies accumulating at an interior point to the reciprocal
logarithmic derivative of `ξ` in the half-plane chart `s = 1/2 - iz`, forces the Riemann
Hypothesis.

The mechanism is threefold and uses no real-axis information.  Vitali upgrades the pointwise
convergence to a locally uniform one, so the limit is holomorphic on the whole half-plane.  The
identity theorem, applied to the *entire* combination `G·(ξ∘σ)' + iκ(ξ∘σ)` rather than to the
quotient itself, propagates the relation past every zero of the denominator.  And a zero of `ξ`
would make the limit vanish there, because the reciprocal logarithmic derivative tends to zero at a
zero of any order — contradicting the strict positivity of the real part, which the minimum
principle supplies from a single positive value.
-/

open Complex Metric Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The half-plane chart `z ↦ 1/2 - iz`, carrying the upper half-plane onto `Re s > 1/2`. -/
def halfPlaneChart (z : ℂ) : ℂ := 1 / 2 - Complex.I * z

/-- Its inverse. -/
def halfPlaneChartInv (s : ℂ) : ℂ := Complex.I * (s - 1 / 2)

@[simp] theorem halfPlaneChart_inv (s : ℂ) : halfPlaneChart (halfPlaneChartInv s) = s := by
  rw [halfPlaneChart, halfPlaneChartInv]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(s - 1 / 2)) * hI

@[simp] theorem halfPlaneChartInv_chart (z : ℂ) : halfPlaneChartInv (halfPlaneChart z) = z := by
  rw [halfPlaneChart, halfPlaneChartInv]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-z) * hI

theorem re_halfPlaneChart (z : ℂ) : (halfPlaneChart z).re = 1 / 2 + z.im := by
  rw [halfPlaneChart]
  simp [Complex.mul_re]

theorem halfPlaneChart_mem_rightHalf {z : ℂ} (hz : 0 < z.im) : halfPlaneChart z ∈ rightHalf := by
  rw [mem_rightHalf, re_halfPlaneChart]
  linarith

theorem im_halfPlaneChartInv (s : ℂ) : (halfPlaneChartInv s).im = s.re - 1 / 2 := by
  rw [halfPlaneChartInv]
  simp [Complex.mul_im]

theorem continuous_halfPlaneChart : Continuous halfPlaneChart := by
  unfold halfPlaneChart
  fun_prop

theorem continuous_halfPlaneChartInv : Continuous halfPlaneChartInv := by
  unfold halfPlaneChartInv
  fun_prop

/-- The chart pullback of `ξ`. -/
def xiChart (z : ℂ) : ℂ := xi (halfPlaneChart z)

theorem differentiable_xiChart : Differentiable ℂ xiChart := by
  intro z
  have h1 : DifferentiableAt ℂ halfPlaneChart z := by
    unfold halfPlaneChart
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
  exact (xi_differentiable _).comp z h1

theorem analyticAt_xiChart (z : ℂ) : AnalyticAt ℂ xiChart z :=
  (differentiable_xiChart.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)

theorem deriv_xiChart (z : ℂ) : deriv xiChart z = -Complex.I * deriv xi (halfPlaneChart z) := by
  have hinner : HasDerivAt halfPlaneChart (-Complex.I) z := by
    have h : HasDerivAt (fun w : ℂ => 1 / 2 - Complex.I * w) (0 - Complex.I * 1) z :=
      (hasDerivAt_const z (1 / 2 : ℂ)).sub ((hasDerivAt_id z).const_mul Complex.I)
    simp only [zero_sub, mul_one] at h
    exact h
  have houter : HasDerivAt xi (deriv xi (halfPlaneChart z)) (halfPlaneChart z) :=
    (xi_differentiable _).hasDerivAt
  have := houter.comp z hinner
  rw [show (xi ∘ halfPlaneChart) = xiChart from rfl] at this
  rw [this.deriv]
  ring

/-- `ξ` is not identically zero near any point of the chart. -/
theorem xiChart_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, xiChart w = 0 := by
  intro h
  refine xi_orderAt_ne_top (halfPlaneChart z) (analyticOrderAt_eq_top.mpr ?_)
  have htend : Tendsto halfPlaneChartInv (𝓝 (halfPlaneChart z)) (𝓝 z) := by
    have := continuous_halfPlaneChartInv.tendsto (halfPlaneChart z)
    rwa [halfPlaneChartInv_chart] at this
  have := htend.eventually h
  filter_upwards [this] with s hs
  rwa [xiChart, halfPlaneChart_inv] at hs

/-- **Theorem I.**  A locally bounded, positive-real-part source family on the upper half-plane
whose values on one accumulating frequency set are the chart reciprocal logarithmic derivative of
`ξ` forces the Riemann Hypothesis. -/
theorem riemannHypothesis_of_upperHalfPlane_source_limit
    {F : ℕ → ℂ → ℂ} {Y : Set ℂ} {z₀ z₁ : ℂ} {κ : ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im})
    (hloc : ∀ z ∈ {z : ℂ | 0 < z.im}, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ {z : ℂ | 0 < z.im} ∧
      ∃ C : ℝ, ∀ n, ∀ w ∈ ball z R, ‖F n w‖ ≤ C)
    (hre : ∀ n, ∀ z ∈ {z : ℂ | 0 < z.im}, 0 ≤ (F n z).re)
    (hz₀ : 0 < z₀.im) (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hYsub : Y ⊆ {z : ℂ | 0 < z.im})
    (hderivY : ∀ z ∈ Y, deriv xi (halfPlaneChart z) ≠ 0)
    (hconv : ∀ z ∈ Y, Tendsto (fun n => F n z) atTop
      (𝓝 (κ * (xi (halfPlaneChart z) / deriv xi (halfPlaneChart z)))))
    (hz₁ : z₁ ∈ Y)
    (hpos : 0 < (κ * (xi (halfPlaneChart z₁) / deriv xi (halfPlaneChart z₁))).re) :
    RiemannHypothesis := by
  classical
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected hUc hF hloc hz₀ hacc
      (fun z hz => ⟨_, hconv z hz⟩)
  have hGY : ∀ z ∈ Y, G z = κ * (xi (halfPlaneChart z) / deriv xi (halfPlaneChart z)) := fun z hz =>
    tendsto_nhds_unique (hGlim.tendsto_at (hYsub hz)) (hconv z hz)
  have hGre : ∀ z ∈ U, 0 < (G z).re := by
    refine re_pos_of_tendstoLocallyUniformlyOn hUopen hUc
      (Filter.Eventually.of_forall hF) hGlim (Filter.Eventually.of_forall hre)
      (hYsub hz₁) ?_
    rw [hGY z₁ hz₁]
    exact hpos
  -- the entire combination vanishing on the uniqueness set
  set c : ℂ := -Complex.I * κ with hcdef
  set Φ : ℂ → ℂ := fun z => G z * deriv xiChart z - c * xiChart z with hΦdef
  have hderivAn : ∀ z, AnalyticAt ℂ (deriv xiChart) z := fun z => (analyticAt_xiChart z).deriv
  have hΦdiff : DifferentiableOn ℂ Φ U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ ?_
    · exact ((hGdiff z hz).differentiableAt (hUopen.mem_nhds hz)).mul
        (hderivAn z).differentiableAt
    · exact (differentiableAt_const c).mul (analyticAt_xiChart z).differentiableAt
  have hΦY : ∀ z ∈ Y, Φ z = 0 := by
    intro z hz
    have hd : deriv xi (halfPlaneChart z) ≠ 0 := hderivY z hz
    rw [hΦdef]
    simp only
    rw [hGY z hz, deriv_xiChart, xiChart, hcdef]
    field_simp
    ring
  have hana : AnalyticOnNhd ℂ Φ U := hΦdiff.analyticOnNhd hUopen
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, Φ z = 0 := hacc.mono fun z hz => hΦY z hz
  have hΦzero : EqOn Φ 0 U :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hfreq
  -- no zero of `ξ` in the right half-plane
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  set w : ℂ := halfPlaneChartInv s with hwdef
  have hwU : w ∈ U := by
    rw [hUdef]
    show 0 < w.im
    rw [hwdef, im_halfPlaneChartInv]
    have := mem_rightHalf.mp hs
    linarith
  have hfw : xiChart w = 0 := by
    rw [xiChart, hwdef, halfPlaneChart_inv]
    exact hzero
  have hnotzero : ¬ ∀ᶠ z in 𝓝 w, xiChart z = 0 := xiChart_not_eventually_zero w
  -- the derivative is eventually nonzero on a punctured neighbourhood
  have hdne : ∀ᶠ z in 𝓝[≠] w, deriv xiChart z ≠ 0 :=
    eventually_deriv_ne_zero_of_zero (analyticAt_xiChart w) hnotzero hfw
  have hEq : ∀ᶠ z in 𝓝[≠] w, G z = c * (xiChart z / deriv xiChart z) := by
    filter_upwards [hdne, nhdsWithin_le_nhds (hUopen.mem_nhds hwU)] with z hz hzU
    have h0 : G z * deriv xiChart z - c * xiChart z = 0 := hΦzero hzU
    field_simp
    linear_combination h0
  have hGw : G w = 0 :=
    eq_zero_of_eventuallyEq_div_deriv (analyticAt_xiChart w) hnotzero hfw
      ((hGdiff w hwU).differentiableAt (hUopen.mem_nhds hwU)).continuousAt hEq
  have := hGre w hwU
  rw [hGw] at this
  simp at this

end RHTower
