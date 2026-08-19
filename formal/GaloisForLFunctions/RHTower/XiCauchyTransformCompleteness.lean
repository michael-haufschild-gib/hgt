import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource

/-!
# The Cauchy transform of a divisor vector

The Cauchy transform `F_u(z) = Σ_q conj(u q) / (α_q - z)` of a square-summable Xi divisor vector is
holomorphic off the centered divisor: the reciprocal-square divisor mass supplies a summable
majorant on every ball avoiding the divisor.

The transform decays to zero along the vertical axis, so a transform with vanishing real part on a
nonempty open set is identically zero.  Multiplicity-fibre annihilation then identifies the vector
with the orthogonal complement of the whole regular Cauchy family.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-- The Cauchy transform of a square-summable divisor vector. -/
def xiCauchyTransform (u : lp (fun _ : XiZeroCopy => ℂ) 2) (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, (starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹

theorem xiCauchyTransform_eq_inner (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (z : XiCRegularPoint) :
    xiCauchyTransform u (z : ℂ) = inner ℂ u (xiWeilCauchyLp z) := by
  rw [xiCauchyTransform, lp.inner_eq_tsum]
  refine tsum_congr (fun q => ?_)
  rw [xiWeilCauchyLp_apply, xiWeilCauchyTest]
  simp [RCLike.inner_apply, mul_comm]

/-- On a ball avoiding the divisor the shifted resolvent is uniformly comparable to the reciprocal
divisor coordinate. -/
theorem norm_cauchy_term_le {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hfree : ∀ z ∈ ball z₀ r, XiC z ≠ 0) (u : lp (fun _ : XiZeroCopy => ℂ) 2)
    (q : XiZeroCopy) {z : ℂ} (hz : z ∈ ball z₀ (r / 2)) :
    ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - z)⁻¹‖ ≤
      max 2 (4 * (‖z₀‖ + r) / r) * (‖u q‖ * ‖xiSpectralPoint q‖⁻¹) := by
  have hα : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hαpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr hα
  have hnot : xiSpectralPoint q ∉ ball z₀ r := by
    intro hmem
    exact hfree _ hmem (XiC_xiSpectralPoint_eq_zero q)
  have hfar : r ≤ ‖xiSpectralPoint q - z₀‖ := by
    rw [mem_ball, Complex.dist_eq] at hnot
    push Not at hnot
    exact hnot
  have hz' : ‖z - z₀‖ < r / 2 := by
    rw [mem_ball, Complex.dist_eq] at hz
    exact hz
  have hlow : r / 2 ≤ ‖xiSpectralPoint q - z‖ := by
    have htri : ‖xiSpectralPoint q - z₀‖ ≤ ‖xiSpectralPoint q - z‖ + ‖z - z₀‖ := by
      have h := norm_add_le (xiSpectralPoint q - z) (z - z₀)
      simpa using h
    linarith
  have hpos : (0 : ℝ) < ‖xiSpectralPoint q - z‖ := by linarith
  have hz₀ : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg _
  have hznorm : ‖z‖ ≤ ‖z₀‖ + r / 2 := by
    have h := norm_add_le (z - z₀) z₀
    simp only [sub_add_cancel] at h
    linarith
  set C : ℝ := max 2 (4 * (‖z₀‖ + r) / r) with hC
  have hC2 : (2 : ℝ) ≤ C := le_max_left _ _
  have hCr : 4 * (‖z₀‖ + r) / r ≤ C := le_max_right _ _
  have hkey : ‖xiSpectralPoint q‖ ≤ C * ‖xiSpectralPoint q - z‖ := by
    rcases le_or_gt (2 * (‖z₀‖ + r)) ‖xiSpectralPoint q‖ with hbig | hsmall
    · have hsub : ‖xiSpectralPoint q‖ - ‖z‖ ≤ ‖xiSpectralPoint q - z‖ :=
        norm_sub_norm_le _ _
      nlinarith
    · have hprod : (4 * (‖z₀‖ + r) / r) * (r / 2) = 2 * (‖z₀‖ + r) := by field_simp; ring
      nlinarith
  rw [norm_mul, RCLike.norm_conj, norm_inv]
  have hbound : ‖xiSpectralPoint q - z‖⁻¹ ≤ C * ‖xiSpectralPoint q‖⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpos hαpos]
    linarith [hkey]
  calc ‖u q‖ * ‖xiSpectralPoint q - z‖⁻¹
      ≤ ‖u q‖ * (C * ‖xiSpectralPoint q‖⁻¹) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg ((u : XiZeroCopy → ℂ) q))
    _ = C * (‖u q‖ * ‖xiSpectralPoint q‖⁻¹) := by ring

theorem summable_cauchy_majorant (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    Summable (fun q : XiZeroCopy => ‖u q‖ * ‖xiSpectralPoint q‖⁻¹) := by
  have hbase : Summable (fun q : XiZeroCopy => ‖(u q) * (xiSpectralPoint q)⁻¹‖) :=
    summable_norm_mul_of_sq (summable_sq_lp u) summable_norm_xiSpectralPoint_inv_sq
  refine hbase.congr (fun q => ?_)
  rw [norm_mul, norm_inv]

/-- **The Cauchy transform is holomorphic off the divisor.** -/
theorem differentiableOn_xiCauchyTransform (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    DifferentiableOn ℂ (xiCauchyTransform u) {z : ℂ | XiC z ≠ 0} := by
  intro z₀ hz₀
  have hopen : IsOpen {z : ℂ | XiC z ≠ 0} :=
    isOpen_ne_fun XiC_differentiable.continuous continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  have hfree : ∀ z ∈ ball z₀ r, XiC z ≠ 0 := fun z hz => hball hz
  have hsub : ball z₀ (r / 2) ⊆ {z : ℂ | XiC z ≠ 0} :=
    fun z hz => hfree z (ball_subset_ball (by linarith) hz)
  have hdiff : DifferentiableOn ℂ (xiCauchyTransform u) (ball z₀ (r / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_cauchy_majorant u).mul_left (max 2 (4 * (‖z₀‖ + r) / r))) ?_ isOpen_ball ?_
    · intro q z hz
      have hne : xiSpectralPoint q - z ≠ 0 := by
        intro hcon
        have hzval : z = xiSpectralPoint q := by linear_combination -hcon
        exact hfree z (ball_subset_ball (by linarith) hz)
          (by rw [hzval]; exact XiC_xiSpectralPoint_eq_zero q)
      exact ((differentiableAt_const _).mul
        (((differentiableAt_const _).sub differentiableAt_id).inv hne)).differentiableWithinAt
    · exact fun q z hz => norm_cauchy_term_le hr hfree u q hz
  exact (hdiff.differentiableAt (isOpen_ball.mem_nhds
    (mem_ball_self (by linarith)))).differentiableWithinAt

/-! ## The regular set -/

theorem isOpen_xiRegularSet : IsOpen {z : ℂ | XiC z ≠ 0} :=
  isOpen_ne_fun XiC_differentiable.continuous continuous_const

theorem countable_xiZeroSet : {z : ℂ | XiC z = 0}.Countable := by
  have hrange : {z : ℂ | XiC z = 0} = Set.range (fun q : XiZeroCopy => xiSpectralPoint q) := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
      exact ⟨q, hq⟩
    · rintro ⟨q, rfl⟩
      exact XiC_xiSpectralPoint_eq_zero q
  rw [hrange]
  exact Set.countable_range _

theorem isPreconnected_xiRegularSet : IsPreconnected {z : ℂ | XiC z ≠ 0} := by
  have hcompl : {z : ℂ | XiC z ≠ 0} = {z : ℂ | XiC z = 0}ᶜ := by
    ext z; simp
  rw [hcompl]
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_ countable_xiZeroSet).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

/-! ## Vanishing real part on an open set kills the transform -/

theorem deriv_eq_zero_of_re_eq_zero_on_ball {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball z₀ r)) (hre : ∀ z ∈ ball z₀ r, (f z).re = 0) :
    deriv f z₀ = 0 := by
  have hg : DifferentiableOn ℂ (fun z => Complex.exp (f z)) (ball z₀ r) := by
    intro z hz
    exact ((Complex.differentiable_exp (f z)).comp_differentiableWithinAt z (hf z hz))
  have hmax : IsMaxOn (norm ∘ fun z => Complex.exp (f z)) (ball z₀ r) z₀ := by
    intro w hw
    simp only [Function.comp_apply, Set.mem_setOf_eq, Complex.norm_exp,
      hre w hw, hre z₀ (mem_ball_self hr)]
    exact le_refl _
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    ((convex_ball z₀ r).isPreconnected) isOpen_ball hg (mem_ball_self hr) hmax
  have hev : (fun z => Complex.exp (f z)) =ᶠ[nhds z₀] fun _ => Complex.exp (f z₀) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact hconst hz
  have hzero : deriv (fun z => Complex.exp (f z)) z₀ = 0 := by
    rw [hev.deriv_eq, deriv_const]
  have hfd : DifferentiableAt ℂ f z₀ :=
    hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hchain : deriv (fun z => Complex.exp (f z)) z₀ =
      Complex.exp (f z₀) * deriv f z₀ := by
    have hcomp : HasDerivAt (fun z => Complex.exp (f z))
        (Complex.exp (f z₀) * deriv f z₀) z₀ :=
      HasDerivAt.cexp hfd.hasDerivAt
    exact hcomp.deriv
  rw [hchain] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (Complex.exp_ne_zero _)

/-! ## Vertical decay -/

theorem four_lt_norm_xiSpectralPoint (q : XiZeroCopy) : 4 < ‖xiSpectralPoint q‖ := by
  have hgap := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hnorm : ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := norm_xiSpectralPoint q
  have hsq : ‖(q.1 : ℂ) - 1 / 2‖ ^ 2 =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 + ((q.1 : ℂ).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  have hpos : 0 ≤ ‖xiSpectralPoint q‖ := norm_nonneg _
  have hbig : 16 < ‖xiSpectralPoint q‖ ^ 2 := by
    rw [hnorm, hsq]
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  nlinarith

theorem half_norm_le_norm_sub_vertical (q : XiZeroCopy) (t : ℝ) :
    ‖xiSpectralPoint q‖ / 2 ≤ ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖ := by
  have him := abs_im_xiSpectralPoint_lt_half q
  have hbig := four_lt_norm_xiSpectralPoint q
  have hre : |(xiSpectralPoint q - Complex.I * (t : ℂ)).re| ≤
      ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖ := Complex.abs_re_le_norm _
  have hval : (xiSpectralPoint q - Complex.I * (t : ℂ)).re = (xiSpectralPoint q).re := by
    simp [Complex.mul_re]
  rw [hval] at hre
  have hsplit : ‖xiSpectralPoint q‖ ≤ |(xiSpectralPoint q).re| + |(xiSpectralPoint q).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  linarith

theorem tendsto_xiCauchyTransform_vertical (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    Filter.Tendsto (fun t : ℝ => xiCauchyTransform u (Complex.I * (t : ℂ)))
      Filter.atTop (nhds 0) := by
  have hbound : Summable (fun q : XiZeroCopy => 2 * (‖u q‖ * ‖xiSpectralPoint q‖⁻¹)) :=
    (summable_cauchy_majorant u).mul_left 2
  have hpoint : ∀ q : XiZeroCopy, Filter.Tendsto
      (fun t : ℝ => (starRingEnd ℂ) (u q) * (xiSpectralPoint q - Complex.I * (t : ℂ))⁻¹)
      Filter.atTop (nhds 0) := by
    intro q
    have hnorm : Filter.Tendsto
        (fun t : ℝ => ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - Complex.I * (t : ℂ))⁻¹‖)
        Filter.atTop (nhds 0) := by
      have hden : Filter.Tendsto
          (fun t : ℝ => ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖) Filter.atTop Filter.atTop := by
        have hge : ∀ t : ℝ, |t| - ‖xiSpectralPoint q‖ ≤
            ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖ := by
          intro t
          have h1 : ‖Complex.I * (t : ℂ)‖ = |t| := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          have h2 := norm_sub_norm_le (xiSpectralPoint q) (Complex.I * (t : ℂ))
          have h3 := norm_sub_rev (xiSpectralPoint q) (Complex.I * (t : ℂ))
          have h4 : ‖Complex.I * (t : ℂ)‖ - ‖xiSpectralPoint q‖ ≤
              ‖Complex.I * (t : ℂ) - xiSpectralPoint q‖ :=
            norm_sub_norm_le _ _
          rw [← h3] at h4
          rw [← h1]
          exact h4
        refine Filter.tendsto_atTop_mono hge ?_
        exact Filter.tendsto_atTop_add_const_right _ _ (tendsto_abs_atTop_atTop)
      have hinv : Filter.Tendsto
          (fun t : ℝ => ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖⁻¹) Filter.atTop (nhds 0) :=
        hden.inv_tendsto_atTop
      have hmul := hinv.const_mul ‖u q‖
      rw [mul_zero] at hmul
      refine hmul.congr (fun t => ?_)
      rw [norm_mul, RCLike.norm_conj, norm_inv]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hdom : ∀ᶠ t : ℝ in Filter.atTop, ∀ q : XiZeroCopy,
      ‖(starRingEnd ℂ) (u q) * (xiSpectralPoint q - Complex.I * (t : ℂ))⁻¹‖ ≤
        2 * (‖u q‖ * ‖xiSpectralPoint q‖⁻¹) := by
    filter_upwards with t q
    have hlow := half_norm_le_norm_sub_vertical q t
    have hαpos : 0 < ‖xiSpectralPoint q‖ := by
      have := four_lt_norm_xiSpectralPoint q; linarith
    have hpos : 0 < ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖ := by linarith
    rw [norm_mul, RCLike.norm_conj, norm_inv]
    have hinvle : ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖⁻¹ ≤
        2 * ‖xiSpectralPoint q‖⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpos hαpos]
      linarith
    calc ‖u q‖ * ‖xiSpectralPoint q - Complex.I * (t : ℂ)‖⁻¹
        ≤ ‖u q‖ * (2 * ‖xiSpectralPoint q‖⁻¹) :=
          mul_le_mul_of_nonneg_left hinvle (norm_nonneg _)
      _ = 2 * (‖u q‖ * ‖xiSpectralPoint q‖⁻¹) := by ring
  have h := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  rw [tsum_zero] at h
  exact h

/-! ## The completeness theorem -/

theorem XiC_ne_zero_vertical {t : ℝ} (ht : 1 ≤ t) : XiC (Complex.I * (t : ℂ)) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hzero
  have him := abs_im_xiSpectralPoint_lt_half q
  rw [hq] at him
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul] at him
  rw [zero_add, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)] at him
  linarith

/-- **Cauchy-transform completeness.**  A divisor vector whose Cauchy transform has vanishing real
part on one nonempty ball inside the regular set has identically vanishing transform. -/
theorem xiCauchyTransform_eq_zero_of_re_eq_zero_on_ball
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball z₀ r ⊆ {z : ℂ | XiC z ≠ 0})
    (hre : ∀ z ∈ ball z₀ r, (xiCauchyTransform u z).re = 0)
    {z : ℂ} (hz : XiC z ≠ 0) :
    xiCauchyTransform u z = 0 := by
  have hU := isOpen_xiRegularSet
  have hconn := isPreconnected_xiRegularSet
  have hdiff := differentiableOn_xiCauchyTransform u
  have hz₀ : z₀ ∈ {z : ℂ | XiC z ≠ 0} := hball (mem_ball_self hr)
  have hderivball : ∀ w ∈ ball z₀ r, deriv (xiCauchyTransform u) w = 0 := by
    intro w hw
    have hd : dist w z₀ < r := by rwa [mem_ball] at hw
    set ρ : ℝ := r - dist w z₀ with hρ
    have hρpos : 0 < ρ := by rw [hρ]; linarith
    have hsub : ball w ρ ⊆ ball z₀ r := by
      intro y hy
      rw [mem_ball] at hy ⊢
      have := dist_triangle y w z₀
      rw [hρ] at hy
      linarith
    refine deriv_eq_zero_of_re_eq_zero_on_ball hρpos ?_ (fun y hy => hre y (hsub hy))
    exact hdiff.mono (fun y hy => hball (hsub hy))
  have hana : AnalyticOnNhd ℂ (deriv (xiCauchyTransform u)) {z : ℂ | XiC z ≠ 0} :=
    ((hdiff.analyticOnNhd hU)).deriv
  have hev : deriv (xiCauchyTransform u) =ᶠ[nhds z₀] 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    exact hderivball w hw
  have hzeroDeriv : Set.EqOn (deriv (xiCauchyTransform u)) 0 {z : ℂ | XiC z ≠ 0} :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hev
  have hconst : ∀ {x y : ℂ}, x ∈ {z : ℂ | XiC z ≠ 0} → y ∈ {z : ℂ | XiC z ≠ 0} →
      xiCauchyTransform u x = xiCauchyTransform u y :=
    fun hx hy => hU.is_const_of_deriv_eq_zero hconn hdiff hzeroDeriv hx hy
  have hlimit := tendsto_xiCauchyTransform_vertical u
  have heq : ∀ᶠ t : ℝ in Filter.atTop,
      xiCauchyTransform u (Complex.I * (t : ℂ)) = xiCauchyTransform u z := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    exact hconst (XiC_ne_zero_vertical ht) hz
  have hconstlim : Filter.Tendsto (fun _ : ℝ => xiCauchyTransform u z) Filter.atTop (nhds 0) :=
    hlimit.congr' heq
  exact tendsto_nhds_unique (tendsto_const_nhds (x := xiCauchyTransform u z)
    (f := Filter.atTop (α := ℝ))) hconstlim

/-- The multiplicity fibre sums vanish for such a vector. -/
theorem xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball z₀ r ⊆ {z : ℂ | XiC z ≠ 0})
    (hre : ∀ z ∈ ball z₀ r, (xiCauchyTransform u z).re = 0)
    (ρ : XiDivisorSupport) :
    xiWeilFiberSum (fun q => u q) ρ = 0 := by
  refine xiWeilFiberSum_eq_zero_of_inner_xiWeilCauchyLp_eq_zero u (fun w => ?_) ρ
  have hval : inner ℂ u (xiWeilCauchyLp w) = 0 := by
    rw [← xiCauchyTransform_eq_inner]
    exact xiCauchyTransform_eq_zero_of_re_eq_zero_on_ball u hr hball hre w.2
  have hconj := congrArg (starRingEnd ℂ) hval
  rw [inner_conj_symm, map_zero] at hconj
  exact hconj

end

end RHTower
