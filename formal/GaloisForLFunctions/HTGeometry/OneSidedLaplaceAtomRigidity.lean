import Mathlib
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected

/-!
# One-sided Laplace identities kill atoms in the upper half-plane

Let `c_i` be absolutely summable weights at points `q_i` of the open upper half-plane, with
bounded imaginary parts and no accumulation point in the half-plane, and let `h ∈ L¹(ℝ)`.
Suppose that for every *positive* frequency `u`

`∑ c_i e^{-i u q_i} = ∫ h(t) e^{-i u t} dt`.

Then every `c_i` vanishes.

**Proof.** For `Im w` above all the points, `1/(z - w) = i ∫₀^∞ e^{-iu(z-w)} du` for every point
`z` of the half-plane or of the real line, so Fubini turns the identity into an identity of Cauchy
transforms, `∑ c_i/(q_i - w) = ∫ h(t)/(t - w) dt`. The right side is holomorphic on the whole upper
half-plane. The left side is holomorphic off the points, the half-plane minus a countable set is
connected, and the identity theorem extends the equality down to every point. Near `q_i` the
right side stays bounded while the left side carries the polar part `c_i/(q_i - w)`; hence
`c_i = 0`.

Only positive frequencies are used, and no growth of `h` beyond integrability enters.
-/

open Complex MeasureTheory Set Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The one-sided Laplace representation of the Cauchy kernel: if `Im z < Im w`, then
`i ∫₀^∞ e^{-iu(z-w)} du = 1/(z - w)`. -/
theorem I_mul_integral_Ioi_laplaceKernel {z w : ℂ} (h : z.im < w.im) :
    I * ∫ u in Ioi (0 : ℝ), cexp (-(I * (z - w)) * u) = 1 / (z - w) := by
  have hre : (-(I * (z - w))).re < 0 := by
    simp only [neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg, sub_im]
    linarith
  have hzw : z - w ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [sub_im, zero_im] at this
    linarith
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem norm_laplaceKernel (z w : ℂ) (u : ℝ) :
    ‖cexp (-(I * (z - w)) * u)‖ = Real.exp (u * (z.im - w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, I_re, sub_re, zero_mul, I_im, sub_im, one_mul, zero_sub,
    ofReal_re, ofReal_im, mul_zero, sub_zero, neg_neg]
  ring

theorem integrableOn_laplaceKernel {z w : ℂ} (h : z.im < w.im) :
    IntegrableOn (fun u : ℝ => cexp (-(I * (z - w)) * u)) (Ioi 0) := by
  have hre : (-(I * (z - w))).re < 0 := by
    simp only [neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg, sub_im]
    linarith
  exact integrableOn_exp_mul_complex_Ioi hre 0

theorem integral_norm_laplaceKernel {z w : ℂ} (h : z.im < w.im) :
    ∫ u in Ioi (0 : ℝ), ‖cexp (-(I * (z - w)) * u)‖ = 1 / (w.im - z.im) := by
  simp_rw [norm_laplaceKernel]
  have ha : z.im - w.im < 0 := by linarith
  simp_rw [mul_comm _ (z.im - w.im)]
  rw [integral_exp_mul_Ioi ha 0]
  simp only [mul_zero, Real.exp_zero]
  rw [neg_div, ← div_neg, neg_sub]

/-! ## The Cauchy transform of an integrable function -/

theorem norm_sub_ge_im {t : ℝ} {w : ℂ} (hw : 0 ≤ w.im) : w.im ≤ ‖(t : ℂ) - w‖ := by
  have hle := Complex.abs_im_le_norm ((t : ℂ) - w)
  have he : ((t : ℂ) - w).im = -w.im := by simp [Complex.sub_im]
  rw [he, abs_neg, abs_of_nonneg hw] at hle
  exact hle

/-- The Cauchy transform `w ↦ ∫ h(t)/(t - w) dt` of an integrable `h` is holomorphic on the open
upper half-plane. -/
theorem differentiableOn_integral_div_sub_upperHalfPlane {h : ℝ → ℂ} (hh : Integrable h) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t : ℝ, h t / ((t : ℂ) - w)) {w : ℂ | 0 < w.im} := by
  intro w₀ hw₀
  have hw₀' : 0 < w₀.im := hw₀
  set r : ℝ := w₀.im / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hball : ∀ w ∈ ball w₀ r, r ≤ w.im := by
    intro w hw
    have hd : |w.im - w₀.im| < r := by
      calc |w.im - w₀.im| = |(w - w₀).im| := by simp
        _ ≤ ‖w - w₀‖ := Complex.abs_im_le_norm _
        _ < r := by simpa [dist_eq_norm] using hw
    have := (abs_lt.mp hd).1
    rw [hr] at this ⊢
    linarith
  have hne : ∀ w ∈ ball w₀ r, ∀ t : ℝ, (t : ℂ) - w ≠ 0 := by
    intro w hw t h0
    have hlow := norm_sub_ge_im (t := t) (le_trans hrpos.le (hball w hw))
    rw [h0, norm_zero] at hlow
    linarith [hball w hw]
  have hderiv : ∀ t : ℝ, ∀ w ∈ ball w₀ r,
      HasDerivAt (fun w : ℂ => h t / ((t : ℂ) - w)) (h t / ((t : ℂ) - w) ^ 2) w := by
    intro t w hw
    have h1 : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub (t : ℂ)
    have h2 : HasDerivAt (fun w : ℂ => h t / ((t : ℂ) - w))
        ((0 * ((t : ℂ) - w) - h t * -1) / ((t : ℂ) - w) ^ 2) w :=
      (hasDerivAt_const w (h t)).div h1 (hne w hw t)
    exact h2.congr_deriv (by ring)
  have hbound : ∀ t : ℝ, ∀ w ∈ ball w₀ r,
      ‖h t / ((t : ℂ) - w) ^ 2‖ ≤ ‖h t‖ * (r ^ 2)⁻¹ := by
    intro t w hw
    rw [norm_div, norm_pow, div_eq_mul_inv]
    gcongr
    exact le_trans (hball w hw) (norm_sub_ge_im (le_trans hrpos.le (hball w hw)))
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => h t / ((t : ℂ) - w)) volume := by
    intro w
    simp_rw [div_eq_mul_inv]
    exact hh.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.sub_const w).inv.aestronglyMeasurable)
  have hint₀ : Integrable (fun t : ℝ => h t / ((t : ℂ) - w₀)) := by
    refine (hh.norm.mul_const (r⁻¹)).mono' (hmeas w₀) (ae_of_all _ fun t => ?_)
    rw [norm_div, div_eq_mul_inv]
    gcongr
    exact le_trans (hball w₀ (mem_ball_self hrpos))
      (norm_sub_ge_im (le_trans hrpos.le (hball w₀ (mem_ball_self hrpos))))
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w : ℂ => fun t : ℝ => h t / ((t : ℂ) - w))
    (F' := fun w : ℂ => fun t : ℝ => h t / ((t : ℂ) - w) ^ 2)
    (bound := fun t => ‖h t‖ * (r ^ 2)⁻¹) (ball_mem_nhds w₀ hrpos)
    (Eventually.of_forall hmeas) hint₀
    (by
      simp_rw [div_eq_mul_inv]
      exact hh.aestronglyMeasurable.mul
        (((Complex.measurable_ofReal.sub_const w₀).pow_const 2).inv.aestronglyMeasurable))
    (ae_of_all _ fun t w hw => hbound t w hw) (hh.norm.mul_const _)
    (ae_of_all _ fun t w hw => hderiv t w hw)
  exact hres.2.differentiableAt.differentiableWithinAt

/-! ## From one-sided Laplace identities to Cauchy transforms -/

/-- **Cauchy-transform identity.** If the one-sided Laplace identity holds at every positive
frequency, then the Cauchy transforms of the atoms and of `h` agree above all the atoms. -/
theorem tsum_div_sub_eq_cauchyTransform_of_laplace
    {ι : Type*} [Countable ι] {q c : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    {B : ℝ} (hB : ∀ i, (q i).im ≤ B) (hB0 : 0 ≤ B)
    {h : ℝ → ℂ} (hh : Integrable h)
    (hid : ∀ u : ℝ, 0 < u →
      ∑' i, c i * cexp (-(I * q i) * u) = ∫ t : ℝ, h t * cexp (-(I * t) * u))
    {w : ℂ} (hw : B < w.im) :
    ∑' i, c i / (q i - w) = ∫ t : ℝ, h t / ((t : ℂ) - w) := by
  have hwpos : 0 < w.im := lt_of_le_of_lt hB0 hw
  -- kernel and its integral
  have hqw : ∀ i, (q i).im < w.im := fun i => lt_of_le_of_lt (hB i) hw
  have htw : ∀ t : ℝ, ((t : ℂ)).im < w.im := by
    intro t; simpa using hwpos
  -- Step 1: each atom term as a Laplace integral
  have hatom : ∀ i, c i / (q i - w) =
      I * ∫ u in Ioi (0 : ℝ), c i * cexp (-(I * (q i - w)) * u) := by
    intro i
    rw [integral_const_mul, ← mul_assoc, mul_comm I (c i), mul_assoc,
      I_mul_integral_Ioi_laplaceKernel (hqw i), mul_one_div]
  -- Step 2: exchange sum and integral
  have hsumint : Summable fun i => ∫ u in Ioi (0 : ℝ), ‖c i * cexp (-(I * (q i - w)) * u)‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun u => norm_nonneg _)
      (fun i => ?_) (hc.mul_right (1 / (w.im - B)))
    simp_rw [norm_mul]
    rw [integral_const_mul, integral_norm_laplaceKernel (hqw i)]
    gcongr
    linarith [hB i]
  have hswap1 : ∑' i, ∫ u in Ioi (0 : ℝ), c i * cexp (-(I * (q i - w)) * u) =
      ∫ u in Ioi (0 : ℝ), ∑' i, c i * cexp (-(I * (q i - w)) * u) :=
    integral_tsum_of_summable_integral_norm
      (fun i => (integrableOn_laplaceKernel (hqw i)).const_mul (c i)) hsumint
  -- Step 3: use the identity pointwise on `Ioi 0`
  have hpoint : ∀ u ∈ Ioi (0 : ℝ), ∑' i, c i * cexp (-(I * (q i - w)) * u) =
      ∫ t : ℝ, h t * cexp (-(I * ((t : ℂ) - w)) * u) := by
    intro u hu
    have hsplit : ∀ z : ℂ, cexp (-(I * (z - w)) * u) =
        cexp (-(I * z) * u) * cexp (I * w * u) := by
      intro z
      rw [← Complex.exp_add]
      congr 1
      ring
    simp_rw [hsplit, ← mul_assoc]
    rw [tsum_mul_right, hid u hu, integral_mul_const]
  have hstep3 : ∫ u in Ioi (0 : ℝ), ∑' i, c i * cexp (-(I * (q i - w)) * u) =
      ∫ u in Ioi (0 : ℝ), ∫ t : ℝ, h t * cexp (-(I * ((t : ℂ) - w)) * u) :=
    setIntegral_congr_fun measurableSet_Ioi hpoint
  -- Step 4: Fubini
  have hprod : Integrable (Function.uncurry fun (u : ℝ) (t : ℝ) =>
      h t * cexp (-(I * ((t : ℂ) - w)) * u)) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-w.im * p.1) * ‖h p.2‖)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
      have he : Integrable (fun u : ℝ => Real.exp (-w.im * u)) (volume.restrict (Ioi 0)) :=
        integrableOn_exp_mul_Ioi (a := -w.im) (by linarith) 0
      exact he.mul_prod hh.norm
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => h p.2)
          ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
        hh.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => cexp (-(I * ((p.2 : ℂ) - w)) * p.1))
          ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
        exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
          cexp (-(I * ((p.2 : ℂ) - w)) * p.1)).aestronglyMeasurable
      exact hm1.mul hm2
    · obtain ⟨u, t⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [norm_mul, norm_laplaceKernel, ofReal_im, mul_comm]
      exact le_of_eq (by congr 2; ring)
  have hstep4 : ∫ u in Ioi (0 : ℝ), ∫ t : ℝ, h t * cexp (-(I * ((t : ℂ) - w)) * u) =
      ∫ t : ℝ, ∫ u in Ioi (0 : ℝ), h t * cexp (-(I * ((t : ℂ) - w)) * u) :=
    integral_integral_swap hprod
  -- Step 5: evaluate the inner integral
  have hstep5 : ∀ t : ℝ, I * ∫ u in Ioi (0 : ℝ), h t * cexp (-(I * ((t : ℂ) - w)) * u) =
      h t / ((t : ℂ) - w) := by
    intro t
    rw [integral_const_mul, ← mul_assoc, mul_comm I (h t), mul_assoc,
      I_mul_integral_Ioi_laplaceKernel (htw t), mul_one_div]
  calc ∑' i, c i / (q i - w)
      = ∑' i, I * ∫ u in Ioi (0 : ℝ), c i * cexp (-(I * (q i - w)) * u) := tsum_congr hatom
    _ = I * ∑' i, ∫ u in Ioi (0 : ℝ), c i * cexp (-(I * (q i - w)) * u) := tsum_mul_left
    _ = I * ∫ t : ℝ, ∫ u in Ioi (0 : ℝ), h t * cexp (-(I * ((t : ℂ) - w)) * u) := by
        rw [hswap1, hstep3, hstep4]
    _ = ∫ t : ℝ, I * ∫ u in Ioi (0 : ℝ), h t * cexp (-(I * ((t : ℂ) - w)) * u) :=
        (integral_const_mul _ _).symm
    _ = ∫ t : ℝ, h t / ((t : ℂ) - w) := integral_congr_ae (ae_of_all _ hstep5)

/-! ## Atom rigidity -/

/-- Away from a point set that avoids `ball w r`, the atom sum is holomorphic. -/
theorem differentiableOn_tsum_div_sub_of_far {ι : Type*} {q c : ι → ℂ}
    (hc : Summable fun i => ‖c i‖) {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hfar : ∀ i, r ≤ ‖q i - w‖) :
    DifferentiableOn ℂ (fun z => ∑' i, c i / (q i - z)) (ball w (r / 2)) := by
  have hfar' : ∀ i, ∀ z ∈ ball w (r / 2), r / 2 ≤ ‖q i - z‖ := by
    intro i z hz
    have hzw : ‖z - w‖ < r / 2 := by rw [← dist_eq_norm]; exact hz
    have htri := norm_sub_norm_le (q i - w) (z - w)
    rw [sub_sub_sub_cancel_right] at htri
    linarith [hfar i]
  refine differentiableOn_tsum_of_summable_norm (u := fun i => ‖c i‖ * (r / 2)⁻¹)
    (hc.mul_right _) (fun i => ?_) isOpen_ball (fun i z hz => ?_)
  · intro z hz
    have hne : q i - z ≠ 0 := by
      intro h0
      have := hfar' i z hz
      rw [h0, norm_zero] at this
      linarith
    exact ((differentiableAt_const _).div (by fun_prop) hne).differentiableWithinAt
  · rw [norm_div, div_eq_mul_inv]
    gcongr
    exact hfar' i z hz

/-- **One-sided Laplace atom rigidity.** Let `c` be absolutely summable weights at distinct points
`q_i` of the open upper half-plane with bounded imaginary parts and no accumulation point in the
half-plane, and let `h` be integrable on `ℝ`. If
`∑ c_i e^{-iuq_i} = ∫ h(t) e^{-iut} dt` for every `u > 0`, then every weight vanishes. -/
theorem eq_zero_of_oneSidedLaplace_eq
    {ι : Type*} [Countable ι] {q c : ι → ℂ} (hq : Function.Injective q)
    (hc : Summable fun i => ‖c i‖)
    (hpos : ∀ i, 0 < (q i).im) {B : ℝ} (hB : ∀ i, (q i).im ≤ B)
    (hdisc : ∀ z : ℂ, 0 < z.im → ∃ r > 0, ∀ i, q i ∈ ball z r → q i = z)
    {h : ℝ → ℂ} (hh : Integrable h)
    (hid : ∀ u : ℝ, 0 < u →
      ∑' i, c i * cexp (-(I * q i) * u) = ∫ t : ℝ, h t * cexp (-(I * t) * u)) (i₀ : ι) :
    c i₀ = 0 := by
  classical
  set H : Set ℂ := {w : ℂ | 0 < w.im} with hH
  set Z : Set ℂ := Set.range q with hZ
  have hB0 : 0 ≤ B := le_trans (hpos i₀).le (hB i₀)
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hZcount : Z.Countable := Set.countable_range q
  -- the punctured half-plane is open
  have hVopen : IsOpen (H \ Z) := by
    rw [Metric.isOpen_iff]
    intro w hw
    obtain ⟨r, hr, hrq⟩ := hdisc w hw.1
    obtain ⟨r', hr', hr'H⟩ := Metric.isOpen_iff.mp hHopen w hw.1
    refine ⟨min r r', lt_min hr hr', fun z hz => ⟨hr'H (ball_subset_ball (min_le_right _ _) hz), ?_⟩⟩
    rintro ⟨i, rfl⟩
    exact hw.2 ⟨i, hrq i (ball_subset_ball (min_le_left _ _) hz)⟩
  -- far bound from the punctured half-plane
  have hfarV : ∀ w ∈ H \ Z, ∃ r > 0, ∀ i, r ≤ ‖q i - w‖ := by
    intro w hw
    obtain ⟨r, hr, hrq⟩ := hdisc w hw.1
    refine ⟨r, hr, fun i => ?_⟩
    by_contra hlt
    push Not at hlt
    have hin : q i ∈ ball w r := by rw [mem_ball, dist_eq_norm]; exact hlt
    exact hw.2 ⟨i, hrq i hin⟩
  set D : ℂ → ℂ := fun w => ∑' i, c i / (q i - w) with hD
  set R : ℂ → ℂ := fun w => ∫ t : ℝ, h t / ((t : ℂ) - w) with hR
  have hDdiff : DifferentiableOn ℂ D (H \ Z) := by
    intro w hw
    obtain ⟨r, hr, hfar⟩ := hfarV w hw
    exact ((differentiableOn_tsum_div_sub_of_far hc hr hfar).differentiableAt
      (ball_mem_nhds w (by linarith))).differentiableWithinAt
  have hRdiff : DifferentiableOn ℂ R H := differentiableOn_integral_div_sub_upperHalfPlane hh
  have hEan : AnalyticOnNhd ℂ (fun w => D w - R w) (H \ Z) :=
    (hDdiff.sub (hRdiff.mono sdiff_subset)).analyticOnNhd hVopen
  -- a base point above all atoms
  set wstar : ℂ := ((B + 1 : ℝ) : ℂ) * I with hwstar
  have hwstar_im : wstar.im = B + 1 := by simp [hwstar]
  have hwstarV : wstar ∈ H \ Z := by
    refine ⟨?_, ?_⟩
    · show 0 < wstar.im
      rw [hwstar_im]; linarith
    · rintro ⟨i, hi⟩
      have := hB i
      rw [hi, hwstar_im] at this
      linarith
  have hVpre : IsPreconnected (H \ Z) :=
    isPreconnected_diff_of_countable_of_convex_complex (convex_halfSpace_im_gt 0) hHopen
      hZcount hwstarV
  have hev : (fun w => D w - R w) =ᶠ[𝓝 wstar] 0 := by
    have hopen : IsOpen {w : ℂ | B < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have hmem : wstar ∈ {w : ℂ | B < w.im} := by
      show B < wstar.im
      rw [hwstar_im]; linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    simp only [Pi.zero_apply, sub_eq_zero, hD, hR]
    exact tsum_div_sub_eq_cauchyTransform_of_laplace hc hB hB0 hh hid hw
  have hEzero := hEan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVpre hwstarV hev
  -- residue extraction at `q i₀`
  set z₀ := q i₀ with hz₀
  obtain ⟨r, hr, hrq⟩ := hdisc z₀ (hpos i₀)
  set ρ : ℝ := min (r / 2) (z₀.im / 2) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith [hpos i₀])
  have hfar : ∀ i, i ≠ i₀ → r ≤ ‖q i - z₀‖ := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have hin : q i ∈ ball z₀ r := by rw [mem_ball, dist_eq_norm]; exact hlt
    exact hi (hq (hrq i hin))
  set c₁ : ι → ℂ := fun i => if i = i₀ then 0 else c i with hc₁
  have hc₁sum : Summable fun i => ‖c₁ i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hc
    by_cases hi : i = i₀ <;> simp [hc₁, hi]
  set q₁ : ι → ℂ := fun i => if i = i₀ then z₀ + (r : ℂ) else q i with hq₁
  have hfar₁ : ∀ i, r ≤ ‖q₁ i - z₀‖ := by
    intro i
    by_cases hi : i = i₀
    · simp [hq₁, hi, abs_of_pos hr]
    · simpa [hq₁, hi] using hfar i hi
  set D₁ : ℂ → ℂ := fun w => ∑' i, c₁ i / (q₁ i - w) with hD₁
  have hD₁cont : ContinuousAt D₁ z₀ :=
    ((differentiableOn_tsum_div_sub_of_far hc₁sum hr hfar₁).differentiableAt
      (ball_mem_nhds z₀ (by linarith))).continuousAt
  have hRcont : ContinuousAt R z₀ :=
    (hRdiff.differentiableAt (hHopen.mem_nhds (hpos i₀))).continuousAt
  have hsplit : ∀ w ∈ ball z₀ ρ, w ≠ z₀ → D w = c i₀ / (z₀ - w) + D₁ w := by
    intro w hw hne
    have hwr : w ∈ ball z₀ (r / 2) := ball_subset_ball (min_le_left _ _) hw
    have hfarw : ∀ i, i ≠ i₀ → r / 2 ≤ ‖q i - w‖ := by
      intro i hi
      have hzw : ‖w - z₀‖ < r / 2 := by rw [← dist_eq_norm]; exact hwr
      have htri := norm_sub_norm_le (q i - z₀) (w - z₀)
      rw [sub_sub_sub_cancel_right] at htri
      linarith [hfar i hi]
    have hsum₁ : Summable fun i => c₁ i / (q₁ i - w) := by
      refine Summable.of_norm_bounded (g := fun i => ‖c i‖ * (r / 2)⁻¹) (hc.mul_right _)
        (fun i => ?_)
      by_cases hi : i = i₀
      · simp only [hc₁, hi, if_true, zero_div, norm_zero]
        positivity
      · simp only [hc₁, hq₁, hi, if_false]
        rw [norm_div, div_eq_mul_inv]
        gcongr
        exact hfarw i hi
    have hterm : ∀ i, c i / (q i - w) =
        (if i = i₀ then c i₀ / (z₀ - w) else 0) + c₁ i / (q₁ i - w) := by
      intro i
      by_cases hi : i = i₀
      · subst hi; simp [hc₁, hz₀]
      · simp [hc₁, hq₁, hi]
    have hsum₀ : Summable fun i => (if i = i₀ then c i₀ / (z₀ - w) else 0) :=
      (hasSum_ite_eq i₀ (c i₀ / (z₀ - w))).summable
    simp only [hD, hD₁]
    rw [tsum_congr hterm, Summable.tsum_add hsum₀ hsum₁, tsum_ite_eq]
  have hconst : ∀ w ∈ ball z₀ ρ, w ≠ z₀ → c i₀ = (z₀ - w) * (R w - D₁ w) := by
    intro w hw hne
    have hwH : 0 < w.im := by
      have hd : |w.im - z₀.im| < z₀.im / 2 := by
        calc |w.im - z₀.im| = |(w - z₀).im| := by simp
          _ ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
          _ < ρ := by rw [← dist_eq_norm]; exact hw
          _ ≤ z₀.im / 2 := min_le_right _ _
      linarith [(abs_lt.mp hd).1, hpos i₀]
    have hwZ : w ∉ Z := by
      rintro ⟨i, hi⟩
      have hin : q i ∈ ball z₀ r := by
        rw [hi]
        exact ball_subset_ball (le_trans (min_le_left _ _) (by linarith)) hw
      exact hne (hi ▸ hrq i hin)
    have hDR : D w = R w := by
      have := hEzero ⟨hwH, hwZ⟩
      simpa [sub_eq_zero] using this
    rw [hsplit w hw hne] at hDR
    have hzw : z₀ - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hdiv : c i₀ / (z₀ - w) = R w - D₁ w := by rw [← hDR]; ring
    rw [div_eq_iff hzw] at hdiv
    rw [hdiv]
    ring
  have hlim : Tendsto (fun w => (z₀ - w) * (R w - D₁ w)) (𝓝[≠] z₀) (𝓝 0) := by
    have hcont : ContinuousAt (fun w => (z₀ - w) * (R w - D₁ w)) z₀ :=
      (continuousAt_const.sub continuousAt_id).mul (hRcont.sub hD₁cont)
    have := hcont.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hevc : (fun _ : ℂ => c i₀) =ᶠ[𝓝[≠] z₀] fun w => (z₀ - w) * (R w - D₁ w) := by
    have hball : ball z₀ ρ ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hρpos)
    filter_upwards [hball, self_mem_nhdsWithin] with w hw hne
    exact hconst w hw hne
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hevc) hlim

end

end GaloisForLFunctions.HTGeometry
