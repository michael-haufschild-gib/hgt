import GaloisForLFunctions.RHTower.ChronologicalTailProfiles

/-!
# The heat-transform separation

For `0 < θ < 1`, any `ρ` on the critical line, and any bounded measurable tail profile `f`, the
critical transform `K_ρ` and the tail transform `F_f` cannot agree on the sampling interval
`[1,2]`. This is step 1 of the fixed-tail obstruction, and it needs no zeta input at all — only
`Re ρ = 1/2`.

The proof: agreement on `[1,2]` propagates to the whole positive axis (identity theorem in the
transform variable), the Mellin transform in `u` then gives, after cancelling the strictly
positive bracket, the moment identity

  `θ^(ρ-s)/(ρ-s) = ∫_θ¹ f(x) x^(-s) dx`   for real `0 < s < 1/2`.

Both sides are analytic in `s` on the half-plane `Re s < 1/2` — the left because `ρ - s` never
vanishes there, the right because it is a Mellin integral of a bounded function over a compact
interval away from the origin — so the identity continues to that half-plane. At `s = ρ - δ` the
left side has modulus `θ^δ/δ`, which exceeds the uniform bound `C θ^(-1/2)` on the right side as
soon as `δ` is small. No limit is needed: one explicit `δ` already contradicts.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-! ### An exponential form of the tail moment -/

/-- The tail moment written through `Complex.exp`, so that its `w`-derivative is elementary. -/
def tailMomentE (θ : ℝ) (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w))

theorem tailMomentE_eq (θ : ℝ) (f : ℝ → ℂ) (w : ℂ) :
    tailMomentE θ f w = tailMoment θ f w := by
  rw [tailMomentE, tailMoment]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx.1)),
    Complex.ofReal_log hx.1.le]

theorem norm_exp_log_mul {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ‖Complex.exp (((Real.log x : ℝ) : ℂ) * (-w))‖ = x ^ (-w.re) := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos hx]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, zero_mul, sub_zero]

/-! ### A uniform bound for the weight -/

theorem rpow_le_rpow_neg_bound {θ x a R : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hx : θ ≤ x)
    (hx1 : x ≤ 1) (ha : |a| ≤ R) : x ^ a ≤ θ ^ (-R) := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg a) ha
  have hx0 : 0 < x := lt_of_lt_of_le hθ0 hx
  rcases le_or_gt 0 a with h | h
  · have h1 : x ^ a ≤ 1 := Real.rpow_le_one hx0.le hx1 h
    have h2 : (1 : ℝ) ≤ θ ^ (-R) := by
      have := Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 (by linarith : -R ≤ (0 : ℝ))
      rwa [Real.rpow_zero] at this
    linarith
  · have hneg : (0 : ℝ) < -a := by linarith
    have h1 : x ^ a ≤ θ ^ a := by
      rw [show a = -(-a) by ring, Real.rpow_neg hx0.le, Real.rpow_neg hθ0.le,
        ← one_div, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθ0 _)
        (Real.rpow_le_rpow hθ0.le hx hneg.le)
    have h2 : θ ^ a ≤ θ ^ (-R) := by
      refine Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 ?_
      have := abs_le.mp ha
      linarith [this.1]
    linarith

theorem abs_log_le {θ x : ℝ} (hθ0 : 0 < θ) (hx : θ ≤ x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ -Real.log θ := by
  have hx0 : 0 < x := lt_of_lt_of_le hθ0 hx
  have h1 : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have h2 : Real.log θ ≤ Real.log x := Real.log_le_log hθ0 hx
  rw [abs_of_nonpos h1]
  linarith

/-! ### Analyticity of the tail moment -/

/-- The `w`-derivative of the tail moment. -/
def tailMomentEDeriv (θ : ℝ) (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1,
    tailProfile θ f x * (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))

theorem measurable_tailMomentE_integrand (θ : ℝ) {f : ℝ → ℂ} (hfm : Measurable f) (w : ℂ) :
    Measurable (fun x : ℝ =>
      tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w))) :=
  (measurable_tailProfile θ hfm).mul (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp Real.measurable_log).mul measurable_const))

theorem measurable_tailMomentEDeriv_integrand (θ : ℝ) {f : ℝ → ℂ} (hfm : Measurable f) (w : ℂ) :
    Measurable (fun x : ℝ => tailProfile θ f x *
      (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))) :=
  (measurable_tailProfile θ hfm).mul
    (((Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp Real.measurable_log).mul measurable_const))).mul
      ((Complex.measurable_ofReal.comp Real.measurable_log).neg))

theorem hasDerivAt_tailMomentE {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hfm : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ C) (w₀ : ℂ) :
    HasDerivAt (tailMomentE θ f) (tailMomentEDeriv θ f w₀) w₀ := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  set R : ℝ := |w₀.re| + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set K : ℝ := C * (θ ^ (-R) * (-Real.log θ)) with hKdef
  have hlogθ : 0 ≤ -Real.log θ := by
    have := Real.log_nonpos hθ0.le hθ1
    linarith
  have hK0 : 0 ≤ K := by
    refine mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hθ0.le _) hlogθ)
  have hreball : ∀ w ∈ Metric.ball w₀ 1, |w.re| ≤ R := by
    intro w hw
    have h1 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w₀)
    have h2 : ‖w - w₀‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have h3 := abs_le.mp h1
    have h4 := abs_le.mp (le_refl |w₀.re|)
    rw [hRdef]
    rcases abs_cases w.re with ⟨he, -⟩ | ⟨he, -⟩ <;>
      rcases abs_cases w₀.re with ⟨he0, -⟩ | ⟨he0, -⟩ <;> · rw [he]; linarith [h3.1, h3.2]
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ w ∈ Metric.ball w₀ 1,
      ‖tailProfile θ f x *
        (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))‖ ≤ K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx w hw
    have hx0 : (0 : ℝ) < x := hx.1
    by_cases hxθ : θ ≤ x
    · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        norm_exp_log_mul hx0]
      have hw1 : x ^ (-w.re) ≤ θ ^ (-R) := by
        refine rpow_le_rpow_neg_bound hθ0 hθ1 hxθ hx.2.le ?_
        rw [abs_neg]
        exact hreball w hw
      have hw2 : |Real.log x| ≤ -Real.log θ := abs_log_le hθ0 hxθ hx.2.le
      rw [hKdef]
      refine mul_le_mul (norm_tailProfile_le hC hfb x) ?_ ?_ hC
      · exact mul_le_mul hw1 hw2 (abs_nonneg _) (Real.rpow_nonneg hθ0.le _)
      · exact mul_nonneg (Real.rpow_nonneg hx0.le _) (abs_nonneg _)
    · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
      exact hK0
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun w : ℂ => tailProfile θ f x * Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)))
        (tailProfile θ f x *
          (Complex.exp (((Real.log x : ℝ) : ℂ) * (-w)) * (-((Real.log x : ℝ) : ℂ)))) w := by
    filter_upwards with x w _
    have hin : HasDerivAt (fun w : ℂ => ((Real.log x : ℝ) : ℂ) * (-w))
        (-((Real.log x : ℝ) : ℂ)) w := by
      simpa using ((hasDerivAt_id w).neg).const_mul ((Real.log x : ℝ) : ℂ)
    exact (hin.cexp).const_mul (tailProfile θ f x)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : ℝ => K) (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun w =>
      (measurable_tailMomentE_integrand θ hfm w).aestronglyMeasurable)
    (by
      refine Integrable.mono' (g := fun _ : ℝ => C * θ ^ (-R)) (integrable_const _)
        (measurable_tailMomentE_integrand θ hfm w₀).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx0 : (0 : ℝ) < x := hx.1
      by_cases hxθ : θ ≤ x
      · rw [norm_mul, norm_exp_log_mul hx0]
        have hw1 : x ^ (-w₀.re) ≤ θ ^ (-R) :=
          rpow_le_rpow_neg_bound hθ0 hθ1 hxθ hx.2.le (by
            rw [abs_neg]
            exact hreball w₀ (Metric.mem_ball_self one_pos))
        exact mul_le_mul (norm_tailProfile_le hC hfb x) hw1 (Real.rpow_nonneg hx0.le _) hC
      · rw [tailProfile_of_lt (by linarith), zero_mul, norm_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hθ0.le _))
    (measurable_tailMomentEDeriv_integrand θ hfm w₀).aestronglyMeasurable
    hbound (integrable_const _) hdiff
  exact hres.2

theorem differentiable_tailMomentE {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hfm : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ C) :
    Differentiable ℂ (tailMomentE θ f) := fun w =>
  (hasDerivAt_tailMomentE hθ0 hθ1 hC hfm hfb w).differentiableAt

/-! ### The critical moment -/

theorem cpow_ofReal_eq_exp_chronologicalTailSeparation {θ : ℝ} (hθ0 : 0 < θ) (z : ℂ) :
    (θ : ℂ) ^ z = Complex.exp (((Real.log θ : ℝ) : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hθ0)),
    Complex.ofReal_log hθ0.le]

/-- The critical moment `θ^(ρ-w)/(ρ-w)`, written through `Complex.exp`. -/
def criticalMomentE (θ : ℝ) (ρ : ℂ) (w : ℂ) : ℂ :=
  Complex.exp (((Real.log θ : ℝ) : ℂ) * (ρ - w)) / (ρ - w)

theorem criticalMomentE_eq_div {θ : ℝ} (hθ0 : 0 < θ) (ρ w : ℂ) :
    criticalMomentE θ ρ w = (θ : ℂ) ^ (ρ - w) / (ρ - w) := by
  rw [criticalMomentE, cpow_ofReal_eq_exp_chronologicalTailSeparation hθ0]

theorem norm_criticalMomentE {θ : ℝ} (hθ0 : 0 < θ) (ρ w : ℂ) :
    ‖criticalMomentE θ ρ w‖ = θ ^ (ρ - w).re / ‖ρ - w‖ := by
  rw [criticalMomentE, norm_div, Complex.norm_exp, Real.rpow_def_of_pos hθ0]
  congr 2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The half-plane strictly left of the critical line. -/
def leftHalfPlane : Set ℂ := {w : ℂ | w.re < 1 / 2}

theorem mem_leftHalfPlane {w : ℂ} : w ∈ leftHalfPlane ↔ w.re < 1 / 2 := Iff.rfl

theorem isOpen_leftHalfPlane : IsOpen leftHalfPlane :=
  isOpen_lt Complex.continuous_re continuous_const

theorem convex_leftHalfPlane : Convex ℝ leftHalfPlane := by
  have h : leftHalfPlane = {w : ℂ | Complex.reLm w < 1 / 2} := rfl
  rw [h]
  exact convex_halfSpace_lt (LinearMap.isLinear Complex.reLm) _

theorem isPreconnected_leftHalfPlane : IsPreconnected leftHalfPlane :=
  convex_leftHalfPlane.isPreconnected

theorem differentiableOn_criticalMomentE {θ : ℝ} {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    DifferentiableOn ℂ (criticalMomentE θ ρ) leftHalfPlane := by
  intro w hw
  have hre : 0 < (ρ - w).re := by
    rw [Complex.sub_re, hρ]
    have : w.re < 1 / 2 := hw
    linarith
  have hne : ρ - w ≠ 0 := by
    intro hz
    rw [hz] at hre
    simp at hre
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div ?_ ?_ hne
  · exact (Complex.differentiable_exp _).comp w
      ((differentiableAt_const _).mul ((differentiableAt_const ρ).sub differentiableAt_id))
  · exact (differentiableAt_const ρ).sub differentiableAt_id

/-! ### The moment identity on the real segment -/

theorem integrableOn_profile_weight_mul {g : ℝ → ℂ} (hgm : Measurable g) {s : ℝ}
    (hint : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun x : ℝ => g x * ((x ^ (-s) : ℝ) : ℂ)) (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono' hint (hgm.mul (Complex.measurable_ofReal.comp
    (measurable_id.pow_const _))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)]

theorem moment_identity_real {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hfm : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ C)
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ))
    {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 2) :
    criticalMomentE θ ρ (s : ℂ) = tailMomentE θ f (s : ℂ) := by
  have hcm : Measurable (criticalProfile θ ρ) := measurable_criticalProfile θ ρ
  have htm : Measurable (tailProfile θ f) := measurable_tailProfile θ hfm
  have hcw : IntegrableOn (fun x : ℝ => ‖criticalProfile θ ρ x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
    refine integrableOn_criticalProfile_weight ?_
    rw [hρ]; linarith
  have htw : IntegrableOn (fun x : ℝ => ‖tailProfile θ f x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) :=
    integrableOn_tailProfile_weight hθ0 hC hfm hfb hs0.le
  have hci : IntegrableOn (criticalProfile θ ρ) (Ioo (0 : ℝ) 1) :=
    integrableOn_of_weight hcm hs0.le hcw
  have hti : IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1) :=
    integrableOn_of_weight htm hs0.le htw
  set g : ℝ → ℂ := fun x => criticalProfile θ ρ x - tailProfile θ f x with hgdef
  have hgm : Measurable g := hcm.sub htm
  have hgw : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
    refine Integrable.mono' (hcw.add htw)
      ((hgm.norm).mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hw : (0 : ℝ) ≤ x ^ (-s) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    have hnorm : ‖g x‖ ≤ ‖criticalProfile θ ρ x‖ + ‖tailProfile θ f x‖ := norm_sub_le _ _
    calc ‖g x‖ * x ^ (-s)
        ≤ (‖criticalProfile θ ρ x‖ + ‖tailProfile θ f x‖) * x ^ (-s) :=
          mul_le_mul_of_nonneg_right hnorm hw
      _ = ‖criticalProfile θ ρ x‖ * x ^ (-s) + ‖tailProfile θ f x‖ * x ^ (-s) := by ring
  have hzero : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform g (t : ℂ) = 0 := by
    intro t ht
    have hmemD : ((t : ℝ) : ℂ) ∈ boseDomain :=
      ofReal_mem_boseDomain (by linarith [ht.1])
    rw [hgdef, boseTransform_sub hcm htm hci hti hmemD, h t ht, sub_self]
  have hmom := moment_eq_zero_of_transform_eqOn hgm hs0 (by linarith) hgw hzero
  have hsplit : ∫ x in Ioo (0 : ℝ) 1, g x * ((x ^ (-s) : ℝ) : ℂ)
      = (∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ))
        - ∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * ((x ^ (-s) : ℝ) : ℂ) := by
    rw [← integral_sub (integrableOn_profile_weight_mul hcm hcw)
      (integrableOn_profile_weight_mul htm htw)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
    rw [hgdef]
    ring
  rw [hsplit, sub_eq_zero] at hmom
  have hcrit : ∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)
      = criticalMomentE θ ρ (s : ℂ) := by
    rw [criticalMomentE_eq_div hθ0]
    refine integral_criticalProfile_weight hθ0 hθ1.le ?_ ?_
    · rw [hρ]; linarith
    · intro hz
      have hre : (ρ - (s : ℂ)).re = 1 / 2 - s := by
        rw [Complex.sub_re, Complex.ofReal_re, hρ]
      rw [hz] at hre
      simp only [Complex.zero_re] at hre
      linarith
  rw [hcrit] at hmom
  rw [tailMomentE_eq, tailMoment_ofReal θ s]
  exact hmom

/-! ### Continuation to the half-plane -/

theorem criticalMomentE_eq_tailMomentE {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hfm : Measurable f)
    (hfb : ∀ x, ‖f x‖ ≤ C)
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ)) :
    ∀ w ∈ leftHalfPlane, criticalMomentE θ ρ w = tailMomentE θ f w := by
  have hanalytic : AnalyticOnNhd ℂ
      (fun w => criticalMomentE θ ρ w - tailMomentE θ f w) leftHalfPlane :=
    DifferentiableOn.analyticOnNhd
      ((differentiableOn_criticalMomentE hρ).sub
        ((differentiable_tailMomentE hθ0 hθ1.le hC hfm hfb).differentiableOn))
      isOpen_leftHalfPlane
  have hz₀ : (((1 : ℝ) / 4 : ℝ) : ℂ) ∈ leftHalfPlane := by
    rw [mem_leftHalfPlane, Complex.ofReal_re]
    norm_num
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 5)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 5)) atTop atTop :=
      tendsto_atTop_add_const_right _ 5 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 5)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
    simpa [one_div] using h2
  have hfreq : ∃ᶠ w in 𝓝[≠] (((1 : ℝ) / 4 : ℝ) : ℂ),
      (fun w => criticalMomentE θ ρ w - tailMomentE θ f w) w = 0 := by
    have htend : Tendsto (fun n : ℕ => ((1 / 4 + 1 / (n + 5 : ℝ) : ℝ) : ℂ)) atTop
        (𝓝[≠] (((1 : ℝ) / 4 : ℝ) : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · refine (Complex.continuous_ofReal.tendsto _).comp ?_
        simpa using tendsto_const_nhds.add hinv
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcontra
        have hreal := Complex.ofReal_injective hcontra
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 5) := by positivity
        norm_num at hreal
        linarith
    refine htend.frequently (Frequently.of_forall fun n => ?_)
    have hs0 : (0 : ℝ) < 1 / 4 + 1 / ((n : ℝ) + 5) := by positivity
    have hn5 : (5 : ℝ) ≤ (n : ℝ) + 5 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hs : 1 / 4 + 1 / ((n : ℝ) + 5) < 1 / 2 := by
      have : 1 / ((n : ℝ) + 5) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) hn5
      linarith
    simp only [sub_eq_zero]
    exact moment_identity_real hθ0 hθ1 hρ hC hfm hfb h hs0 hs
  have heq := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_leftHalfPlane hz₀ hfreq
  intro w hw
  have hval := heq hw
  simp only [Pi.zero_apply, sub_eq_zero] at hval
  exact hval

/-! ### The separation theorem -/

/-- **Heat-transform separation.** For `0 < θ < 1`, any `ρ` on the critical line and any bounded
measurable tail profile, the critical transform and the tail transform cannot agree on the
sampling interval `[1,2]`. No zeta input is used. -/
theorem heatTransform_separation {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hfm : Measurable f)
    (hfb : ∀ x, ‖f x‖ ≤ C)
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      boseTransform (criticalProfile θ ρ) (t : ℂ) = boseTransform (tailProfile θ f) (t : ℂ)) :
    False := by
  have hCpos : 0 < C + 1 := by linarith
  set δ : ℝ := min (1 / 2) (θ / (2 * (C + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδC : δ ≤ θ / (2 * (C + 1)) := min_le_right _ _
  have hre : (ρ - (δ : ℂ)).re = 1 / 2 - δ := by
    rw [Complex.sub_re, Complex.ofReal_re, hρ]
  have hmem : ρ - (δ : ℂ) ∈ leftHalfPlane := by
    rw [mem_leftHalfPlane, hre]
    linarith
  have hid := criticalMomentE_eq_tailMomentE hθ0 hθ1 hρ hC hfm hfb h _ hmem
  have hsub : ρ - (ρ - (δ : ℂ)) = (δ : ℂ) := by ring
  have hlhs : ‖criticalMomentE θ ρ (ρ - (δ : ℂ))‖ = θ ^ δ / δ := by
    rw [norm_criticalMomentE hθ0, hsub, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ0]
  have hrhs : ‖tailMomentE θ f (ρ - (δ : ℂ))‖ ≤ C * θ ^ (-(1 / 2) : ℝ) := by
    rw [tailMomentE_eq]
    refine norm_tailMoment_le hθ0 hθ1 hC hfm hfb ?_ ?_
    · rw [hre]; linarith
    · rw [hre]; linarith
  have hbound : θ ^ δ / δ ≤ C * θ ^ (-(1 / 2) : ℝ) := by
    rw [← hlhs, hid]
    exact hrhs
  have hθδ : θ ^ ((1 : ℝ) / 2) ≤ θ ^ δ :=
    Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1.le hδ2
  have hhalf : θ ^ ((1 : ℝ) / 2) * θ ^ ((1 : ℝ) / 2) = θ := by
    rw [← Real.rpow_add hθ0]
    norm_num
  have hneg : θ ^ (-(1 / 2) : ℝ) * θ ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hθ0]
    norm_num
  have hp1 : 0 < θ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hθ0 _
  have h1 : θ ^ δ ≤ δ * (C * θ ^ (-(1 / 2) : ℝ)) := by
    rw [div_le_iff₀ hδ0] at hbound
    linarith
  have h2 : θ ≤ δ * C := by
    have hstep := mul_le_mul_of_nonneg_right (le_trans hθδ h1) hp1.le
    rw [hhalf] at hstep
    have hre2 : δ * (C * θ ^ (-(1 / 2) : ℝ)) * θ ^ ((1 : ℝ) / 2)
        = δ * C * (θ ^ (-(1 / 2) : ℝ) * θ ^ ((1 : ℝ) / 2)) := by ring
    rw [hre2, hneg, mul_one] at hstep
    exact hstep
  have h3 : δ * C < θ := by
    calc δ * C ≤ (θ / (2 * (C + 1))) * C := mul_le_mul_of_nonneg_right hδC hC
      _ = θ * (C / (2 * (C + 1))) := by ring
      _ < θ * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hθ0
          rw [div_lt_one (by positivity)]
          linarith
      _ = θ := mul_one θ
  linarith

end RHTower
