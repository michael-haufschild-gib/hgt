import GaloisForLFunctions.HTGeometry.BesselOrderDerivativeEnvelope

/-!
# The order-one Bessel derivative recurrence

The Schläfli integral for `K₁` has an exact first-order companion.  Integrating

`∂_t ( sinh t · e^{-z cosh t} ) = (cosh t − z sinh²t) e^{-z cosh t}`

over the half line, where both boundary values vanish, gives

`0 = K₁(z) + z·K₁'(z) + z·K₀(z)`,   i.e.   `K₁'(z) = −( K₀(z) + K₁(z)/z )`.

Together with `K₀'(z) = −K₁(z)` this closes the pair `(K₀, K₁)` under differentiation with rational
coefficients — a first-order system rather than the second-order Bessel equation.  That is what a
height recursion for a jet-modified mass profile consumes: the profile is `2aτ·K₁(az)/z` with
`z² = τ² + h²`, so `∂_h` moves inside the pair and every iterate stays a rational combination of
`K₀(az)` and `K₁(az)`.
-/

open Complex MeasureTheory Set Filter Topology

namespace HTGeometry

noncomputable section

/-- The modified Bessel function `K₀` of complex argument, by the Schläfli integral. -/
def besselK0C (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-z * Complex.cosh (t : ℂ))

theorem re_neg_mul_cosh (z : ℂ) (t : ℝ) :
    (-z * Complex.cosh (t : ℂ)).re = -(z.re * Real.cosh t) := by
  rw [← Complex.ofReal_cosh]
  simp [Complex.mul_re]

theorem norm_coshPow_mul_exp (z : ℂ) (t : ℝ) (k : ℕ) :
    ‖Complex.cosh (t : ℂ) ^ k * Complex.exp (-z * Complex.cosh (t : ℂ))‖
      = Real.cosh t ^ k * Real.exp (-(z.re * Real.cosh t)) := by
  rw [norm_mul, norm_pow, norm_cosh_ofReal, Complex.norm_exp, re_neg_mul_cosh]

/-- Every Schläfli integrand of order at most two is integrable on the whole line. -/
theorem integrable_coshPow_mul_exp_neg_cosh {z : ℂ} (hz : 0 < z.re) {k : ℕ} (hk : k ≤ 2) :
    Integrable fun t : ℝ =>
      Complex.cosh (t : ℂ) ^ k * Complex.exp (-z * Complex.cosh (t : ℂ)) := by
  have hmaj := integrable_cosh_sq_mul_exp_neg_mul_cosh (Y := z.re) hz
  refine Integrable.mono' hmaj ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.cosh (t : ℂ) ^ k * Complex.exp (-z * Complex.cosh (t : ℂ))).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_coshPow_mul_exp]
    have h1 : (1 : ℝ) ≤ Real.cosh t := Real.one_le_cosh t
    have hk2 : Real.cosh t ^ k ≤ Real.cosh t ^ 2 := pow_le_pow_right₀ h1 hk
    exact mul_le_mul_of_nonneg_right hk2 (Real.exp_pos _).le

/-- The Schläfli boundary term vanishes at infinity. -/
theorem tendsto_sinh_mul_exp_neg_cosh {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => Complex.sinh (t : ℂ) * Complex.exp (-z * Complex.cosh (t : ℂ)))
      atTop (𝓝 0) := by
  set X : ℝ := z.re with hX
  have hX0 : (0 : ℝ) < X := hz
  refine squeeze_zero_norm' ?_ (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  filter_upwards [eventually_ge_atTop (4 / X), eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hcoshle : Real.cosh t ≤ Real.exp t := cosh_le_exp ht0
  have hcoshlow : 1 + t ^ 2 / 2 ≤ Real.cosh t := one_add_sq_div_two_le_cosh ht0
  have hsinh : ‖Complex.sinh (t : ℂ)‖ ≤ Real.cosh t := by
    rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]
    have hsq : Real.sinh t ^ 2 ≤ Real.cosh t ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq t]
    have h1 : Real.sqrt (Real.sinh t ^ 2) ≤ Real.sqrt (Real.cosh t ^ 2) := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Real.cosh_pos t).le] at h1
  have hexp : ‖Complex.exp (-z * Complex.cosh (t : ℂ))‖ = Real.exp (-(X * Real.cosh t)) := by
    rw [Complex.norm_exp, re_neg_mul_cosh]
  have hXt : 4 / X ≤ t := ht
  have hquad : Real.cosh t * Real.exp (-(X * Real.cosh t)) ≤ Real.exp (-t) := by
    have hstep : Real.cosh t * Real.exp (-(X * Real.cosh t))
        ≤ Real.exp t * Real.exp (-(X * (1 + t ^ 2 / 2))) := by
      refine mul_le_mul hcoshle (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
        (Real.exp_pos _).le
    refine hstep.trans ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hXt4 : 4 ≤ X * t := by
      rw [div_le_iff₀ hX0] at hXt
      linarith
    nlinarith [sq_nonneg t, hX0, ht0]
  rw [norm_mul, hexp]
  calc ‖Complex.sinh (t : ℂ)‖ * Real.exp (-(X * Real.cosh t))
      ≤ Real.cosh t * Real.exp (-(X * Real.cosh t)) :=
        mul_le_mul_of_nonneg_right hsinh (Real.exp_pos _).le
    _ ≤ Real.exp (-t) := hquad

/-- The Schläfli boundary function and its derivative. -/
theorem hasDerivAt_sinh_mul_exp_neg_cosh (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.sinh (t : ℂ) * Complex.exp (-z * Complex.cosh (t : ℂ)))
      ((Complex.cosh (t : ℂ) - z * Complex.sinh (t : ℂ) ^ 2)
        * Complex.exp (-z * Complex.cosh (t : ℂ))) t := by
  have hcosh : HasDerivAt (fun t : ℝ => Complex.cosh (t : ℂ)) (Complex.sinh (t : ℂ)) t :=
    (Complex.hasDerivAt_cosh _).comp_ofReal
  have hsinh : HasDerivAt (fun t : ℝ => Complex.sinh (t : ℂ)) (Complex.cosh (t : ℂ)) t :=
    (Complex.hasDerivAt_sinh _).comp_ofReal
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-z * Complex.cosh (t : ℂ)))
      (Complex.exp (-z * Complex.cosh (t : ℂ)) * (-z * Complex.sinh (t : ℂ))) t :=
    (hcosh.const_mul (-z)).cexp
  have hval : (Complex.cosh (t : ℂ) - z * Complex.sinh (t : ℂ) ^ 2)
        * Complex.exp (-z * Complex.cosh (t : ℂ))
      = Complex.cosh (t : ℂ) * Complex.exp (-z * Complex.cosh (t : ℂ))
        + Complex.sinh (t : ℂ)
          * (Complex.exp (-z * Complex.cosh (t : ℂ)) * (-z * Complex.sinh (t : ℂ))) := by
    ring
  rw [hval]
  exact hsinh.mul hexp

/-- **The order-one derivative recurrence.**  `K₁'(z) = −(K₀(z) + K₁(z)/z)`, by one integration by
parts on the Schläfli contour. -/
theorem besselK1CDeriv_eq_neg {z : ℂ} (hz : 0 < z.re) :
    besselK1CDeriv z = -(besselK0C z + besselK1C z / z) := by
  have hz0 : z ≠ 0 := by
    intro hcon
    rw [hcon] at hz
    simp at hz
  set F : ℝ → ℂ := fun t => Complex.sinh (t : ℂ) * Complex.exp (-z * Complex.cosh (t : ℂ)) with hF
  set G : ℝ → ℂ := fun t =>
      Complex.cosh (t : ℂ) ^ 1 * Complex.exp (-z * Complex.cosh (t : ℂ))
        - (z * (Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))
          - z * (Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ)))) with hG
  have hderiv : ∀ t : ℝ, HasDerivAt F (G t) t := by
    intro t
    have h := hasDerivAt_sinh_mul_exp_neg_cosh z t
    have hsq : Complex.sinh (t : ℂ) ^ 2 = Complex.cosh (t : ℂ) ^ 2 - 1 := by
      have hid := Complex.cosh_sq_sub_sinh_sq (t : ℂ)
      linear_combination -hid
    have heq : (Complex.cosh (t : ℂ) - z * Complex.sinh (t : ℂ) ^ 2)
        * Complex.exp (-z * Complex.cosh (t : ℂ)) = G t := by
      rw [hG]
      simp only [hsq, pow_one, pow_zero, one_mul]
      ring
    rwa [heq] at h
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) :=
    (((integrable_coshPow_mul_exp_neg_cosh hz (k := 1) (by norm_num)).sub
      (((integrable_coshPow_mul_exp_neg_cosh hz (k := 2) (by norm_num)).const_mul z).sub
        ((integrable_coshPow_mul_exp_neg_cosh hz (k := 0) (by norm_num)).const_mul z)))).integrableOn
  have hzero : (∫ t in Ioi (0 : ℝ), G t) = 0 := by
    have hFT := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := F) (f' := G) (a := (0 : ℝ)) (m := (0 : ℂ))
      (fun x _ => hderiv x) hGint (tendsto_sinh_mul_exp_neg_cosh hz)
    rw [hFT, hF]
    simp
  have hint0 := (integrable_coshPow_mul_exp_neg_cosh hz (k := 0) (by norm_num)).integrableOn
    (s := Ioi (0 : ℝ))
  have hint1 := (integrable_coshPow_mul_exp_neg_cosh hz (k := 1) (by norm_num)).integrableOn
    (s := Ioi (0 : ℝ))
  have hint2 := (integrable_coshPow_mul_exp_neg_cosh hz (k := 2) (by norm_num)).integrableOn
    (s := Ioi (0 : ℝ))
  have hAint : IntegrableOn (fun t : ℝ =>
      z * (Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))) (Ioi 0) :=
    hint2.const_mul z
  have hBint : IntegrableOn (fun t : ℝ =>
      z * (Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ)))) (Ioi 0) :=
    hint0.const_mul z
  have e2 : (∫ t in Ioi (0 : ℝ),
        (z * (Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))
          - z * (Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ)))))
      = (∫ t in Ioi (0 : ℝ),
            z * (Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))))
        - ∫ t in Ioi (0 : ℝ),
            z * (Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ))) :=
    MeasureTheory.integral_sub hAint hBint
  have e1 : (∫ t in Ioi (0 : ℝ), G t)
      = (∫ t in Ioi (0 : ℝ),
            Complex.cosh (t : ℂ) ^ 1 * Complex.exp (-z * Complex.cosh (t : ℂ)))
        - ∫ t in Ioi (0 : ℝ),
            (z * (Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))
              - z * (Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ)))) :=
    MeasureTheory.integral_sub hint1 (hAint.sub hBint)
  rw [e1, e2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hzero
  have hK1 : (∫ t in Ioi (0 : ℝ),
      Complex.cosh (t : ℂ) ^ 1 * Complex.exp (-z * Complex.cosh (t : ℂ))) = besselK1C z := by
    rw [besselK1C]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show Complex.cosh (t : ℂ) ^ 1 * Complex.exp (-z * Complex.cosh (t : ℂ))
      = Complex.exp (-z * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ)
    rw [pow_one, mul_comm]
  have hK0 : (∫ t in Ioi (0 : ℝ),
      Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ))) = besselK0C z := by
    rw [besselK0C]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ))
      = Complex.exp (-z * Complex.cosh (t : ℂ))
    rw [pow_zero, one_mul]
  have hK2 : (∫ t in Ioi (0 : ℝ),
      Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))
      = -besselK1CDeriv z := by
    rw [besselK1CDeriv, ← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show Complex.cosh (t : ℂ) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ))
      = -(-(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-z * Complex.cosh (t : ℂ)))
    ring
  rw [hK1, hK0, hK2] at hzero
  field_simp
  linear_combination hzero

/-- The order-zero Schläfli integrand is integrable on the whole line. -/
theorem integrable_exp_neg_cosh {z : ℂ} (hz : 0 < z.re) :
    Integrable fun t : ℝ => Complex.exp (-z * Complex.cosh (t : ℂ)) := by
  have h := integrable_coshPow_mul_exp_neg_cosh hz (k := 0) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  show Complex.cosh (t : ℂ) ^ 0 * Complex.exp (-z * Complex.cosh (t : ℂ))
    = Complex.exp (-z * Complex.cosh (t : ℂ))
  rw [pow_zero, one_mul]

/-- **The order-zero derivative.**  `K₀'(z) = −K₁(z)`, by differentiation under the Schläfli
integral. -/
theorem hasDerivAt_besselK0C {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt besselK0C (-besselK1C w) w := by
  set X : ℝ := w.re with hX
  have hX2 : (0 : ℝ) < X / 2 := by linarith
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : ℂ → ℝ → ℂ := fun v t => Complex.exp (-v * Complex.cosh (t : ℂ)) with hF
  set F' : ℂ → ℝ → ℂ := fun v t =>
    -Complex.cosh (t : ℂ) * Complex.exp (-v * Complex.cosh (t : ℂ)) with hF'
  set bound : ℝ → ℝ := fun t => Real.cosh t ^ 2 * Real.exp (-(X / 2 * Real.cosh t)) with hbound
  have hs : Metric.ball w (X / 2) ∈ nhds w := Metric.ball_mem_nhds w hX2
  have hmeas : ∀ᶠ v : ℂ in nhds w, AEStronglyMeasurable (F v) μ := by
    filter_upwards with v
    exact ((by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-v * Complex.cosh (t : ℂ)))).aestronglyMeasurable
  have hint : Integrable (F w) μ := (integrable_exp_neg_cosh hw).integrableOn
  have hmeas' : AEStronglyMeasurable (F' w) μ :=
    ((by fun_prop : Continuous fun t : ℝ =>
      -Complex.cosh (t : ℂ) * Complex.exp (-w * Complex.cosh (t : ℂ)))).aestronglyMeasurable
  have hre : ∀ v : ℂ, v ∈ Metric.ball w (X / 2) → X / 2 < v.re := by
    intro v hv
    have hdist : ‖v - w‖ < X / 2 := by
      rw [← Complex.dist_eq]
      exact hv
    have hle : |v.re - w.re| ≤ ‖v - w‖ := by
      have := Complex.abs_re_le_norm (v - w)
      simpa [Complex.sub_re] using this
    have habs : |v.re - X| < X / 2 := by rw [hX]; linarith
    have := (abs_lt.1 habs).1
    linarith
  have hbnd : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball w (X / 2), ‖F' v t‖ ≤ bound t := by
    filter_upwards with t
    intro v hv
    have hvre := hre v hv
    rw [hF', hbound]
    simp only
    rw [norm_mul, norm_neg, norm_cosh_ofReal, Complex.norm_exp, re_neg_mul_cosh]
    have hexp : Real.exp (-(v.re * Real.cosh t)) ≤ Real.exp (-(X / 2 * Real.cosh t)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [Real.cosh_pos t]
    have hcosh : Real.cosh t ≤ Real.cosh t ^ 2 := by
      nlinarith [Real.one_le_cosh t]
    exact mul_le_mul hcosh hexp (Real.exp_pos _).le (by positivity)
  have hboundint : Integrable bound μ := by
    rw [hbound]
    exact (integrable_cosh_sq_mul_exp_neg_mul_cosh hX2).integrableOn
  have hderiv : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball w (X / 2), HasDerivAt (fun z => F z t) (F' v t) v := by
    filter_upwards with t
    intro v _
    have hbase : HasDerivAt (fun z : ℂ => -z * Complex.cosh (t : ℂ))
        (-Complex.cosh (t : ℂ)) v := by
      simpa using ((hasDerivAt_id v).neg.mul_const (Complex.cosh (t : ℂ)))
    have hexp := hbase.cexp
    rw [hF, hF']
    simp only
    have heq : Complex.exp (-v * Complex.cosh (t : ℂ)) * -Complex.cosh (t : ℂ)
        = -Complex.cosh (t : ℂ) * Complex.exp (-v * Complex.cosh (t : ℂ)) := by ring
    rw [← heq]
    exact hexp
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := w)
    (F := F) (F' := F') (bound := bound) (s := Metric.ball w (X / 2))
    hs hmeas hint hmeas' hbnd hboundint hderiv
  have hbessel : (fun v : ℂ => ∫ t, F v t ∂μ) = besselK0C := by
    funext v
    rw [besselK0C, hμ, hF]
  rw [hbessel] at hmain
  have hval : (∫ t, F' w t ∂μ) = -besselK1C w := by
    rw [hF', hμ, besselK1C, ← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show -Complex.cosh (t : ℂ) * Complex.exp (-w * Complex.cosh (t : ℂ))
      = -(Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ))
    ring
  rw [hval] at hmain
  exact hmain.2

/-- **The closed first-order system.**  On the right half plane the pair `(K₀, K₁)` differentiates
into itself with rational coefficients. -/
theorem hasDerivAt_besselK1C_pair {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt besselK1C (-(besselK0C z + besselK1C z / z)) z := by
  rw [← besselK1CDeriv_eq_neg hz]
  exact hasDerivAt_besselK1C_deriv hz

end

end HTGeometry
