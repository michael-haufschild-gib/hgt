import GaloisForLFunctions.HTGeometry.FresnelImproperLimit
import GaloisForLFunctions.HTGeometry.ComplexScaledGammaIntegral

/-!
# The damped oscillatory tail is uniformly small

Damping the Fresnel kernel by `e^{-εu}` cannot spoil the tail bound: for every scale `c` with
`Re c ≥ 0` and `‖c‖ ≥ 1`, one integration by parts gives

`‖∫_a^b u^{-1/2} e^{-cu} du‖ ≤ 2 a^{-1/2}`,

uniformly in `c`.  With `c = ε - i` this is exactly the uniformity needed to exchange the limits
`ε ↓ 0` and `R → ∞` in the evaluation of the half-log scattering constant.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The damped oscillatory half-power kernel. -/
def dampedKernel (c : ℂ) (u : ℝ) : ℂ := ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(c * u))

/-- The primitive used in the damped integration by parts. -/
def dampedPrimitive (c : ℂ) (u : ℝ) : ℂ := Complex.exp (-(c * u)) / (-c)

theorem norm_dampedPrimitive_le {c : ℂ} (hc : 1 ≤ ‖c‖) (hre : 0 ≤ c.re) (u : ℝ) (hu : 0 ≤ u) :
    ‖dampedPrimitive c u‖ ≤ 1 := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp only [norm_zero] at hc
    linarith
  rw [dampedPrimitive, norm_div, norm_neg, Complex.norm_exp]
  have hre' : (-(c * (u : ℂ))).re = -(c.re * u) := by
    simp [Complex.mul_re]
  rw [hre']
  have hexp : Real.exp (-(c.re * u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [hre, hu]
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le one_pos hc
  rw [div_le_one hcpos]
  linarith [hexp, hc]

theorem hasDerivAt_dampedPrimitive {c : ℂ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (dampedPrimitive c) (Complex.exp (-(c * u))) u := by
  have h10 : HasDerivAt (fun x : ℝ => -(c * (x : ℂ))) (-(c * 1)) u :=
    ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul c).neg
  rw [mul_one] at h10
  have h1 : HasDerivAt (fun x : ℝ => -(c * (x : ℂ))) (-c) u := h10
  have hbase : HasDerivAt (fun x : ℝ => Complex.exp (-(c * (x : ℂ))))
      (Complex.exp (-(c * u)) * -c) u := h1.cexp
  have hdiv := hbase.div_const (-c)
  have hval : Complex.exp (-(c * u)) * -c / (-c) = Complex.exp (-(c * u)) := by
    field_simp
  have hfun : dampedPrimitive c = fun x : ℝ => Complex.exp (-(c * (x : ℂ))) / (-c) := rfl
  rw [hfun, ← hval]
  exact hdiv

/-- **The damped tail bound, uniform in the scale.** -/
theorem norm_integral_dampedKernel_le {c : ℂ} (hc : 1 ≤ ‖c‖) (hre : 0 ≤ c.re)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ u in a..b, dampedKernel c u‖ ≤ 2 * a ^ (-(1:ℝ)/2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp only [norm_zero] at hc
    linarith
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [huIcc]
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv_u : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ))
        (((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) x :=
    fun x hx => hasDerivAt_ofReal_rpow (hsub hx)
  have hderiv_v : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (dampedPrimitive c) (Complex.exp (-(c * x))) x :=
    fun x _ => hasDerivAt_dampedPrimitive hcne x
  have hcont_u' : ContinuousOn
      (fun x : ℝ => ((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) (Set.uIcc a b) := by
    intro x hx
    have hx0 : 0 < x := hsub hx
    have h1 : ContinuousAt (fun y : ℝ => y ^ (-(1:ℝ)/2 - 1)) x :=
      Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0))
    exact ((Complex.continuous_ofReal.continuousAt).comp
      (continuousAt_const.mul h1)).continuousWithinAt
  have hint_u : IntervalIntegrable
      (fun x : ℝ => ((-(1:ℝ)/2 * x ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) volume a b :=
    hcont_u'.intervalIntegrable
  have hint_v : IntervalIntegrable (fun x : ℝ => Complex.exp (-(c * x))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hparts := integral_mul_deriv_eq_deriv_mul hderiv_u hderiv_v hint_u hint_v
  have hfun : (fun u : ℝ => dampedKernel c u)
      = fun u : ℝ => ((u ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(c * u)) := rfl
  rw [hfun, hparts]
  -- the three pieces
  have hzero : (0:ℝ) ∉ Set.uIcc a b := by
    rw [huIcc]
    intro hcon
    exact absurd hcon.1 (not_le.mpr ha)
  have hnormEq : ∀ u ∈ Set.uIcc a b,
      ‖((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * dampedPrimitive c u‖
        ≤ (1:ℝ)/2 * u ^ (-(3:ℝ)/2) := by
    intro u hu
    have hu0 : 0 < u := hsub hu
    have hprim := norm_dampedPrimitive_le hc hre u hu0.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hexp : -(1:ℝ)/2 - 1 = -(3:ℝ)/2 := by ring
    rw [hexp]
    have habs : |(-(1:ℝ)/2 * u ^ (-(3:ℝ)/2))| = (1:ℝ)/2 * u ^ (-(3:ℝ)/2) := by
      rw [abs_of_nonpos (by
        have : (0:ℝ) < u ^ (-(3:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
        nlinarith)]
      ring
    rw [habs]
    nlinarith [hprim, Real.rpow_pos_of_pos hu0 (-(3:ℝ)/2)]
  have hintNorm : IntervalIntegrable (fun u : ℝ => (1:ℝ)/2 * u ^ (-(3:ℝ)/2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : 0 < x := hsub hx
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0)))).continuousWithinAt
  have hvalue : (∫ u in a..b, (1:ℝ)/2 * u ^ (-(3:ℝ)/2))
      = a ^ (-(1:ℝ)/2) - b ^ (-(1:ℝ)/2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hexp : -(3:ℝ)/2 + 1 = -(1:ℝ)/2 := by ring
    rw [hexp]
    field_simp
    ring
  have hrem : ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * dampedPrimitive c u‖
      ≤ a ^ (-(1:ℝ)/2) - b ^ (-(1:ℝ)/2) := by
    have hstep : ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * dampedPrimitive c u‖
        ≤ ∫ u in a..b, (1:ℝ)/2 * u ^ (-(3:ℝ)/2) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hintNorm
      filter_upwards with u hu
      have humem : u ∈ Set.uIcc a b := by
        rw [huIcc]
        exact ⟨le_of_lt hu.1, hu.2⟩
      exact hnormEq u humem
    rw [hvalue] at hstep
    exact hstep
  have hbb : ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c b‖ ≤ b ^ (-(1:ℝ)/2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hb _)]
    nlinarith [norm_dampedPrimitive_le hc hre b hb.le, Real.rpow_pos_of_pos hb (-(1:ℝ)/2),
      norm_nonneg (dampedPrimitive c b)]
  have haa : ‖((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c a‖ ≤ a ^ (-(1:ℝ)/2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ha _)]
    nlinarith [norm_dampedPrimitive_le hc hre a ha.le, Real.rpow_pos_of_pos ha (-(1:ℝ)/2),
      norm_nonneg (dampedPrimitive c a)]
  have hbpos : (0:ℝ) < b ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hb _
  calc ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c b
        - ((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c a
        - ∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * dampedPrimitive c u‖
      ≤ ‖((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c b
          - ((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c a‖
        + ‖∫ u in a..b, ((-(1:ℝ)/2 * u ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) * dampedPrimitive c u‖ :=
        norm_sub_le _ _
    _ ≤ 2 * a ^ (-(1:ℝ)/2) := by
        have htri := norm_sub_le (((b ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c b)
          (((a ^ (-(1:ℝ)/2) : ℝ) : ℂ) * dampedPrimitive c a)
        linarith [htri, hbb, haa, hrem, hbpos]

/-! ## The Lebesgue tail -/

theorem dampedKernel_eq_cpow {c : ℂ} {t : ℝ} (ht : 0 < t) :
    dampedKernel c t = (t : ℂ) ^ ((1/2 : ℂ) - 1) * Complex.exp (-(c * t)) := by
  rw [dampedKernel]
  congr 1
  have hexp : ((1/2 : ℂ) - 1) = ((-(1:ℝ)/2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, ← Complex.ofReal_cpow ht.le]

theorem integrableOn_dampedKernel {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (dampedKernel c) (Set.Ioi 0) volume := by
  have hbase := integrableOn_cpow_mul_cexp (a := (1/2 : ℂ)) (c := c) (by norm_num) hc
  refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (dampedKernel_eq_cpow (c := c) ht).symm

/-- **The Lebesgue tail bound, uniform in the scale.** -/
theorem norm_integral_Ioi_dampedKernel_le {c : ℂ} (hc : 1 ≤ ‖c‖) (hre : 0 < c.re)
    {R : ℝ} (hR : 0 < R) :
    ‖∫ u in Set.Ioi R, dampedKernel c u‖ ≤ 2 * R ^ (-(1:ℝ)/2) := by
  have hint : IntegrableOn (dampedKernel c) (Set.Ioi R) volume :=
    (integrableOn_dampedKernel hre).mono_set (Set.Ioi_subset_Ioi hR.le)
  have hlim : Filter.Tendsto (fun b : ℝ => ∫ u in R..b, dampedKernel c u) Filter.atTop
      (𝓝 (∫ u in Set.Ioi R, dampedKernel c u)) :=
    intervalIntegral_tendsto_integral_Ioi R hint Filter.tendsto_id
  have hnorm : Filter.Tendsto (fun b : ℝ => ‖∫ u in R..b, dampedKernel c u‖) Filter.atTop
      (𝓝 ‖∫ u in Set.Ioi R, dampedKernel c u‖) := hlim.norm
  refine le_of_tendsto hnorm ?_
  filter_upwards [Filter.eventually_ge_atTop R] with b hb
  exact norm_integral_dampedKernel_le hc hre.le hR hb

end

end GaloisForLFunctions.HTGeometry
