import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic

/-!
# The order-one Schläfli asymptotic with an error in the modulus

The Laplace form of the order-one Schläfli integral leaves the remainder

`∫₀^∞ e^{-w v²} (P(v) − 1/√2) dv`,

whose crude bound is controlled by `Re w` alone and therefore says nothing when the argument runs
out along a ray close to the imaginary axis.  Writing the profile defect as `v` times its own
difference quotient and integrating by parts converts one power of `v` into one power of `w`: the
difference quotient is bounded, its derivative is bounded, and both boundary terms vanish.  The
remainder is then smaller than the leading term by a full power of `|w|`, so the asymptotic
survives along every ray in the open right half plane.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace HTGeometry

noncomputable section

/-! ## The profile defect and its difference quotient -/

/-- The defect of the Schläfli profile against its value at the origin. -/
def besselLaplaceDefect (v : ℝ) : ℝ := besselLaplaceProfile v - 1 / Real.sqrt 2

/-- The difference quotient of the profile defect. -/
def besselLaplaceRatio (v : ℝ) : ℝ := besselLaplaceDefect v / v

/-- The derivative of the Schläfli profile. -/
def besselLaplaceProfileDeriv (v : ℝ) : ℝ := v * (3 + v ^ 2) / Real.sqrt (2 + v ^ 2) ^ 3

/-- The derivative of the difference quotient. -/
def besselLaplaceRatioDeriv (v : ℝ) : ℝ :=
  besselLaplaceProfileDeriv v / v - besselLaplaceDefect v / v ^ 2

theorem two_add_sq_pos (v : ℝ) : (0 : ℝ) < 2 + v ^ 2 := by positivity

theorem sqrt_two_add_sq_pos (v : ℝ) : (0 : ℝ) < Real.sqrt (2 + v ^ 2) :=
  Real.sqrt_pos.2 (two_add_sq_pos v)

theorem sq_sqrt_two_add_sq (v : ℝ) : Real.sqrt (2 + v ^ 2) ^ 2 = 2 + v ^ 2 :=
  Real.sq_sqrt (two_add_sq_pos v).le

theorem besselLaplaceDefect_nonneg (v : ℝ) : 0 ≤ besselLaplaceDefect v :=
  besselLaplaceProfile_sub_nonneg v

theorem besselLaplaceDefect_le (v : ℝ) : besselLaplaceDefect v ≤ v ^ 2 / Real.sqrt 2 :=
  besselLaplaceProfile_sub_le v

theorem hasDerivAt_besselLaplaceProfile (v : ℝ) :
    HasDerivAt besselLaplaceProfile (besselLaplaceProfileDeriv v) v := by
  have hg : HasDerivAt (fun y : ℝ => Real.sqrt (2 + y ^ 2))
      (2 * v / (2 * Real.sqrt (2 + v ^ 2))) v := by
    have hbase : HasDerivAt (fun y : ℝ => 2 + y ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_pow 2 v).const_add (2 : ℝ))
    simpa using hbase.sqrt (ne_of_gt (two_add_sq_pos v))
  have hf : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * v) v := by
    simpa using ((hasDerivAt_pow 2 v).const_add (1 : ℝ))
  have hdiv := hf.div hg (ne_of_gt (sqrt_two_add_sq_pos v))
  have hval : (2 * v * Real.sqrt (2 + v ^ 2) -
        (1 + v ^ 2) * (2 * v / (2 * Real.sqrt (2 + v ^ 2)))) / Real.sqrt (2 + v ^ 2) ^ 2
      = besselLaplaceProfileDeriv v := by
    rw [besselLaplaceProfileDeriv, sq_sqrt_two_add_sq]
    have hs : Real.sqrt (2 + v ^ 2) ≠ 0 := ne_of_gt (sqrt_two_add_sq_pos v)
    have hcube : Real.sqrt (2 + v ^ 2) ^ 3
        = Real.sqrt (2 + v ^ 2) * (2 + v ^ 2) := by
      rw [pow_succ' (Real.sqrt (2 + v ^ 2)) 2, sq_sqrt_two_add_sq]
    rw [hcube]
    field_simp
    simp only [sq_sqrt_two_add_sq]
    ring
  rw [← hval]
  exact hdiv

theorem hasDerivAt_besselLaplaceDefect (v : ℝ) :
    HasDerivAt besselLaplaceDefect (besselLaplaceProfileDeriv v) v :=
  (hasDerivAt_besselLaplaceProfile v).sub_const (1 / Real.sqrt 2)

theorem hasDerivAt_besselLaplaceRatio {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt besselLaplaceRatio (besselLaplaceRatioDeriv v) v := by
  have hdiv := (hasDerivAt_besselLaplaceDefect v).div (hasDerivAt_id v) hv
  have hval : (besselLaplaceProfileDeriv v * v - besselLaplaceDefect v * 1) / v ^ 2
      = besselLaplaceRatioDeriv v := by
    rw [besselLaplaceRatioDeriv]
    field_simp
  rw [← hval]
  exact hdiv

/-! ## Bounds -/

theorem besselLaplaceProfileDeriv_div_nonneg {v : ℝ} (hv : 0 < v) :
    0 ≤ besselLaplaceProfileDeriv v / v := by
  rw [besselLaplaceProfileDeriv]
  have h1 : (0 : ℝ) < Real.sqrt (2 + v ^ 2) ^ 3 := by positivity
  positivity

theorem besselLaplaceProfileDeriv_div_le {v : ℝ} (hv : 0 < v) :
    besselLaplaceProfileDeriv v / v ≤ 3 / (2 * Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt (2 + v ^ 2) := sqrt_two_add_sq_pos v
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hge : Real.sqrt 2 ≤ Real.sqrt (2 + v ^ 2) := sqrt_two_le_sqrt_two_add_sq v
  have hcube : Real.sqrt (2 + v ^ 2) ^ 3 = Real.sqrt (2 + v ^ 2) * (2 + v ^ 2) := by
    rw [pow_succ' (Real.sqrt (2 + v ^ 2)) 2, sq_sqrt_two_add_sq]
  have hquot : besselLaplaceProfileDeriv v / v
      = (3 + v ^ 2) / Real.sqrt (2 + v ^ 2) ^ 3 := by
    rw [besselLaplaceProfileDeriv]
    field_simp
  rw [hquot, hcube]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : (3 + v ^ 2) * (2 * Real.sqrt 2) ≤ 3 * (Real.sqrt 2 * (2 + v ^ 2)) := by
    nlinarith [sq_nonneg v, h2.le, hge]
  nlinarith [hkey, h2.le, hge, sq_nonneg v]

theorem besselLaplaceDefect_div_sq_le {v : ℝ} (hv : 0 < v) :
    besselLaplaceDefect v / v ^ 2 ≤ 1 / Real.sqrt 2 := by
  have hpos : (0 : ℝ) < v ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos (Real.sqrt_pos.2 (by norm_num))]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h' : besselLaplaceDefect v * Real.sqrt 2 ≤ v ^ 2 :=
    (le_div_iff₀ h2).mp (besselLaplaceDefect_le v)
  linarith

theorem besselLaplaceDefect_div_sq_nonneg {v : ℝ} (hv : 0 < v) :
    0 ≤ besselLaplaceDefect v / v ^ 2 :=
  div_nonneg (besselLaplaceDefect_nonneg v) (by positivity)

/-- The derivative of the difference quotient is bounded by two. -/
theorem abs_besselLaplaceRatioDeriv_le {v : ℝ} (hv : 0 < v) :
    |besselLaplaceRatioDeriv v| ≤ 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hone : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [h2, h2sq]
  have h1 := besselLaplaceProfileDeriv_div_nonneg hv
  have h2' := besselLaplaceProfileDeriv_div_le hv
  have h3 := besselLaplaceDefect_div_sq_nonneg hv
  have h4 := besselLaplaceDefect_div_sq_le hv
  have hb1 : 1 / Real.sqrt 2 ≤ 2 := by
    rw [div_le_iff₀ h2]
    nlinarith [hone, h2]
  have hb2 : 3 / (2 * Real.sqrt 2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hone, h2]
  rw [abs_le, besselLaplaceRatioDeriv]
  constructor
  · linarith
  · linarith

/-- The difference quotient is bounded by two. -/
theorem abs_besselLaplaceRatio_le {v : ℝ} (hv : 0 < v) : |besselLaplaceRatio v| ≤ 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hone : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [h2, h2sq]
  have hnn : 0 ≤ besselLaplaceRatio v :=
    div_nonneg (besselLaplaceDefect_nonneg v) hv.le
  rw [abs_of_nonneg hnn, besselLaplaceRatio, div_le_iff₀ hv]
  rcases le_or_gt v 1 with hle | hlt
  · have h := besselLaplaceDefect_le v
    have : v ^ 2 / Real.sqrt 2 ≤ 2 * v := by
      rw [div_le_iff₀ h2]
      nlinarith [hv.le, hle, hone]
    linarith
  · have hs : Real.sqrt (2 + v ^ 2) ≠ 0 := ne_of_gt (sqrt_two_add_sq_pos v)
    have hsge : v ≤ Real.sqrt (2 + v ^ 2) := by
      have : v ^ 2 ≤ 2 + v ^ 2 := by linarith
      nlinarith [sq_sqrt_two_add_sq v, sqrt_two_add_sq_pos v, hv.le]
    have hprof : besselLaplaceProfile v ≤ (1 + v ^ 2) / v := by
      rw [besselLaplaceProfile]
      exact div_le_div_of_nonneg_left (by positivity) hv hsge
    have hdef : besselLaplaceDefect v ≤ (1 + v ^ 2) / v := by
      have := besselLaplaceDefect
      rw [besselLaplaceDefect]
      have : (0:ℝ) ≤ 1 / Real.sqrt 2 := by positivity
      linarith [hprof]
    have hfin : (1 + v ^ 2) / v ≤ 2 * v := by
      rw [div_le_iff₀ hv]
      nlinarith [hlt]
    linarith

/-- Near the origin the difference quotient is linear. -/
theorem abs_besselLaplaceRatio_le_linear {v : ℝ} (hv : 0 < v) :
    |besselLaplaceRatio v| ≤ v / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnn : 0 ≤ besselLaplaceRatio v :=
    div_nonneg (besselLaplaceDefect_nonneg v) hv.le
  rw [abs_of_nonneg hnn, besselLaplaceRatio, div_le_iff₀ hv]
  have h := besselLaplaceDefect_le v
  have hval : v ^ 2 / Real.sqrt 2 = v / Real.sqrt 2 * v := by
    field_simp
  linarith [h, hval]

theorem besselLaplaceDefect_eq_mul (v : ℝ) (hv : v ≠ 0) :
    besselLaplaceRatio v * v = besselLaplaceDefect v := by
  rw [besselLaplaceRatio, div_mul_cancel₀ _ hv]

/-! ## Continuity and integrability -/

theorem continuous_besselLaplaceDefect : Continuous besselLaplaceDefect :=
  continuous_besselLaplaceProfile.sub continuous_const

theorem continuous_besselLaplaceProfileDeriv : Continuous besselLaplaceProfileDeriv := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun v => ?_
  exact ne_of_gt (by positivity : (0:ℝ) < Real.sqrt (2 + v ^ 2) ^ 3)

theorem continuousOn_besselLaplaceRatioDeriv :
    ContinuousOn besselLaplaceRatioDeriv (Ioi 0) := by
  refine ContinuousOn.sub ?_ ?_
  · exact continuous_besselLaplaceProfileDeriv.continuousOn.div continuousOn_id
      fun x hx => ne_of_gt hx
  · exact continuous_besselLaplaceDefect.continuousOn.div
      (continuous_pow 2).continuousOn fun x hx => by
        have hx' : (0:ℝ) < x := hx
        exact ne_of_gt (by positivity)

theorem continuousOn_besselLaplaceRatio : ContinuousOn besselLaplaceRatio (Ioi 0) :=
  continuous_besselLaplaceDefect.continuousOn.div continuousOn_id fun _x hx => ne_of_gt hx

theorem norm_cexp_neg_mul_sq (w : ℂ) (v : ℝ) :
    ‖Complex.exp (-w * (v : ℂ) ^ 2)‖ = Real.exp (-(w.re * v ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-! ## The antiderivative of the Gaussian weight -/

/-- The antiderivative of `v ↦ v e^{-w v²}`. -/
def besselGaussAnti (w : ℂ) (v : ℝ) : ℂ := -(1 / (2 * w)) * Complex.exp (-w * (v : ℂ) ^ 2)

theorem hasDerivAt_cexp_neg_mul_sq (w : ℂ) (v : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-w * (x : ℂ) ^ 2))
      (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ)))) v := by
  have hz : HasDerivAt (fun z : ℂ => Complex.exp (-w * z ^ 2))
      (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ)))) (v : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => -w * z ^ 2) (-w * (2 * (v : ℂ))) (v : ℂ) := by
      simpa using (hasDerivAt_pow 2 (v : ℂ)).const_mul (-w)
    exact h1.cexp
  exact hz.comp_ofReal

theorem hasDerivAt_besselGaussAnti {w : ℂ} (hw : w ≠ 0) (v : ℝ) :
    HasDerivAt (besselGaussAnti w) ((v : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2)) v := by
  have h := (hasDerivAt_cexp_neg_mul_sq w v).const_mul (-(1 / (2 * w)))
  have hval : -(1 / (2 * w)) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ))))
      = (v : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2) := by
    field_simp
  rw [← hval]
  exact h

theorem norm_besselGaussAnti (w : ℂ) (v : ℝ) :
    ‖besselGaussAnti w v‖ = Real.exp (-(w.re * v ^ 2)) / (2 * ‖w‖) := by
  rw [besselGaussAnti, norm_mul, norm_neg, norm_div, norm_mul, norm_cexp_neg_mul_sq]
  simp
  ring

/-! ## The integration by parts -/

theorem ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  intro h
  rw [h] at hw
  simp at hw

theorem integrableOn_defect_gauss {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceDefect v : ℂ))
      (Ioi 0) := by
  refine Integrable.mono' (((integrable_sq_mul_exp_neg_mul_sq hw).const_mul
    ((Real.sqrt 2)⁻¹)).integrableOn) ?_ ?_
  · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2)).mul
      (Complex.continuous_ofReal.comp continuous_besselLaplaceDefect)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    rw [norm_mul, norm_cexp_neg_mul_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (besselLaplaceDefect_nonneg v)]
    have hbound := besselLaplaceDefect_le v
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hexp : (0 : ℝ) < Real.exp (-(w.re * v ^ 2)) := Real.exp_pos _
    have heq : Real.exp (-(w.re * v ^ 2)) = Real.exp (-w.re * v ^ 2) := by ring_nf
    calc Real.exp (-(w.re * v ^ 2)) * besselLaplaceDefect v
        ≤ Real.exp (-(w.re * v ^ 2)) * (v ^ 2 / Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hbound hexp.le
      _ = (Real.sqrt 2)⁻¹ * (v ^ 2 * Real.exp (-w.re * v ^ 2)) := by
          rw [heq, div_eq_mul_inv]
          ring

theorem integrableOn_ratioDeriv_gauss {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceRatioDeriv v : ℂ))
      (Ioi 0) := by
  refine Integrable.mono' (((integrable_exp_neg_mul_sq hw).const_mul (2 : ℝ)).integrableOn) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((by fun_prop : Continuous fun v : ℝ =>
      Complex.exp (-w * (v : ℂ) ^ 2)).continuousOn).mul
      (Complex.continuous_ofReal.continuousOn.comp continuousOn_besselLaplaceRatioDeriv
        (fun x hx => Set.mem_univ _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, norm_cexp_neg_mul_sq, Complex.norm_real, Real.norm_eq_abs]
    have hbound := abs_besselLaplaceRatioDeriv_le hv
    have hexp : (0 : ℝ) < Real.exp (-(w.re * v ^ 2)) := Real.exp_pos _
    have heq : Real.exp (-(w.re * v ^ 2)) = Real.exp (-w.re * v ^ 2) := by ring_nf
    calc Real.exp (-(w.re * v ^ 2)) * |besselLaplaceRatioDeriv v|
        ≤ Real.exp (-(w.re * v ^ 2)) * 2 := mul_le_mul_of_nonneg_left hbound hexp.le
      _ = 2 * Real.exp (-w.re * v ^ 2) := by rw [heq]; ring

/-- The integration-by-parts identity on a compact subinterval of the open half line. -/
theorem integral_defect_gauss_interval {w : ℂ} (hw : 0 < w.re) {ε T : ℝ} (hε : 0 < ε)
    (hεT : ε ≤ T) :
    (∫ v in ε..T, Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceDefect v : ℂ))
      = (besselLaplaceRatio T : ℂ) * besselGaussAnti w T
        - (besselLaplaceRatio ε : ℂ) * besselGaussAnti w ε
        + (1 / (2 * w)) *
          ∫ v in ε..T, Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceRatioDeriv v : ℂ) := by
  have hwne : w ≠ 0 := ne_zero_of_re_pos hw
  have hsub : Set.uIcc ε T ⊆ Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hεT]
    intro x hx
    exact lt_of_lt_of_le hε hx.1
  have hu : ∀ x ∈ Set.uIcc ε T,
      HasDerivAt (fun y : ℝ => (besselLaplaceRatio y : ℂ))
        ((besselLaplaceRatioDeriv x : ℂ)) x := fun x hx =>
    (hasDerivAt_besselLaplaceRatio (ne_of_gt (hsub hx))).ofReal_comp
  have hv : ∀ x ∈ Set.uIcc ε T,
      HasDerivAt (besselGaussAnti w) ((x : ℂ) * Complex.exp (-w * (x : ℂ) ^ 2)) x :=
    fun x _ => hasDerivAt_besselGaussAnti hwne x
  have hu' : IntervalIntegrable (fun x : ℝ => (besselLaplaceRatioDeriv x : ℂ)) volume ε T := by
    refine ContinuousOn.intervalIntegrable ?_
    exact Complex.continuous_ofReal.continuousOn.comp
      (continuousOn_besselLaplaceRatioDeriv.mono hsub) (fun x hx => Set.mem_univ _)
  have hv' : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) * Complex.exp (-w * (x : ℂ) ^ 2)) volume ε T :=
    (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) * Complex.exp (-w * (x : ℂ) ^ 2)).intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft : (∫ x in ε..T, (besselLaplaceRatio x : ℂ) *
      ((x : ℂ) * Complex.exp (-w * (x : ℂ) ^ 2)))
      = ∫ v in ε..T, Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceDefect v : ℂ) := by
    rw [intervalIntegral.integral_of_le hεT, intervalIntegral.integral_of_le hεT]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hε hx.1)
    rw [← besselLaplaceDefect_eq_mul x hx0]
    push_cast
    ring
  have hright : (∫ x in ε..T, (besselLaplaceRatioDeriv x : ℂ) * besselGaussAnti w x)
      = -(1 / (2 * w)) *
        ∫ v in ε..T, Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceRatioDeriv v : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [besselGaussAnti]
    ring
  rw [hleft, hright] at hIBP
  rw [hIBP]
  ring

/-! ## Passing to the half line -/

theorem iUnion_Ioc_eq_Ioi :
    (⋃ n : ℕ, Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) = Ioi (0 : ℝ) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn, _⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have h1 : 1 / x < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
      have h2 : 1 / x < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hx] at h2
      linarith
    · have h1 : x < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
      linarith

theorem tendsto_setIntegral_Ioc_atTop {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Tendsto (fun n : ℕ => ∫ v in Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1), f v) atTop
      (𝓝 (∫ v in Ioi (0 : ℝ), f v)) := by
  have hmono : Monotone fun n : ℕ => Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    refine Set.Ioc_subset_Ioc ?_ (by linarith)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmeas : ∀ n : ℕ, MeasurableSet (Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n => measurableSet_Ioc
  have := MeasureTheory.tendsto_setIntegral_of_monotone hmeas hmono
    (by rw [iUnion_Ioc_eq_Ioi]; exact hf)
  rw [iUnion_Ioc_eq_Ioi] at this
  exact this

theorem exp_neg_le_one_div {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) hy]
  nlinarith [Real.add_one_le_exp y]

/-- **The integration-by-parts identity on the half line.** -/
theorem integral_defect_gauss_eq {w : ℂ} (hw : 0 < w.re) :
    (∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceDefect v : ℂ))
      = (1 / (2 * w)) *
        ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2)
          * (besselLaplaceRatioDeriv v : ℂ) := by
  have hwne : w ≠ 0 := ne_zero_of_re_pos hw
  have hwnorm : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwne
  set L : ℕ → ℂ := fun n =>
    ∫ v in Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
      Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceDefect v : ℂ) with hL
  set R : ℕ → ℂ := fun n =>
    ∫ v in Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1),
      Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceRatioDeriv v : ℂ) with hR
  have hstep : ∀ n : ℕ, L n =
      (besselLaplaceRatio ((n : ℝ) + 1) : ℂ) * besselGaussAnti w ((n : ℝ) + 1)
        - (besselLaplaceRatio (1 / ((n : ℝ) + 1)) : ℂ) * besselGaussAnti w (1 / ((n : ℝ) + 1))
        + (1 / (2 * w)) * R n := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hεT : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h := integral_defect_gauss_interval hw hε hεT
    rw [intervalIntegral.integral_of_le hεT, intervalIntegral.integral_of_le hεT] at h
    exact h
  have hbig : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hTop : Tendsto
      (fun n : ℕ => (besselLaplaceRatio ((n : ℝ) + 1) : ℂ) * besselGaussAnti w ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => 1 / (w.re * ‖w‖) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hbig.const_mul (1 / (w.re * ‖w‖))
    refine squeeze_zero_norm (fun n => ?_) hg
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_besselGaussAnti]
    have h1 : |besselLaplaceRatio ((n : ℝ) + 1)| ≤ 2 := abs_besselLaplaceRatio_le hn
    have h2 : Real.exp (-(w.re * ((n : ℝ) + 1) ^ 2)) ≤ 1 / (w.re * ((n : ℝ) + 1) ^ 2) :=
      exp_neg_le_one_div (by positivity)
    have hge1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hge1]
    have h3 : (1 : ℝ) / (w.re * ((n : ℝ) + 1) ^ 2) ≤ 1 / (w.re * ((n : ℝ) + 1)) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_left hsq hw.le
    calc |besselLaplaceRatio ((n : ℝ) + 1)| *
          (Real.exp (-(w.re * ((n : ℝ) + 1) ^ 2)) / (2 * ‖w‖))
        ≤ 2 * ((1 / (w.re * ((n : ℝ) + 1))) / (2 * ‖w‖)) := by
          gcongr
          exact le_trans h2 h3
      _ = 1 / (w.re * ‖w‖) * (1 / ((n : ℝ) + 1)) := by
          field_simp
  have hBot : Tendsto
      (fun n : ℕ => (besselLaplaceRatio (1 / ((n : ℝ) + 1)) : ℂ) *
        besselGaussAnti w (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => 1 / (Real.sqrt 2 * (2 * ‖w‖)) * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa using hbig.const_mul (1 / (Real.sqrt 2 * (2 * ‖w‖)))
    refine squeeze_zero_norm (fun n => ?_) hg
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_besselGaussAnti]
    have h1 : |besselLaplaceRatio (1 / ((n : ℝ) + 1))| ≤ (1 / ((n : ℝ) + 1)) / Real.sqrt 2 :=
      abs_besselLaplaceRatio_le_linear hn
    have hexple : Real.exp (-(w.re * (1 / ((n : ℝ) + 1)) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnn : (0 : ℝ) ≤ w.re * (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
      linarith
    calc |besselLaplaceRatio (1 / ((n : ℝ) + 1))| *
          (Real.exp (-(w.re * (1 / ((n : ℝ) + 1)) ^ 2)) / (2 * ‖w‖))
        ≤ ((1 / ((n : ℝ) + 1)) / Real.sqrt 2) * (1 / (2 * ‖w‖)) := by
          gcongr
      _ = 1 / (Real.sqrt 2 * (2 * ‖w‖)) * (1 / ((n : ℝ) + 1)) := by
          field_simp
  have hLlim := tendsto_setIntegral_Ioc_atTop (integrableOn_defect_gauss hw)
  have hRlim := tendsto_setIntegral_Ioc_atTop (integrableOn_ratioDeriv_gauss hw)
  have hcomb : Tendsto L atTop
      (𝓝 (0 - 0 + (1 / (2 * w)) *
        ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2)
          * (besselLaplaceRatioDeriv v : ℂ))) := by
    refine Tendsto.congr (fun n => (hstep n).symm) ?_
    exact (hTop.sub hBot).add (hRlim.const_mul _)
  rw [zero_sub, neg_zero, zero_add] at hcomb
  exact tendsto_nhds_unique hLlim hcomb

/-! ## The asymptotic with an error in the modulus -/

/-- **The order-one Schläfli asymptotic with a modulus error.**  On the open right half plane the
remainder is smaller than the leading term by a full power of `|w|`, uniformly along every ray. -/
theorem norm_besselK1C_sub_leading_le_norm {w : ℂ} (hw : 0 < w.re) :
    ‖besselK1C w
        - Complex.exp (-w) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ)‖
      ≤ Real.exp (-w.re) * Real.sqrt (Real.pi / w.re) / ‖w‖ := by
  have hwne : w ≠ 0 := ne_zero_of_re_pos hw
  have hwnorm : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwne
  have hsplit := besselK1C_sub_leading hw
  have hid : ∀ v : ℝ, ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)
      = (besselLaplaceDefect v : ℂ) := fun v => rfl
  simp only [hid] at hsplit
  rw [hsplit, integral_defect_gauss_eq hw]
  have hbound : ‖∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2)
      * (besselLaplaceRatioDeriv v : ℂ)‖ ≤ Real.sqrt (Real.pi / w.re) := by
    have hnorm := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2) * (besselLaplaceRatioDeriv v : ℂ))
    refine le_trans hnorm ?_
    have hmono : (∫ v in Ioi (0 : ℝ), ‖Complex.exp (-w * (v : ℂ) ^ 2)
        * (besselLaplaceRatioDeriv v : ℂ)‖)
        ≤ ∫ v in Ioi (0 : ℝ), 2 * Real.exp (-w.re * v ^ 2) := by
      refine setIntegral_mono_on ((integrableOn_ratioDeriv_gauss hw).norm)
        ((integrable_exp_neg_mul_sq hw).const_mul (2 : ℝ)).integrableOn measurableSet_Ioi ?_
      intro v hv
      rw [norm_mul, norm_cexp_neg_mul_sq, Complex.norm_real, Real.norm_eq_abs]
      have hbd := abs_besselLaplaceRatioDeriv_le hv
      have hexp : (0 : ℝ) < Real.exp (-(w.re * v ^ 2)) := Real.exp_pos _
      have heq : Real.exp (-(w.re * v ^ 2)) = Real.exp (-w.re * v ^ 2) := by ring_nf
      calc Real.exp (-(w.re * v ^ 2)) * |besselLaplaceRatioDeriv v|
          ≤ Real.exp (-(w.re * v ^ 2)) * 2 := mul_le_mul_of_nonneg_left hbd hexp.le
        _ = 2 * Real.exp (-w.re * v ^ 2) := by rw [heq]; ring
    refine le_trans hmono (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, integral_gaussian_Ioi]
    ring
  have hre : (-w).re = -w.re := by simp
  set X : ℂ := ∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2)
    * (besselLaplaceRatioDeriv v : ℂ) with hX
  have hassoc : (2 : ℂ) * Complex.exp (-w) * ((1 / (2 * w)) * X)
      = ((2 : ℂ) * Complex.exp (-w) * (1 / (2 * w))) * X := by ring
  rw [hassoc, norm_mul]
  have hfac : ‖(2 : ℂ) * Complex.exp (-w) * (1 / (2 * w))‖ = Real.exp (-w.re) / ‖w‖ := by
    rw [norm_mul, norm_mul, Complex.norm_exp, hre, norm_div, norm_one, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    field_simp
  rw [hfac]
  calc Real.exp (-w.re) / ‖w‖ * ‖X‖
      ≤ Real.exp (-w.re) / ‖w‖ * Real.sqrt (Real.pi / w.re) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = Real.exp (-w.re) * Real.sqrt (Real.pi / w.re) / ‖w‖ := by ring

end

end HTGeometry
