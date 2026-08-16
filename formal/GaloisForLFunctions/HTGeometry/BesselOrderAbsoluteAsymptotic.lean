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
        have : (0:ℝ) < x := hx
        positivity

theorem continuousOn_besselLaplaceRatio : ContinuousOn besselLaplaceRatio (Ioi 0) :=
  continuous_besselLaplaceDefect.continuousOn.div continuousOn_id fun x hx => ne_of_gt hx

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
  have hbase : HasDerivAt (fun x : ℝ => -w * (x : ℂ) ^ 2) (-w * (2 * (v : ℂ))) v := by
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 v := by
      simpa using (hasDerivAt_id v).ofReal_comp
    have hsq : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (v : ℂ)) v := by
      simpa using hid.pow 2
    simpa using hsq.const_mul (-w)
  exact hbase.cexp

theorem hasDerivAt_besselGaussAnti {w : ℂ} (hw : w ≠ 0) (v : ℝ) :
    HasDerivAt (besselGaussAnti w) ((v : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2)) v := by
  have h := (hasDerivAt_cexp_neg_mul_sq w v).const_mul (-(1 / (2 * w)))
  have hval : -(1 / (2 * w)) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ))))
      = (v : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2) := by
    field_simp
    ring
  rw [← hval]
  exact h

theorem norm_besselGaussAnti {w : ℂ} (hw : w ≠ 0) (v : ℝ) :
    ‖besselGaussAnti w v‖ = Real.exp (-(w.re * v ^ 2)) / (2 * ‖w‖) := by
  rw [besselGaussAnti, norm_mul, norm_neg, norm_div, norm_mul, norm_cexp_neg_mul_sq]
  simp [Complex.norm_ofNat]
  ring

end

end HTGeometry
