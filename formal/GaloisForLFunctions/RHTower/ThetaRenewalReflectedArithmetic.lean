import GaloisForLFunctions.RHTower.ThetaRenewalCausalArithmetic

/-!
# Full arithmetic forcing of the renewal causal field

The backward action uses the literal reflected prime, Gamma and pole
kernels. At every full divisor point its terms are absolutely admitted,
and the sum of both actions is the first bilateral source moment.
No simplicity, critical-axis, or positivity assumption is used.
-/

noncomputable section

open MeasureTheory Set Filter Topology HurwitzZeta

namespace RHTower.ThetaSourceWard

/-- The full bilateral transform is exactly the causal reflection defect. -/
theorem thetaCausalField_reflection_defect (w : ℂ) (x : ℝ) :
    thetaCausalField w x + thetaCausalField (-w) (-x) =
      Complex.exp (-(w * x)) * bilateralLaplace thetaCuspTiltSource w := by
  have hi : (∫ t in Ioi (-x), (thetaCuspFullSource t : ℂ) *
      Complex.exp ((-w) * t)) =
      ∫ t in Iic x, (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
    calc
      _ = ∫ t in Ioi (-x), (thetaCuspFullSource (-t) : ℂ) *
          Complex.exp (w * ((-t : ℝ) : ℂ)) := by
        simp only [thetaCuspFullSource_neg, Complex.ofReal_neg, mul_neg, neg_mul]
      _ = _ := by
        simpa only [neg_neg] using integral_comp_neg_Ioi (-x)
          (fun t : ℝ => (thetaCuspFullSource t : ℂ) * Complex.exp (w * t))
  have hs := integral_add_compl (s := Iic x) measurableSet_Iic
    (integrable_bilateralLaplace thetaCuspTiltSource w)
  simp only [compl_Iic, thetaCuspTiltSource_k] at hs
  rw [thetaCausalField_eq_tail, thetaCausalField_eq_tail, hi]
  simp only [Complex.ofReal_neg, neg_mul_neg]
  unfold bilateralLaplace
  simp only [thetaCuspTiltSource_k]
  linear_combination Complex.exp (-(w * x)) * hs

theorem thetaCausalField_reflection {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (x : ℝ) :
    thetaCausalField w x = -thetaCausalField (-w) (-x) := by
  have h := thetaCausalField_reflection_defect w x
  rw [hzero, mul_zero] at h
  linear_combination h

def reflectedCausalGammaTerm (w : ℂ) (x u : ℝ) : ℂ :=
  ((Real.exp (-2 * u) : ℂ) * thetaCausalField w x -
    (Real.exp (-u / 2) : ℂ) * thetaCausalField w (x - u)) /
      ((1 - Real.exp (-2 * u) : ℝ) : ℂ)

def reflectedCausalPolarTerm (a : ℝ) (w : ℂ) (x u : ℝ) : ℂ :=
  (Real.exp (a * u) : ℂ) * thetaCausalField w (x - u)

def reflectedCausalPrimeTerm (w : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  primeCoefficient n * thetaCausalField w (x - Real.log n)

theorem reflectedCausalGammaTerm_eq {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (x u : ℝ) :
    reflectedCausalGammaTerm w x u = -causalGammaTerm (-w) (-x) u := by
  rw [reflectedCausalGammaTerm, causalGammaTerm,
    thetaCausalField_reflection hzero x, thetaCausalField_reflection hzero (x - u),
    show -(x - u) = -x + u by ring]
  ring

theorem reflectedCausalPolarTerm_eq {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (a x u : ℝ) :
    reflectedCausalPolarTerm a w x u = -causalPolarTerm a (-w) (-x) u := by
  rw [reflectedCausalPolarTerm, causalPolarTerm,
    thetaCausalField_reflection hzero (x - u), show -(x - u) = -x + u by ring]
  ring

theorem reflectedCausalPrimeTerm_eq {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (x : ℝ) (n : ℕ) :
    reflectedCausalPrimeTerm w x n = -causalPrimeTerm (-w) (-x) n := by
  rw [reflectedCausalPrimeTerm, causalPrimeTerm,
    thetaCausalField_reflection hzero (x - Real.log n),
    show -(x - Real.log n) = -x + Real.log n by ring]
  ring

theorem integrableOn_reflectedCausalGammaTerm {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0)
    (hw : -(3 / 4) ≤ w.re) (x : ℝ) :
    IntegrableOn (reflectedCausalGammaTerm w x) (Ioi 0) := by
  have h := (integrableOn_causalGammaTerm
    (w := -w) (by simp only [Complex.neg_re]; linarith) (-x)).neg
  apply h.congr
  exact Eventually.of_forall fun u => (reflectedCausalGammaTerm_eq hzero x u).symm

theorem integrableOn_reflectedCausalPolarTerm {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hzero : bilateralLaplace thetaCuspTiltSource w = 0)
    (hw : -(3 / 4) ≤ w.re) (x : ℝ) :
    IntegrableOn (reflectedCausalPolarTerm a w x) (Ioi 0) := by
  have h := (integrableOn_causalPolarTerm ha
    (w := -w) (by simp only [Complex.neg_re]; linarith) (-x)).neg
  apply h.congr
  exact Eventually.of_forall fun u => (reflectedCausalPolarTerm_eq hzero a x u).symm

theorem summable_norm_reflectedCausalPrimeTerm {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (x : ℝ) :
    Summable (fun n => ‖reflectedCausalPrimeTerm w x n‖) := by
  simpa only [reflectedCausalPrimeTerm_eq hzero, norm_neg] using
    summable_norm_causalPrimeTerm (-w) (-x)

/-- The literal backward action, with both poles and all prime powers. -/
def reflectedCausalArithmeticAction (w : ℂ) (x : ℝ) : ℂ :=
  -archConstant * thetaCausalField w x +
    (∫ u in Ioi (0 : ℝ), reflectedCausalGammaTerm w x u) +
    (∫ u in Ioi (0 : ℝ), reflectedCausalPolarTerm (1 / 2) w x u) +
    (∫ u in Ioi (0 : ℝ), reflectedCausalPolarTerm (-1 / 2) w x u) -
    ∑' n, reflectedCausalPrimeTerm w x n

theorem reflectedCausalArithmeticAction_eq {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (x : ℝ) :
    reflectedCausalArithmeticAction w x = -causalArithmeticAction (-w) (-x) := by
  simp only [reflectedCausalArithmeticAction, causalArithmeticAction,
    reflectedCausalGammaTerm_eq hzero, reflectedCausalPolarTerm_eq hzero,
    reflectedCausalPrimeTerm_eq hzero, integral_neg, tsum_neg]
  rw [thetaCausalField_reflection hzero x]
  ring

theorem neg_reflected_forwardAction_eq_moment {w : ℂ}
    (hw : -(3 / 4) ≤ w.re) (x : ℝ) :
    -causalArithmeticAction (-w) (-x) = Complex.exp (-(w * x)) *
      ∫ t in Iic x, (t : ℂ) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  rw [causalArithmeticAction_eq_moment (by simp only [Complex.neg_re]; linarith)]
  have hi : (∫ t in Ioi (-x), (t : ℂ) * (thetaCuspFullSource t : ℂ) *
      Complex.exp ((-w) * t)) =
      -(∫ t in Iic x, (t : ℂ) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) := by
    rw [← integral_neg, ← neg_neg x, ← integral_comp_neg_Ioi]
    simp only [neg_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [thetaCuspFullSource_neg, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
  rw [hi]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

theorem reflectedCausalArithmeticAction_eq_moment {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0)
    (hw : -(3 / 4) ≤ w.re) (x : ℝ) :
    reflectedCausalArithmeticAction w x = Complex.exp (-(w * x)) *
      ∫ t in Iic x, (t : ℂ) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  rw [reflectedCausalArithmeticAction_eq hzero, neg_reflected_forwardAction_eq_moment hw]

/-- Before restriction to the divisor, the exact source reflection defect
regularizes the backward field. Its complete forcing is still the first moment. -/
theorem causalArithmeticAction_sub_reflected_eq_deriv {w : ℂ}
    (hlo : -(3 / 4) ≤ w.re) (hhi : w.re ≤ 3 / 4) (x : ℝ) :
    causalArithmeticAction w x - causalArithmeticAction (-w) (-x) =
      Complex.exp (-(w * x)) * deriv (bilateralLaplace thetaCuspTiltSource) w := by
  rw [sub_eq_add_neg, neg_reflected_forwardAction_eq_moment hlo,
    causalArithmeticAction_eq_moment hhi, deriv_bilateralLaplace]
  have hs := integral_add_compl (s := Iic x) measurableSet_Iic (momentIntegrand_integrable w)
  simp only [compl_Iic] at hs
  unfold bilateralLaplaceDeriv
  simp only [thetaCuspTiltSource_k]
  linear_combination Complex.exp (-(w * x)) * hs

/-- Full arithmetic forcing at every full zero, including multiple zeros. -/
theorem fullCausalArithmeticAction_eq_deriv {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0)
    (hlo : -(3 / 4) ≤ w.re) (hhi : w.re ≤ 3 / 4) (x : ℝ) :
    causalArithmeticAction w x + reflectedCausalArithmeticAction w x =
      Complex.exp (-(w * x)) * deriv (bilateralLaplace thetaCuspTiltSource) w := by
  rw [reflectedCausalArithmeticAction_eq hzero, ← sub_eq_add_neg]
  exact causalArithmeticAction_sub_reflected_eq_deriv hlo hhi x

theorem bilateralLaplace_renewal_parameter (lam : ℂ) :
    bilateralLaplace thetaCuspTiltSource (-2 * lam) = XiC (2 * Complex.I * lam) := by
  rw [bilateralLaplace_thetaCuspTiltSource_eq_xiCent, xiCent_eq_XiC]
  congr 1
  ring

/-- The forcing law specializes to the actual full RN divisor. -/
theorem fullCausalArithmeticAction_at_full_divisor {lam : ℂ}
    (hzero : XiC (2 * Complex.I * lam) = 0)
    (hlo : -(3 / 8) ≤ lam.re) (hhi : lam.re ≤ 3 / 8) (x : ℝ) :
    causalArithmeticAction (-2 * lam) x + reflectedCausalArithmeticAction (-2 * lam) x =
      Complex.exp (2 * lam * x) * deriv (bilateralLaplace thetaCuspTiltSource) (-2 * lam) := by
  have hz : bilateralLaplace thetaCuspTiltSource (-2 * lam) = 0 := by
    rwa [bilateralLaplace_renewal_parameter]
  have hl : -(3 / 4) ≤ (-2 * lam).re := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  have hh : (-2 * lam).re ≤ 3 / 4 := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  convert fullCausalArithmeticAction_eq_deriv hz hl hh x using 1
  congr 2
  ring

theorem hasDerivAt_fullDivisor_renewal_parameter (lam : ℂ) :
    HasDerivAt (fun z => XiC (2 * Complex.I * z))
      (-2 * deriv (bilateralLaplace thetaCuspTiltSource) (-2 * lam)) lam := by
  have h := (hasDerivAt_bilateralLaplace thetaCuspTiltSource (-2 * lam)).comp lam
    ((hasDerivAt_id lam).const_mul (-2 : ℂ))
  have hf : (-2 : ℂ) * deriv (bilateralLaplace thetaCuspTiltSource) (-2 * lam) =
      bilateralLaplaceDeriv thetaCuspTiltSource (-2 * lam) * (-2) := by
    rw [deriv_bilateralLaplace]
    ring
  rw [hf]
  simpa only [Function.comp_def, mul_one, bilateralLaplace_renewal_parameter] using h

/-- The native forcing coefficient is the derivative of the charged full divisor,
multiplied by its nonvanishing renewal boundary charge. -/
theorem fullCausalArithmeticAction_at_renewal_charge {lam : ℂ}
    (hzero : XiC (2 * Complex.I * lam) = 0)
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) (x : ℝ) :
    causalArithmeticAction (-2 * lam) x + reflectedCausalArithmeticAction (-2 * lam) x =
      -Complex.exp (2 * lam * x) * thetaRenewalFullCharge lam *
        deriv thetaRenewalChargedQuotient lam / 2 := by
  have hC := thetaRenewalFullCharge_ne_zero hs hy
  have hD := ((hasDerivAt_fullDivisor_renewal_parameter lam).div
    (differentiable_thetaRenewalFullCharge lam).hasDerivAt hC).deriv
  change deriv thetaRenewalChargedQuotient lam = _ at hD
  rw [hzero, zero_mul, sub_zero] at hD
  rw [fullCausalArithmeticAction_at_full_divisor hzero
    (by linarith [(abs_lt.mp hs).1]) (by linarith [(abs_lt.mp hs).2]), hD]
  field_simp

end RHTower.ThetaSourceWard
