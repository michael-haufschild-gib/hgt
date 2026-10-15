import GaloisForLFunctions.RHTower.ThetaRenewalReflectedArithmetic

/-!
# Whole-line mixed arithmetic pairing of renewal causal fields

Weighted admission and the causal ODE determine the full Laplace transform
of every admitted field, including its value at the source zero. These
evaluations retain the literal prime, Gamma and pole action in the pairing.
They do not assert positivity or exclude an off-axis divisor point.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace RHTower.ThetaSourceWard

theorem continuous_thetaCausalField (w : ℂ) : Continuous (thetaCausalField w) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_thetaCausalField w x).continuousAt

/-- Every polynomial and exponential weight is admitted at a full zero. -/
theorem integrable_thetaCausalField_moment {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (z : ℂ) (m : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ m * Complex.exp (z * x) * thetaCausalField w x) := by
  have hi : Integrable (fun x : ℝ => Complex.exp (w * x) *
      (thetaCuspFullSource x : ℂ)) := by
    simpa only [thetaCuspTiltSource_k, mul_comm] using
      integrable_bilateralLaplace thetaCuspTiltSource w
  have hz : (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)) = 0 := by
    simpa only [bilateralLaplace, thetaCuspTiltSource_k, mul_comm] using hzero
  obtain ⟨C, hC⟩ := exists_norm_rightCausalResponse_le
    HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource hi hz (|z.re| + 2)
  change ∀ x, ‖thetaCausalField w x‖ ≤ C * Real.exp (-((|z.re| + 2) * |x|)) at hC
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have hc : Continuous (fun x : ℝ =>
      (x : ℂ) ^ m * Complex.exp (z * x) * thetaCausalField w x) :=
    (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) ^ m * Complex.exp (z * x))).mul
      (continuous_thetaCausalField w)
  apply ((_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs m two_pos).const_mul C).mono'
    hc.aestronglyMeasurable
  filter_upwards with x
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, Complex.re_mul_ofReal]
  have he : Real.exp (z.re * x) * Real.exp (-((|z.re| + 2) * |x|)) ≤
      Real.exp (-(2 * |x|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := le_abs_self (z.re * x)
    rw [abs_mul] at h
    nlinarith
  calc
    _ ≤ |x| ^ m * Real.exp (z.re * x) *
        (C * Real.exp (-((|z.re| + 2) * |x|))) := by gcongr; exact hC x
    _ = C * |x| ^ m *
        (Real.exp (z.re * x) * Real.exp (-((|z.re| + 2) * |x|))) := by ring
    _ ≤ C * |x| ^ m * Real.exp (-(2 * |x|)) := by gcongr
    _ = _ := by ring

theorem integrable_thetaCausalField_laplace {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (z * x) * thetaCausalField w x) := by
  simpa only [pow_zero, one_mul] using integrable_thetaCausalField_moment hzero z 0

def thetaCausalLaplace (w z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (z * x) * thetaCausalField w x

private theorem weightedCausal_deriv (w z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * t) * thetaCausalField w t)
      ((z - w) * (Complex.exp (z * x) * thetaCausalField w x) -
        (thetaCuspFullSource x : ℂ) * Complex.exp (z * x)) x := by
  have hlin : HasDerivAt (fun t : ℝ => z * (t : ℂ)) z x := by
    simpa using ((hasDerivAt_id' x).ofReal_comp).const_mul z
  refine (hlin.cexp.mul (hasDerivAt_thetaCausalField w x)).congr_deriv ?_
  ring

/-- The whole-line causal transform is the divided difference of the full source. -/
theorem thetaCausalLaplace_mul_sub {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) (z : ℂ) :
    (z - w) * thetaCausalLaplace w z = bilateralLaplace thetaCuspTiltSource z := by
  have hu := integrable_thetaCausalField_laplace hzero z
  have hk : Integrable (fun x : ℝ => (thetaCuspFullSource x : ℂ) * Complex.exp (z * x)) := by
    simpa only [thetaCuspTiltSource_k] using integrable_bilateralLaplace thetaCuspTiltSource z
  have h := integral_eq_zero_of_hasDerivAt_of_integrable (weightedCausal_deriv w z)
    ((hu.const_mul (z - w)).sub hk) hu
  rw [integral_sub (hu.const_mul (z - w)) hk, integral_const_mul] at h
  exact sub_eq_zero.mp h

/-- The removable value is proved by an integrable primitive, without dividing by `z-w`. -/
theorem thetaCausalLaplace_self {w : ℂ}
    (hzero : bilateralLaplace thetaCuspTiltSource w = 0) :
    thetaCausalLaplace w w = deriv (bilateralLaplace thetaCuspTiltSource) w := by
  have hu := integrable_thetaCausalField_laplace hzero w
  have hm := momentIntegrand_integrable w
  have hp : Integrable (fun x : ℝ => (x : ℂ) *
      (Complex.exp (w * x) * thetaCausalField w x)) := by
    simpa only [pow_one, mul_assoc] using integrable_thetaCausalField_moment hzero w 1
  have hd (x : ℝ) : HasDerivAt
      (fun t : ℝ => (t : ℂ) * (Complex.exp (w * t) * thetaCausalField w t))
      (Complex.exp (w * x) * thetaCausalField w x -
        (x : ℂ) * (thetaCuspFullSource x : ℂ) * Complex.exp (w * x)) x := by
    have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp
    refine (hc.mul (weightedCausal_deriv w w x)).congr_deriv ?_
    ring
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hd (hu.sub hm) hp
  rw [integral_sub hu hm] at h
  rw [deriv_bilateralLaplace]
  exact sub_eq_zero.mp h

theorem thetaCausalLaplace_at_distinct_zero {w z : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hz : bilateralLaplace thetaCuspTiltSource z = 0) (hne : z ≠ w) :
    thetaCausalLaplace w z = 0 := by
  have h := thetaCausalLaplace_mul_sub hw z
  rw [hz] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

/-- Normalization uses the actual source derivative, not a fitted boundary datum. -/
def thetaNormalizedCausalField (w : ℂ) (x : ℝ) : ℂ :=
  thetaCausalField w x / deriv (bilateralLaplace thetaCuspTiltSource) w

def thetaNormalizedCausalAction (w : ℂ) (x : ℝ) : ℂ :=
  (causalArithmeticAction w x + reflectedCausalArithmeticAction w x) /
    deriv (bilateralLaplace thetaCuspTiltSource) w

def thetaCausalArithmeticDensity (w v : ℂ) (x : ℝ) : ℂ :=
  conj (thetaNormalizedCausalField w x) * thetaNormalizedCausalAction v x

def thetaCausalArithmeticPair (w v : ℂ) : ℂ :=
  ∫ x : ℝ, thetaCausalArithmeticDensity w v x

theorem thetaNormalizedCausalAction_eq {v : ℂ}
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) (x : ℝ) :
    thetaNormalizedCausalAction v x = Complex.exp (-(v * x)) := by
  rw [thetaNormalizedCausalAction, fullCausalArithmeticAction_eq_deriv hv hlo hhi]
  field_simp

theorem thetaCausalArithmeticDensity_eq {v : ℂ}
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) (w : ℂ) (x : ℝ) :
    thetaCausalArithmeticDensity w v x =
      conj ((Complex.exp ((-conj v) * x) * thetaCausalField w x) /
        deriv (bilateralLaplace thetaCuspTiltSource) w) := by
  rw [thetaCausalArithmeticDensity, thetaNormalizedCausalAction_eq hv hdv hlo hhi,
    thetaNormalizedCausalField]
  simp only [map_div₀, map_mul, ← Complex.exp_conj, map_neg, conj_conj,
    Complex.conj_ofReal, neg_mul]
  ring

/-- Whole-line admission is proved for the actual complete forcing, not postulated. -/
theorem integrable_thetaCausalArithmeticDensity {w v : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) :
    Integrable (thetaCausalArithmeticDensity w v) := by
  have hi := Complex.conjCLE.toContinuousLinearMap.integrable_comp
    ((integrable_thetaCausalField_laplace hw (-conj v)).div_const
      (deriv (bilateralLaplace thetaCuspTiltSource) w))
  apply hi.congr
  exact Eventually.of_forall fun x =>
    (thetaCausalArithmeticDensity_eq hv hdv hlo hhi w x).symm

theorem thetaCausalArithmeticPair_eq {v : ℂ}
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) (w : ℂ) :
    thetaCausalArithmeticPair w v =
      conj (thetaCausalLaplace w (-conj v) /
        deriv (bilateralLaplace thetaCuspTiltSource) w) := by
  unfold thetaCausalArithmeticPair
  simp_rw [thetaCausalArithmeticDensity_eq hv hdv hlo hhi w]
  simp only [integral_conj, integral_div, thetaCausalLaplace]

theorem bilateralLaplace_reflected_zero {w : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0) :
    bilateralLaplace thetaCuspTiltSource (-conj w) = 0 := by
  rw [bilateralLaplace_neg, ← bilateralLaplace_conj, hw, map_zero]

theorem deriv_bilateralLaplace_reflected (w : ℂ) :
    deriv (bilateralLaplace thetaCuspTiltSource) (-conj w) =
      -conj (deriv (bilateralLaplace thetaCuspTiltSource) w) := by
  rw [deriv_bilateralLaplace, bilateralLaplaceDeriv_neg,
    ← bilateralLaplaceDeriv_conj, deriv_bilateralLaplace]

theorem thetaCausalArithmeticPair_off_reflection {w v : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) (hne : -conj v ≠ w) :
    thetaCausalArithmeticPair w v = 0 := by
  rw [thetaCausalArithmeticPair_eq hv hdv hlo hhi,
    thetaCausalLaplace_at_distinct_zero hw (bilateralLaplace_reflected_zero hv) hne,
    zero_div, map_zero]

theorem thetaCausalArithmeticPair_on_reflection {w v : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hv : bilateralLaplace thetaCuspTiltSource v = 0)
    (hdw : deriv (bilateralLaplace thetaCuspTiltSource) w ≠ 0)
    (hdv : deriv (bilateralLaplace thetaCuspTiltSource) v ≠ 0)
    (hlo : -(3 / 4) ≤ v.re) (hhi : v.re ≤ 3 / 4) (heq : -conj v = w) :
    thetaCausalArithmeticPair w v = 1 := by
  rw [thetaCausalArithmeticPair_eq hv hdv hlo hhi, heq,
    thetaCausalLaplace_self hw, div_self hdw, map_one]

/-- The full action on a difference of normalized admitted fields, paired with that difference. -/
def thetaCausalNormalEnergy (w v : ℂ) : ℂ :=
  ∫ x : ℝ, conj (thetaNormalizedCausalField w x - thetaNormalizedCausalField v x) *
    (thetaNormalizedCausalAction w x - thetaNormalizedCausalAction v x)

theorem thetaCausalNormalEnergy_eq_pairs {w v : ℂ}
    (hww : Integrable (thetaCausalArithmeticDensity w w))
    (hvv : Integrable (thetaCausalArithmeticDensity v v))
    (hwv : Integrable (thetaCausalArithmeticDensity w v))
    (hvw : Integrable (thetaCausalArithmeticDensity v w)) :
    thetaCausalNormalEnergy w v = thetaCausalArithmeticPair w w +
      thetaCausalArithmeticPair v v - thetaCausalArithmeticPair w v -
      thetaCausalArithmeticPair v w := by
  have he : (fun x : ℝ =>
      conj (thetaNormalizedCausalField w x - thetaNormalizedCausalField v x) *
        (thetaNormalizedCausalAction w x - thetaNormalizedCausalAction v x)) =
      fun x => thetaCausalArithmeticDensity w w x + thetaCausalArithmeticDensity v v x -
        thetaCausalArithmeticDensity w v x - thetaCausalArithmeticDensity v w x := by
    funext x
    simp only [thetaCausalArithmeticDensity, map_sub]
    ring
  have h₁ := integral_sub ((hww.add hvv).sub hwv) hvw
  have h₂ := integral_sub (hww.add hvv) hwv
  have h₃ := integral_add hww hvv
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂ h₃
  rw [thetaCausalNormalEnergy, he, h₁, h₂, h₃]
  rfl

theorem thetaCausalArithmeticPair_critical_self {w : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hdw : deriv (bilateralLaplace thetaCuspTiltSource) w ≠ 0) (haxis : w.re = 0) :
    thetaCausalArithmeticPair w w = 1 := by
  apply thetaCausalArithmeticPair_on_reflection hw hw hdw hdw
    (by rw [haxis]; norm_num) (by rw [haxis]; norm_num)
  apply Complex.ext <;> simp [haxis]

/-- Exact native negative block at a hypothetical off-axis simple full zero.
This evaluates the obstruction; it does not prove the required opposite inequality. -/
theorem thetaCausalNormalEnergy_off_axis {w : ℂ}
    (hw : bilateralLaplace thetaCuspTiltSource w = 0)
    (hdw : deriv (bilateralLaplace thetaCuspTiltSource) w ≠ 0)
    (hlo : -(3 / 4) ≤ w.re) (hhi : w.re ≤ 3 / 4) (haxis : w.re ≠ 0) :
    thetaCausalNormalEnergy w (-conj w) = -2 := by
  have hv := bilateralLaplace_reflected_zero hw
  have hdv : deriv (bilateralLaplace thetaCuspTiltSource) (-conj w) ≠ 0 := by
    rw [deriv_bilateralLaplace_reflected]
    simpa using hdw
  have hvlo : -(3 / 4) ≤ (-conj w).re := by simpa using neg_le_neg hhi
  have hvhi : (-conj w).re ≤ 3 / 4 := by simpa using neg_le_neg hlo
  have hne : -conj w ≠ w := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hr
    exact haxis (by linarith)
  have heq : -conj (-conj w) = w := by simp
  rw [thetaCausalNormalEnergy_eq_pairs
    (integrable_thetaCausalArithmeticDensity hw hw hdw hlo hhi)
    (integrable_thetaCausalArithmeticDensity hv hv hdv hvlo hvhi)
    (integrable_thetaCausalArithmeticDensity hw hv hdv hvlo hvhi)
    (integrable_thetaCausalArithmeticDensity hv hw hdw hlo hhi),
    thetaCausalArithmeticPair_off_reflection hw hw hdw hlo hhi hne,
    thetaCausalArithmeticPair_off_reflection hv hv hdv hvlo hvhi
      (by rwa [heq, ne_comm]),
    thetaCausalArithmeticPair_on_reflection hw hv hdw hdv hvlo hvhi heq,
    thetaCausalArithmeticPair_on_reflection hv hw hdv hdw hlo hhi rfl]
  norm_num

end RHTower.ThetaSourceWard
