import GaloisForLFunctions.RHTower.PrimeArchEndpointFrequencyAccretivity
import GaloisForLFunctions.HTGeometry.VerticalModulusDerivative

/-!
# The complete signed prime–archimedean current

Clearing the logarithmic derivative's denominator gives the vertical modulus current.
It is continuous through every zero and retains the exact source sign off the divisor.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open Complex

abbrev Height := {a : ℝ // 0 < a ∧ a < 1 / 2}

def point (a : Height) (x : ℝ) : ℂ := (x : ℂ) + (a : ℂ) * I

def current (a : Height) (x : ℝ) : ℝ :=
  -(deriv XiC (point a x) * star (XiC (point a x))).im

theorem point_re (a : Height) (x : ℝ) : (point a x).re = x := by simp [point]

theorem point_im (a : Height) (x : ℝ) : (point a x).im = a := by simp [point]

private theorem point_re_pos (a : Height) (x : ℝ) :
    0 < (1 / 2 + point a x * I).re := by
  simp [point]
  linarith [a.property.2]

private theorem point_ne_one (a : Height) (x : ℝ) : 1 / 2 + point a x * I ≠ 1 := by
  intro h
  have hr := congrArg Complex.re h
  simp [point] at hr
  linarith [a.property.1]

theorem point_zeta_ne_iff (a : Height) (x : ℝ) :
    riemannZeta (1 / 2 + point a x * I) ≠ 0 ↔ XiC (point a x) ≠ 0 := by
  simpa only [XiC] using (xi_eq_zero_iff (point_re_pos a x) (point_ne_one a x)).not.symm

theorem continuous_current (a : Height) : Continuous (current a) := by
  have hd : Continuous (deriv XiC) := continuous_iff_continuousAt.mpr fun z =>
    (XiC_analytic z (Set.mem_univ z)).deriv.continuousAt
  have hX : Continuous XiC := XiC_analytic.continuous
  have hp : Continuous (point a) := by unfold point; fun_prop
  exact (Complex.continuous_im.comp ((hd.comp hp).mul (hX.comp hp).star)).neg

/-- Multiplication by the exact squared amplitude also handles the zeros. -/
theorem current_eq_primeArch (a : Height) (x : ℝ) :
    current a x = -Complex.normSq (XiC (point a x)) *
      (continuedPrimeArchSourceRelativeTrace (point a x)).im := by
  by_cases hXi : XiC (point a x) = 0
  · simp [current, hXi]
  have hsource : continuedPrimeArchSourceRelativeTrace (point a x) =
      logDeriv XiC (point a x) :=
    (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      (point_re_pos a x) (point_ne_one a x) ((point_zeta_ne_iff a x).mpr hXi)).trans
      (logDeriv_XiC_eq_relativeResolventTrace hXi).symm
  rw [hsource]
  have h := HTGeometry.neg_two_im_deriv_mul_conj_eq XiC hXi
  change -(deriv XiC (point a x) * star (XiC (point a x))).im = _
  change -2 * (deriv XiC (point a x) * star (XiC (point a x))).im = _ at h
  linarith

theorem current_zero_at_zero (a : Height) (x : ℝ) (h : XiC (point a x) = 0) :
    current a x = 0 := by simp [current, h]

/-- Twice the current is the actual vertical derivative of squared Xi modulus. -/
theorem hasDerivAt_normSq (a : Height) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.normSq (XiC ((x : ℂ) + (t : ℂ) * I)))
      (2 * current a x) (a : ℝ) := by
  convert HTGeometry.hasDerivAt_normSq_vertical_general XiC x (a : ℝ)
    (XiC_analytic (point a x) (Set.mem_univ _)).differentiableAt using 1
  simp [current, point]
  ring

/-- Any frequency region can be retained without canceling an amplitude at a zero. -/
theorem sign_iff_source (P : ℝ → Prop) :
    (∀ a : Height, ∀ x, P x → 0 ≤ current a x) ↔
      ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → P z.re →
        riemannZeta (1 / 2 + z * I) ≠ 0 →
          (continuedPrimeArchSourceRelativeTrace z).im ≤ 0 := by
  constructor
  · intro h z hz0 hz1 hP hzeta
    let a : Height := ⟨z.im, hz0, hz1⟩
    have hp : point a z.re = z := by simp [point, a]
    have hn := h a z.re hP
    rw [current_eq_primeArch, hp] at hn
    have hXi : XiC z ≠ 0 := by
      rw [← hp]
      apply (point_zeta_ne_iff a z.re).mp
      simpa only [hp] using hzeta
    nlinarith [Complex.normSq_pos.mpr hXi]
  · intro h a x hx
    by_cases hXi : XiC (point a x) = 0
    · exact (current_zero_at_zero a x hXi).ge
    rw [current_eq_primeArch]
    have ht := h (point a x) (by simpa only [point_im] using a.property.1)
      (by simpa only [point_im] using a.property.2) (by simpa only [point_re] using hx)
      ((point_zeta_ne_iff a x).mpr hXi)
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Complex.normSq_nonneg _)) ht

theorem forall_current_nonneg_iff_rh :
    (∀ a : Height, ∀ x, 0 ≤ current a x) ↔ RiemannHypothesis := by
  have h := (sign_iff_source fun _ => True).trans
    (show (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → True →
      riemannZeta (1 / 2 + z * I) ≠ 0 →
        (continuedPrimeArchSourceRelativeTrace z).im ≤ 0) ↔ RiemannHypothesis by
      simpa only [true_implies, ContinuedPrimeArchUpperAntiHerglotz] using
        continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis)
  simpa only [true_implies] using h

theorem high_frequency_current_nonneg_iff_rh :
    (∀ a : Height, ∀ x, 161 / 40 < x → 0 ≤ current a x) ↔ RiemannHypothesis :=
  (sign_iff_source fun x => 161 / 40 < x).trans
    continuedPrimeArchPositiveFrequencyAbove_oneSixtyOne_fortieths_iff_rh

end
end RHTower.PaperPrimeArch
