/-
Exact local analytic orders for reflected-Gamma quartet relocation.

This leaf supplies the multiplicity bookkeeping omitted by support-level
relocation: the common Gamma order is additive, while an undisplaced Cosh
lattice point has Cosh order two and each nonzero displaced lattice point has
Cosh (and full-carrier) order one.
-/
import GaloisForLFunctions.RHTower.ReflectedGammaQuartetRelocation

open Complex

namespace RHTower

/-- Local analytic order of the full carrier is the sum of Gamma and Cosh orders. -/
theorem analyticOrderAt_reflectedGammaQuartetCarrier
    (beta a : ℝ) (z : ℂ) :
    analyticOrderAt (reflectedGammaQuartetCarrier beta a) z =
      analyticOrderAt (reflectedGammaCarrier beta) z +
        analyticOrderAt (coshQuartetEnvelope a) z := by
  unfold reflectedGammaQuartetCarrier
  exact analyticOrderAt_mul
    (reflectedGammaCarrier_analyticOnNhd beta z (by simp))
    (coshQuartetEnvelope_analyticAt a z)

/-- Every zero of a nontrivially displaced Cosh quartet envelope is simple. -/
theorem analyticOrderAt_coshQuartetEnvelope_eq_one_of_eq_zero
    {a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    analyticOrderAt (coshQuartetEnvelope a) z = 1 := by
  exact (coshQuartetEnvelope_analyticAt a z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hz (deriv_coshQuartetEnvelope_ne_zero_of_eq_zero ha hz)

/-- A displaced Cosh lattice zero remains a simple zero of the full carrier. -/
theorem analyticOrderAt_reflectedGammaQuartetCarrier_eq_one_of_cosh_zero
    {beta a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    analyticOrderAt (reflectedGammaQuartetCarrier beta a) z = 1 := by
  have hcentral : z.re ≠ 0 := coshQuartetEnvelope_zero_re_ne_zero ha hz
  have hgamma : reflectedGammaCarrier beta z ≠ 0 := by
    intro hzero
    exact hcentral (reflectedGammaCarrier_zero_re_eq_zero hzero)
  have hgammaOrder : analyticOrderAt (reflectedGammaCarrier beta) z = 0 :=
    (reflectedGammaCarrier_analyticOnNhd beta z (by simp)).analyticOrderAt_eq_zero.mpr hgamma
  rw [analyticOrderAt_reflectedGammaQuartetCarrier, hgammaOrder,
    analyticOrderAt_coshQuartetEnvelope_eq_one_of_eq_zero ha hz, zero_add]

/-- An undisplaced Cosh quartet zero has analytic order two. -/
theorem analyticOrderAt_coshQuartetEnvelope_zero_eq_two
    {z : ℂ} (hz : coshQuartetEnvelope 0 z = 0) :
    analyticOrderAt (coshQuartetEnvelope 0) z = 2 := by
  have hcosh : Complex.cosh z = 0 := by
    have hz' : Complex.cosh z * Complex.cosh z = 0 := by
      simpa [coshQuartetEnvelope] using hz
    rcases mul_eq_zero.mp hz' with h | h
    · exact h
    · exact h
  have hsinh : Complex.sinh z ≠ 0 := by
    intro h
    have hid := Complex.cosh_sq_sub_sinh_sq z
    rw [hcosh, h] at hid
    norm_num at hid
  have horder : analyticOrderAt Complex.cosh z = 1 := by
    refine Complex.analyticAt_cosh.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hcosh ?_
    rw [(Complex.hasDerivAt_cosh z).deriv]
    exact hsinh
  have hsplit : coshQuartetEnvelope 0 =
      fun w : ℂ => Complex.cosh w * Complex.cosh w := by
    funext w
    simp [coshQuartetEnvelope]
  rw [hsplit]
  change analyticOrderAt (Complex.cosh * Complex.cosh) z = 2
  rw [analyticOrderAt_mul Complex.analyticAt_cosh Complex.analyticAt_cosh, horder]
  norm_num

/-- At an undisplaced Cosh zero, the full multiplicity is common Gamma multiplicity plus two. -/
theorem analyticOrderAt_reflectedGammaQuartetCarrier_zero_eq_gamma_add_two
    {beta : ℝ} {z : ℂ} (hz : coshQuartetEnvelope 0 z = 0) :
    analyticOrderAt (reflectedGammaQuartetCarrier beta 0) z =
      analyticOrderAt (reflectedGammaCarrier beta) z + 2 := by
  rw [analyticOrderAt_reflectedGammaQuartetCarrier,
    analyticOrderAt_coshQuartetEnvelope_zero_eq_two hz]

end RHTower
