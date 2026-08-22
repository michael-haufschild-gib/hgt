import GaloisForLFunctions.RHTower.CoshQuartetEnvelope

/-!
# Simple zeros of displaced cosh quartet envelopes

The two off-axis `cosh` lattices in a nontrivially displaced quartet envelope
are disjoint.  This leaf records the resulting simple-zero fact, needed when
the envelope is used as a divisor-relocation witness.
-/

noncomputable section

namespace RHTower

/-- Exact derivative of a displaced cosh quartet envelope. -/
theorem hasDerivAt_coshQuartetEnvelope (a : ℝ) (z : ℂ) :
    HasDerivAt (coshQuartetEnvelope a)
      (Complex.sinh (z - (a : ℂ)) * Complex.cosh (z + (a : ℂ)) +
        Complex.cosh (z - (a : ℂ)) * Complex.sinh (z + (a : ℂ))) z := by
  unfold coshQuartetEnvelope
  simpa [Function.comp_apply] using! ((Complex.hasDerivAt_cosh (z - (a : ℂ))).comp z
    ((hasDerivAt_id z).sub_const (a : ℂ))).mul
    ((Complex.hasDerivAt_cosh (z + (a : ℂ))).comp z
      ((hasDerivAt_id z).add_const (a : ℂ)))

/-- With nonzero displacement, every zero of the quartet envelope is simple. -/
theorem deriv_coshQuartetEnvelope_ne_zero_of_eq_zero
    {a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    deriv (coshQuartetEnvelope a) z ≠ 0 := by
  rw [coshQuartetEnvelope, mul_eq_zero] at hz
  rcases hz with hleft | hright
  · have hleftre : (z - (a : ℂ)).re = 0 := by
      by_contra hne
      exact (cosh_ne_zero_of_re_ne_zero hne) hleft
    have hotherre : (z + (a : ℂ)).re = 2 * a := by
      change z.re - a = 0 at hleftre
      change z.re + a = 2 * a
      linarith
    have hother : Complex.cosh (z + (a : ℂ)) ≠ 0 :=
      cosh_ne_zero_of_re_ne_zero (by rw [hotherre]; exact mul_ne_zero two_ne_zero ha)
    have hsinh : Complex.sinh (z - (a : ℂ)) ≠ 0 := by
      intro hsinh
      have hid := Complex.cosh_sq_sub_sinh_sq (z - (a : ℂ))
      rw [hleft, hsinh] at hid
      norm_num at hid
    rw [(hasDerivAt_coshQuartetEnvelope a z).deriv, hleft, zero_mul, add_zero]
    exact mul_ne_zero hsinh hother
  · have hrightr : (z + (a : ℂ)).re = 0 := by
      by_contra hne
      exact (cosh_ne_zero_of_re_ne_zero hne) hright
    have hotherre : (z - (a : ℂ)).re = -2 * a := by
      change z.re + a = 0 at hrightr
      change z.re - a = -2 * a
      linarith
    have hother : Complex.cosh (z - (a : ℂ)) ≠ 0 :=
      cosh_ne_zero_of_re_ne_zero (by rw [hotherre]; exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) ha)
    have hsinh : Complex.sinh (z + (a : ℂ)) ≠ 0 := by
      intro hsinh
      have hid := Complex.cosh_sq_sub_sinh_sq (z + (a : ℂ))
      rw [hright, hsinh] at hid
      norm_num at hid
    rw [(hasDerivAt_coshQuartetEnvelope a z).deriv]
    simp only [hright, mul_zero, zero_add]
    exact mul_ne_zero hother hsinh

/-- A nontrivially displaced quartet envelope has no zero on its central vertical line. -/
theorem coshQuartetEnvelope_zero_re_ne_zero
    {a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    z.re ≠ 0 := by
  rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
  · intro hzero
    have hre := congrArg Complex.re hk
    simp at hre
    exact ha (hre.symm.trans hzero)
  · intro hzero
    have hre := congrArg Complex.re hk
    simp at hre
    exact ha (neg_eq_zero.mp (hre.symm.trans hzero))

end RHTower
