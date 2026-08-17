import GaloisForLFunctions.HTGeometry.MassCarrierDistortionFactors

/-!
# The shell factors as principal powers

On the right half plane every principal root and every inverse power of a principal root is a
principal complex power with a real exponent.  The quarter power appears because the distortion
carries a root of a root; its argument is a quarter of the argument of the shell quantity, so it
stays well inside the right half plane and no branch is crossed.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ShellPowers

/-- A principal power with a real exponent in `(0,1]` keeps the right half plane. -/
theorem cpow_ofReal_re_pos {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    0 < (z ^ ((c : ℝ) : ℂ)).re := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have harg : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [Complex.cpow_def_of_ne_zero hzne, Complex.exp_re]
  have him : (Complex.log z * ((c : ℝ) : ℂ)).im = z.arg * c := by
    simp [Complex.mul_im, Complex.log_im]
  rw [him]
  have hcos : 0 < Real.cos (z.arg * c) := by
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have h1 := (abs_lt.1 harg).1
      nlinarith [Real.pi_pos, hc0, hc1]
    · have h2 := (abs_lt.1 harg).2
      nlinarith [Real.pi_pos, hc0, hc1]
  positivity

theorem inv_csqrt_eq_cpow {z : ℂ} (hz : 0 < z.re) :
    (_root_.HTGeometry.csqrt z)⁻¹ = z ^ (((-1 / 2 : ℝ)) : ℂ) := by
  rw [_root_.HTGeometry.csqrt_eq_cpow_half hz,
    show (((-1 / 2 : ℝ)) : ℂ) = -(1 / 2 : ℂ) by push_cast; ring, Complex.cpow_neg]

theorem csqrt_csqrt_eq_cpow {z : ℂ} (hz : 0 < z.re) :
    _root_.HTGeometry.csqrt (_root_.HTGeometry.csqrt z) = z ^ (((1 / 4 : ℝ)) : ℂ) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hre : 0 < (_root_.HTGeometry.csqrt z).re := by
    rw [_root_.HTGeometry.csqrt_re]
    exact _root_.HTGeometry.csqrtRe_pos hz
  have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  have h1 : -Real.pi < (Complex.log z * (1 / 2 : ℂ)).im := by
    rw [him]
    have := Complex.neg_pi_lt_arg z
    linarith [Real.pi_pos]
  have h2 : (Complex.log z * (1 / 2 : ℂ)).im ≤ Real.pi := by
    rw [him]
    have := Complex.arg_le_pi z
    linarith [Real.pi_pos]
  have hmul := Complex.cpow_mul (x := z) (y := (1 / 2 : ℂ)) (1 / 2 : ℂ) h1 h2
  rw [_root_.HTGeometry.csqrt_eq_cpow_half hre, _root_.HTGeometry.csqrt_eq_cpow_half hz,
    ← hmul, show (((1 / 4 : ℝ)) : ℂ) = (1 / 2 : ℂ) * (1 / 2 : ℂ) by push_cast; ring]

theorem inv_csqrt_csqrt_eq_cpow {z : ℂ} (hz : 0 < z.re) :
    (_root_.HTGeometry.csqrt (_root_.HTGeometry.csqrt z))⁻¹ = z ^ (((-1 / 4 : ℝ)) : ℂ) := by
  rw [csqrt_csqrt_eq_cpow hz,
    show (((-1 / 4 : ℝ)) : ℂ) = -(((1 / 4 : ℝ)) : ℂ) by push_cast; ring, Complex.cpow_neg]

theorem csqrt_pow_eq_cpow {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    (_root_.HTGeometry.csqrt z) ^ k = z ^ ((((k : ℝ) / 2 : ℝ)) : ℂ) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, _root_.HTGeometry.csqrt_eq_cpow_half hz, ← Complex.cpow_add _ _ hzne]
      congr 1
      push_cast
      ring

theorem inv_csqrt_pow_eq_cpow {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ((_root_.HTGeometry.csqrt z)⁻¹) ^ k = z ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ) := by
  rw [inv_pow, csqrt_pow_eq_cpow hz k,
    show (((-(k : ℝ) / 2 : ℝ)) : ℂ) = -((((k : ℝ) / 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.cpow_neg]

end ShellPowers

end

end GaloisForLFunctions.HTGeometry
