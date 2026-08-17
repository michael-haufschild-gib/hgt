import GaloisForLFunctions.HTGeometry.MassCarrierRatioIdentity

/-!
# Multiplicativity of the principal square root near the unit

On the right half plane the principal root has real part above its modulus over the square root of
two, because squaring turns the difference of the squared coordinates into the real part of the
argument.  Consequently multiplying by a factor whose root is within that margin of one keeps the
product in the right half plane, and the principal root of the product is the product of the roots.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section RootMultiplicative

/-- On the right half plane the principal root's modulus is at most `√2` times its real part. -/
theorem norm_csqrt_le_sqrt_two_mul_re {t : ℂ} (ht : 0 < t.re) :
    ‖_root_.HTGeometry.csqrt t‖ ≤ Real.sqrt 2 * (_root_.HTGeometry.csqrt t).re := by
  set p : ℝ := (_root_.HTGeometry.csqrt t).re with hp
  set q : ℝ := (_root_.HTGeometry.csqrt t).im with hq
  have hppos : 0 < p := by
    rw [hp, _root_.HTGeometry.csqrt_re]
    exact _root_.HTGeometry.csqrtRe_pos ht
  have hsq : _root_.HTGeometry.csqrt t ^ 2 = t := _root_.HTGeometry.csqrt_sq ht
  have hre : p ^ 2 - q ^ 2 = t.re := by
    have := congrArg Complex.re hsq
    rw [pow_two, Complex.mul_re] at this
    rw [← this, hp, hq]
    ring
  have hqlt : q ^ 2 < p ^ 2 := by linarith
  have hnorm : ‖_root_.HTGeometry.csqrt t‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hp, hq]
    ring
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ ‖_root_.HTGeometry.csqrt t‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ Real.sqrt 2 * p := by positivity
  have hsqle : ‖_root_.HTGeometry.csqrt t‖ ^ 2 ≤ (Real.sqrt 2 * p) ^ 2 := by
    rw [mul_pow, hsqrt2, hnorm]
    linarith [hqlt]
  have h1 : ‖_root_.HTGeometry.csqrt t‖ = Real.sqrt (‖_root_.HTGeometry.csqrt t‖ ^ 2) :=
    (Real.sqrt_sq hnn).symm
  have h2 : Real.sqrt 2 * p = Real.sqrt ((Real.sqrt 2 * p) ^ 2) := (Real.sqrt_sq hrhs).symm
  rw [h1, h2]
  exact Real.sqrt_le_sqrt hsqle

/-- **Multiplicativity of the principal root at a factor near one.** -/
theorem csqrt_mul_of_near_one {t s : ℂ} (ht : 0 < t.re) (hs : 0 < s.re)
    (hts : 0 < (t * s).re) (hclose : Real.sqrt 2 * ‖s - 1‖ < 1) :
    _root_.HTGeometry.csqrt (t * s)
      = _root_.HTGeometry.csqrt t * _root_.HTGeometry.csqrt s := by
  have hcsq : ‖_root_.HTGeometry.csqrt s - 1‖ ≤ ‖s - 1‖ := by
    have h := _root_.HTGeometry.norm_csqrt_sub_one_le hs
    exact h
  have hppos : 0 < (_root_.HTGeometry.csqrt t).re := by
    rw [_root_.HTGeometry.csqrt_re]
    exact _root_.HTGeometry.csqrtRe_pos ht
  have hnb := norm_csqrt_le_sqrt_two_mul_re ht
  set v : ℂ := _root_.HTGeometry.csqrt t * _root_.HTGeometry.csqrt s with hvdef
  have hsub : v - _root_.HTGeometry.csqrt t
      = _root_.HTGeometry.csqrt t * (_root_.HTGeometry.csqrt s - 1) := by
    rw [hvdef]
    ring
  have hvb : ‖v - _root_.HTGeometry.csqrt t‖
      ≤ ‖_root_.HTGeometry.csqrt t‖ * ‖s - 1‖ := by
    rw [hsub, norm_mul]
    exact mul_le_mul_of_nonneg_left hcsq (norm_nonneg _)
  have hvre : 0 < v.re := by
    have hb : |(v - _root_.HTGeometry.csqrt t).re| ≤ ‖v - _root_.HTGeometry.csqrt t‖ :=
      Complex.abs_re_le_norm _
    have hbb := abs_le.mp hb
    have hsplit : (v - _root_.HTGeometry.csqrt t).re = v.re - (_root_.HTGeometry.csqrt t).re := by
      simp
    rw [hsplit] at hbb
    nlinarith [hbb.1, hvb, hnb, hppos, norm_nonneg (s - 1), hclose]
  have hvsq : v ^ 2 = t * s := by
    rw [hvdef, mul_pow, _root_.HTGeometry.csqrt_sq ht, _root_.HTGeometry.csqrt_sq hs]
  exact _root_.HTGeometry.csqrt_eq_of_sq_of_re_pos hts hvre hvsq

end RootMultiplicative

end

end GaloisForLFunctions.HTGeometry
