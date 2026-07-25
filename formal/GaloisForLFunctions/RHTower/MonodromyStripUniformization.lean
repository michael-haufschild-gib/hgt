import GaloisForLFunctions.Hurwitz.MonodromyScalar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The monodromy uniformization of the critical strip

The Hurwitz monodromy scalar `mu(s) = exp(-2 π i s)` has period one, exactly the width of the open
critical strip.  In the `mu` coordinate the strip becomes the plane slit along the positive real
axis, the **critical line becomes the negative real axis**, and the functional-equation/Schwarz
reflection `s ↦ 1 - conj s` becomes ordinary **complex conjugation**.

So the critical line is not a metric accident: it is the fixed locus of conjugation in the
uniformizing coordinate in which the functional equation is conjugation.
-/

open Complex

namespace RHTower

noncomputable section

open HurwitzOrbit

theorem monoScalar_re (s : ℂ) :
    (monoScalar s).re = Real.exp (2 * Real.pi * s.im) * Real.cos (2 * Real.pi * s.re) := by
  rw [monoScalar, Complex.exp_re]
  have hre : (-(2 * (Real.pi : ℂ) * Complex.I * s)).re = 2 * Real.pi * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : (-(2 * (Real.pi : ℂ) * Complex.I * s)).im = -(2 * Real.pi * s.re) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, him, Real.cos_neg]

theorem monoScalar_im (s : ℂ) :
    (monoScalar s).im = -(Real.exp (2 * Real.pi * s.im) * Real.sin (2 * Real.pi * s.re)) := by
  rw [monoScalar, Complex.exp_im]
  have hre : (-(2 * (Real.pi : ℂ) * Complex.I * s)).re = 2 * Real.pi * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : (-(2 * (Real.pi : ℂ) * Complex.I * s)).im = -(2 * Real.pi * s.re) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, him, Real.sin_neg]
  ring

/-- **The functional-equation reflection is conjugation in the monodromy coordinate.** -/
theorem monoScalar_lineConj (s : ℂ) :
    monoScalar (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (monoScalar s) := by
  have hconj : (starRingEnd ℂ) (monoScalar s)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) s) := by
    rw [monoScalar, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hconj, monoScalar]
  have hsplit : -(2 * (Real.pi : ℂ) * Complex.I * (1 - (starRingEnd ℂ) s))
      = -(2 * (Real.pi : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) s := by
    ring
  rw [hsplit, Complex.exp_add]
  have h1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I (-1)
  rw [h1, one_mul]

/-- **The critical line is exactly the real locus of the monodromy coordinate.**  Inside the open
critical strip, `mu(s)` is real precisely when `Re s = 1/2`. -/
theorem monoScalar_im_eq_zero_iff_re_eq_half {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (monoScalar s).im = 0 ↔ s.re = 1 / 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [monoScalar_im, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro (hexp | hsin)
    · exact absurd hexp (ne_of_gt (Real.exp_pos _))
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
      have hns : (n : ℝ) = 2 * s.re := by
        have h2 : (n : ℝ) * Real.pi = 2 * Real.pi * s.re := hn
        have := mul_right_cancel₀ (ne_of_gt hpi) (by linarith : (n : ℝ) * Real.pi = (2 * s.re) * Real.pi)
        exact this
      have hlo : (0 : ℝ) < (n : ℝ) := by rw [hns]; linarith
      have hhi : (n : ℝ) < 2 := by rw [hns]; linarith
      have hn1 : n = 1 := by
        have a1 : (0 : ℤ) < n := by exact_mod_cast hlo
        have a2 : n < 2 := by exact_mod_cast hhi
        omega
      rw [hn1] at hns
      push_cast at hns
      linarith
  · intro hhalf
    right
    rw [hhalf]
    have : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
    rw [this, Real.sin_pi]

/-- On the critical line the monodromy coordinate is a strictly negative real number. -/
theorem monoScalar_re_neg_of_re_eq_half {s : ℂ} (h : s.re = 1 / 2) :
    (monoScalar s).re < 0 := by
  rw [monoScalar_re, h]
  have : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [this, Real.cos_pi]
  simpa using Real.exp_pos (2 * Real.pi * s.im)

end

end RHTower
