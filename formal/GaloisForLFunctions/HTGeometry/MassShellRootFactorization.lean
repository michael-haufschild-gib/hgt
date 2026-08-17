import GaloisForLFunctions.HTGeometry.MassBesselDeepTimeCarrier
import GaloisForLFunctions.HTGeometry.ShellRootDefectExpansion

/-!
# Factoring the mass-shell root through the spectral parameter

Off the negative real axis the principal root is the unique square root with positive real part, so
identifying `√(t²+x²)` with `t·√(1+x²/t²)` only needs the second factor to keep the product in the
right half plane.  The principal root is one-Lipschitz at the unit, so that holds as soon as the
squared frequency is below the product of the real part and the modulus of the spectral parameter.

This is the change of variable that turns the deep-time expansion into an expansion in the
reciprocal spectral parameter.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section RootFactorization

/-- Off the negative real axis the principal root is the unique square root with positive real
part. -/
theorem csqrt_eq_of_sq_of_re_pos_of_im_ne_zero {w v : ℂ} (hw : w.im ≠ 0) (hv : 0 < v.re)
    (hsq : v ^ 2 = w) : _root_.HTGeometry.csqrt w = v := by
  have hcs : _root_.HTGeometry.csqrt w ^ 2 = w := _root_.HTGeometry.csqrt_sq_of_im_ne_zero hw
  have hcre : 0 < (_root_.HTGeometry.csqrt w).re :=
    _root_.HTGeometry.csqrt_re_pos_of_im_ne_zero hw
  have hfac : (_root_.HTGeometry.csqrt w - v) * (_root_.HTGeometry.csqrt w + v) = 0 := by
    have : (_root_.HTGeometry.csqrt w - v) * (_root_.HTGeometry.csqrt w + v)
        = _root_.HTGeometry.csqrt w ^ 2 - v ^ 2 := by ring
    rw [this, hcs, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : _root_.HTGeometry.csqrt w = -v := by
      have := add_eq_zero_iff_eq_neg.mp h
      exact this
    rw [hneg] at hcre
    simp only [Complex.neg_re] at hcre
    linarith

theorem norm_shellQuot (t : ℂ) (x : ℝ) : ‖((x : ℂ)) ^ 2 / t ^ 2‖ = x ^ 2 / ‖t‖ ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The mass-shell root factors through the spectral parameter.** -/
theorem massBesselRoot_eq_mul_csqrt {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ)
    (hsmall : x ^ 2 < t.re * ‖t‖) :
    _root_.HTGeometry.massBesselRoot t x
      = t * _root_.HTGeometry.csqrt (1 + ((x : ℂ)) ^ 2 / t ^ 2) := by
  have htne : t ≠ 0 := by
    intro h
    rw [h] at htre
    simp at htre
  have htnorm : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr htne
  have hrele : t.re ≤ ‖t‖ := Complex.re_le_norm t
  have hu : ‖((x : ℂ)) ^ 2 / t ^ 2‖ = x ^ 2 / ‖t‖ ^ 2 := norm_shellQuot t x
  have hulet : ‖((x : ℂ)) ^ 2 / t ^ 2‖ * ‖t‖ = x ^ 2 / ‖t‖ := by
    rw [hu]
    field_simp
  have hxlt : x ^ 2 / ‖t‖ < t.re := by
    rw [div_lt_iff₀ htnorm]
    exact hsmall
  have hulr : ‖((x : ℂ)) ^ 2 / t ^ 2‖ < 1 := by
    rw [hu, div_lt_one (by positivity)]
    nlinarith [hsmall, hrele, htnorm, htre]
  have hre1 : 0 < (1 + ((x : ℂ)) ^ 2 / t ^ 2).re := by
    have hb : |(((x : ℂ)) ^ 2 / t ^ 2).re| ≤ ‖((x : ℂ)) ^ 2 / t ^ 2‖ :=
      Complex.abs_re_le_norm _
    have := abs_le.mp hb
    simp only [Complex.add_re, Complex.one_re]
    linarith [this.1, hulr]
  have hcsl : ‖_root_.HTGeometry.csqrt (1 + ((x : ℂ)) ^ 2 / t ^ 2) - 1‖
      ≤ ‖((x : ℂ)) ^ 2 / t ^ 2‖ := by
    have h := _root_.HTGeometry.norm_csqrt_sub_one_le hre1
    simpa using h
  set v : ℂ := t * _root_.HTGeometry.csqrt (1 + ((x : ℂ)) ^ 2 / t ^ 2) with hvdef
  have hvt : ‖v - t‖ ≤ x ^ 2 / ‖t‖ := by
    have hfac : v - t = t * (_root_.HTGeometry.csqrt (1 + ((x : ℂ)) ^ 2 / t ^ 2) - 1) := by
      rw [hvdef]
      ring
    rw [hfac, norm_mul]
    calc ‖t‖ * ‖_root_.HTGeometry.csqrt (1 + ((x : ℂ)) ^ 2 / t ^ 2) - 1‖
        ≤ ‖t‖ * ‖((x : ℂ)) ^ 2 / t ^ 2‖ := mul_le_mul_of_nonneg_left hcsl (norm_nonneg t)
      _ = x ^ 2 / ‖t‖ := by rw [mul_comm]; exact hulet
  have hvre : 0 < v.re := by
    have hb : |(v - t).re| ≤ ‖v - t‖ := Complex.abs_re_le_norm _
    have := abs_le.mp hb
    have hsub : (v - t).re = v.re - t.re := by simp
    rw [hsub] at this
    linarith [this.1, hvt, hxlt]
  have hvsq : v ^ 2 = t ^ 2 + ((x : ℂ)) ^ 2 := by
    have hsq := _root_.HTGeometry.csqrt_sq hre1
    rw [hvdef, mul_pow, hsq]
    field_simp
  have him : (t ^ 2 + ((x : ℂ)) ^ 2).im ≠ 0 :=
    _root_.HTGeometry.massShell_im_ne_zero htre htim x
  rw [_root_.HTGeometry.massBesselRoot]
  exact csqrt_eq_of_sq_of_re_pos_of_im_ne_zero him hvre hvsq

end RootFactorization

end

end GaloisForLFunctions.HTGeometry
