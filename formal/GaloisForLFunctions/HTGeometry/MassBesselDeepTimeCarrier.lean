import GaloisForLFunctions.HTGeometry.BesselOrderAbsoluteAsymptotic
import GaloisForLFunctions.HTGeometry.PrincipalSquareRootDeriv

/-!
# The massive radiation carrier at deep spectral time

The carrier of a single logarithmic frequency in the mass-Bessel aperture is

`B_a(t,x) = 2 a t K₁(a √(t²+x²)) / √(t²+x²)`.

Splitting the order-one Schläfli integral into its leading term and its remainder writes the
carrier as its deep-time profile `√(2πa) e^{-at}/√t` times an explicit distortion factor, plus a
remainder controlled by the modulus of the argument.  The distortion factor is a cube of a ratio of
principal square roots times an exponential of the root defect, so it is close to one exactly when
the root is close to the spectral parameter.
-/

open Complex

namespace HTGeometry

noncomputable section

/-! ## A square root with positive real part off the negative axis -/

theorem norm_add_re_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < ‖w‖ + w.re := by
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnn : 0 ≤ ‖w‖ := norm_nonneg w
  have him : 0 < w.im ^ 2 := by positivity
  nlinarith [hsq, hnn, him, sq_nonneg (‖w‖ + w.re), sq_nonneg (‖w‖ - w.re)]

theorem csqrtRe_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < csqrtRe w := by
  rw [csqrtRe]
  exact Real.sqrt_pos.mpr (by linarith [norm_add_re_pos_of_im_ne_zero hw])

theorem csqrt_re_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < (csqrt w).re := by
  rw [csqrt_re]
  exact csqrtRe_pos_of_im_ne_zero hw

theorem csqrt_sq_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : csqrt w ^ 2 = w := by
  have hp : 0 < csqrtRe w := csqrtRe_pos_of_im_ne_zero hw
  have hrad : 0 < ‖w‖ + w.re := norm_add_re_pos_of_im_ne_zero hw
  have hpsq : csqrtRe w ^ 2 = (‖w‖ + w.re) / 2 := by
    rw [csqrtRe, Real.sq_sqrt (by linarith)]
  have hnormsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hqsq : csqrtIm w ^ 2 = (‖w‖ - w.re) / 2 := by
    rw [csqrtIm, div_pow, mul_pow, hpsq]
    rw [div_eq_iff (by nlinarith [hrad] : ((2:ℝ) ^ 2 * ((‖w‖ + w.re) / 2)) ≠ 0)]
    nlinarith [hnormsq, hrad]
  have hprod : 2 * (csqrtRe w * csqrtIm w) = w.im := by
    rw [csqrtIm]
    field_simp
  apply Complex.ext
  · rw [pow_two, Complex.mul_re, csqrt_re, csqrt_im]
    nlinarith [hpsq, hqsq]
  · rw [pow_two, Complex.mul_im, csqrt_re, csqrt_im]
    nlinarith [hprod]

/-! ## The carrier and its deep-time profile -/

/-- The principal root of the mass shell. -/
def massBesselRoot (t : ℂ) (x : ℝ) : ℂ := csqrt (t ^ 2 + (x : ℂ) ^ 2)

/-- The massive radiation carrier of one logarithmic frequency. -/
def massBesselCarrier (a : ℝ) (t : ℂ) (x : ℝ) : ℂ :=
  2 * (a : ℂ) * t * besselK1C ((a : ℂ) * massBesselRoot t x) / massBesselRoot t x

/-- The deep-time profile of the carrier. -/
def massBesselLeading (a : ℝ) (t : ℂ) : ℂ :=
  ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * Complex.exp (-((a : ℂ) * t)) / csqrt t

/-- The remainder of the order-one Schläfli asymptotic at the shell argument. -/
def massBesselRemainder (a : ℝ) (t : ℂ) (x : ℝ) : ℂ :=
  besselK1C ((a : ℂ) * massBesselRoot t x)
    - Complex.exp (-((a : ℂ) * massBesselRoot t x)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
      * ((Real.pi : ℂ) / ((a : ℂ) * massBesselRoot t x)) ^ (1 / 2 : ℂ)

/-! ## The leading term in closed form -/

theorem cpow_half_pi_div_eq {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt Real.pi : ℝ) : ℂ) * (((Real.sqrt a : ℝ) : ℂ) * csqrt z)⁻¹ := by
  have haz : 0 < ((a : ℂ) * z).re := re_ofReal_mul_pos ha hz
  have hinv : 0 < (((a : ℂ) * z)⁻¹).re := re_inv_pos haz
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpre : 0 < ((Real.pi : ℂ) * ((a : ℂ) * z)⁻¹).re := re_ofReal_mul_pos hpi hinv
  have hrw : (Real.pi : ℂ) / ((a : ℂ) * z) = (Real.pi : ℂ) * ((a : ℂ) * z)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hrw, ← csqrt_eq_cpow_half hpre, csqrt_ofReal_mul hpi hinv, csqrt_inv haz,
    csqrt_ofReal_mul ha hz]

theorem sqrt_two_pi_mul (a : ℝ) (ha : 0 < a) :
    Real.sqrt 2 * Real.sqrt a * Real.sqrt Real.pi = Real.sqrt (2 * Real.pi * a) := by
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- Twice the mass times the Schläfli leading term is the deep-time profile of the carrier. -/
theorem two_mul_besselLeading_eq {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    2 * (a : ℂ) * (Complex.exp (-((a : ℂ) * z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ))
      = ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * Complex.exp (-((a : ℂ) * z)) / csqrt z := by
  have hcsz : csqrt z ≠ 0 := csqrt_ne_zero hz
  have hs2r : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have har : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs2r
  have hasne : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt har
  have hs2sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hasq : ((Real.sqrt a : ℝ) : ℂ) ^ 2 = (a : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  have hconst : ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, sqrt_two_pi_mul a ha]
  rw [cpow_half_pi_div_eq ha hz, hconst, Complex.ofReal_inv, ← hasq, ← hs2sq]
  field_simp

/-- The carrier splits into its deep-time profile, distorted by the root defect, plus the
remainder of the Schläfli asymptotic. -/
theorem massBesselCarrier_eq {a : ℝ} (ha : 0 < a) {t : ℂ} (ht : 0 < t.re) (x : ℝ)
    (hz : 0 < (massBesselRoot t x).re) :
    massBesselCarrier a t x
      = massBesselLeading a t *
          ((t / massBesselRoot t x) * (csqrt t / csqrt (massBesselRoot t x)) *
            Complex.exp (-((a : ℂ) * (massBesselRoot t x - t))))
        + 2 * (a : ℂ) * t * massBesselRemainder a t x / massBesselRoot t x := by
  set z : ℂ := massBesselRoot t x with hzdef
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hcsz : csqrt z ≠ 0 := csqrt_ne_zero hz
  have hcst : csqrt t ≠ 0 := csqrt_ne_zero ht
  have hcstsq : csqrt t ^ 2 = t := csqrt_sq ht
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  have hexp : Complex.exp (-((a : ℂ) * t)) * Complex.exp (-((a : ℂ) * (z - t)))
      = Complex.exp (-((a : ℂ) * z)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hkey := two_mul_besselLeading_eq ha hz
  have hsplit : massBesselCarrier a t x
      = t / z * (2 * (a : ℂ) * (Complex.exp (-((a : ℂ) * z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * ((Real.pi : ℂ) / ((a : ℂ) * z)) ^ (1 / 2 : ℂ)))
        + 2 * (a : ℂ) * t * massBesselRemainder a t x / z := by
    rw [massBesselCarrier, massBesselRemainder, ← hzdef]
    field_simp
    ring
  rw [hsplit, hkey, massBesselLeading, ← hexp]
  field_simp

/-! ## Geometry of the mass-shell root -/

theorem massShell_im (t : ℂ) (x : ℝ) : (t ^ 2 + (x : ℂ) ^ 2).im = 2 * t.re * t.im := by
  simp [pow_two, Complex.add_im, Complex.mul_im]
  ring

theorem massShell_im_ne_zero {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    (t ^ 2 + (x : ℂ) ^ 2).im ≠ 0 := by
  rw [massShell_im]
  positivity

theorem massBesselRoot_sq {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    massBesselRoot t x ^ 2 = t ^ 2 + (x : ℂ) ^ 2 :=
  csqrt_sq_of_im_ne_zero (massShell_im_ne_zero htre htim x)

theorem massBesselRoot_re_pos {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    0 < (massBesselRoot t x).re :=
  csqrt_re_pos_of_im_ne_zero (massShell_im_ne_zero htre htim x)

theorem massBesselRoot_im_pos {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    0 < (massBesselRoot t x).im := by
  rw [massBesselRoot, csqrt_im, csqrtIm]
  have hp : 0 < csqrtRe (t ^ 2 + (x : ℂ) ^ 2) :=
    csqrtRe_pos_of_im_ne_zero (massShell_im_ne_zero htre htim x)
  have hnum : 0 < (t ^ 2 + (x : ℂ) ^ 2).im := by
    rw [massShell_im]
    positivity
  positivity

/-- The root differs from the spectral parameter by at most the square of the frequency over the
spectral height. -/
theorem norm_massBesselRoot_sub_le {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    ‖massBesselRoot t x - t‖ ≤ x ^ 2 / t.im := by
  set z : ℂ := massBesselRoot t x with hzdef
  have hzim : 0 < z.im := massBesselRoot_im_pos htre htim x
  have hzsq : z ^ 2 = t ^ 2 + (x : ℂ) ^ 2 := massBesselRoot_sq htre htim x
  have hsum : 0 < (z + t).im := by
    rw [Complex.add_im]
    linarith
  have hsumne : z + t ≠ 0 := by
    intro h
    rw [h] at hsum
    simp at hsum
  have hnormsum : t.im ≤ ‖z + t‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm (z + t))
    rw [Complex.add_im] at hsum ⊢
    rw [abs_of_pos hsum]
    linarith
  have hprod : (z - t) * (z + t) = (x : ℂ) ^ 2 := by
    have : (z - t) * (z + t) = z ^ 2 - t ^ 2 := by ring
    rw [this, hzsq]
    ring
  have hnormprod : ‖z - t‖ * ‖z + t‖ = x ^ 2 := by
    rw [← norm_mul, hprod, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hsumpos : (0 : ℝ) < ‖z + t‖ := lt_of_lt_of_le htim hnormsum
  rw [le_div_iff₀ htim]
  calc ‖z - t‖ * t.im ≤ ‖z - t‖ * ‖z + t‖ :=
        mul_le_mul_of_nonneg_left hnormsum (norm_nonneg _)
    _ = x ^ 2 := hnormprod

theorem massBesselRoot_re_ge {t : ℂ} (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    t.re - x ^ 2 / t.im ≤ (massBesselRoot t x).re := by
  set z : ℂ := massBesselRoot t x with hzdef
  have h := norm_massBesselRoot_sub_le htre htim x
  have hre : |(z - t).re| ≤ ‖z - t‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at hre
  have := abs_le.mp hre
  linarith [this.1, h]

/-! ## Norms of the profile and the remainder -/

theorem re_neg_ofReal_mul (a : ℝ) (t : ℂ) : (-((a : ℂ) * t)).re = -(a * t.re) := by
  simp [Complex.mul_re]

theorem norm_massBesselLeading {t : ℂ} (a : ℝ) (ht : 0 < t.re) :
    ‖massBesselLeading a t‖
      = Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * t.re)) / Real.sqrt ‖t‖ := by
  rw [massBesselLeading, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp, norm_csqrt ht, re_neg_ofReal_mul]

theorem norm_massBesselRemainder_le {a : ℝ} (ha : 0 < a) {t : ℂ}
    (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) :
    ‖massBesselRemainder a t x‖
      ≤ Real.exp (-(a * (massBesselRoot t x).re))
        * Real.sqrt (Real.pi / (a * (massBesselRoot t x).re))
        / (a * ‖massBesselRoot t x‖) := by
  have hz : 0 < (massBesselRoot t x).re := massBesselRoot_re_pos htre htim x
  have hw : 0 < ((a : ℂ) * massBesselRoot t x).re := re_ofReal_mul_pos ha hz
  have h := norm_besselK1C_sub_leading_le_norm hw
  have hre : ((a : ℂ) * massBesselRoot t x).re = a * (massBesselRoot t x).re := by
    simp [Complex.mul_re]
  have hnorm : ‖(a : ℂ) * massBesselRoot t x‖ = a * ‖massBesselRoot t x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [hre, hnorm] at h
  exact h

/-! ## The deep-time estimate -/

/-- The carrier is its deep-time profile up to a relative distortion built from the root defect,
plus the Schläfli remainder. -/
theorem norm_massBesselCarrier_sub_leading_le {a : ℝ} (ha : 0 < a) {t : ℂ}
    (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ) {α β γ : ℝ}
    (hα : ‖massBesselRoot t x - t‖ / ‖massBesselRoot t x‖ ≤ α)
    (hβ : ‖csqrt t - csqrt (massBesselRoot t x)‖ / ‖csqrt (massBesselRoot t x)‖ ≤ β)
    (hβ1 : β ≤ 1)
    (hγ : 2 * (a * ‖massBesselRoot t x - t‖) ≤ γ) (hγ1 : γ ≤ 1)
    (hexpsmall : a * ‖massBesselRoot t x - t‖ ≤ 1) :
    ‖massBesselCarrier a t x - massBesselLeading a t‖
      ≤ ‖massBesselLeading a t‖ * (4 * α + 2 * β + γ)
        + 2 * a * ‖t‖ * ‖massBesselRemainder a t x‖ / ‖massBesselRoot t x‖ := by
  set z : ℂ := massBesselRoot t x with hzdef
  have hz : 0 < z.re := massBesselRoot_re_pos htre htim x
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hcsz : csqrt z ≠ 0 := csqrt_ne_zero hz
  have hcst : csqrt t ≠ 0 := csqrt_ne_zero htre
  have heq := massBesselCarrier_eq ha htre x hz
  have hsub : massBesselCarrier a t x - massBesselLeading a t
      = massBesselLeading a t *
          ((t / z) * (csqrt t / csqrt z) * Complex.exp (-((a : ℂ) * (z - t))) - 1)
        + 2 * (a : ℂ) * t * massBesselRemainder a t x / z := by
    rw [heq]
    ring
  have hA : ‖t / z - 1‖ ≤ α := by
    have hval : t / z - 1 = -((z - t) / z) := by
      field_simp
      ring
    rw [hval, norm_neg, norm_div]
    exact hα
  have hB : ‖csqrt t / csqrt z - 1‖ ≤ β := by
    have hval : csqrt t / csqrt z - 1 = (csqrt t - csqrt z) / csqrt z := by
      field_simp
    rw [hval, norm_div]
    exact hβ
  have hC : ‖Complex.exp (-((a : ℂ) * (z - t))) - 1‖ ≤ γ := by
    have hnorm : ‖-((a : ℂ) * (z - t))‖ = a * ‖z - t‖ := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    refine le_trans (Complex.norm_exp_sub_one_le (by rw [hnorm]; exact hexpsmall)) ?_
    rw [hnorm]
    exact hγ
  have hG := norm_mul3_sub_one_le hA hB hC hβ1 hγ1
  rw [hsub]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hG (norm_nonneg _)
  · rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    simp

/-- The principal square root is Lipschitz with constant the reciprocal of one root's real part. -/
theorem norm_csqrt_sub_le {t z : ℂ} (ht : 0 < t.re) (hz : 0 < z.re) :
    ‖csqrt t - csqrt z‖ ≤ ‖t - z‖ / (csqrt t).re := by
  have hcstre : 0 < (csqrt t).re := by rw [csqrt_re]; exact csqrtRe_pos ht
  have hcszre : 0 < (csqrt z).re := by rw [csqrt_re]; exact csqrtRe_pos hz
  have hsumre : 0 < (csqrt t + csqrt z).re := by
    rw [Complex.add_re]
    linarith
  have hsum : (csqrt t).re ≤ ‖csqrt t + csqrt z‖ := by
    refine le_trans ?_ (Complex.re_le_norm (csqrt t + csqrt z))
    rw [Complex.add_re]
    linarith
  have hprod : (csqrt t - csqrt z) * (csqrt t + csqrt z) = t - z := by
    have h1 : csqrt t ^ 2 = t := csqrt_sq ht
    have h2 : csqrt z ^ 2 = z := csqrt_sq hz
    have : (csqrt t - csqrt z) * (csqrt t + csqrt z) = csqrt t ^ 2 - csqrt z ^ 2 := by ring
    rw [this, h1, h2]
  have hnorm : ‖csqrt t - csqrt z‖ * ‖csqrt t + csqrt z‖ = ‖t - z‖ := by
    rw [← norm_mul, hprod]
  rw [le_div_iff₀ hcstre]
  calc ‖csqrt t - csqrt z‖ * (csqrt t).re
      ≤ ‖csqrt t - csqrt z‖ * ‖csqrt t + csqrt z‖ :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖t - z‖ := hnorm

end

end HTGeometry
