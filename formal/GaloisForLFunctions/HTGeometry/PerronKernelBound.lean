import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The smoothed-Perron kernel bound

Every smoothed-Perron contour argument in the corpus needs the same estimate for the second-order
kernel `1 / (s (s + 1))`, on three different contours: a vertical line in the right half-plane, a
horizontal segment at large height, and a deep vertical line `Re s = -M`.  All three are instances
of a single inequality:

  if a positive radius `r` bounds `‖s‖` and `‖s + 1‖` from below, then `‖(s (s+1))⁻¹‖ ≤ r⁻²`.

This file carries that law together with its three standard specialisations and the integrability
of the resulting reciprocal-quadratic majorant.  It is source-independent complex analysis, so it
lives in `HTGeometry` and is available to every contour file.
-/

open Complex MeasureTheory

namespace HTGeometry

/-- **The Perron kernel bound.**  A positive radius `r` bounding both `‖s‖` and `‖s + 1‖` from
below bounds the second-order Perron kernel by `r⁻²`.  Every contour estimate for `1/(s(s+1))`
in the corpus is this inequality with a contour-specific choice of `r`. -/
theorem norm_inv_mul_add_one_le {s : ℂ} {r : ℝ} (hr : 0 < r) (hs : r ≤ ‖s‖) (hs1 : r ≤ ‖s + 1‖) :
    ‖(s * (s + 1))⁻¹‖ ≤ (r ^ (2 : ℕ))⁻¹ := by
  have hge : r ^ (2 : ℕ) ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, sq]
    exact mul_le_mul hs hs1 hr.le (le_trans hr.le hs)
  rw [norm_inv]
  exact inv_anti₀ (by positivity) hge

/-- Kernel decay at large height: the displacement `s ↦ s + 1` does not change the imaginary part,
so `|Im s| ≥ T > 0` bounds both factors below by `T`. -/
theorem norm_inv_mul_add_one_le_of_abs_im {s : ℂ} {T : ℝ} (hT : 0 < T) (hs : T ≤ |s.im|) :
    ‖(s * (s + 1))⁻¹‖ ≤ (T ^ (2 : ℕ))⁻¹ := by
  have him1 : (s + 1).im = s.im := by rw [Complex.add_im, Complex.one_im, add_zero]
  refine norm_inv_mul_add_one_le hT (le_trans hs (Complex.abs_im_le_norm s)) (le_trans hs ?_)
  have h := Complex.abs_im_le_norm (s + 1)
  rwa [him1] at h

/-- Kernel decay on a horizontal segment at height `|t| ≥ T > 0`, in the explicit coordinates used
by the contour files. -/
theorem norm_inv_mul_add_one_le_of_line {t T : ℝ} (hT : 0 < T) (ht : T ≤ |t|) (x : ℝ) :
    ‖(((x : ℂ) + (t : ℂ) * I) * ((x : ℂ) + (t : ℂ) * I + 1))⁻¹‖ ≤ (T ^ (2 : ℕ))⁻¹ := by
  refine norm_inv_mul_add_one_le_of_abs_im hT ?_
  simpa using ht

/-- Kernel decay on the vertical line `Re s = c > 0`: here `‖s‖ = √(c²+t²)` is the smaller of the
two factors, because the shift `+1` moves away from the imaginary axis. -/
theorem norm_inv_mul_add_one_le_of_re_pos {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ ≤ (c ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹ := by
  have hnn : (0 : ℝ) ≤ c ^ (2 : ℕ) + t ^ (2 : ℕ) := by positivity
  have hA : ‖((c : ℂ) + (t : ℂ) * I)‖ = Real.sqrt (c ^ (2 : ℕ) + t ^ (2 : ℕ)) := Complex.norm_add_mul_I c t
  have hBeq : ((c : ℂ) + (t : ℂ) * I + 1) = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  have hB : ‖((c : ℂ) + (t : ℂ) * I + 1)‖ = Real.sqrt ((c + 1) ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
    rw [hBeq, Complex.norm_add_mul_I]
  have hpos : (0 : ℝ) < Real.sqrt (c ^ (2 : ℕ) + t ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hkey := norm_inv_mul_add_one_le (s := (c : ℂ) + (t : ℂ) * I)
    (r := Real.sqrt (c ^ (2 : ℕ) + t ^ (2 : ℕ))) hpos (le_of_eq hA.symm)
    (by rw [hB]; exact Real.sqrt_le_sqrt (by nlinarith))
  rwa [Real.sq_sqrt hnn] at hkey

/-- Kernel decay on the deep vertical line `Re s = -M` with `M > 1`: here `‖s + 1‖ = √((M−1)²+y²)`
is the smaller factor, because the shift `+1` moves toward the imaginary axis. -/
theorem norm_inv_mul_add_one_le_of_re_neg {M y : ℝ} (hM : 1 < M) :
    ‖((((-M : ℝ) : ℂ) + (y : ℂ) * I) * ((((-M : ℝ) : ℂ) + (y : ℂ) * I) + 1))⁻¹‖ ≤
      ((M - 1) ^ (2 : ℕ) + y ^ (2 : ℕ))⁻¹ := by
  have hnn : (0 : ℝ) ≤ (M - 1) ^ (2 : ℕ) + y ^ (2 : ℕ) := by positivity
  have hden : (0 : ℝ) < (M - 1) ^ (2 : ℕ) + y ^ (2 : ℕ) := by nlinarith [sq_nonneg y]
  have hA : ‖(((-M : ℝ) : ℂ) + (y : ℂ) * I)‖ = Real.sqrt ((-M) ^ (2 : ℕ) + y ^ (2 : ℕ)) :=
    Complex.norm_add_mul_I (-M) y
  have hBeq : ((((-M : ℝ) : ℂ) + (y : ℂ) * I) + 1) = ((1 - M : ℝ) : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  have hB : ‖((((-M : ℝ) : ℂ) + (y : ℂ) * I) + 1)‖ = Real.sqrt ((1 - M) ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    rw [hBeq, Complex.norm_add_mul_I]
  have hpos : (0 : ℝ) < Real.sqrt ((M - 1) ^ (2 : ℕ) + y ^ (2 : ℕ)) := Real.sqrt_pos.mpr hden
  have hkey := norm_inv_mul_add_one_le (s := ((-M : ℝ) : ℂ) + (y : ℂ) * I)
    (r := Real.sqrt ((M - 1) ^ (2 : ℕ) + y ^ (2 : ℕ))) hpos
    (by rw [hA]; exact Real.sqrt_le_sqrt (by nlinarith))
    (by rw [hB]; exact Real.sqrt_le_sqrt (by nlinarith))
  rwa [Real.sq_sqrt hnn] at hkey

/-- The reciprocal quadratic majorant produced by the kernel bound is Lebesgue integrable. -/
theorem integrable_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (a ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹) := by
  have hbase := integrable_inv_one_add_sq.comp_div ha.ne'
  have hscaled := hbase.const_mul (a⁻¹ ^ (2 : ℕ))
  refine hscaled.congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp
  field_simp

end HTGeometry
