import GaloisForLFunctions.HTGeometry.MassDispersionRadiationCorona
import GaloisForLFunctions.HTGeometry.MassDispersionUnitExpansion

/-!
# The outgoing expansion of the gauged mass dispersion

At the outgoing end the gauged dispersion is a shifted plane wave up to an explicit inverse power:

`ω_{a,λ}(η − r) = (r − η) + iλ + a²/(2(r − η + iλ)) + O(r^{-3})`.

The radicand is `z² + a²` with `z = (r − η) + iλ`, whose real part is `r − η > 0`, so the complex
principal-root expansion applies with the explicit remainder `a⁴/(4 Re z ‖z‖²)`.

Two consequences are recorded.  On a fixed band the increment of the dispersion is the increment of
the plane wave up to `O(r^{-2})`, which is what a wave packet of width `O(1)` at frequency `-r`
sees; and at the band centre the real part is `r + O(r^{-1})`, so a fixed real-time damping costs
only `e^{-σ r}`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The outgoing base point `z = -ξ + iλ` of the dispersion. -/
noncomputable def outgoingBase (lambda xi : ℝ) : ℂ := ((-xi : ℝ) : ℂ) + (lambda : ℂ) * Complex.I

@[simp] theorem outgoingBase_re (lambda xi : ℝ) : (outgoingBase lambda xi).re = -xi := by
  simp [outgoingBase]

@[simp] theorem outgoingBase_im (lambda xi : ℝ) : (outgoingBase lambda xi).im = lambda := by
  simp [outgoingBase]

theorem normSq_outgoingBase (lambda xi : ℝ) :
    ‖outgoingBase lambda xi‖ ^ 2 = xi ^ 2 + lambda ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, outgoingBase_re, outgoingBase_im]
  ring

theorem massGaugeRadicand_eq_outgoingBase (a lambda xi : ℝ) :
    massGaugeRadicand a lambda xi = outgoingBase lambda xi ^ 2 + ((a : ℝ) : ℂ) ^ 2 := by
  rw [massGaugeRadicand, outgoingBase]
  push_cast
  ring

/-- **(24.50) The outgoing expansion of the dispersion, with an explicit remainder.** -/
theorem norm_massGaugeDispersion_sub_le {a lambda xi : ℝ} (hxi : xi < 0) :
    ‖massGaugeDispersion a lambda xi
        - (outgoingBase lambda xi
          + ((a : ℝ) : ℂ) ^ 2 / (2 * outgoingBase lambda xi))‖
      ≤ a ^ 4 / (4 * (-xi) * (xi ^ 2 + lambda ^ 2)) := by
  have hre : 0 < (outgoingBase lambda xi).re := by
    rw [outgoingBase_re]
    linarith
  have hbase := norm_sqrt_sq_add_sq_sub_le (z := outgoingBase lambda xi) hre a
  rw [massGaugeDispersion, massGaugeRadicand_eq_outgoingBase]
  rw [outgoingBase_re, normSq_outgoingBase] at hbase
  exact hbase

theorem outgoingBase_shift (lambda r eta : ℝ) :
    outgoingBase lambda (eta - r) = (((r - eta : ℝ)) : ℂ) + (lambda : ℂ) * Complex.I := by
  rw [outgoingBase]
  push_cast
  ring

theorem outgoingBase_neg (lambda r : ℝ) :
    outgoingBase lambda (-r) = ((r : ℝ) : ℂ) + (lambda : ℂ) * Complex.I := by
  rw [outgoingBase]
  push_cast
  ring

theorem norm_outgoingBase_ge (lambda xi : ℝ) :
    -xi ≤ ‖outgoingBase lambda xi‖ := by
  have h := Complex.re_le_norm (outgoingBase lambda xi)
  rwa [outgoingBase_re] at h

/-- **(24.50) The band increment.**  On a band at the outgoing frequency `-r` the increment of the
dispersion is the increment of the plane wave up to `O(r^{-2})`. -/
theorem norm_massGaugeDispersion_increment_le {a lambda r eta : ℝ} (hr : 0 < r)
    (heta : 0 ≤ eta) (hetar : eta < r) :
    ‖massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r) + (eta : ℂ)‖
      ≤ a ^ 2 * eta / (2 * (r - eta) * r)
        + a ^ 4 / (4 * (r - eta) ^ 3) + a ^ 4 / (4 * r ^ 3) := by
  have hlt1 : eta - r < 0 := by linarith
  have hlt0 : (-r : ℝ) < 0 := by linarith
  have h1 := norm_massGaugeDispersion_sub_le (a := a) (lambda := lambda) hlt1
  have h0 := norm_massGaugeDispersion_sub_le (a := a) (lambda := lambda) hlt0
  set z1 : ℂ := outgoingBase lambda (eta - r) with hz1
  set z0 : ℂ := outgoingBase lambda (-r) with hz0
  have hz1re : z1.re = r - eta := by
    rw [hz1, outgoingBase_re]
    ring
  have hz0re : z0.re = r := by
    rw [hz0, outgoingBase_re]
    ring
  have hz1pos : (0 : ℝ) < r - eta := by linarith
  have hz1n : (r - eta : ℝ) ≤ ‖z1‖ := by
    have h := Complex.re_le_norm z1
    rwa [hz1re] at h
  have hz0n : (r : ℝ) ≤ ‖z0‖ := by
    have h := Complex.re_le_norm z0
    rwa [hz0re] at h
  have hz1ne : z1 ≠ 0 := by
    intro h
    rw [h] at hz1re
    simp at hz1re
    linarith
  have hz0ne : z0 ≠ 0 := by
    intro h
    rw [h] at hz0re
    simp at hz0re
    linarith
  have hdiff : z1 - z0 = -(eta : ℂ) := by
    rw [hz1, hz0, outgoingBase_shift, outgoingBase_neg]
    push_cast
    ring
  have hsplit : massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
      + (eta : ℂ)
      = (massGaugeDispersion a lambda (eta - r) - (z1 + ((a : ℝ) : ℂ) ^ 2 / (2 * z1)))
        - (massGaugeDispersion a lambda (-r) - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0)))
        + (((a : ℝ) : ℂ) ^ 2 / (2 * z1) - ((a : ℝ) : ℂ) ^ 2 / (2 * z0)) := by
    have : z1 - z0 + (eta : ℂ) = 0 := by
      rw [hdiff]
      ring
    linear_combination this
  have hmid : ‖((a : ℝ) : ℂ) ^ 2 / (2 * z1) - ((a : ℝ) : ℂ) ^ 2 / (2 * z0)‖
      ≤ a ^ 2 * eta / (2 * (r - eta) * r) := by
    have hval : ((a : ℝ) : ℂ) ^ 2 / (2 * z1) - ((a : ℝ) : ℂ) ^ 2 / (2 * z0)
        = ((a : ℝ) : ℂ) ^ 2 * (eta : ℂ) / (2 * z1 * z0) := by
      field_simp
      linear_combination (-(((a : ℝ) : ℂ) ^ 2)) * hdiff
    rw [hval, norm_div]
    have hnum : ‖((a : ℝ) : ℂ) ^ 2 * (eta : ℂ)‖ = a ^ 2 * eta := by
      rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg heta, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2)]
    have hden : ‖(2 : ℂ) * z1 * z0‖ = 2 * (‖z1‖ * ‖z0‖) := by
      rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      ring
    rw [hnum, hden]
    have hprod : (r - eta) * r ≤ ‖z1‖ * ‖z0‖ :=
      mul_le_mul hz1n hz0n (by linarith) (norm_nonneg _)
    have hX : (0 : ℝ) ≤ a ^ 2 * eta := by positivity
    have hcpos : (0 : ℝ) < 2 * (r - eta) * r := by positivity
    refine div_le_div_of_nonneg_left hX hcpos ?_
    nlinarith [hprod]
  have hE1 : ‖massGaugeDispersion a lambda (eta - r) - (z1 + ((a : ℝ) : ℂ) ^ 2 / (2 * z1))‖
      ≤ a ^ 4 / (4 * (r - eta) ^ 3) := by
    refine le_trans h1 ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg lambda, hz1pos, mul_pos hz1pos hz1pos]
  have hE0 : ‖massGaugeDispersion a lambda (-r) - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))‖
      ≤ a ^ 4 / (4 * r ^ 3) := by
    refine le_trans h0 ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg lambda, hr, mul_pos hr hr]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hfirst : ‖massGaugeDispersion a lambda (eta - r) - (z1 + ((a : ℝ) : ℂ) ^ 2 / (2 * z1))
      - (massGaugeDispersion a lambda (-r) - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0)))‖
      ≤ a ^ 4 / (4 * (r - eta) ^ 3) + a ^ 4 / (4 * r ^ 3) :=
    le_trans (norm_sub_le _ _) (add_le_add hE1 hE0)
  linarith [hfirst, hmid]


/-- **(24.51)** At the band centre the real part of the dispersion is `r + O(1/r)`, so a fixed
real-time damping costs only `e^{-σ r}` up to a bounded factor. -/
theorem massGaugeDispersion_re_le {a lambda r : ℝ} (hr : 0 < r) :
    (massGaugeDispersion a lambda (-r)).re ≤ r + a ^ 2 / (2 * r) + a ^ 4 / (4 * r ^ 3) := by
  have hlt : (-r : ℝ) < 0 := by linarith
  have hbound := norm_massGaugeDispersion_sub_le (a := a) (lambda := lambda) hlt
  set z0 : ℂ := outgoingBase lambda (-r) with hz0
  have hz0re : z0.re = r := by
    rw [hz0, outgoingBase_re]
    ring
  have hz0sq : ‖z0‖ ^ 2 = r ^ 2 + lambda ^ 2 := by
    rw [hz0, normSq_outgoingBase]
    ring
  have hz0pos : (0 : ℝ) < ‖z0‖ := by
    have := Complex.re_le_norm z0
    rw [hz0re] at this
    linarith
  have hdivre : (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).re = a ^ 2 * r / (2 * (r ^ 2 + lambda ^ 2)) := by
    have hns : Complex.normSq z0 = ‖z0‖ ^ 2 := Complex.normSq_eq_norm_sq z0
    rw [Complex.div_re]
    simp [Complex.normSq_mul, hns, hz0sq, hz0re, pow_two]
    field_simp
  have hsplit : (massGaugeDispersion a lambda (-r)).re
      = (massGaugeDispersion a lambda (-r) - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).re
        + z0.re + (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).re := by
    simp only [Complex.sub_re, Complex.add_re]
    ring
  have hre_le : (massGaugeDispersion a lambda (-r)
      - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).re ≤ a ^ 4 / (4 * r ^ 3) := by
    refine le_trans (Complex.re_le_norm _) (le_trans hbound ?_)
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg lambda, hr, mul_pos hr hr]
  have hdiv_le : a ^ 2 * r / (2 * (r ^ 2 + lambda ^ 2)) ≤ a ^ 2 / (2 * r) := by
    rw [div_le_div_iff₀ (by nlinarith [sq_nonneg lambda, mul_pos hr hr]) (by positivity)]
    nlinarith [sq_nonneg lambda, sq_nonneg a, hr]
  rw [hsplit, hz0re, hdivre]
  linarith [hre_le, hdiv_le]

/-- The real part of the dispersion at the band centre is at least `r`. -/
theorem le_massGaugeDispersion_re {a lambda : ℝ} (ha : lambda ≤ a) (hlambda : 0 ≤ lambda)
    {r : ℝ} (hr : 0 ≤ r) : r ≤ (massGaugeDispersion a lambda (-r)).re := by
  have h := abs_le_massGaugeDispersion_re ha hlambda (-r)
  rwa [abs_neg, abs_of_nonneg hr] at h


end GaloisForLFunctions.HTGeometry
