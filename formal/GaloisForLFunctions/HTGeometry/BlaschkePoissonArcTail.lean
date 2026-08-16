import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGroupDelay

/-!
# The boundary tail of a radial Blaschke section

For a Blaschke section whose zero sits at the radial point `r ζ` with `ζ` on the unit circle, the
squared distance from a boundary point `z` splits exactly:

`‖z - r ζ‖² = (1 - r)² + r ‖z - ζ‖²`,

the radial defect plus the boundary separation.  Consequently the boundary group delay away from
`ζ` is at most `(1 - r²) / (r d²)` at separation `d`: a section of small radial depth concentrates
essentially all of its phase in an arbitrarily small arc about `ζ`, and the phase it spends outside
that arc is controlled by the radial depth alone.

This is the quantitative form of the statement that the total phase of a deep Blaschke section is
recovered, up to `O((1 - r)/d²)`, on any fixed arc about its centre.

The same squared distance appears in `SzegoOuterBoundary.norm_sub_circleMap_sq` in the polar normal
form `r² - 2r cos(θ-φ) + 1`; the radial-defect form used here is what makes the tail bound
algebraic.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **Radial split of the boundary distance.**  For unit `ζ` and `z` the squared distance from `z`
to the radial point `r ζ` is the radial defect plus `r` times the boundary separation. -/
theorem norm_sub_radial_sq {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1) (r : ℝ) :
    ‖z - (r : ℂ) * ζ‖ ^ 2 = (1 - r) ^ 2 + r * ‖z - ζ‖ ^ 2 := by
  have hnz : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hnζ : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ]; norm_num
  have hL : ‖z - (r : ℂ) * ζ‖ ^ 2 = Complex.normSq (z - (r : ℂ) * ζ) :=
    (Complex.normSq_eq_norm_sq _).symm
  have hR : ‖z - ζ‖ ^ 2 = Complex.normSq (z - ζ) := (Complex.normSq_eq_norm_sq _).symm
  rw [hL, hR, Complex.normSq_sub, Complex.normSq_sub, hnz, hnζ]
  have hmul : Complex.normSq ((r : ℂ) * ζ) = r ^ 2 := by
    rw [Complex.normSq_mul, hnζ, Complex.normSq_ofReal]
    ring
  have hre : (z * (starRingEnd ℂ) ((r : ℂ) * ζ)).re = r * (z * (starRingEnd ℂ) ζ).re := by
    rw [map_mul, Complex.conj_ofReal]
    have : z * ((r : ℂ) * (starRingEnd ℂ) ζ) = (r : ℂ) * (z * (starRingEnd ℂ) ζ) := by ring
    rw [this, Complex.mul_re]
    simp
  rw [hmul, hre]
  ring

/-- The Poisson kernel of a radial disc point at a boundary point, in split form. -/
theorem poissonKernel_radial_eq {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    poissonKernel 0 ((r : ℂ) * ζ) z = (1 - r ^ 2) / ((1 - r) ^ 2 + r * ‖z - ζ‖ ^ 2) := by
  have hw : ‖(r : ℂ) * ζ‖ = r := by
    rw [norm_mul, hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
  rw [poissonKernel_def]
  simp only [sub_zero]
  rw [hz, hw, norm_sub_radial_sq hζ hz r]
  norm_num

/-- **Arc tail bound.**  Away from its centre the boundary group delay of a radial Blaschke section
is controlled by the radial depth alone. -/
theorem poissonKernel_radial_le {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    {r d : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hzd : d ≤ ‖z - ζ‖) :
    poissonKernel 0 ((r : ℂ) * ζ) z ≤ (1 - r ^ 2) / (r * d ^ 2) := by
  rw [poissonKernel_radial_eq hζ hz hr0.le]
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hd2 : d ^ 2 ≤ ‖z - ζ‖ ^ 2 := by nlinarith [norm_nonneg (z - ζ)]
  have hden : 0 < r * d ^ 2 := by positivity
  refine div_le_div_of_nonneg_left hnum hden ?_
  nlinarith [sq_nonneg (1 - r)]

/-- The tail bound in radial-depth form: a section of depth `1 - r` spends at most
`2 (1 - r) / (r d²)` of its boundary phase rate at separation `d`. -/
theorem poissonKernel_radial_le_depth {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    {r d : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hzd : d ≤ ‖z - ζ‖) :
    poissonKernel 0 ((r : ℂ) * ζ) z ≤ 2 * (1 - r) / (r * d ^ 2) := by
  refine (poissonKernel_radial_le hζ hz hr0 hr1 hd hzd).trans ?_
  have hden : 0 < r * d ^ 2 := by positivity
  refine div_le_div_of_nonneg_right ?_ hden.le
  nlinarith

end GaloisForLFunctions.HTGeometry
