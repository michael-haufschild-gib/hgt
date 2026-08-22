import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.LineScalingL2

/-!
# The exact isometry constant on the `w = σ + i y` parametrisation

`HalfLineLaplaceFourier` computes the mass of a Hardy function on the vertical line in the
*frequency* parametrisation `rayLine σ ξ = σ + 2πiξ`, where the Fourier--Plancherel identity has no
constant.  Burnol's normalisation is the arclength one, `w = σ + i y` with `|dw|/2π`.  The change of
variables `y = 2πξ` supplies the missing `2π`, and with it the Paley--Wiener isometry becomes exact:

`∫_ℝ ‖𝓛φ(σ + iy)‖² dy = 2π ∫_0^∞ e^{-2σx}‖φ(x)‖² dx  ↑  2π ∫_0^∞ ‖φ(x)‖² dx`   as `σ ↓ 0`.

## Main results

* `hardyVerticalLine`, `rayLine_eq_hardyVerticalLine`
* `integral_norm_sq_vertical_eq` — the `2π` conversion, for an arbitrary function
* `integral_norm_sq_laplaceRay_vertical` — Plancherel in the arclength normalisation
* `tendsto_integral_norm_sq_laplaceRay_vertical` — the boundary limit
* `isHalfPlaneHardy_integral_norm_sq_vertical_eq` — the isometry for a Hardy function, through its
  Paley--Wiener datum
* `norm_le_of_isHalfPlaneHardy` — a Hardy function is bounded on each closed sub-half-plane
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The vertical line in the arclength parametrisation `w = σ + i y`. -/
def hardyVerticalLine (σ y : ℝ) : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem hardyVerticalLine_re (σ y : ℝ) : (hardyVerticalLine σ y).re = σ := by
  simp [hardyVerticalLine]

theorem rayLine_eq_hardyVerticalLine (σ y : ℝ) :
    rayLine σ ((2 * Real.pi)⁻¹ * y) = hardyVerticalLine σ y := by
  rw [rayLine, hardyVerticalLine]
  congr 2
  push_cast
  field_simp

theorem memLp_two_vertical {F : ℂ → ℂ} {σ : ℝ}
    (hF : MemLp (fun ξ : ℝ => F (rayLine σ ξ)) 2 volume) :
    MemLp (fun y : ℝ => F (hardyVerticalLine σ y)) 2 volume := by
  have hne : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by positivity
  have h := memLp_two_comp_const_mul hF hne
  refine h.ae_eq ?_
  filter_upwards with y
  rw [rayLine_eq_hardyVerticalLine]

/-- **The `2π` of the arclength normalisation.** -/
theorem integral_norm_sq_vertical_eq (F : ℂ → ℂ) (σ : ℝ) :
    (∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2)
      = 2 * Real.pi * ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2 := by
  have hcomp : (∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2)
      = ∫ y : ℝ, ‖F (rayLine σ ((2 * Real.pi)⁻¹ * y))‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [rayLine_eq_hardyVerticalLine]
  rw [hcomp, integral_norm_sq_comp_const_mul (fun ξ : ℝ => F (rayLine σ ξ)) ((2 * Real.pi)⁻¹)]
  have hpos : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  rw [abs_of_pos hpos, inv_inv]

/-- **Plancherel on the vertical line, arclength normalisation.** -/
theorem integral_norm_sq_laplaceRay_vertical {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    (∫ y : ℝ, ‖laplaceRay φ (hardyVerticalLine σ y)‖ ^ 2)
      = 2 * Real.pi * ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2 := by
  rw [integral_norm_sq_vertical_eq, integral_norm_sq_laplaceRay_line hφ hσ]

/-- **The boundary limit of the mass.**  The exact Paley--Wiener isometry constant is `2π`. -/
theorem tendsto_integral_norm_sq_laplaceRay_vertical {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, ‖laplaceRay φ (hardyVerticalLine σ y)‖ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Real.pi * ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2)) := by
  have hev : (fun σ : ℝ => 2 * Real.pi * ∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] fun σ : ℝ => ∫ y : ℝ, ‖laplaceRay φ (hardyVerticalLine σ y)‖ ^ 2 := by
    filter_upwards with σ
    exact (integral_norm_sq_vertical_eq (laplaceRay φ) σ).symm
  refine Tendsto.congr' hev ?_
  exact (tendsto_integral_norm_sq_laplaceRay_line hφ).const_mul _

/-- **The Paley--Wiener isometry for a Hardy function.**  Its mass on the line `Re w = σ`, measured
with arclength, is `2π` times the exponentially damped mass of its datum. -/
theorem isHalfPlaneHardy_integral_norm_sq_vertical_eq {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) {σ : ℝ} (hσ : 0 < σ) :
    (∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2)
      = 2 * Real.pi * ∫ x in Ioi (0 : ℝ),
          Real.exp (-(2 * σ * x)) * ‖hardyDatum F hF x‖ ^ 2 := by
  have hcongr : (∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2)
      = ∫ y : ℝ, ‖laplaceRay (hardyDatum F hF) (hardyVerticalLine σ y)‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [isHalfPlaneHardy_eq_laplaceRay hF (w := hardyVerticalLine σ y) (by simpa using hσ)]
  rw [hcongr, integral_norm_sq_laplaceRay_vertical (memLp_two_hardyDatum hF) hσ]

/-- **The boundary isometry.**  As the line approaches the boundary the arclength mass of a Hardy
function increases to `2π` times the mass of its datum. -/
theorem tendsto_isHalfPlaneHardy_integral_norm_sq_vertical {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * Real.pi * ∫ x in Ioi (0 : ℝ), ‖hardyDatum F hF x‖ ^ 2)) := by
  have hev : (fun σ : ℝ => ∫ y : ℝ, ‖laplaceRay (hardyDatum F hF) (hardyVerticalLine σ y)‖ ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] fun σ : ℝ => ∫ y : ℝ, ‖F (hardyVerticalLine σ y)‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [isHalfPlaneHardy_eq_laplaceRay hF (w := hardyVerticalLine σ y) (by simpa using hσ)]
  refine Tendsto.congr' hev ?_
  exact tendsto_integral_norm_sq_laplaceRay_vertical (memLp_two_hardyDatum hF)

/-- **A Hardy function is bounded away from the boundary.**  This is the pointwise estimate that
Burnol's Theorem 4.8 feeds into Phragmén--Lindelöf. -/
theorem norm_le_of_isHalfPlaneHardy {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {w : ℂ} (hw : 0 < w.re) :
    ‖F w‖ ≤ rayL2Norm (hardyDatum F hF) / Real.sqrt (2 * w.re) := by
  rw [isHalfPlaneHardy_eq_laplaceRay hF hw]
  exact norm_laplaceRay_le (memLp_two_hardyDatum hF) hw

end GaloisForLFunctions.HTGeometry

end
