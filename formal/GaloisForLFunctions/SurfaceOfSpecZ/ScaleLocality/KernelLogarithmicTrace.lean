import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveKernelLeakage
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveKernelConvolution
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaQuartetFilter
import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSeeEveryConfiguration

/-! Logarithmic absolute moments control the leakage of positive quartet
averages applied to the normalized zeta trace. -/

open MeasureTheory Complex
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower

/-- Positive kernels of logarithmic moment growth preserve a local floor of
the normalized zeta trace, with exponentially small leakage. -/
theorem zeta_kernel_logarithmic_floor {k : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hkc : Continuous k) (hk : ∀ x, 0 < k x)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|)
    (hb : ∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (s * |x|) * k x) ≤
      C * Real.exp ((s + 6) * Real.log (s + 6)))
    (α : ℝ) {K T B t : ℝ} (hK : 0 ≤ K) (hT : 6 ≤ T)
    (hbT : 1 / 2 + 2 * |α| ≤ T)
    (hE : 3 / 2 + |α| ≤ Real.log (T + 2)) (ht : |t| ≤ T + B)
    (hlocal : ∀ u, |u - t| ≤ 8 * Real.log (T + 2) →
      -K ≤ Real.exp (-α * u) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re)) :
    -K * (∫ x, Real.exp (α * x) * k x) -
      (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖) * C *
        Real.exp ((1 / 2 + |α|) * B - T) ≤
      ∑' z : ℂ, (evenCoeff zetaZeroConfig (boxSpline 1 3) z *
        sourceTransform (fun x => (k x : ℂ)) (I * z) *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
  let c : ℂ → ℂ := evenCoeff zetaZeroConfig (boxSpline 1 3)
  let A : ℝ := ∑' z, ‖c z‖
  let D : ℝ := 1 / 2 + |α|
  let b : ℝ := D + |α|
  let κ : ℝ → ℝ := fun x => Real.exp (α * x) * k x
  let F : ℝ → ℝ := fun u => Real.exp (-α * u) *
    (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb0 : 0 ≤ b := add_nonneg hD (abs_nonneg α)
  have hc := summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig
  have hw : ∀ z, c z ≠ 0 → |(z - (α : ℂ)).re| ≤ D :=
    fun z hz => configuration_shifted_exponent_bound α hz
  have hseries (u : ℝ) : F u = ∑' z, (c z * Complex.exp ((z - (α : ℂ)) * u)).re :=
    configuration_shifted_trace_series temperedConfig_zetaZeroConfig α u
  have hFc : Continuous F := by
    have hc := continuous_two_re_lagStructure temperedConfig_zetaZeroConfig
    dsimp [F]
    fun_prop
  have hFbound (u : ℝ) : |F u| ≤ A * Real.exp (D * |u|) := by
    rw [hseries]
    exact abs_cexp_series_le c (fun z => z - (α : ℂ)) hc hw u
  have hκc : Continuous κ := by dsimp [κ]; fun_prop
  have hκ (x : ℝ) : 0 < κ x := mul_pos (Real.exp_pos _) (hk x)
  have hκm (s : ℝ) : Integrable fun x => Real.exp (s * |x|) * |κ x| :=
    integrable_tilted_abs_moment hkc hm α s
  have hκi : Integrable κ := by
    simpa only [zero_mul, Real.exp_zero, one_mul, abs_of_pos (hκ _)] using hκm 0
  have hκT : Integrable fun x => Real.exp ((D + T) * |x|) * κ x := by
    simpa only [abs_of_pos (hκ _)] using hκm (D + T)
  have hFi : Integrable fun x => κ x * F (t + x) :=
    integrable_kernel_of_strip_bound (A := A)
      (by dsimp [A]; positivity) hD hFc hκc (hκm D) hFbound t
  have hmoment : (∫ x, Real.exp ((D + T) * |x|) * κ x) ≤
      C * Real.exp ((b + T + 6) * Real.log (b + T + 6)) := by
    have hh := tilted_abs_moment_le hkc hm α (D + T)
    change (∫ x, Real.exp ((D + T) * |x|) * |κ x|) ≤
      ∫ x, Real.exp ((D + T + |α|) * |x|) * |k x| at hh
    simp only [abs_of_pos (hκ _), abs_of_pos (hk _)] at hh
    have he : D + T + |α| = b + T := by dsimp [b]; ring
    rw [he] at hh
    exact hh.trans (hb (b + T) (by linarith only [hb0, hT]))
  have hfloor := positive_kernel_logarithmic_floor (F := F) (k := κ) (A := A)
    (by dsimp [A]; positivity) hC.le hb0
    (show b ≤ T by dsimp [b, D]; linarith only [hbT]) hD hK hT
    (show D + 1 ≤ Real.log (T + 2) by dsimp [D]; linarith only [hE]) ht
    (fun x => (hκ x).le) hκi hκT hFi hFbound hmoment
    (fun x hx => hlocal (t + x) (by simpa only [add_sub_cancel_left] using hx))
  have hconv : (∫ x, κ x * F (t + x)) =
      ∑' z : ℂ, (c z * sourceTransform (fun x => (k x : ℂ)) (I * z) *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
    simp_rw [hseries]
    rw [integral_kernel_cexp_tsum c (fun z => z - (α : ℂ)) hD hc hw hκc hκm t]
    apply tsum_congr
    intro z
    dsimp only [κ]
    rw [integral_tilt_cexp_shift, ← sourceTransform_I_mul_eq_laplace]
  rw [hconv] at hfloor
  exact hfloor

#print axioms zeta_kernel_logarithmic_floor
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
