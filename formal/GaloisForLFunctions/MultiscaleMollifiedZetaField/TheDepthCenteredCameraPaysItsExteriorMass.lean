import GaloisForLFunctions.MultiscaleMollifiedZetaField.OnlyComparablyDeepZerosCompete
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# Depth centering pays the exterior camera mass

Tilt the camera by the negative of the actual zero width. Every zero then
has nonpositive relative depth. For a camera supported at positive lags,
its transform is bounded by a Lorentzian kernel with no exponential
amplification. Beyond any fixed ordinate gap, the entire exterior mass
is bounded by the unit-scale zero mass divided by the squared camera width.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open ZeroConfigurationGeometry (tilt)

/-- The camera with its exponential growth measured relative to depth `b`. -/
def depthCenteredCamera (v : ℝ → ℝ) (b δ y : ℝ) : ℝ → ℂ :=
  tilt (-b) (cameraTest v δ y)

private theorem tilt_add (a b : ℝ) (f : ℝ → ℂ) :
    tilt a (tilt b f) = tilt (a + b) f := by
  funext u
  simp only [tilt]
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Centering the camera shifts every zero by the same real depth. -/
theorem paperFT_depthCenteredCamera (v : ℝ → ℝ) (b δ y t : ℝ) (ρ : ℂ) :
    paperFT (depthCenteredCamera v b δ y) (gammaOf ρ - t) =
      paperFT (cameraTest v δ y) (gammaOf (ρ - (b : ℂ)) - t) := by
  have harg (z : ℂ) : gammaOf z - (t : ℂ) =
      (((z.im - t : ℝ) : ℂ)) - I * ((z.re - 1 / 2 : ℝ) : ℂ) := by
    rw [ZeroConfigurationGeometry.gammaOf_eq, ZeroConfigurationGeometry.depth]
    push_cast
    ring
  rw [depthCenteredCamera, harg ρ,
    ZeroConfigurationGeometry.paperFT_sub_I_mul_eq_tilt,
    tilt_add, harg (ρ - (b : ℂ)),
    ZeroConfigurationGeometry.paperFT_sub_I_mul_eq_tilt]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
  congr 2
  ring

/-- A zero below the centering depth has no exponential amplification at
positive lags. -/
theorem norm_paperFT_depthCenteredCamera_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {b δ y t : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) {ρ : ℂ}
    (hρ : ρ.re - 1 / 2 ≤ b) :
    ‖paperFT (depthCenteredCamera v b δ y) (gammaOf ρ - t)‖ ≤
      profileMass v * lorentzKernel δ (ρ.im - t) := by
  rw [paperFT_depthCenteredCamera]
  have h := norm_paperFT_companion_le hv hsupp hδ y t (ρ - (b : ℂ))
  have hb : (ρ - (b : ℂ)).re - 1 / 2 ≤ 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [hρ]
  have he : ((ρ - (b : ℂ)).re - 1 / 2) * y +
      |(ρ - (b : ℂ)).re - 1 / 2| * δ ≤ 0 := by
    rw [abs_of_nonpos hb]
    nlinarith only [hb, hy]
  have hk := companionWeight_le_of_exponent (t := t) he
  simp only [Real.exp_zero, one_mul, Complex.sub_im, Complex.ofReal_im, sub_zero] at hk
  exact h.trans (mul_le_mul_of_nonneg_left hk (profileMass_nonneg v))

/-- The actual zero width supplies the centering bound for every zero,
without a zero-free half-plane hypothesis. -/
theorem norm_paperFT_widthCenteredCamera_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) (ρ : zetaZeroConfig.carrier) :
    ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖ ≤
      profileMass v * lorentzKernel δ ((ρ : ℂ).im - t) := by
  apply norm_paperFT_depthCenteredCamera_le hv hsupp hδ hy
  exact (le_abs_self _).trans
    (SquareRootThreshold.abs_re_sub_half_le_zetaZeroWidth ρ.2)

/-- Beyond distance `g`, a narrow Lorentzian kernel is dominated by the
unit-scale kernel with factor `(1+g²)/(δ²g²)`. -/
theorem lorentzKernel_le_unit_of_gap {δ g d : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hd : g ≤ |d|) :
    lorentzKernel δ d ≤ ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) * (1 / (1 + d ^ 2)) := by
  have hsq : g ^ 2 ≤ d ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hg.le hd 2
  have hprod : 0 ≤ δ ^ 2 * (d ^ 2 - g ^ 2) :=
    mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hsq)
  unfold lorentzKernel
  rw [← div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith only [hprod, sq_nonneg g]

/-- All exterior zeros are paid by the known unit-scale Lorentzian mass.
There is no assumption on their number or their depths. -/
theorem sum_widthCenteredCamera_exterior_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t g : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) (hg : 0 < g)
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖) ≤
      profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) * lorentzMass t := by
  have hC : 0 ≤ (1 + g ^ 2) / (δ ^ 2 * g ^ 2) := by positivity
  have hsum := sum_mult_unit_le_lorentzMass t (F.image Subtype.val)
    (fun ρ hρ => by obtain ⟨ρ', _, rfl⟩ := Finset.mem_image.mp hρ; exact ρ'.2)
  rw [Finset.sum_image Subtype.val_injective.injOn] at hsum
  have hterm (ρ : zetaZeroConfig.carrier) (hρ : ρ ∈ F) :
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖ ≤
      (profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2))) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by
    have h := (norm_paperFT_widthCenteredCamera_le hv hsupp hδ hy ρ).trans
      (mul_le_mul_of_nonneg_left (lorentzKernel_le_unit_of_gap hδ hg (hgap ρ hρ))
        (profileMass_nonneg v))
    have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (zetaZeroConfig.mult ρ))
    have he : ((ρ : ℂ).im - t) ^ 2 = (t - (ρ : ℂ).im) ^ 2 := by ring
    rw [he] at hm
    convert hm using 1 <;> ring
  calc
    _ ≤ ∑ ρ ∈ F, (profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2))) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) :=
      Finset.sum_le_sum hterm
    _ = (profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2))) *
        ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg (profileMass_nonneg v) hC)

/-- The exterior estimate has an explicit logarithmic majorant. -/
theorem sum_widthCenteredCamera_exterior_le_log
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t g : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) (hg : 0 < g)
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖) ≤
      profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))) :=
  (sum_widthCenteredCamera_exterior_le hv hsupp hδ hy hg F hgap).trans
    (mul_le_mul_of_nonneg_left (lorentzMass_le_log t)
      (mul_nonneg (profileMass_nonneg v) (by positivity)))

end GaloisForLFunctions.MultiscaleMollifiedZetaField
