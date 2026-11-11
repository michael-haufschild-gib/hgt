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

open SquareRootThreshold (zetaZeroWidth)
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

/-- Zeros a fixed distance below the centering depth are exponentially
suppressed, including those arbitrarily close in ordinate. -/
theorem norm_paperFT_depthCenteredCamera_le_of_shallow
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {b δ y t d : ℝ} (hδ : 0 < δ) (hy : δ ≤ y) (hd : 0 ≤ d) {ρ : ℂ}
    (hρ : ρ.re - 1 / 2 ≤ b - d) :
    ‖paperFT (depthCenteredCamera v b δ y) (gammaOf ρ - t)‖ ≤
      profileMass v * Real.exp (-(d * (y - δ))) * lorentzKernel δ (ρ.im - t) := by
  rw [paperFT_depthCenteredCamera]
  have h := norm_paperFT_companion_le hv hsupp hδ y t (ρ - (b : ℂ))
  have hb : (ρ - (b : ℂ)).re - 1 / 2 ≤ -d := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [hρ]
  have hb0 : (ρ - (b : ℂ)).re - 1 / 2 ≤ 0 := hb.trans (neg_nonpos.mpr hd)
  have he : ((ρ - (b : ℂ)).re - 1 / 2) * y +
      |(ρ - (b : ℂ)).re - 1 / 2| * δ ≤ -(d * (y - δ)) := by
    rw [abs_of_nonpos hb0]
    have hh := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hy)
    nlinarith only [hh]
  have hk := companionWeight_le_of_exponent (t := t) he
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hk
  exact (h.trans (mul_le_mul_of_nonneg_left hk (profileMass_nonneg v))).trans_eq
    (by ring)

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
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
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

/-- Only the deep exterior zeros need an ordinate gap. Shallow zeros are
paid by exponential damping, with their full multiplicities retained. -/
theorem sum_widthCenteredCamera_exterior_le_deep_gap
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t g d : ℝ} (hδ : 1 ≤ δ) (hy : δ ≤ y) (hg : 0 < g) (hd : 0 ≤ d)
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2 →
      g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖) ≤
      profileMass v * (((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) +
        Real.exp (-(d * (y - δ)))) * lorentzMass t := by
  classical
  let P := fun ρ : zetaZeroConfig.carrier => zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2
  have hδ0 : 0 < δ := one_pos.trans_le hδ
  have hdeep := sum_widthCenteredCamera_exterior_le hv hsupp hδ0 hy hg (F.filter P)
    (fun ρ hρ => hgap ρ (Finset.mem_filter.mp hρ).1 (Finset.mem_filter.mp hρ).2)
  have hshallow : (∑ ρ ∈ F.filter (fun ρ => ¬ P ρ), (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖) ≤
      (profileMass v * Real.exp (-(d * (y - δ)))) * lorentzMass t := by
    let G := F.filter (fun ρ => ¬ P ρ)
    have hmass := sum_mult_unit_le_lorentzMass t (G.image Subtype.val)
      (fun ρ hρ => by obtain ⟨ρ', _, rfl⟩ := Finset.mem_image.mp hρ; exact ρ'.2)
    rw [Finset.sum_image Subtype.val_injective.injOn] at hmass
    have hterm (ρ : zetaZeroConfig.carrier) (hρ : ρ ∈ G) :
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)‖ ≤
        (profileMass v * Real.exp (-(d * (y - δ)))) *
          ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by
      have hp : (ρ : ℂ).re - 1 / 2 ≤ zetaZeroWidth - d :=
        (not_le.mp (Finset.mem_filter.mp hρ).2).le
      have hn := norm_paperFT_depthCenteredCamera_le_of_shallow hv hsupp hδ0 hy hd hp
      have hk : lorentzKernel δ ((ρ : ℂ).im - t) ≤ 1 / (1 + (t - (ρ : ℂ).im) ^ 2) := by
        unfold lorentzKernel
        apply one_div_le_one_div_of_le (by positivity)
        have hs : 1 ≤ δ ^ 2 := by nlinarith only [hδ]
        have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg ((ρ : ℂ).im - t))
        nlinarith only [hh]
      have h := mul_le_mul_of_nonneg_left
        (hn.trans (mul_le_mul_of_nonneg_left hk
          (mul_nonneg (profileMass_nonneg v) (Real.exp_pos _).le)))
        (Nat.cast_nonneg (zetaZeroConfig.mult ρ))
      convert h using 1 <;> ring
    calc
      _ ≤ ∑ ρ ∈ G, (profileMass v * Real.exp (-(d * (y - δ)))) *
          ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) :=
        Finset.sum_le_sum hterm
      _ = (profileMass v * Real.exp (-(d * (y - δ)))) *
          ∑ ρ ∈ G, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (profileMass_nonneg v) (Real.exp_pos _).le)
  rw [← Finset.sum_filter_add_sum_filter_not F P]
  calc
    _ ≤ profileMass v * ((1 + g ^ 2) / (δ ^ 2 * g ^ 2)) * lorentzMass t +
        (profileMass v * Real.exp (-(d * (y - δ)))) * lorentzMass t := add_le_add hdeep hshallow
    _ = _ := by ring

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

/-- The centered zero field is absolutely summable at every camera width at
least one. -/
theorem summable_widthCenteredCamera
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t : ℝ} (hδ : 1 ≤ δ) (hy : δ ≤ y) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) *
      paperFT (depthCenteredCamera v zetaZeroWidth δ y) (gammaOf ρ - t)) := by
  apply Summable.of_norm
  refine ((summable_mult_lorentzKernel hδ t).mul_left (profileMass v)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left
    (norm_paperFT_widthCenteredCamera_le hv hsupp (lt_of_lt_of_le one_pos hδ) hy ρ)
    (Nat.cast_nonneg (zetaZeroConfig.mult ρ))
  convert h using 1 <;> ring

/-- On a dyadic height interval the complete exterior mass is `O(1/log T)`
when the camera width is `c log T`. -/
theorem sum_widthCenteredCamera_exterior_le_inv_log
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {c g T y t : ℝ} (hc : 0 < c) (hg : 0 < g) (hT : 4 ≤ T)
    (hL : 1 ≤ Real.log T) (hy : c * Real.log T ≤ y) (ht : t ∈ Ioc T (2 * T))
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth (c * Real.log T) y) (gammaOf ρ - t)‖) ≤
      (8 * profileMass v * (1 + g ^ 2) * (xiLineTwoLogDerivConstant + 2) /
        (c ^ 2 * g ^ 2)) / Real.log T := by
  have hL0 : 0 < Real.log T := lt_of_lt_of_le one_pos hL
  have hδ : 0 < c * Real.log T := mul_pos hc hL0
  have ht0 : 0 ≤ t := by linarith only [hT, ht.1]
  have hlog : Real.log (t + 4) ≤ 2 * Real.log T := by
    have hsq : t + 4 ≤ T ^ 2 := by nlinarith only [hT, ht.2]
    calc
      _ ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith only [ht0]) hsq
      _ = _ := by rw [Real.log_pow]; norm_num
  have hunit : lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + 2) * Real.log T := by
    have h := lorentzMass_le_log t
    rw [abs_of_nonneg ht0] at h
    have hC := le_mul_of_one_le_right xiLineTwoLogDerivConstant_nonneg hL
    nlinarith only [h, hlog, hC]
  calc
    _ ≤ profileMass v * ((1 + g ^ 2) / ((c * Real.log T) ^ 2 * g ^ 2)) * lorentzMass t :=
      sum_widthCenteredCamera_exterior_le hv hsupp hδ hy hg F hgap
    _ ≤ profileMass v * ((1 + g ^ 2) / ((c * Real.log T) ^ 2 * g ^ 2)) *
        (8 * (xiLineTwoLogDerivConstant + 2) * Real.log T) :=
      mul_le_mul_of_nonneg_left hunit
        (mul_nonneg (profileMass_nonneg v) (by positivity))
    _ = _ := by field_simp [hc.ne', hg.ne', hL0.ne']; ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
