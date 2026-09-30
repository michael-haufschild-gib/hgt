import GaloisForLFunctions.RHTower.SteinhausEulerPoissonTilt
import GaloisForLFunctions.RHTower.RandomEulerObservableFactor


/-!
# Nondegenerate centered moments under the Euler Poisson tilt

For `0<=r<=3/4`, the actual centered real logarithmic increment is bounded by
`6r`, while its tilted second moment is at least `r^2/336`. The lower bound
comes from the fixed far arc `[1/3,2/3]`, where the increment is at most `-r/4`
and the density is at least `1/7`. Every absolute moment has the corresponding
pointwise upper bound. No symmetry of the tilted law is used.
These are concrete prime-coordinate inputs for the BAG critical-mass argument.
-/

noncomputable section
open MeasureTheory Complex Metric
namespace RHTower

private theorem norm_eulerArg_bounds {r : ℝ} (hr0 : 0 ≤ r) (x : ℝ) :
    1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ ∧
    ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ ≤ 1 + r := by
  have hn : ‖(r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ = r := by
    rw [norm_mul, norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    norm_num
  constructor
  · simpa only [hn, norm_one] using norm_sub_norm_le (1 : ℂ) ((r : ℂ) * circleMap 0 1 (2 * Real.pi * x))
  · simpa only [hn, norm_one] using norm_sub_le (1 : ℂ) ((r : ℂ) * circleMap 0 1 (2 * Real.pi * x))

/-- The actual tilt density has a uniform positive lower bound. -/
theorem steinhausEulerTiltWeight_lower {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) (x : ℝ) :
    1 / 7 ≤ steinhausEulerTiltWeight r x := by
  obtain ⟨hnlo, hnhi⟩ := norm_eulerArg_bounds hr0 x
  have hn0 : 0 < ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ := by linarith
  have hn2 := pow_le_pow_left₀ (norm_nonneg ((1 : ℂ) -
    (r : ℂ) * circleMap 0 1 (2 * Real.pi * x))) hnhi 2
  rw [steinhausEulerTiltWeight, le_div_iff₀ (sq_pos_of_pos hn0)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 4 - r) (by linarith : 0 ≤ r + 1)]

/-- Uniform linear envelope for the centered real log increment. -/
theorem abs_steinhausEulerTiltCenteredLog_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4)
    (x : ℝ) : |steinhausEulerTiltCenteredLog r x| ≤ 6 * r := by
  obtain ⟨hnlo, hnhi⟩ := norm_eulerArg_bounds hr0 x
  set u := ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ with hu
  have hu0 : 0 < u := by linarith
  have hu4 : 1 / 4 ≤ u := by linarith
  have hilog := Real.one_sub_inv_le_log_of_pos hu0
  have hlog := Real.log_le_sub_one_of_pos hu0
  have hfrac : u⁻¹ - 1 ≤ 4 * r := by
    have heq : u⁻¹ - 1 = (1 - u) / u := by field_simp
    rw [heq, div_le_iff₀ hu0]
    nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ u - 1 / 4)]
  have huabs : |Real.log u| ≤ 4 * r := by rw [abs_le]; constructor <;> linarith
  have hc0 : 0 < 1 - r ^ 2 := by nlinarith
  have hc7 : 7 / 16 ≤ 1 - r ^ 2 := by nlinarith
  have hclog := Real.one_sub_inv_le_log_of_pos hc0
  have hcupper := Real.log_le_sub_one_of_pos hc0
  have hcfrac : (1 - r ^ 2)⁻¹ - 1 ≤ 2 * r := by
    have heq : (1 - r ^ 2)⁻¹ - 1 = r ^ 2 / (1 - r ^ 2) := by field_simp; ring
    rw [heq, div_le_iff₀ hc0]
    nlinarith [mul_le_mul_of_nonneg_left hc7 hr0, mul_le_mul_of_nonneg_left hr hr0]
  have hcabs : |Real.log (1 - r ^ 2)| ≤ 2 * r := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |steinhausEulerTiltCenteredLog r x|
      ≤ |Real.log u| + |Real.log (1 - r ^ 2)| := by
        simpa [steinhausEulerTiltCenteredLog, steinhausEulerTiltLog, hu] using
          abs_add_le (-Real.log u) (Real.log (1 - r ^ 2))
    _ ≤ 6 * r := by linarith

/-- The centered increment is negative by a fixed amount on the far arc. -/
theorem steinhausEulerTiltCenteredLog_far_arc {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)) :
    steinhausEulerTiltCenteredLog r x ≤ -(r / 4) := by
  have hcos := GaloisForLFunctions.RHTower.cos_twoPi_le_neg_half hx.1 hx.2
  have hsq := GaloisForLFunctions.RHTower.normSq_one_sub_randomEulerLogArg r x
  have he : circleMap (0 : ℂ) 1 (2 * Real.pi * x) =
      Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by simp [circleMap]
  set u := ‖(1 : ℂ) - (r : ℂ) * circleMap 0 1 (2 * Real.pi * x)‖ with hu
  have hge : 1 + r ≤ u ^ 2 := by rw [hu, he, hsq]; nlinarith
  have hu0 : 0 < u := by
    have := (norm_eulerArg_bounds hr0 x).1
    change 1 - r ≤ u at this
    linarith
  have hlog : Real.log (1 + r) ≤ 2 * Real.log u := by
    have hh := Real.log_le_log (by linarith : 0 < 1 + r) hge
    simpa [Real.log_pow] using hh
  have hlower : r / 2 ≤ Real.log (1 + r) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + r)
    have hf : r / 2 ≤ 1 - (1 + r)⁻¹ := by
      have heq : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
      rw [heq, le_div_iff₀ (by linarith : 0 < 1 + r)]
      nlinarith
    exact hf.trans hh
  have hc : Real.log (1 - r ^ 2) ≤ 0 :=
    le_trans (Real.log_le_sub_one_of_pos (by nlinarith)) (by nlinarith)
  change -Real.log u + Real.log (1 - r ^ 2) ≤ _
  linarith

private theorem continuous_tiltCenteredLog {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (steinhausEulerTiltCenteredLog r) :=
  (continuous_steinhausEulerTiltLog hr0 hr1).add continuous_const

/-- A nonzero centered second moment from the explicit far arc. -/
theorem integral_sq_steinhausEulerTiltCenteredLog_lower {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) :
    r ^ 2 / 336 ≤ ∫ x, steinhausEulerTiltCenteredLog r x ^ 2 ∂steinhausEulerTiltMeasure r := by
  have hr1 : r < 1 := by linarith
  rw [integral_steinhausEulerTiltMeasure hr0 hr1]
  have hi : IntegrableOn (fun x => steinhausEulerTiltWeight r x * steinhausEulerTiltCenteredLog r x ^ 2)
      (Set.Icc (0 : ℝ) 1) volume :=
    ((continuous_steinhausEulerTiltWeight hr0 hr1).mul
      ((continuous_tiltCenteredLog hr0 hr1).pow 2)).integrableOn_Icc
  have hsub : Set.Icc (1 / 3 : ℝ) (2 / 3) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpt : ∀ x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3), r ^ 2 / 112 ≤
      steinhausEulerTiltWeight r x * steinhausEulerTiltCenteredLog r x ^ 2 := by
    intro x hx
    have hz := steinhausEulerTiltCenteredLog_far_arc hr0 hr1 hx
    have hw := steinhausEulerTiltWeight_lower hr0 hr x
    have hz2 : r ^ 2 / 16 ≤ steinhausEulerTiltCenteredLog r x ^ 2 := by
      nlinarith [sq_nonneg (steinhausEulerTiltCenteredLog r x + r / 4)]
    nlinarith [mul_le_mul_of_nonneg_left hz2 (steinhausEulerTiltWeight_pos hr0 hr1 x).le,
      mul_le_mul_of_nonneg_right hw (sq_nonneg r)]
  have h₁ : ∫ _x in Set.Icc (1 / 3 : ℝ) (2 / 3), r ^ 2 / 112 ≤
      ∫ x in Set.Icc (1 / 3 : ℝ) (2 / 3),
        steinhausEulerTiltWeight r x * steinhausEulerTiltCenteredLog r x ^ 2 :=
    setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc])) (hi.mono_set hsub)
      measurableSet_Icc hpt
  have h₂ : ∫ x in Set.Icc (1 / 3 : ℝ) (2 / 3),
        steinhausEulerTiltWeight r x * steinhausEulerTiltCenteredLog r x ^ 2 ≤
      ∫ x in Set.Icc (0 : ℝ) 1,
        steinhausEulerTiltWeight r x * steinhausEulerTiltCenteredLog r x ^ 2 :=
    setIntegral_mono_set hi (Filter.Eventually.of_forall fun x =>
      mul_nonneg (steinhausEulerTiltWeight_pos hr0 hr1 x).le (sq_nonneg _))
      (LE.le.eventuallyLE hsub)
  have hc : ∫ _x in Set.Icc (1 / 3 : ℝ) (2 / 3), r ^ 2 / 112 = r ^ 2 / 336 := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
    norm_num
    ring
  rw [hc] at h₁
  exact h₁.trans h₂

/-- All absolute moments are controlled under the concrete tilted law. -/
theorem integral_pow_steinhausEulerTiltCenteredLog_upper {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) (k : ℕ) :
    ∫ x, |steinhausEulerTiltCenteredLog r x| ^ k ∂steinhausEulerTiltMeasure r ≤ (6 * r) ^ k := by
  have hr1 : r < 1 := by linarith
  rw [integral_steinhausEulerTiltMeasure hr0 hr1]
  have hi₁ : Integrable (fun x => steinhausEulerTiltWeight r x * |steinhausEulerTiltCenteredLog r x| ^ k)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((continuous_steinhausEulerTiltWeight hr0 hr1).mul
      ((continuous_tiltCenteredLog hr0 hr1).abs.pow k)).integrableOn_Icc
  have hi₂ : Integrable (fun x => steinhausEulerTiltWeight r x * (6 * r) ^ k)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((continuous_steinhausEulerTiltWeight hr0 hr1).mul continuous_const).integrableOn_Icc
  calc ∫ x, steinhausEulerTiltWeight r x * |steinhausEulerTiltCenteredLog r x| ^ k
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ∫ x, steinhausEulerTiltWeight r x * (6 * r) ^ k
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        integral_mono hi₁ hi₂ fun x => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (abs_steinhausEulerTiltCenteredLog_le hr0 hr x) k)
          (steinhausEulerTiltWeight_pos hr0 hr1 x).le
    _ = (6 * r) ^ k := by
      rw [integral_mul_const, integral_steinhausEulerTiltWeight hr0 hr1, one_mul]

end RHTower
