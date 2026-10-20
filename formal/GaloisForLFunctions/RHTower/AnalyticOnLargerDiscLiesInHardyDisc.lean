import GaloisForLFunctions.HTGeometry.HardyDiskSpace
import GaloisForLFunctions.HTGeometry.CaratheodoryCoefficient
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Functions analytic on a larger disc lie in the Hardy space

A function differentiable on the closed disc of radius `R > 1` about `0` and bounded by `B` on
the circle of radius `R` has Cauchy coefficients `‖c_n‖ ≤ B R^{−n}`
(`norm_cauchyCoeff_le_of_circle_bound`), hence square-summable.  The resulting element of the Hardy space `HardyDisk = ℓ²(ℕ)` represents the
function on the open unit disc (`hardyFun_hardyDiskOfAnalytic`).
-/

open Complex Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The Cauchy coefficient `cauchyCoeff f R n` is the `n`-th coefficient of the Cauchy power
series. -/
theorem cauchyCoeff_eq_coeff (f : ℂ → ℂ) (R : ℝ) (n : ℕ) :
    cauchyCoeff f R n = (cauchyPowerSeries f 0 R).coeff n := rfl

/-- **Cauchy's coefficient estimate**: `‖c_n‖ ≤ B R^{−n}` when `‖f‖ ≤ B` on the circle. -/
theorem norm_cauchyCoeff_le_of_circle_bound {f : ℂ → ℂ} {R B : ℝ} (hR : 0 < R)
    (hB : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ B) (n : ℕ) :
    ‖cauchyCoeff f R n‖ ≤ B * R⁻¹ ^ n := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have h1 : ‖cauchyCoeff f R n‖ ≤ ‖cauchyPowerSeries f 0 R n‖ := by
    rw [cauchyCoeff_eq_coeff, FormalMultilinearSeries.norm_apply_eq_norm_coef]
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖ ≤ B * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ => ‖f (circleMap 0 R θ)‖) (a := 0) (b := 2 * Real.pi) (C := B)
      fun θ _ => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hB θ
    rw [sub_zero, abs_of_nonneg (by positivity)] at h
    exact le_trans (le_abs_self _) h
  calc ‖cauchyCoeff f R n‖ ≤ ‖cauchyPowerSeries f 0 R n‖ := h1
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 R θ)‖) * |R|⁻¹ ^ n :=
        norm_cauchyPowerSeries_le f 0 R n
    _ ≤ ((2 * Real.pi)⁻¹ * (B * (2 * Real.pi))) * |R|⁻¹ ^ n := by gcongr
    _ = B * R⁻¹ ^ n := by
        rw [abs_of_pos hR]
        field_simp

/-- Square-summability of the Cauchy coefficients for `R > 1`. -/
theorem memℓp_cauchyCoeff {f : ℂ → ℂ} {R B : ℝ} (hR : 1 < R)
    (hB : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ B) : Memℓp (cauchyCoeff f R) 2 := by
  have hR0 : 0 < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hinv : R⁻¹ ^ 2 < 1 := by
    have h1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    have h0 : 0 ≤ R⁻¹ := by positivity
    nlinarith
  rw [memℓp_gen_iff (by norm_num)]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) hinv).mul_left (B ^ 2))
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖cauchyCoeff f R n‖ ^ 2 ≤ (B * R⁻¹ ^ n) ^ 2 := by
        gcongr
        exact norm_cauchyCoeff_le_of_circle_bound hR0 hB n
    _ = B ^ 2 * (R⁻¹ ^ 2) ^ n := by ring

/-- The Hardy-space element of a function analytic on a disc of radius `R > 1`. -/
def hardyDiskOfAnalytic (f : ℂ → ℂ) {R B : ℝ} (hR : 1 < R)
    (hB : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ B) : HardyDisk :=
  ⟨cauchyCoeff f R, memℓp_cauchyCoeff hR hB⟩

theorem hardyDiskOfAnalytic_apply (f : ℂ → ℂ) {R B : ℝ} (hR : 1 < R)
    (hB : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ B) (n : ℕ) :
    (hardyDiskOfAnalytic f hR hB) n = cauchyCoeff f R n := rfl

/-- **The Hardy-space element represents `f` on the open unit disc.** -/
theorem hardyFun_hardyDiskOfAnalytic {f : ℂ → ℂ} {R B : ℝ} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R))
    (hB : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ B) {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (hardyDiskOfAnalytic f hR hB) q = f q := by
  set Rn : NNReal := ⟨R, by linarith⟩ with hRn
  have hRR : ((Rn : NNReal) : ℝ) = R := rfl
  have hps : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 Rn := by
    have := hf.hasFPowerSeriesOnBall (R := Rn) (by
      rw [← NNReal.coe_pos, hRR]; linarith)
    simpa [hRR] using this
  have hq' : q ∈ Metric.eball (0 : ℂ) Rn := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, hRR]
    linarith
  have hsum := hps.hasSum hq'
  rw [zero_add] at hsum
  unfold hardyFun
  rw [← hsum.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, hardyDiskOfAnalytic_apply,
    cauchyCoeff_eq_coeff, mul_comm]

end RHTower
