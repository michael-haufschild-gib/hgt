import GaloisForLFunctions.RHTower.XiZeroCountingFunction
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import Mathlib.Analysis.Complex.JensenFormula

/-!
# The zero count of `ξ` is at most `T log T`

Jensen's inequality bounds the number of zeros of an analytic function in a disc by the logarithm
of its maximum on a larger concentric disc.  For `ξ` the maximum is the order-one envelope
`exp (C (1 + R) log (2 + R))` and the centre value is `ξ(0) = 1/2`, so doubling the radius gives

`n(r) ≤ [C (1 + 2r) log (2 + 2r) + log 2] / log 2`.

Every zero counted by `N(T)` lies in the closed disc of radius `1 + T` about the origin, so
`N(T) ≤ c T log T`.
-/

open Complex Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The growth envelope of `ξ` -/

theorem xi_eq_riemannXi_xiZeroCountJensenBound (s : ℂ) : xi s = riemannXi s := by
  rw [xi, riemannXi]
  ring

theorem orderOneEnvelope_xi : OrderOneEnvelope xi :=
  orderOneEnvelope_riemannXi.congr fun s => (xi_eq_riemannXi_xiZeroCountJensenBound s).symm

/-! ## Jensen's bound on a disc -/

/-- **Jensen's inequality for `ξ`.**  The divisor mass of a disc is bounded by the order-one
envelope at twice the radius. -/
theorem xiRegionOrderSum_closedBall_le {C : ℝ} (hC : 0 < C)
    (hgrow : ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (orderOneWeight C s)) {r : ℝ} (hr : 0 < r) :
    (xiRegionOrderSum (closedBall (0 : ℂ) r) : ℝ)
      ≤ (C * (1 + 2 * r) * Real.log (2 + 2 * r) + Real.log 2) / Real.log 2 := by
  have hR : (0 : ℝ) < 2 * r := by linarith
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |2 * r| = 2 * r := abs_of_pos hR
  set M : ℝ := Real.exp (C * (1 + 2 * r) * Real.log (2 + 2 * r)) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    refine Real.one_le_exp ?_
    have h1 : (0 : ℝ) ≤ Real.log (2 + 2 * r) := Real.log_nonneg (by linarith)
    positivity
  have hbound : ∀ z ∈ sphere (0 : ℂ) |2 * r|, ‖xi z‖ ≤ M := by
    intro z hz
    have hnorm : ‖z‖ = 2 * r := by
      have := mem_sphere_iff_norm.mp hz
      rw [sub_zero] at this
      rw [this, habsR]
    refine le_trans (hgrow z) ?_
    rw [hM, orderOneWeight, hnorm]
  have hjensen := (xi_analyticOnNhd (closedBall (0 : ℂ) |2 * r|)).sum_divisor_le
    (r := r) (R := 2 * r) (M := M) (by rw [habsr]; exact hr)
    (by rw [habsr, habsR]; linarith) hM1 (by simpa using xi_zero ▸ (by norm_num : (1 : ℂ) / 2 ≠ 0))
    hbound
  rw [habsr] at hjensen
  rw [xiRegionOrderSum]
  refine le_trans hjensen (le_of_eq ?_)
  rw [xi_zero]
  have hlog : Real.log (2 * r / r) = Real.log 2 := by
    rw [mul_div_assoc, div_self hr.ne', mul_one]
  rw [hlog]
  congr 1
  rw [hM, show ‖(1 : ℂ) / 2‖ = 1 / 2 by norm_num, div_div_eq_mul_div]
  norm_num
  rw [Real.log_mul (Real.exp_ne_zero _) (by norm_num), Real.log_exp]

/-! ## The zero-counting function -/

theorem xiCountingBox_subset_closedBall {T : ℝ} (hT : 0 ≤ T) :
    xiCountingBox T ⊆ closedBall (0 : ℂ) (1 + T) := by
  intro s hs
  obtain ⟨hre, him⟩ := hs
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im s) ?_
  have h1 : |s.re| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hre.1], hre.2⟩
  have h2 : |s.im| ≤ T := by
    rw [abs_le]
    exact ⟨by linarith [him.1], him.2⟩
  linarith

/-- **`N(T) ≪ T log T`.**  The zero-counting function of `ξ` grows at most like `T log T`. -/
theorem exists_xiZeroCount_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 2 ≤ T → (xiZeroCount T : ℝ) ≤ c * T * Real.log T := by
  obtain ⟨C, hC, hgrow⟩ := orderOneEnvelope_xi
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(16 * C + 1) / Real.log 2, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : (0 : ℝ) < Real.log T := lt_of_lt_of_le hlog2 hlogT
  have hr : (0 : ℝ) < 1 + T := by linarith
  have hmono : xiZeroCount T ≤ xiRegionOrderSum (closedBall (0 : ℂ) (1 + T)) :=
    xiRegionOrderSum_mono (isCompact_closedBall _ _)
      (xiCountingBox_subset_closedBall (by linarith))
  have hmono' : (xiZeroCount T : ℝ) ≤ (xiRegionOrderSum (closedBall (0 : ℂ) (1 + T)) : ℝ) := by
    exact_mod_cast hmono
  refine le_trans hmono' (le_trans (xiRegionOrderSum_closedBall_le hC hgrow hr) ?_)
  rw [div_le_iff₀ hlog2]
  have hlogbound : Real.log (2 + 2 * (1 + T)) ≤ 4 * Real.log T := by
    have hstep : Real.log (2 + 2 * (1 + T)) ≤ Real.log (8 * T) :=
      Real.log_le_log (by linarith) (by linarith)
    have hval : Real.log (8 * T) = Real.log 8 + Real.log T :=
      Real.log_mul (by norm_num) hT0.ne'
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hle : Real.log 8 ≤ 3 * Real.log T := by
      rw [h8]
      linarith
    linarith [hstep, hval]
  have hlin : C * (1 + 2 * (1 + T)) * Real.log (2 + 2 * (1 + T))
      ≤ 16 * C * (T * Real.log T) := by
    calc C * (1 + 2 * (1 + T)) * Real.log (2 + 2 * (1 + T))
        ≤ (C * (4 * T)) * (4 * Real.log T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlogbound
            (Real.log_nonneg (by linarith)) (by positivity)
      _ = 16 * C * (T * Real.log T) := by ring
  have hlog2le : Real.log 2 ≤ T * Real.log T := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - 1) hlogT0.le, hlogT]
  have hrhs : (16 * C + 1) / Real.log 2 * T * Real.log T * Real.log 2
      = (16 * C + 1) * (T * Real.log T) := by
    field_simp
  rw [hrhs]
  linarith [hlin, hlog2le]

end RHTower
