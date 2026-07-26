/-
# Explicit operator bounds for Bourgain's local phase maps

On the square-root application range `1/2 ≤ a < b ≤ 1`, the literal
osculating-coordinate map has operator norm at most six.  An anisotropic
parabola dilation by a scale in `[0,1]` has operator norm at most one.
-/
import GaloisForLFunctions.RHTower.BourgainAnisotropicPlanarTransfer

namespace RHTower

noncomputable section

theorem norm_bourgainParabolaPhaseScale_le_one
    {scale : ℝ} (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1)
    (y : Fin 4 → ℝ) :
    ‖bourgainParabolaPhaseScale scale y‖ ≤ ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
  intro i
  have hy (j : Fin 4) : ‖y j‖ ≤ ‖y‖ :=
    norm_apply_le_norm_bourgainPhaseSpace y j
  have hs : ‖scale‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hscale0]
    exact hscale1
  have hs2 : ‖scale ^ (2 : ℕ)‖ ≤ 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg scale]
  fin_cases i
  · change ‖scale * y 0‖ ≤ ‖y‖
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs).trans (hy 0)
  · change ‖scale ^ (2 : ℕ) * y 1‖ ≤ ‖y‖
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs2).trans (hy 1)
  · change ‖scale * y 2‖ ≤ ‖y‖
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs).trans (hy 2)
  · change ‖scale ^ (2 : ℕ) * y 3‖ ≤ ‖y‖
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs2).trans (hy 3)

theorem opNorm_bourgainParabolaPhaseScale_le_one
    {scale : ℝ} (hscale : scale ≠ 0)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) :
    ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  calc
    ‖(bourgainParabolaPhaseScaleContinuousLinearEquiv hscale :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) y‖ =
        ‖bourgainParabolaPhaseScale scale y‖ := by
          congr 1
          exact
            bourgainParabolaPhaseScaleContinuousLinearEquiv_apply hscale y
    _ ≤ ‖y‖ :=
      norm_bourgainParabolaPhaseScale_le_one hscale0 hscale1 y
    _ = 1 * ‖y‖ := by ring

private theorem norm_bourgainSquareRootLinearPhaseRow_le_six
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (x : Fin 4 → ℝ) :
    ‖x 0 + 2 * p ^ 2 * x 1 + (3 * p / 2) * x 2 +
        (1 / (2 * p)) * x 3‖ ≤
      6 * ‖x‖ := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) hp0
  have hp2 : p ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg p]
  have hc1 : ‖2 * p ^ (2 : ℕ)‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hc2 : ‖3 * p / 2‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hc3 : ‖1 / (2 * p)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).2 (by nlinarith)
  have hx (i : Fin 4) : ‖x i‖ ≤ ‖x‖ :=
    norm_apply_le_norm_bourgainPhaseSpace x i
  have ht1 : ‖2 * p ^ 2 * x 1‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul]
    exact mul_le_mul hc1 (hx 1) (norm_nonneg _) (by norm_num)
  have ht2 : ‖(3 * p / 2) * x 2‖ ≤ 2 * ‖x‖ := by
    rw [norm_mul]
    exact mul_le_mul hc2 (hx 2) (norm_nonneg _) (by norm_num)
  have ht3 : ‖(1 / (2 * p)) * x 3‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc3).trans (hx 3)
  calc
    ‖x 0 + 2 * p ^ 2 * x 1 + (3 * p / 2) * x 2 +
        (1 / (2 * p)) * x 3‖ ≤
      ‖x 0‖ + ‖2 * p ^ 2 * x 1‖ + ‖(3 * p / 2) * x 2‖ +
        ‖(1 / (2 * p)) * x 3‖ := norm_add₄_le
    _ ≤ 6 * ‖x‖ := by
      nlinarith [hx 0, ht1, ht2, ht3]

private theorem norm_bourgainSquareRootQuadraticPhaseRow_le_six
    {p : ℝ} (hp0 : 1 / 2 ≤ p)
    (x : Fin 4 → ℝ) :
    ‖x 1 + (3 / (8 * p)) * x 2 -
        (1 / (8 * p ^ 3)) * x 3‖ ≤
      6 * ‖x‖ := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) hp0
  have hp3 : (1 / 2 : ℝ) ^ (3 : ℕ) ≤ p ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hp0 3
  have hc2 : ‖3 / (8 * p)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).2 (by nlinarith)
  have hc3 : ‖1 / (8 * p ^ (3 : ℕ))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).2 (by
      norm_num at hp3
      nlinarith)
  have hx (i : Fin 4) : ‖x i‖ ≤ ‖x‖ :=
    norm_apply_le_norm_bourgainPhaseSpace x i
  have ht2 : ‖(3 / (8 * p)) * x 2‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc2).trans (hx 2)
  have ht3 : ‖(1 / (8 * p ^ 3)) * x 3‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc3).trans (hx 3)
  rw [sub_eq_add_neg]
  calc
    ‖x 1 + (3 / (8 * p)) * x 2 +
        -((1 / (8 * p ^ 3)) * x 3)‖ ≤
      ‖x 1‖ + ‖(3 / (8 * p)) * x 2‖ +
        ‖-((1 / (8 * p ^ 3)) * x 3)‖ := norm_add₃_le
    _ ≤ 6 * ‖x‖ := by
      rw [norm_neg]
      nlinarith [hx 1, ht2, ht3, norm_nonneg x]

theorem norm_bourgainSquareRootPhaseCoordinates_le_six
    {a b : ℝ} (ha0 : 1 / 2 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (x : Fin 4 → ℝ) :
    ‖bourgainSquareRootPhaseCoordinates a b x‖ ≤ 6 * ‖x‖ := by
  have ha1 : a ≤ 1 := le_trans hab.le hb1
  have hb0 : 1 / 2 ≤ b := ha0.trans hab.le
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))]
  intro i
  fin_cases i
  · change ‖bourgainSquareRootPhaseCoordinates a b x 0‖ ≤ 6 * ‖x‖
    rw [bourgainSquareRootPhaseCoordinates_zero]
    exact norm_bourgainSquareRootLinearPhaseRow_le_six ha0 ha1 x
  · change ‖bourgainSquareRootPhaseCoordinates a b x 1‖ ≤ 6 * ‖x‖
    rw [bourgainSquareRootPhaseCoordinates_one]
    exact norm_bourgainSquareRootQuadraticPhaseRow_le_six ha0 x
  · change ‖bourgainSquareRootPhaseCoordinates a b x 2‖ ≤ 6 * ‖x‖
    rw [bourgainSquareRootPhaseCoordinates_two]
    exact norm_bourgainSquareRootLinearPhaseRow_le_six hb0 hb1 x
  · change ‖bourgainSquareRootPhaseCoordinates a b x 3‖ ≤ 6 * ‖x‖
    rw [bourgainSquareRootPhaseCoordinates_three]
    exact norm_bourgainSquareRootQuadraticPhaseRow_le_six hb0 x

theorem opNorm_bourgainSquareRootPhaseCoordinates_le_six
    {a b : ℝ} (ha0 : 1 / 2 ≤ a) (hab : a < b) (hb1 : b ≤ 1) :
    ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
        (lt_of_lt_of_le (by norm_num) ha0) hab :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))‖ ≤ 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  calc
    ‖(bourgainSquareRootPhaseCoordinateContinuousLinearEquiv
        (lt_of_lt_of_le (by norm_num) ha0) hab :
        (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) x‖ =
      ‖bourgainSquareRootPhaseCoordinates a b x‖ := by
        exact congrArg norm
          (bourgainSquareRootPhaseCoordinateContinuousLinearEquiv_apply
            (lt_of_lt_of_le (by norm_num) ha0) hab x)
    _ ≤ 6 * ‖x‖ :=
      norm_bourgainSquareRootPhaseCoordinates_le_six ha0 hab hb1 x

end

end RHTower
