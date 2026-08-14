import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGlobalDerivativeBound

/-!
# Global derivative bound for the squared neutral chi carrier

The square approximate functional equation carries the square of the normalized chi ratio.
Although a naive global product estimate loses three conductor powers, neutral relative variation
in the central window and frequency domination outside it leave only one conductor power.  This is
the scale required to freeze the exact square-dual carrier coefficientwise.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Squared normalized chi carrier on the positive dual contour. -/
def smoothAFEZetaChiShiftRatioSq (tau v : ℝ) : ℂ :=
  (smoothAFEZetaChiShiftRatio (linePt tau)
    (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2

/-- Exact height derivative of the squared normalized chi carrier. -/
theorem deriv_smoothAFEZetaChiShiftRatioSq (tau v : ℝ) :
    deriv (fun u : ℝ => smoothAFEZetaChiShiftRatioSq u v) tau =
      2 * smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
        deriv
          (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau := by
  have h :=
    hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line tau v
  have hp := (h.pow 2).deriv
  change deriv
      (fun u : ℝ =>
        (smoothAFEZetaChiShiftRatio (linePt u)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) ^ 2) tau = _ at hp
  unfold smoothAFEZetaChiShiftRatioSq
  rw [hp, h.deriv]
  norm_num

/-- Squaring the neutral chi ratio leaves only one conductor power in its
height derivative.  In the outer region that power is absorbed by frequency. -/
theorem exists_norm_deriv_smoothAFEZetaChiShiftRatioSq_le_global :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {tau : ℝ}, 4 ≤ tau → ∀ v : ℝ,
      ‖deriv (fun u : ℝ => smoothAFEZetaChiShiftRatioSq u v) tau‖ ≤
        K * (1 + tau) * (1 + |v|) ^ 5 := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global
  let C : ℝ := 6 + 2 * Real.pi
  let K : ℝ := 4 * C + 8 * D
  refine ⟨K, by dsimp only [K, C]; positivity, ?_⟩
  intro tau htau v
  have htau0 : 0 < tau := by linarith
  have habstau : |tau| = tau := abs_of_pos htau0
  have hb : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hb0 : 0 ≤ 1 + |v| := by linarith
  have htau1 : 0 ≤ 1 + tau := by linarith
  have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
  rw [habstau] at hratio
  have hnorm :
      ‖deriv (fun u : ℝ => smoothAFEZetaChiShiftRatioSq u v) tau‖ =
        2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          ‖deriv
            (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau‖ := by
    rw [deriv_smoothAFEZetaChiShiftRatioSq, norm_mul, norm_mul]
    norm_num
  rw [hnorm]
  by_cases hv : 2 * |v| ≤ tau
  · have hder :=
      norm_deriv_smoothAFEZetaChiShiftRatio_neg_right_one_line_le htau hv
    have hC : 0 ≤ C := by
      dsimp only [C]
      positivity
    have hscale : (1 + tau) * tau⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ htau0]
      linarith
    have hpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 5 := by
      calc
        (1 + |v|) ^ 3 = (1 + |v|) ^ 3 * 1 := by ring
        _ ≤ (1 + |v|) ^ 3 * (1 + |v|) ^ 2 := by
          gcongr
          nlinarith
        _ = (1 + |v|) ^ 5 := by ring
    have hK : 4 * C ≤ K := by
      dsimp only [K]
      linarith
    have hcoef : 2 * C * ((1 + tau) * tau⁻¹) ≤ 4 * C := by
      calc
        2 * C * ((1 + tau) * tau⁻¹) ≤ 2 * C * 2 := by gcongr
        _ = 4 * C := by ring
    calc
      2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖deriv
              (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
                (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau‖
        ≤ 2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            (‖smoothAFEZetaChiShiftRatio (linePt tau)
                (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
              (C * (1 + |v|) / tau)) := by
            dsimp only [C]
            gcongr
      _ ≤ 2 * ((1 + tau) * (1 + |v|)) *
            (((1 + tau) * (1 + |v|)) *
              (C * (1 + |v|) / tau)) := by gcongr
      _ = (2 * C * ((1 + tau) * tau⁻¹)) *
            ((1 + tau) * (1 + |v|) ^ 3) := by
          rw [div_eq_mul_inv]
          ring
      _ ≤ (4 * C) * ((1 + tau) * (1 + |v|) ^ 3) := by
          exact mul_le_mul_of_nonneg_right hcoef
            (mul_nonneg htau1 (pow_nonneg hb0 3))
      _ ≤ (4 * C) * ((1 + tau) * (1 + |v|) ^ 5) := by gcongr
      _ ≤ K * (1 + tau) * (1 + |v|) ^ 5 := by
          calc
            (4 * C) * ((1 + tau) * (1 + |v|) ^ 5)
              ≤ K * ((1 + tau) * (1 + |v|) ^ 5) := by gcongr
            _ = K * (1 + tau) * (1 + |v|) ^ 5 := by ring
  · have htail : tau < 2 * |v| := lt_of_not_ge hv
    have hheight : (1 + tau) ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by
      nlinarith [sq_nonneg (1 + tau), sq_nonneg (1 + |v|)]
    have hder := hglobal tau v
    rw [habstau] at hder
    have hK : 8 * D ≤ K := by
      dsimp only [K]
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      linarith
    have hcoef :
        2 * D * (1 + tau) ^ 2 ≤ 8 * D * (1 + |v|) ^ 2 := by
      calc
        2 * D * (1 + tau) ^ 2
          ≤ 2 * D * (4 * (1 + |v|) ^ 2) := by gcongr
        _ = 8 * D * (1 + |v|) ^ 2 := by ring
    calc
      2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖deriv
              (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
                (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau‖
        ≤ 2 * ((1 + tau) * (1 + |v|)) *
            (D * (1 + tau) ^ 2 * (1 + |v|) ^ 2) := by gcongr
      _ = (2 * D * (1 + tau) ^ 2) *
            ((1 + tau) * (1 + |v|) ^ 3) := by ring
      _ ≤ (8 * D * (1 + |v|) ^ 2) *
            ((1 + tau) * (1 + |v|) ^ 3) := by
          exact mul_le_mul_of_nonneg_right hcoef
            (mul_nonneg htau1 (pow_nonneg hb0 3))
      _ = (8 * D) * ((1 + tau) * (1 + |v|) ^ 5) := by ring
      _ ≤ K * ((1 + tau) * (1 + |v|) ^ 5) := by gcongr
      _ = K * (1 + tau) * (1 + |v|) ^ 5 := by ring

end RHTower
