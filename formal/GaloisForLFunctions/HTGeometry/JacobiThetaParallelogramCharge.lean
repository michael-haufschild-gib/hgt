/-
# The fundamental-parallelogram charge of Jacobi theta

The theta constraints determine the logarithmic-derivative boundary charge without a product
formula. Opposite edges cancel by period one, while quasiperiodicity contributes exactly `2*pi*i`.
This is the constraint-side input for the exact zero-counting theorem on a fundamental
parallelogram.
-/
import GaloisForLFunctions.HTGeometry.JacobiThetaDivisorSimple
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- The pointwise logarithmic derivative of the fixed-parameter Jacobi theta function. -/
def thetaLogDeriv (z τ : ℂ) : ℂ := jacobiTheta₂' z τ / jacobiTheta₂ z τ

/-- The theta logarithmic derivative is one-periodic. -/
theorem thetaLogDeriv_add_one (z τ : ℂ) :
    thetaLogDeriv (z + 1) τ = thetaLogDeriv z τ := by
  rw [thetaLogDeriv, thetaLogDeriv, jacobiTheta₂'_add_left, jacobiTheta₂_add_left]

/-- Away from a theta zero, translation by the quasiperiod subtracts `2*pi*i` from the
logarithmic derivative. -/
theorem thetaLogDeriv_add_tau {z τ : ℂ} (hz : jacobiTheta₂ z τ ≠ 0) :
    thetaLogDeriv (z + τ) τ = thetaLogDeriv z τ - 2 * Real.pi * I := by
  rw [thetaLogDeriv, thetaLogDeriv, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  have he : Complex.exp (-Real.pi * I * (τ + 2 * z)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- A fundamental parallelogram based at `a` is boundary-regular when theta is nonzero on its
bottom and left edges. Periodicity and quasiperiodicity then make all four edges zero-free. -/
def ThetaParallelogramBoundaryRegular (τ a : ℂ) : Prop :=
  (∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → jacobiTheta₂ (a + t) τ ≠ 0) ∧
    ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → jacobiTheta₂ (a + t * τ) τ ≠ 0

theorem thetaParallelogramBoundaryRegular_top {τ a : ℂ}
    (h : ThetaParallelogramBoundaryRegular τ a) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
    jacobiTheta₂ (a + τ + t) τ ≠ 0 := by
  have hbase := h.1 t ht
  have hq := jacobiTheta₂_add_left' (a + t) τ
  rw [show a + t + τ = a + τ + t by ring] at hq
  rw [hq]
  exact mul_ne_zero (Complex.exp_ne_zero _) hbase

theorem thetaParallelogramBoundaryRegular_right {τ a : ℂ}
    (h : ThetaParallelogramBoundaryRegular τ a) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
    jacobiTheta₂ (a + 1 + t * τ) τ ≠ 0 := by
  have hbase := h.2 t ht
  rw [show a + 1 + t * τ = (a + t * τ) + 1 by ring, jacobiTheta₂_add_left]
  exact hbase

/-- The positively oriented logarithmic-derivative integral around the parallelogram with vertices
`a`, `a+1`, `a+1+τ`, and `a+τ`. -/
def thetaParallelogramIntegral (τ a : ℂ) : ℂ :=
    (∫ t : ℝ in 0..1, thetaLogDeriv (a + t) τ) +
      τ * (∫ t : ℝ in 0..1, thetaLogDeriv (a + 1 + t * τ) τ) -
      (∫ t : ℝ in 0..1, thetaLogDeriv (a + τ + t) τ) -
      τ * (∫ t : ℝ in 0..1, thetaLogDeriv (a + t * τ) τ)

/-- **Constraint-side boundary charge.** Every zero-free fundamental boundary carries the exact
theta logarithmic-derivative charge `2*pi*i`. The result uses only the period and quasiperiod
constraints; it does not use the triple product or an a priori theta divisor. -/
theorem thetaParallelogramIntegral_eq_two_pi_I {τ a : ℂ} (hτ : 0 < τ.im)
    (hregular : ThetaParallelogramBoundaryRegular τ a) :
    thetaParallelogramIntegral τ a = 2 * Real.pi * I := by
  have hbotI : IntervalIntegrable (fun t : ℝ => thetaLogDeriv (a + t) τ)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : jacobiTheta₂ (a + t) τ ≠ 0 := hregular.1 t ht
    have hedge : ContinuousAt (fun s : ℝ => a + (s : ℂ)) t := by fun_prop
    have hθp : ContinuousAt (jacobiTheta₂' · τ) (a + (t : ℂ)) :=
      ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) (a + t) (mem_univ _)).continuousAt
    have hθ : ContinuousAt (jacobiTheta₂ · τ) (a + (t : ℂ)) :=
      ((jacobiTheta₂_analyticOnNhd_fst τ hτ) (a + t) (mem_univ _)).continuousAt
    exact ((hθp.comp_of_eq hedge rfl).div (hθ.comp_of_eq hedge rfl) hn).continuousWithinAt
  have hright : (∫ t : ℝ in 0..1, thetaLogDeriv (a + 1 + t * τ) τ) =
      ∫ t : ℝ in 0..1, thetaLogDeriv (a + t * τ) τ := by
    apply integral_congr
    intro t _
    show thetaLogDeriv (a + 1 + (t : ℂ) * τ) τ = thetaLogDeriv (a + (t : ℂ) * τ) τ
    rw [show a + 1 + (t : ℂ) * τ = a + t * τ + 1 by ring]
    exact thetaLogDeriv_add_one (a + t * τ) τ
  have htop : (∫ t : ℝ in 0..1, thetaLogDeriv (a + τ + t) τ) =
      ∫ t : ℝ in 0..1, (thetaLogDeriv (a + t) τ - 2 * Real.pi * I) := by
    apply integral_congr
    intro t ht
    have ht' : t ∈ uIcc (0 : ℝ) 1 := by simpa using ht
    show thetaLogDeriv (a + τ + (t : ℂ)) τ = thetaLogDeriv (a + (t : ℂ)) τ - 2 * Real.pi * I
    rw [show a + τ + (t : ℂ) = a + t + τ by ring]
    exact thetaLogDeriv_add_tau (hregular.1 t ht')
  rw [thetaParallelogramIntegral, hright, htop,
    integral_sub hbotI intervalIntegrable_const]
  rw [intervalIntegral.integral_const]
  norm_num

end

end GaloisForLFunctions
