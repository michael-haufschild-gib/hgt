import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Polynomial
open MeasureTheory Metric Set Polynomial

example (r : ℝ) (hr : 0 < r) (x₀ : Fin 1 → ℝ) (x : Fin 1 → ℝ) :
    x ∈ ball x₀ r ↔ x 0 ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) := by
  rw [mem_ball, dist_pi_lt_iff hr, mem_Ioo]
  constructor
  · intro h
    have h0 := h 0
    rw [Real.dist_eq, abs_lt] at h0
    constructor <;> linarith [h0.1, h0.2]
  · intro h i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [h.1, h.2]

example (A : Set ℝ) : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' A = {x : Fin 1 → ℝ | x 0 ∈ A} := by
  rfl

example (x₀ : Fin 1 → ℝ) (r : ℝ) (hr : 0 < r) :
    (volume (ball x₀ r : Set (Fin 1 → ℝ))).toReal = (x₀ 0 + r) - (x₀ 0 - r) := by
  rw [Real.volume_pi_ball _ hr]
  simp only [Fintype.card_fin, pow_one, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 2*r)]
  ring

example (P : Polynomial ℝ) : Continuous fun t : ℝ => P.eval t := P.continuous
