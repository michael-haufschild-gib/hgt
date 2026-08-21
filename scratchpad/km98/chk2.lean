import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Metric Set Polynomial

example : True := by
  have h1 := @Lagrange.eq_interpolate
  have h2 := @Lagrange.interpolate_apply
  have h5 := @MeasureTheory.measure_biUnion_finset_le
  have h6 := @Real.volume_ball
  have h7 := @dist_pi_lt_iff
  trivial

example (s : Finset ℕ) (v : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    (Lagrange.basis s v i).eval x = ∏ j ∈ s.erase i, (Lagrange.basisDivisor (v i) (v j)).eval x := by
  simp [Lagrange.basis, eval_prod]

example (x y t : ℝ) : (Lagrange.basisDivisor x y).eval t = (x - y)⁻¹ * (t - y) := by
  simp [Lagrange.basisDivisor]

example (s : Finset ℕ) (v : ℕ → ℝ) (r : ℕ → ℝ) (x : ℝ) :
    (Lagrange.interpolate s v r).eval x = ∑ i ∈ s, r i * (Lagrange.basis s v i).eval x := by
  simp [Lagrange.interpolate_apply, eval_finset_sum]

example : MeasureTheory.MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
  MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
