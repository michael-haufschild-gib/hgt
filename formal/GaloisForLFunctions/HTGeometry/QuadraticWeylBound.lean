/-
Composing the two halves: the correlation of a quadratic phase is a linear exponential sum.

For `f(n) = α n² + β n` the differenced phase is

    f(n + h) - f(n) = (2αh)·n + (αh² + βh),

which is *linear* in `n`.  So each correlation of the quadratic exponential sum is a geometric series,
and the linear bound applies to it:

    ‖ Σ_{n < M} e(f(n+h) - f(n)) ‖  ≤  1 / (2‖2αh‖).

Feeding this into the van der Corput correlation bound is Weyl's inequality for quadratics: the step
that turns a bound with no cancellation into one with square-root-type cancellation, and the first
place where an exponent is *derived* rather than recorded.
-/
import GaloisForLFunctions.HTGeometry.LinearExponentialSum

namespace HTGeometry

open Finset Complex

/-- Conjugation reverses the character. -/
theorem conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The character turns sums into products, in the form needed below. -/
theorem ee_sub (x y : ℝ) : ee x * ee (-y) = ee (x - y) := by
  rw [← ee_add, sub_eq_add_neg]

/-- A quadratic phase. -/
noncomputable def quadPhase (α β : ℝ) (n : ℝ) : ℝ := α * n^(2 : ℕ) + β * n

/-- **The differenced quadratic phase is linear.** -/
theorem quadPhase_diff (α β : ℝ) (h n : ℝ) :
    quadPhase α β (n + h) - quadPhase α β n = (2 * α * h) * n + (α * h^(2 : ℕ) + β * h) := by
  unfold quadPhase
  ring

/-- **The correlation of a quadratic exponential sum is a rotated geometric series.** -/
theorem quad_correlation_eq (α β : ℝ) (M : ℕ) (h : ℝ) :
    ∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + h)) * (starRingEnd ℂ) (ee (quadPhase α β n))
      = ee (α * h^(2 : ℕ) + β * h) * ∑ n ∈ range M, ee ((n : ℝ) * (2 * α * h)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [conj_ee, ee_sub, quadPhase_diff]
  rw [← ee_add]
  congr 1
  ring

/-- **The quadratic correlation bound.**  Each correlation of a quadratic exponential sum obeys the
linear bound at the differenced frequency `2αh`, uniformly in the length. -/
theorem norm_quad_correlation_le (α β : ℝ) (M : ℕ) (h : ℝ)
    (hd : 0 < distToInt (2 * α * h)) :
    ‖∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + h)) * (starRingEnd ℂ) (ee (quadPhase α β n))‖
      ≤ 1 / (2 * distToInt (2 * α * h)) := by
  rw [quad_correlation_eq, norm_mul, norm_ee, one_mul]
  exact norm_sum_ee_le (2 * α * h) M hd

/-- The trivial bound on the same correlation: it has `M` unimodular terms. -/
theorem norm_quad_correlation_le_card (α β : ℝ) (M : ℕ) (h : ℝ) :
    ‖∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + h)) * (starRingEnd ℂ) (ee (quadPhase α β n))‖
      ≤ (M : ℝ) := by
  calc ‖∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + h))
        * (starRingEnd ℂ) (ee (quadPhase α β n))‖
      ≤ ∑ n ∈ range M, ‖ee (quadPhase α β ((n : ℝ) + h))
        * (starRingEnd ℂ) (ee (quadPhase α β n))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ range M, (1 : ℝ) := Finset.sum_congr rfl fun n _ => by
        rw [norm_mul, norm_ee, RCLike.norm_conj, norm_ee, one_mul]
    _ = (M : ℝ) := by simp

/-- **The dichotomy that drives Weyl's inequality.**  Every correlation of a quadratic exponential
sum is bounded by the minimum of the trivial bound and the reciprocal of the distance of its
differenced frequency to the integers. -/
theorem norm_quad_correlation_le_min (α β : ℝ) (M : ℕ) (h : ℝ)
    (hd : 0 < distToInt (2 * α * h)) :
    ‖∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + h)) * (starRingEnd ℂ) (ee (quadPhase α β n))‖
      ≤ min (M : ℝ) (1 / (2 * distToInt (2 * α * h))) :=
  le_min (norm_quad_correlation_le_card α β M h) (norm_quad_correlation_le α β M h hd)

/-- At shift `h = 0` the correlation is exactly the length: there is no cancellation on the
diagonal, which is the term the van der Corput inequality pays for in full. -/
@[simp] theorem quad_correlation_zero (α β : ℝ) (M : ℕ) :
    ∑ n ∈ range M, ee (quadPhase α β ((n : ℝ) + 0)) * (starRingEnd ℂ) (ee (quadPhase α β n))
      = (M : ℂ) := by
  have hterm : ∀ n ∈ range M,
      ee (quadPhase α β ((n : ℝ) + 0)) * (starRingEnd ℂ) (ee (quadPhase α β n)) = 1 := by
    intro n _
    rw [add_zero, conj_ee, ee_sub, sub_self]
    simp [ee]
  rw [Finset.sum_congr rfl hterm]
  simp

end HTGeometry
