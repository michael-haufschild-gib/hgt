import GaloisForLFunctions.HTGeometry.HardySpace

/-!
# Polarized polynomial Parseval identity

This file supplies the complex cross-term form of polynomial Parseval on a circle.  Unlike the
norm-square specialization, it retains the phase of two different coefficient rows.
-/

open MeasureTheory Complex
open scoped BigOperators Real Interval ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Polarized polynomial Parseval on the circle of radius `r`. -/
theorem circleAverage_poly_mul_conj
    (r : ℝ) (M : ℕ) (c d : ℕ → ℂ) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (∫ theta in (0 : ℝ)..2 * Real.pi,
          (∑ k ∈ Finset.range M, c k * circleMap 0 r theta ^ k) *
            conj (∑ j ∈ Finset.range M, d j * circleMap 0 r theta ^ j)) =
      ∑ k ∈ Finset.range M,
        c k * conj (d k) * (r : ℂ) ^ (2 * k) := by
  let z : ℝ → ℂ := fun theta => circleMap 0 r theta
  have hpoint (theta : ℝ) :
      (∑ k ∈ Finset.range M, c k * z theta ^ k) *
          conj (∑ j ∈ Finset.range M, d j * z theta ^ j) =
        ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c k * conj (d j) * (z theta ^ k * conj (z theta ^ j)) := by
    change (∑ k ∈ Finset.range M, c k * z theta ^ k) *
        (starRingEnd ℂ) (∑ j ∈ Finset.range M, d j * z theta ^ j) = _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    simp only [starRingEnd_apply]
    ring
  have hcont (k j : ℕ) : Continuous
      (fun theta : ℝ =>
        c k * conj (d j) * (z theta ^ k * conj (z theta ^ j))) := by
    fun_prop
  have hintegral :
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        (∑ k ∈ Finset.range M, c k * z theta ^ k) *
          conj (∑ j ∈ Finset.range M, d j * z theta ^ j)) =
        ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M,
          c k * conj (d j) *
            (∫ theta in (0 : ℝ)..2 * Real.pi,
              z theta ^ k * conj (z theta ^ j)) := by
    rw [intervalIntegral.integral_congr (fun theta _ => hpoint theta),
      intervalIntegral.integral_finsetSum
        (fun k _ => (continuous_finsetSum _ (fun j _ => hcont k j)).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_finsetSum
      (fun j _ => (hcont k j).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        (∑ k ∈ Finset.range M, c k * z theta ^ k) *
          conj (∑ j ∈ Finset.range M, d j * z theta ^ j)) = _
  rw [hintegral]
  simp only [z]
  simp_rw [integral_circleMap_pow_conj]
  have hcollapse (k : ℕ) (hk : k ∈ Finset.range M) :
      (∑ j ∈ Finset.range M,
        c k * conj (d j) *
          (if k = j then (r : ℂ) ^ (2 * k) * (2 * Real.pi) else 0)) =
        c k * conj (d k) * (r : ℂ) ^ (2 * k) * (2 * Real.pi) := by
    rw [Finset.sum_eq_single_of_mem k hk]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg (fun h => hj h.symm), mul_zero]
  have hsum :
      (∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M,
        c k * conj (d j) *
          (if k = j then (r : ℂ) ^ (2 * k) * (2 * Real.pi) else 0)) =
        ∑ k ∈ Finset.range M,
          c k * conj (d k) * (r : ℂ) ^ (2 * k) * (2 * Real.pi) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hcollapse k hk
  rw [hsum, ← Finset.sum_mul]
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  field_simp [hpi]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
