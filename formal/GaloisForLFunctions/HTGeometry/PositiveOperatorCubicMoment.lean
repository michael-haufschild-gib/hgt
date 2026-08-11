import Mathlib.Analysis.InnerProductSpace.Positive
import GaloisForLFunctions.HTGeometry.BesselPSD

/-!
# Cubic moment amplification for positive operators

A positive operator turns a lower bound for its first vector moment into the same cubed lower
bound for its third vector moment.  The proof uses ordinary Cauchy--Schwarz together with
Cauchy--Schwarz for the positive semidefinite form induced by the operator.
-/

open RCLike
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If `T` is positive and `x` is a unit vector, then its third vector moment dominates the cube
of its first vector moment. -/
theorem IsPositive.re_inner_pow_three_ge {T : H →L[ℂ] H}
    (hT : T.IsPositive) (x : H) (hx : ‖x‖ = 1) :
    (re (inner ℂ x (T x))) ^ 3 ≤ re (inner ℂ x ((T ^ 3) x)) := by
  let Q : H → ℝ := fun y => re (inner ℂ y (T y))
  have hQ_nonneg : ∀ y : H, 0 ≤ Q y := hT.re_inner_nonneg_right
  have hform : ‖inner ℂ (T x) (T x)‖ ^ 2 ≤ Q x * Q (T x) := by
    have h := HTGeometry.cauchy_schwarz_psd
      (fun u v : H => inner ℂ v (T u))
      (fun u v w => by rw [map_add, inner_add_right])
      (fun c u v => by rw [map_smul, inner_smul_right])
      (fun u v => by
        calc
          inner ℂ u (T v) = inner ℂ (T u) v :=
            (hT.inner_left_eq_inner_right u v).symm
          _ = (starRingEnd ℂ) (inner ℂ v (T u)) := (inner_conj_symm _ _).symm)
      hT.re_inner_nonneg_right x (T x)
    simpa [Q] using h
  have hinner_self : ‖inner ℂ (T x) (T x)‖ = ‖T x‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [hinner_self] at hform
  have ha0 : 0 ≤ re (inner ℂ x (T x)) := hT.re_inner_nonneg_right x
  have ha_le : re (inner ℂ x (T x)) ≤ ‖T x‖ := by
    calc
      re (inner ℂ x (T x)) ≤ ‖inner ℂ x (T x)‖ := re_le_norm _
      _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
      _ = ‖T x‖ := by rw [hx, one_mul]
  have hsq : (re (inner ℂ x (T x))) ^ 2 ≤ ‖T x‖ ^ 2 := by
    nlinarith [norm_nonneg (T x)]
  have hQx : Q x = re (inner ℂ x (T x)) := by
    rfl
  have hQTx : Q (T x) = re (inner ℂ x ((T ^ 3) x)) := by
    dsimp [Q]
    rw [hT.inner_left_eq_inner_right]
    simp [pow_succ]
  rw [hQx, hQTx] at hform
  by_cases ha : re (inner ℂ x (T x)) = 0
  · rw [ha]
    rw [← hQTx]
    simpa using hQ_nonneg (T x)
  · have ha_pos : 0 < re (inner ℂ x (T x)) := lt_of_le_of_ne ha0 (Ne.symm ha)
    nlinarith [sq_nonneg (‖T x‖ ^ 2 - (re (inner ℂ x (T x))) ^ 2)]

end ContinuousLinearMap
