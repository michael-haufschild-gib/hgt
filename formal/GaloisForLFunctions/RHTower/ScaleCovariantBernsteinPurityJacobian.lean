import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPurityChart
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Jacobian of the global Bernstein purity chart

Rows are purity-jet coordinates and columns are moment coordinates.  The coordinate Jacobian is
lower triangular, and its diagonal is explicit.  Hence the global pointed chart has no critical
point.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem eraseMoment_update_self
    (m : ℕ → ℝ) (r : ℕ) (t : ℝ) :
    eraseMoment (Function.update m r t) r = eraseMoment m r := by
  funext j
  by_cases hj : j = r <;> simp [eraseMoment, hj]

private theorem bernsteinScalePurityLower_update_self
    (m : ℕ → ℝ) (N r : ℕ) (t : ℝ) :
    bernsteinScalePurityLower (Function.update m r t) N r =
      bernsteinScalePurityLower m N r := by
  rw [bernsteinScalePurityLower, bernsteinScalePurityLower,
    eraseMoment_update_self]

/-- Coordinate-slice definition of the finite purity-jet Jacobian. -/
def bernsteinPurityJetJacobian (N : ℕ) (m : ℕ → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun r j => deriv
    (fun t : ℝ =>
      (bernsteinScalePurityPolynomial (Function.update m (j : ℕ) t) N).coeff r)
    (m j)

/-- A moment coordinate above the output degree has zero partial derivative. -/
theorem bernsteinPurityJetJacobian_apply_eq_zero_of_lt
    (N : ℕ) (m : ℕ → ℝ) {r j : Fin (N + 1)} (hrj : r < j) :
    bernsteinPurityJetJacobian N m r j = 0 := by
  rw [bernsteinPurityJetJacobian]
  have hfun :
      (fun t : ℝ =>
        (bernsteinScalePurityPolynomial (Function.update m (j : ℕ) t) N).coeff r) =
      fun _ : ℝ => (bernsteinScalePurityPolynomial m N).coeff r := by
    funext t
    apply coeff_bernsteinScalePurityPolynomial_congr_prefix
    intro k hk
    have hkj : k ≠ (j : ℕ) :=
      Nat.ne_of_lt (lt_of_le_of_lt hk hrj)
    simp [hkj]
  rw [hfun, deriv_const]

/-- The diagonal partial derivative in degree zero. -/
private theorem deriv_bernsteinPurityJet_zero_slice
    (N : ℕ) (m : ℕ → ℝ) :
    deriv
      (fun t : ℝ =>
        (bernsteinScalePurityPolynomial (Function.update m 0 t) N).coeff 0)
      (m 0) = 2 * m 0 := by
  have hfun :
      (fun t : ℝ =>
        (bernsteinScalePurityPolynomial (Function.update m 0 t) N).coeff 0) =
      fun t : ℝ => t ^ 2 := by
    funext t
    rw [coeff_zero_bernsteinScalePurityPolynomial]
    simp
  rw [hfun]
  simpa using ((hasDerivAt_id (m 0)).pow 2).deriv

/-- The diagonal partial derivative in every positive degree. -/
private theorem deriv_bernsteinPurityJet_positive_slice
    (N : ℕ) (m : ℕ → ℝ) {r : ℕ} (hr0 : 0 < r) (hrN : r ≤ N) :
    deriv
      (fun t : ℝ =>
        (bernsteinScalePurityPolynomial (Function.update m r t) N).coeff r)
      (m r) = 2 * (-1 : ℝ) ^ r * N.choose r * m 0 := by
  let c : ℝ := 2 * (-1 : ℝ) ^ r * N.choose r * m 0
  let q : ℝ := bernsteinScalePurityLower m N r
  have hrne : r ≠ 0 := hr0.ne'
  have hfun :
      (fun t : ℝ =>
        (bernsteinScalePurityPolynomial (Function.update m r t) N).coeff r) =
      fun t : ℝ => c * t + q := by
    funext t
    rw [coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower
      (Function.update m r t) N hr0 hrN]
    rw [bernsteinScalePurityLower_update_self]
    have hself : Function.update m r t r = t := by
      simp
    have hzero : Function.update m r t 0 = m 0 := by
      simp [Ne.symm hrne]
    rw [hself, hzero]
  rw [hfun]
  have hderiv := (((hasDerivAt_id (m r)).const_mul c).add_const q).deriv
  simpa only [mul_one, add_zero, c, id_eq] using hderiv

/-- Uniform diagonal law for the purity-jet Jacobian. -/
theorem bernsteinPurityJetJacobian_diagonal
    (N : ℕ) (m : ℕ → ℝ) (r : Fin (N + 1)) :
    bernsteinPurityJetJacobian N m r r =
      2 * (-1 : ℝ) ^ (r : ℕ) * N.choose (r : ℕ) * m 0 := by
  rw [bernsteinPurityJetJacobian]
  by_cases hr0 : (r : ℕ) = 0
  · have hr : r = (0 : Fin (N + 1)) := Fin.ext hr0
    subst r
    simpa using deriv_bernsteinPurityJet_zero_slice N m
  · exact deriv_bernsteinPurityJet_positive_slice N m
      (Nat.pos_of_ne_zero hr0) (Nat.le_of_lt_succ r.isLt)

/-- The coordinate Jacobian is lower triangular. -/
theorem bernsteinPurityJetJacobian_lowerTriangular
    (N : ℕ) (m : ℕ → ℝ) :
    (bernsteinPurityJetJacobian N m).BlockTriangular OrderDual.toDual := by
  intro r j hrj
  exact bernsteinPurityJetJacobian_apply_eq_zero_of_lt N m hrj

/-- Closed determinant formula for the global purity chart. -/
theorem det_bernsteinPurityJetJacobian
    (N : ℕ) (m : ℕ → ℝ) :
    (bernsteinPurityJetJacobian N m).det =
      (-1 : ℝ) ^ (N * (N + 1) / 2) *
        (2 * m 0) ^ (N + 1) *
          ∏ r : Fin (N + 1), (N.choose (r : ℕ) : ℝ) := by
  rw [Matrix.det_of_lowerTriangular _
    (bernsteinPurityJetJacobian_lowerTriangular N m)]
  simp_rw [bernsteinPurityJetJacobian_diagonal]
  calc
    (∏ r : Fin (N + 1),
        2 * (-1 : ℝ) ^ (r : ℕ) * N.choose (r : ℕ) * m 0) =
        ∏ r : Fin (N + 1),
          (2 * m 0) * (((-1 : ℝ) ^ (r : ℕ)) * N.choose (r : ℕ)) := by
            apply Finset.prod_congr rfl
            intro r hr
            ring
    _ = (∏ _r : Fin (N + 1), (2 * m 0)) *
        ∏ r : Fin (N + 1),
          (((-1 : ℝ) ^ (r : ℕ)) * N.choose (r : ℕ)) := by
            rw [Finset.prod_mul_distrib]
    _ = (2 * m 0) ^ (N + 1) *
        ((∏ r : Fin (N + 1), (-1 : ℝ) ^ (r : ℕ)) *
          ∏ r : Fin (N + 1), (N.choose (r : ℕ) : ℝ)) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ (N * (N + 1) / 2) *
        (2 * m 0) ^ (N + 1) *
          ∏ r : Fin (N + 1), (N.choose (r : ℕ) : ℝ) := by
            have hsum :
                (∑ r : Fin (N + 1), (r : ℕ)) = N * (N + 1) / 2 := by
              rw [Finset.sum_fin_eq_sum_range]
              calc
                (∑ x ∈ Finset.range (N + 1),
                    if h : x < N + 1 then x else 0) =
                    ∑ x ∈ Finset.range (N + 1), x := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      simp [Finset.mem_range.mp hx]
                _ = N * (N + 1) / 2 := by
                      rw [Finset.sum_range_id]
                      simp only [Nat.add_sub_cancel]
                      rw [Nat.mul_comm (N + 1) N]
            rw [Finset.prod_pow_eq_pow_sum, hsum]
            ring

/-- The pointed purity chart has no critical point. -/
theorem det_bernsteinPurityJetJacobian_ne_zero
    (N : ℕ) {m : ℕ → ℝ} (hm0 : m 0 ≠ 0) :
    (bernsteinPurityJetJacobian N m).det ≠ 0 := by
  rw [det_bernsteinPurityJetJacobian]
  refine mul_ne_zero
    (mul_ne_zero
      (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
      (pow_ne_zero _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hm0))) ?_
  exact Finset.prod_ne_zero_iff.mpr fun r _ => by
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ r.isLt)).ne'

end

end RHTower
