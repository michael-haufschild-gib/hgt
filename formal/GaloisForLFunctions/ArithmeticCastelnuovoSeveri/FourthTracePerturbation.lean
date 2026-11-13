import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Fourth-trace perturbations controlled by the second moment

Frobenius Cauchy–Schwarz and operator norm multiplication bounds control
quartic mixed terms without assuming a fourth-moment bound for the large matrix.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Entrywise squared Hilbert–Schmidt norm. -/
def matrixFrobeniusEnergy (A : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

private theorem matrixFrobeniusEnergy_nonneg' (A : Matrix n n ℂ) : 0 ≤ matrixFrobeniusEnergy A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private theorem matrixFrobeniusEnergy_adjoint (A : Matrix n n ℂ) : matrixFrobeniusEnergy Aᴴ = matrixFrobeniusEnergy A := by
  simp only [matrixFrobeniusEnergy, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

/-- The trace pairing is bounded by the two Frobenius norms. -/
theorem norm_trace_mul_le_frobenius (A B : Matrix n n ℂ) :
    ‖(A * B).trace‖ ≤ Real.sqrt (matrixFrobeniusEnergy A) * Real.sqrt (matrixFrobeniusEnergy B) := by
  classical
  let S : ℝ := ∑ p : n × n, ‖A p.1 p.2‖ * ‖B p.2 p.1‖
  have hS : ‖(A * B).trace‖ ≤ S := by
    unfold Matrix.trace
    calc ‖∑ i, (A * B) i i‖ ≤ ∑ i, ‖(A * B) i i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖B j i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa only [Matrix.mul_apply, norm_mul] using
          norm_sum_le (Finset.univ : Finset n) (fun j => A i j * B j i)
      _ = S := by simp only [S, Fintype.sum_prod_type]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (n × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.2 p.1‖)
  have hsumA : (∑ p : n × n, ‖A p.1 p.2‖ ^ 2) = matrixFrobeniusEnergy A := by
    simp only [Fintype.sum_prod_type, matrixFrobeniusEnergy]
  have hsumB : (∑ p : n × n, ‖B p.2 p.1‖ ^ 2) = matrixFrobeniusEnergy B := by
    simp only [Fintype.sum_prod_type, matrixFrobeniusEnergy]
    exact Finset.sum_comm
  rw [hsumA, hsumB] at hcs
  have hsq : ‖(A * B).trace‖ ^ 2 ≤ matrixFrobeniusEnergy A * matrixFrobeniusEnergy B :=
    (pow_le_pow_left₀ (norm_nonneg _) hS 2).trans hcs
  calc ‖(A * B).trace‖ = Real.sqrt (‖(A * B).trace‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (matrixFrobeniusEnergy A * matrixFrobeniusEnergy B) := Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_mul (matrixFrobeniusEnergy_nonneg' A) _

/-- Left multiplication costs its operator norm in Frobenius energy. -/
theorem matrixFrobeniusEnergy_mul_le_opNorm (A B : Matrix n n ℂ) :
    matrixFrobeniusEnergy (A * B) ≤ ‖A‖ ^ 2 * matrixFrobeniusEnergy B := by
  classical
  have hcol (j : n) : (∑ i, ‖(A * B) i j‖ ^ 2) ≤
      ‖A‖ ^ 2 * ∑ i, ‖B i j‖ ^ 2 := by
    let v : EuclideanSpace ℂ n := (EuclideanSpace.equiv n ℂ).symm (fun i => B i j)
    have hv : v.ofLp = fun i => B i j := rfl
    have hm : A *ᵥ v.ofLp = fun i => (A * B) i j := by
      funext i
      simp only [hv, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have h := Matrix.l2_opNorm_mulVec A v
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [hm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, mul_pow] at hsq
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsq
    exact hsq
  rw [matrixFrobeniusEnergy, Finset.sum_comm]
  calc (∑ j, ∑ i, ‖(A * B) i j‖ ^ 2) ≤
      ∑ j, ‖A‖ ^ 2 * ∑ i, ‖B i j‖ ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = ‖A‖ ^ 2 * matrixFrobeniusEnergy B := by rw [← Finset.mul_sum, Finset.sum_comm]; rfl

/-- Right multiplication obeys the same Frobenius bound. -/
theorem matrixFrobeniusEnergy_mul_le_opNorm_right (A B : Matrix n n ℂ) :
    matrixFrobeniusEnergy (A * B) ≤ ‖B‖ ^ 2 * matrixFrobeniusEnergy A := by
  have h := matrixFrobeniusEnergy_mul_le_opNorm Bᴴ Aᴴ
  rw [← Matrix.conjTranspose_mul, matrixFrobeniusEnergy_adjoint, matrixFrobeniusEnergy_adjoint] at h
  simpa only [← Matrix.star_eq_conjTranspose, norm_star] using h

private theorem sqrt_matrixFrobeniusEnergy_mul_le (A B : Matrix n n ℂ) :
    Real.sqrt (matrixFrobeniusEnergy (A * B)) ≤ ‖A‖ * Real.sqrt (matrixFrobeniusEnergy B) := by
  have h := Real.sqrt_le_sqrt (matrixFrobeniusEnergy_mul_le_opNorm A B)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

private theorem sqrt_matrixFrobeniusEnergy_mul_le_right (A B : Matrix n n ℂ) :
    Real.sqrt (matrixFrobeniusEnergy (A * B)) ≤ ‖B‖ * Real.sqrt (matrixFrobeniusEnergy A) := by
  have h := Real.sqrt_le_sqrt (matrixFrobeniusEnergy_mul_le_opNorm_right A B)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- The cubic-linear trace term uses the second moment of the large matrix. -/
theorem norm_trace_cube_mul_le_secondMoment (P Q : Matrix n n ℂ) :
    ‖(P ^ 3 * Q).trace‖ ≤ ‖P‖ * ‖Q‖ * matrixFrobeniusEnergy P := by
  have hid : P ^ 3 * Q = (P * P) * (P * Q) := by noncomm_ring
  rw [hid]
  calc ‖((P * P) * (P * Q)).trace‖ ≤
      Real.sqrt (matrixFrobeniusEnergy (P * P)) * Real.sqrt (matrixFrobeniusEnergy (P * Q)) :=
        norm_trace_mul_le_frobenius _ _
    _ ≤ (‖P‖ * Real.sqrt (matrixFrobeniusEnergy P)) * (‖Q‖ * Real.sqrt (matrixFrobeniusEnergy P)) :=
      mul_le_mul (sqrt_matrixFrobeniusEnergy_mul_le P P) (sqrt_matrixFrobeniusEnergy_mul_le_right P Q)
        (Real.sqrt_nonneg _) (by positivity)
    _ = ‖P‖ * ‖Q‖ * (Real.sqrt (matrixFrobeniusEnergy P)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (matrixFrobeniusEnergy_nonneg' P)]

theorem norm_trace_alternating_four_le_secondMoment (P Q : Matrix n n ℂ) :
    ‖((P * Q) * (P * Q)).trace‖ ≤ ‖Q‖ ^ 2 * matrixFrobeniusEnergy P := by
  calc _ ≤ Real.sqrt (matrixFrobeniusEnergy (P * Q)) * Real.sqrt (matrixFrobeniusEnergy (P * Q)) :=
      norm_trace_mul_le_frobenius _ _
    _ = matrixFrobeniusEnergy (P * Q) := by rw [← sq, Real.sq_sqrt (matrixFrobeniusEnergy_nonneg' _)]
    _ ≤ _ := matrixFrobeniusEnergy_mul_le_opNorm_right P Q

/-- The two square blocks obey the same second-moment estimate. -/
theorem norm_trace_square_mul_square_le_secondMoment (P Q : Matrix n n ℂ) :
    ‖(P ^ 2 * Q ^ 2).trace‖ ≤ ‖Q‖ ^ 2 * matrixFrobeniusEnergy P := by
  have hc : (P ^ 2 * Q ^ 2).trace = ((Q * P) * (P * Q)).trace := by
    simpa only [pow_two, mul_assoc] using Matrix.trace_mul_cycle (P * P) Q Q
  rw [hc]
  calc _ ≤ Real.sqrt (matrixFrobeniusEnergy (Q * P)) * Real.sqrt (matrixFrobeniusEnergy (P * Q)) :=
      norm_trace_mul_le_frobenius _ _
    _ ≤ (‖Q‖ * Real.sqrt (matrixFrobeniusEnergy P)) * (‖Q‖ * Real.sqrt (matrixFrobeniusEnergy P)) :=
      mul_le_mul (sqrt_matrixFrobeniusEnergy_mul_le Q P) (sqrt_matrixFrobeniusEnergy_mul_le_right P Q)
        (Real.sqrt_nonneg _) (by positivity)
    _ = ‖Q‖ ^ 2 * (Real.sqrt (matrixFrobeniusEnergy P)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (matrixFrobeniusEnergy_nonneg' P)]

private theorem matrixFrobeniusEnergy_le_card_mul_opNorm_sq (Q : Matrix n n ℂ) :
    matrixFrobeniusEnergy Q ≤ (Fintype.card n : ℝ) * ‖Q‖ ^ 2 := by
  have h := matrixFrobeniusEnergy_mul_le_opNorm Q (1 : Matrix n n ℂ)
  rw [mul_one] at h
  have hi : matrixFrobeniusEnergy (1 : Matrix n n ℂ) = (Fintype.card n : ℝ) := by
    simp [matrixFrobeniusEnergy, Matrix.one_apply, apply_ite]
  rw [hi, mul_comm] at h
  exact h

private theorem sqrt_matrixFrobeniusEnergy_le_sqrt_card_mul_norm (Q : Matrix n n ℂ) :
    Real.sqrt (matrixFrobeniusEnergy Q) ≤ Real.sqrt (Fintype.card n : ℝ) * ‖Q‖ := by
  have h := Real.sqrt_le_sqrt (matrixFrobeniusEnergy_le_card_mul_opNorm_sq Q)
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- A cubic small factor costs only the square root of the large factor's energy. -/
theorem norm_trace_mul_cube_le_secondMoment (P Q : Matrix n n ℂ) :
    ‖(P * Q ^ 3).trace‖ ≤
      ‖Q‖ ^ 3 * Real.sqrt (Fintype.card n : ℝ) * Real.sqrt (matrixFrobeniusEnergy P) := by
  calc _ ≤ Real.sqrt (matrixFrobeniusEnergy P) * Real.sqrt (matrixFrobeniusEnergy (Q ^ 3)) :=
      norm_trace_mul_le_frobenius _ _
    _ ≤ Real.sqrt (matrixFrobeniusEnergy P) * (‖Q‖ * (‖Q‖ *
        (Real.sqrt (Fintype.card n : ℝ) * ‖Q‖))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      calc
        Real.sqrt (matrixFrobeniusEnergy (Q ^ 3)) = Real.sqrt (matrixFrobeniusEnergy (Q * (Q * Q))) := by
          congr 2
          noncomm_ring
        _ ≤ ‖Q‖ * Real.sqrt (matrixFrobeniusEnergy (Q * Q)) := sqrt_matrixFrobeniusEnergy_mul_le _ _
        _ ≤ ‖Q‖ * (‖Q‖ * Real.sqrt (matrixFrobeniusEnergy Q)) := by
          gcongr
          exact sqrt_matrixFrobeniusEnergy_mul_le Q Q
        _ ≤ _ := by
          gcongr
          exact sqrt_matrixFrobeniusEnergy_le_sqrt_card_mul_norm Q
    _ = _ := by ring

/-- The pure fourth term is bounded by dimension times the fourth operator norm. -/
theorem norm_trace_fourth_le_card (Q : Matrix n n ℂ) :
    ‖(Q ^ 4).trace‖ ≤ (Fintype.card n : ℝ) * ‖Q‖ ^ 4 := by
  have h := norm_trace_alternating_four_le_secondMoment Q Q
  have he : (Q * Q) * (Q * Q) = Q ^ 4 := by noncomm_ring
  rw [he] at h
  calc _ ≤ ‖Q‖ ^ 2 * matrixFrobeniusEnergy Q := h
    _ ≤ ‖Q‖ ^ 2 * ((Fintype.card n : ℝ) * ‖Q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (matrixFrobeniusEnergy_le_card_mul_opNorm_sq Q) (sq_nonneg _)
    _ = _ := by ring

/-- Cyclicity reduces the noncommutative quartic expansion to five trace words. -/
theorem trace_fourth_add_sub (P Q : Matrix n n ℂ) :
    ((P + Q) ^ 4 - P ^ 4).trace =
      4 * (P ^ 3 * Q).trace + 4 * (P ^ 2 * Q ^ 2).trace +
      2 * ((P * Q) * (P * Q)).trace + 4 * (P * Q ^ 3).trace + (Q ^ 4).trace := by
  have h1 : (P * P * Q * P).trace = (P * P * P * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P * P * Q) (P)
  have h3 : (P * Q * P * P).trace = (P * P * P * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P * Q) (P * P)
  have h5 : (P * Q * Q * P).trace = (P * P * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P * Q * Q) (P)
  have h7 : (Q * P * P * P).trace = (P * P * P * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q) (P * P * P)
  have h8 : (Q * P * P * Q).trace = (P * P * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q) (P * P * Q)
  have h9 : (Q * P * Q * P).trace = (P * Q * P * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q) (P * Q * P)
  have h10 : (Q * P * Q * Q).trace = (P * Q * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q) (P * Q * Q)
  have h11 : (Q * Q * P * P).trace = (P * P * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q * Q) (P * P)
  have h12 : (Q * Q * P * Q).trace = (P * Q * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q * Q) (P * Q)
  have h13 : (Q * Q * Q * P).trace = (P * Q * Q * Q).trace := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (Q * Q * Q) (P)
  have he : (P + Q) ^ 4 - P ^ 4 =
      (P * P * P * Q) +
      (P * P * Q * P) +
      (P * P * Q * Q) +
      (P * Q * P * P) +
      (P * Q * P * Q) +
      (P * Q * Q * P) +
      (P * Q * Q * Q) +
      (Q * P * P * P) +
      (Q * P * P * Q) +
      (Q * P * Q * P) +
      (Q * P * Q * Q) +
      (Q * Q * P * P) +
      (Q * Q * P * Q) +
      (Q * Q * Q * P) +
      (Q * Q * Q * Q) := by noncomm_ring
  rw [he]
  simp only [Matrix.trace_add, h1, h3, h5, h7, h8, h9, h10, h11, h12, h13]
  simp only [pow_succ, pow_zero, mul_one, one_mul, ← mul_assoc]
  ring

/-- Quartic perturbation uses the second moment of the large matrix, together
with operator norms of both factors. No fourth moment is assumed. -/
theorem norm_trace_fourth_perturbation_le_secondMoment (P Q : Matrix n n ℂ) :
    ‖((P + Q) ^ 4 - P ^ 4).trace‖ ≤
      4 * ‖P‖ * ‖Q‖ * matrixFrobeniusEnergy P + 6 * ‖Q‖ ^ 2 * matrixFrobeniusEnergy P +
      4 * ‖Q‖ ^ 3 * Real.sqrt (Fintype.card n : ℝ) * Real.sqrt (matrixFrobeniusEnergy P) +
      (Fintype.card n : ℝ) * ‖Q‖ ^ 4 := by
  rw [trace_fourth_add_sub]
  have h1 := norm_add_le (4 * (P ^ 3 * Q).trace) (4 * (P ^ 2 * Q ^ 2).trace)
  have h2 := norm_add_le (4 * (P ^ 3 * Q).trace + 4 * (P ^ 2 * Q ^ 2).trace)
    (2 * ((P * Q) * (P * Q)).trace)
  have h3 := norm_add_le (4 * (P ^ 3 * Q).trace + 4 * (P ^ 2 * Q ^ 2).trace +
    2 * ((P * Q) * (P * Q)).trace) (4 * (P * Q ^ 3).trace)
  have h4 := norm_add_le (4 * (P ^ 3 * Q).trace + 4 * (P ^ 2 * Q ^ 2).trace +
    2 * ((P * Q) * (P * Q)).trace + 4 * (P * Q ^ 3).trace) (Q ^ 4).trace
  norm_num only [norm_mul, Complex.norm_ofNat] at h1 h2 h3 h4
  have h31 := norm_trace_cube_mul_le_secondMoment P Q
  have h22 := norm_trace_square_mul_square_le_secondMoment P Q
  have h22' := norm_trace_alternating_four_le_secondMoment P Q
  have h13 := norm_trace_mul_cube_le_secondMoment P Q
  have h04 := norm_trace_fourth_le_card Q
  linarith only [h1, h2, h3, h4, h31, h22, h22', h13, h04]

/-- Centering the quartic inertia polynomial removes its odd powers. -/
theorem quartic_inertia_centered (H : Matrix n n ℂ) :
    14 * H - 23 * H ^ 2 + 16 * H ^ 3 - 4 * H ^ 4 =
      3 + (H - 1) ^ 2 - 4 * (H - 1) ^ 4 := by
  noncomm_ring <;> simp

/-- A positive spectrum of mean one and upper edge `α ≤ 2` has fourth centered
moment at most `α - 1` times its dimension. -/
theorem sum_fourth_centered_le_edge_defect {ι : Type*} [Fintype ι]
    (x : ι → ℝ) {α : ℝ} (hα : α ≤ 2)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ α)
    (hsum : ∑ i, x i = (Fintype.card ι : ℝ)) :
    ∑ i, (x i - 1) ^ 4 ≤ (α - 1) * (Fintype.card ι : ℝ) := by
  have hpoint (i : ι) : (x i - 1) ^ 4 ≤ (α - 2) * x i + 1 := by
    have hx2 : x i ≤ 2 := (hx i).2.trans hα
    have hb : (x i - 1) ^ 2 ≤ 1 := by nlinarith only [(hx i).1, hx2]
    have h4 : (x i - 1) ^ 4 ≤ (x i - 1) ^ 2 := by
      nlinarith only [sq_nonneg (x i - 1), mul_nonneg (sq_nonneg (x i - 1)) (sub_nonneg.mpr hb)]
    have hxx := mul_nonneg (hx i).1 (sub_nonneg.mpr (hx i).2)
    nlinarith only [h4, hxx]
  calc _ ≤ ∑ i, ((α - 2) * x i + 1) := Finset.sum_le_sum fun i _ => hpoint i
    _ = (α - 1) * (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.norm_trace_fourth_perturbation_le_secondMoment
