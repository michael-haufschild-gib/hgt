import GaloisForLFunctions.HTGeometry.Sl2AdjointIrreducible
import GaloisForLFunctions.HTGeometry.BlockAverageAntiConcentration

/-!
# Polynomial observation of unipotent orbits

The polynomial coefficient mechanism of Nguyen–Wei, Lemma 6.7,
arXiv:2611.15182, gives explicit bounds from finitely many samples.
For the adjoint action of `sl₂`, three samples isolate the linear and quadratic
coefficients. A globally bounded orbit is fixed by the unipotent subgroup.
-/

noncomputable section

open Polynomial
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Sum of observations on a scaled interpolation grid. -/
def polynomialSampleMass (P : ℂ[X]) (R : ℂ) : ℝ :=
  ∑ i : Fin (P.natDegree + 1), ‖P.eval (R * (unitFixedNodes (P.natDegree + 1) i : ℂ))‖

/-- Every scaled coefficient is controlled by finitely many scaled observations.
The estimate also covers the zero polynomial and a collapsed sampling scale. -/
theorem scaled_coefficient_le_samples (P : ℂ[X]) (R : ℂ) (k : ℕ) :
    ‖P.coeff k * R ^ k‖ ≤
      polynomialSampleMass P R * unitCoeffConst (P.natDegree + 1) k := by
  let Q := P.comp (C R * X)
  have hd : Q.natDegree ≤ P.natDegree := by
    exact natDegree_comp_le.trans (by
      simpa using Nat.mul_le_mul_left P.natDegree (natDegree_C_mul_le R (X : ℂ[X])))
  have hd' : Q.degree < ((P.natDegree + 1 : ℕ) : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hd)
  have hi : Function.Injective
      (fun i : Fin (P.natDegree + 1) => (unitFixedNodes (P.natDegree + 1) i : ℂ)) :=
    Complex.ofReal_injective.comp unitFixedNodes_injective
  have hs (i : Fin (P.natDegree + 1)) :
      ‖Q.eval (unitFixedNodes (P.natDegree + 1) i : ℂ)‖ ≤ polynomialSampleMass P R := by
    simp only [Q, eval_comp, eval_mul, eval_C, eval_X]
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (P.eval (R * (unitFixedNodes (P.natDegree + 1) j : ℂ))))
      (Finset.mem_univ i)
  simpa only [Q, comp_C_mul_X_coeff, unitCoeffConst] using
    norm_coeff_le_of_nodes _ hi Q hd' hs k

/-- The odd part of the upper conjugation orbit reads the diagonal difference. -/
theorem upperConj_linear_coefficient (A : Matrix (Fin 2) (Fin 2) ℝ) (R : ℝ) :
    upperConj R A 0 1 - upperConj (-R) A 0 1 = 2 * R * (A 1 1 - A 0 0) := by
  rw [(upperConj_entry R A).2.1, (upperConj_entry (-R) A).2.1]
  ring

/-- The even second difference reads the opposite root coefficient. -/
theorem upperConj_quadratic_coefficient (A : Matrix (Fin 2) (Fin 2) ℝ) (R : ℝ) :
    upperConj R A 0 1 + upperConj (-R) A 0 1 - 2 * A 0 1 =
      -2 * R ^ 2 * A 1 0 := by
  rw [(upperConj_entry R A).2.1, (upperConj_entry (-R) A).2.1]
  ring

/-- Three orbit samples quantitatively recover the opposite root coordinate. -/
theorem upperConj_quadratic_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (R : ℝ) :
    |R ^ 2 * A 1 0| ≤
      (|upperConj R A 0 1| + |upperConj (-R) A 0 1| + 2 * |A 0 1|) / 2 := by
  have h := abs_add_le (upperConj R A 0 1 + upperConj (-R) A 0 1) (-(2 * A 0 1))
  simp only [← sub_eq_add_neg, abs_neg] at h
  rw [upperConj_quadratic_coefficient] at h
  have hn : |-2 * R ^ 2 * A 1 0| = 2 * |R ^ 2 * A 1 0| := by
    rw [mul_assoc, abs_mul]
    norm_num
  rw [hn, abs_mul (2 : ℝ) (A 0 1), abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith only [h, abs_add_le (upperConj R A 0 1) (upperConj (-R) A 0 1)]

/-- Two opposite samples quantitatively recover the diagonal difference. -/
theorem upperConj_linear_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (R : ℝ) :
    |R * (A 1 1 - A 0 0)| ≤
      (|upperConj R A 0 1| + |upperConj (-R) A 0 1|) / 2 := by
  have h := abs_add_le (upperConj R A 0 1) (-upperConj (-R) A 0 1)
  simp only [← sub_eq_add_neg, abs_neg] at h
  rw [upperConj_linear_coefficient, mul_assoc, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith only [h]

private theorem affine_bounded_slope_zero (a b C : ℝ)
    (h : ∀ t : ℝ, |b + t * a| ≤ C) : a = 0 := by
  by_contra ha
  have ht := h ((C + |b| + 1) / a)
  rw [div_mul_cancel₀ _ ha] at ht
  have hb := neg_abs_le b
  have hl := le_abs_self (b + (C + |b| + 1))
  linarith only [ht, hb, hl]

/-- An upper-unipotent conjugation orbit is bounded exactly on the centralizer. -/
theorem upperConj_bounded_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, ∀ i j, |upperConj t A i j| ≤ C) ↔
      A 1 0 = 0 ∧ A 1 1 = A 0 0 := by
  constructor
  · rintro ⟨C, hC⟩
    have h10 : A 1 0 = 0 := affine_bounded_slope_zero _ _ C fun t => by
      simpa only [(upperConj_entry t A).1] using hC t 0 0
    refine ⟨h10, ?_⟩
    have hd : A 1 1 - A 0 0 = 0 := affine_bounded_slope_zero _ _ C fun t => by
      simpa only [(upperConj_entry t A).2.1, h10, mul_zero, sub_zero] using hC t 0 1
    exact sub_eq_zero.mp hd
  · rintro ⟨h10, hd⟩
    refine ⟨|A 0 0| + |A 0 1| + |A 1 1|, fun t i j => ?_⟩
    obtain ⟨h00, h01, h10', h11⟩ := upperConj_entry t A
    fin_cases i <;> fin_cases j
    · change |upperConj t A 0 0| ≤ _
      rw [h00, h10, mul_zero, add_zero]
      linarith only [abs_nonneg (A 0 1), abs_nonneg (A 1 1)]
    · change |upperConj t A 0 1| ≤ _
      rw [h01, h10, hd, sub_self, mul_zero, mul_zero, add_zero, sub_zero]
      linarith only [abs_nonneg (A 0 0)]
    · change |upperConj t A 1 0| ≤ _
      rw [h10', h10, abs_zero]
      positivity
    · change |upperConj t A 1 1| ≤ _
      rw [h11, h10, mul_zero, sub_zero]
      linarith only [abs_nonneg (A 0 0), abs_nonneg (A 0 1)]

/-- The coefficient classification identifies bounded orbits with fixed matrices. -/
theorem upperConj_bounded_iff_fixed (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ C : ℝ, ∀ t : ℝ, ∀ i j, |upperConj t A i j| ≤ C) ↔
      ∀ t : ℝ, upperConj t A = A := by
  rw [upperConj_bounded_iff]
  constructor
  · rintro ⟨h10, hd⟩ t
    obtain ⟨h00, h01, h10', h11⟩ := upperConj_entry t A
    ext i j
    fin_cases i <;> fin_cases j
    · change upperConj t A 0 0 = A 0 0
      rw [h00, h10, mul_zero, add_zero]
    · change upperConj t A 0 1 = A 0 1
      rw [h01, h10, hd, sub_self, mul_zero, mul_zero, add_zero, sub_zero]
    · exact h10'
    · change upperConj t A 1 1 = A 1 1
      rw [h11, h10, mul_zero, sub_zero]
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) (h 1)
    rw [(upperConj_entry 1 A).1, one_mul] at h00
    have h10 : A 1 0 = 0 := by linarith only [h00]
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) (h 1)
    rw [(upperConj_entry 1 A).2.1, h10, mul_zero, sub_zero, one_mul] at h01
    exact ⟨h10, by linarith only [h01]⟩

end GaloisForLFunctions.BiarithmeticGeometry
