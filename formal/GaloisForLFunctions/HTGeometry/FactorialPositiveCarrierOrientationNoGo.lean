import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryKreinCrossing

open Matrix Polynomial

namespace HTGeometry

noncomputable section

/-- Factorial-normalized moments of a positive two-atom carrier. -/
def factorialTwoAtomMoment
    (weight node : Fin 2 → ℝ) (k : ℕ) : ℝ :=
  (∑ i, weight i * node i ^ k) / (k.factorial : ℝ)

def factorialPositiveCarrierWeight : Fin 2 → ℝ := ![16 / 17, 1 / 17]
def factorialPositiveCarrierNode : Fin 2 → ℝ := ![3 / 4, 5]
def factorialNegativeCarrierWeight : Fin 2 → ℝ := ![4 / 5, 1 / 5]
def factorialNegativeCarrierNode : Fin 2 → ℝ := ![1 / 2, 3]

theorem factorialPositiveCarrier_strictlyPositive :
    ∀ i, 0 < factorialPositiveCarrierWeight i ∧
      0 < factorialPositiveCarrierNode i := by
  intro i
  fin_cases i <;>
    norm_num [factorialPositiveCarrierWeight, factorialPositiveCarrierNode]

theorem factorialNegativeCarrier_strictlyPositive :
    ∀ i, 0 < factorialNegativeCarrierWeight i ∧
      0 < factorialNegativeCarrierNode i := by
  intro i
  fin_cases i <;>
    norm_num [factorialNegativeCarrierWeight, factorialNegativeCarrierNode]

@[simp] theorem factorialPositiveCarrierMoment_zero :
    factorialTwoAtomMoment factorialPositiveCarrierWeight
      factorialPositiveCarrierNode 0 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialPositiveCarrierWeight,
    factorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialPositiveCarrierMoment_one :
    factorialTwoAtomMoment factorialPositiveCarrierWeight
      factorialPositiveCarrierNode 1 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialPositiveCarrierWeight,
    factorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialPositiveCarrierMoment_two :
    factorialTwoAtomMoment factorialPositiveCarrierWeight
      factorialPositiveCarrierNode 2 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialPositiveCarrierWeight,
    factorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialPositiveCarrierMoment_three :
    factorialTwoAtomMoment factorialPositiveCarrierWeight
      factorialPositiveCarrierNode 3 = 31 / 24 := by
  norm_num [factorialTwoAtomMoment, factorialPositiveCarrierWeight,
    factorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialNegativeCarrierMoment_zero :
    factorialTwoAtomMoment factorialNegativeCarrierWeight
      factorialNegativeCarrierNode 0 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialNegativeCarrierWeight,
    factorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialNegativeCarrierMoment_one :
    factorialTwoAtomMoment factorialNegativeCarrierWeight
      factorialNegativeCarrierNode 1 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialNegativeCarrierWeight,
    factorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialNegativeCarrierMoment_two :
    factorialTwoAtomMoment factorialNegativeCarrierWeight
      factorialNegativeCarrierNode 2 = 1 := by
  norm_num [factorialTwoAtomMoment, factorialNegativeCarrierWeight,
    factorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem factorialNegativeCarrierMoment_three :
    factorialTwoAtomMoment factorialNegativeCarrierWeight
      factorialNegativeCarrierNode 3 = 11 / 12 := by
  norm_num [factorialTwoAtomMoment, factorialNegativeCarrierWeight,
    factorialNegativeCarrierNode, Fin.sum_univ_two]

def factorialCarrierNoGoKernel : Fin 2 → ℝ := ![-1, 1]

theorem factorialPositiveCarrier_head_posDef :
    (momentHankelMatrix
      (factorialTwoAtomMoment factorialPositiveCarrierWeight
        factorialPositiveCarrierNode) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact momentHankelMatrix_isHermitian _ _
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one,
      momentHankelMatrix]
    norm_num only [Fin.val_zero, zero_add]
    rw [factorialPositiveCarrierMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

theorem factorialPositiveCarrier_kernel :
    momentHankelMatrix
        (factorialTwoAtomMoment factorialPositiveCarrierWeight
          factorialPositiveCarrierNode) 2 *ᵥ
      factorialCarrierNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix,
      factorialCarrierNoGoKernel]

theorem factorialNegativeCarrier_kernel :
    momentHankelMatrix
        (factorialTwoAtomMoment factorialNegativeCarrierWeight
          factorialNegativeCarrierNode) 2 *ᵥ
      factorialCarrierNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix,
      factorialCarrierNoGoKernel]

theorem factorialCarriers_sameFace :
    momentHankelMatrix
        (factorialTwoAtomMoment factorialPositiveCarrierWeight
          factorialPositiveCarrierNode) 2 =
      momentHankelMatrix
        (factorialTwoAtomMoment factorialNegativeCarrierWeight
          factorialNegativeCarrierNode) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [momentHankelMatrix]

theorem factorialCarrierNoGo_monicNullPolynomial :
    finiteHankelNullMonicPolynomial factorialCarrierNoGoKernel = X - C 1 := by
  have hraw : finiteHankelNullPolynomial factorialCarrierNoGoKernel = X - C 1 := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_two]
    simp [factorialCarrierNoGoKernel, monomial_one_right_eq_X_pow]
    ring
  rw [finiteHankelNullMonicPolynomial, hraw]
  have hdeg : (C (1 : ℝ)).degree < (X : Polynomial ℝ).degree := by simp
  rw [Polynomial.leadingCoeff_sub_of_degree_lt hdeg, Polynomial.leadingCoeff_X]
  simp

theorem factorialPositiveCarrier_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (factorialTwoAtomMoment factorialPositiveCarrierWeight
        factorialPositiveCarrierNode) factorialCarrierNoGoKernel = 7 / 24 := by
  rw [finiteHankelBoundaryMonicRemainder,
    factorialCarrierNoGo_monicNullPolynomial]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ (2 : ℕ) * (X - C 1) = X ^ (3 : ℕ) - X ^ (2 : ℕ) := by
    simp
    ring
  rw [hpoly, sub_eq_add_neg, momentFunctional_add]
  rw [show -((X : Polynomial ℝ) ^ (2 : ℕ)) = (-1 : ℝ) • X ^ (2 : ℕ) by rw [neg_one_smul],
    momentFunctional_smul, momentFunctional_X_pow, momentFunctional_X_pow,
    factorialPositiveCarrierMoment_three,
    factorialPositiveCarrierMoment_two]
  norm_num

theorem factorialNegativeCarrier_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (factorialTwoAtomMoment factorialNegativeCarrierWeight
        factorialNegativeCarrierNode) factorialCarrierNoGoKernel = -(1 / 12) := by
  rw [finiteHankelBoundaryMonicRemainder,
    factorialCarrierNoGo_monicNullPolynomial]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ (2 : ℕ) * (X - C 1) = X ^ (3 : ℕ) - X ^ (2 : ℕ) := by
    simp
    ring
  rw [hpoly, sub_eq_add_neg, momentFunctional_add]
  rw [show -((X : Polynomial ℝ) ^ (2 : ℕ)) = (-1 : ℝ) • X ^ (2 : ℕ) by rw [neg_one_smul],
    momentFunctional_smul, momentFunctional_X_pow, momentFunctional_X_pow,
    factorialNegativeCarrierMoment_three,
    factorialNegativeCarrierMoment_two]
  norm_num

/-- **Positive-carrier factorial orientation no-go.** Strictly positive carrier weights and nodes,
followed by the exact Gamma/factorial normalization, can produce the same positive singular Hankel
face with either Krein crossing orientation. -/
theorem factorialPositiveCarrierOrientationNoGo :
    (∀ i, 0 < factorialPositiveCarrierWeight i ∧
      0 < factorialPositiveCarrierNode i) ∧
    (∀ i, 0 < factorialNegativeCarrierWeight i ∧
      0 < factorialNegativeCarrierNode i) ∧
    momentHankelMatrix
        (factorialTwoAtomMoment factorialPositiveCarrierWeight
          factorialPositiveCarrierNode) 2 =
      momentHankelMatrix
        (factorialTwoAtomMoment factorialNegativeCarrierWeight
          factorialNegativeCarrierNode) 2 ∧
    (momentHankelMatrix
      (factorialTwoAtomMoment factorialPositiveCarrierWeight
        factorialPositiveCarrierNode) 1).PosDef ∧
    momentHankelMatrix
        (factorialTwoAtomMoment factorialPositiveCarrierWeight
          factorialPositiveCarrierNode) 2 *ᵥ
      factorialCarrierNoGoKernel = 0 ∧
    momentHankelMatrix
        (factorialTwoAtomMoment factorialNegativeCarrierWeight
          factorialNegativeCarrierNode) 2 *ᵥ
      factorialCarrierNoGoKernel = 0 ∧
    finiteHankelBoundaryNullCrossingForm
      (factorialTwoAtomMoment factorialPositiveCarrierWeight
        factorialPositiveCarrierNode) factorialCarrierNoGoKernel = 7 / 24 ∧
    finiteHankelBoundaryNullCrossingForm
      (factorialTwoAtomMoment factorialNegativeCarrierWeight
        factorialNegativeCarrierNode) factorialCarrierNoGoKernel = -(1 / 12) := by
  have hlast : factorialCarrierNoGoKernel (Fin.last 1) ≠ 0 := by
    change (1 : ℝ) ≠ 0
    norm_num
  exact ⟨factorialPositiveCarrier_strictlyPositive,
    factorialNegativeCarrier_strictlyPositive,
    factorialCarriers_sameFace,
    factorialPositiveCarrier_head_posDef,
    factorialPositiveCarrier_kernel,
    factorialNegativeCarrier_kernel,
    (finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
      _ _ factorialPositiveCarrier_kernel hlast).trans
        factorialPositiveCarrier_monicRemainder,
    (finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
      _ _ factorialNegativeCarrier_kernel hlast).trans
        factorialNegativeCarrier_monicRemainder⟩

end

end HTGeometry
