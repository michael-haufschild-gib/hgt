import GaloisForLFunctions.HTGeometry.TiedPowerEndpointOrientationNoGo

/-!
# Global-budget tied-power orientation no-go

Three copies of the exact opposite-orientation four-atom clouds, scaled by `1 / 2880`, fit not
only the strict Xi sector and radius constraints but also the corpus central zeroth-moment window,
the first-moment upper bound, and the global transverse-orientation-energy upper bound.  They
still determine the same positive singular current face and have opposite first unseen Krein
crossings.  Thus those scalar global budgets do not supply the missing source-conditioned
orientation.
-/

open Matrix Polynomial
open scoped ComplexConjugate

namespace HTGeometry

noncomputable section

def tiedPowerGlobalBudgetPositiveNodes : Fin 4 → ℂ :=
  tiedPowerScaleNodes (1 / 2880) tiedPowerPositiveNodes

def tiedPowerGlobalBudgetNegativeNodes : Fin 4 → ℂ :=
  tiedPowerScaleNodes (1 / 2880) tiedPowerNegativeNodes

/-- Moment sequence of three identical copies of a four-atom tied-power cloud. -/
def tiedPowerMultiplicityThreeMoment (nodes : Fin 4 → ℂ) (k : ℕ) : ℝ :=
  3 * tiedPowerMoment nodes k

/-- Transverse-square energy of three identical copies of a four-atom cloud. -/
def tiedPowerMultiplicityThreeOrientationEnergy (nodes : Fin 4 → ℂ) : ℝ :=
  3 * ∑ i, (nodes i).im ^ 2

def tiedPowerMultiplicityThreeTrajectory
    (nodes : Fin 4 → ℂ) (k : ℕ) (h : ℂ) : ℂ :=
  3 * tiedPowerMobiusTrajectory nodes k h

theorem tiedPowerMultiplicityThreeTrajectory_hasDerivAt
    (nodes : Fin 4 → ℂ) (k : ℕ) :
    HasDerivAt (tiedPowerMultiplicityThreeTrajectory nodes k)
      (3 * (-((k + 1 : ℕ) : ℂ) * ∑ i, nodes i ^ (k + 2))) 0 := by
  change HasDerivAt (fun h => 3 * tiedPowerMobiusTrajectory nodes k h) _ 0
  simpa using (tiedPowerMobiusTrajectory_hasDerivAt nodes k).const_mul (3 : ℂ)

theorem tiedPowerGlobalBudgetPositiveNodes_geometry :
    ∀ i, 0 < (tiedPowerGlobalBudgetPositiveNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetPositiveNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerGlobalBudgetPositiveNodes i).re ^ 2 ∧
      (41 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetPositiveNodes i) < 4 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes, Complex.normSq_apply]

theorem tiedPowerGlobalBudgetNegativeNodes_geometry :
    ∀ i, 0 < (tiedPowerGlobalBudgetNegativeNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetNegativeNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerGlobalBudgetNegativeNodes i).re ^ 2 ∧
      (41 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetNegativeNodes i) < 4 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes, Complex.normSq_apply]

theorem tiedPowerGlobalBudgetPositiveNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerGlobalBudgetPositiveNodes i) =
      tiedPowerGlobalBudgetPositiveNodes j := by
  intro i
  obtain ⟨j, hj⟩ := tiedPowerPositiveNodes_conjugationClosed i
  refine ⟨j, ?_⟩
  rw [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes, map_mul,
    Complex.conj_ofReal, hj]
  rfl

theorem tiedPowerGlobalBudgetNegativeNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerGlobalBudgetNegativeNodes i) =
      tiedPowerGlobalBudgetNegativeNodes j := by
  intro i
  obtain ⟨j, hj⟩ := tiedPowerNegativeNodes_conjugationClosed i
  refine ⟨j, ?_⟩
  rw [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes, map_mul,
    Complex.conj_ofReal, hj]
  rfl

@[simp] theorem tiedPowerGlobalBudgetPositiveMoment_zero :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 0 = 1 / 24 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetPositiveNodes,
    tiedPowerMoment_scale, tiedPowerPositiveMoment_zero]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetPositiveMoment_one :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 1 = 1 / 6912 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetPositiveNodes,
    tiedPowerMoment_scale, tiedPowerPositiveMoment_one]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetPositiveMoment_two :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 2 =
      1 / 1990656 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetPositiveNodes,
    tiedPowerMoment_scale, tiedPowerPositiveMoment_two]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetPositiveMoment_three :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 3 =
      10001 / 5733089280000 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetPositiveNodes,
    tiedPowerMoment_scale, tiedPowerPositiveMoment_three]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetNegativeMoment_zero :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes 0 = 1 / 24 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetNegativeNodes,
    tiedPowerMoment_scale, tiedPowerNegativeMoment_zero]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetNegativeMoment_one :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes 1 = 1 / 6912 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetNegativeNodes,
    tiedPowerMoment_scale, tiedPowerNegativeMoment_one]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetNegativeMoment_two :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes 2 =
      1 / 1990656 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetNegativeNodes,
    tiedPowerMoment_scale, tiedPowerNegativeMoment_two]
  norm_num

@[simp] theorem tiedPowerGlobalBudgetNegativeMoment_three :
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes 3 =
      833 / 477757440000 := by
  rw [tiedPowerMultiplicityThreeMoment, tiedPowerGlobalBudgetNegativeNodes,
    tiedPowerMoment_scale, tiedPowerNegativeMoment_three]
  norm_num

theorem tiedPowerGlobalBudgetPositiveOrientationEnergy :
    tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetPositiveNodes =
      1 / 1382400 := by
  have h0 : (tiedPowerGlobalBudgetPositiveNodes 0).im = 0 := by
    rw [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes_zero]
    norm_num
  have h1 : (tiedPowerGlobalBudgetPositiveNodes 1).im = 0 := by
    rw [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes_one]
    norm_num
  have h2 : (tiedPowerGlobalBudgetPositiveNodes 2).im = 1 / 2880 := by
    rw [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes_two]
    norm_num
  have h3 : (tiedPowerGlobalBudgetPositiveNodes 3).im = -(1 / 2880) := by
    rw [tiedPowerGlobalBudgetPositiveNodes, tiedPowerScaleNodes,
      tiedPowerPositiveNodes_three]
    norm_num
  rw [tiedPowerMultiplicityThreeOrientationEnergy, Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  norm_num

theorem tiedPowerGlobalBudgetNegativeOrientationEnergy :
    tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetNegativeNodes =
      1 / 691200 := by
  have h0 : (tiedPowerGlobalBudgetNegativeNodes 0).im = 1 / 2880 := by
    rw [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes_zero]
    norm_num
  have h1 : (tiedPowerGlobalBudgetNegativeNodes 1).im = 1 / 2880 := by
    rw [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes_one]
    norm_num
  have h2 : (tiedPowerGlobalBudgetNegativeNodes 2).im = -(1 / 2880) := by
    rw [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes_two]
    norm_num
  have h3 : (tiedPowerGlobalBudgetNegativeNodes 3).im = -(1 / 2880) := by
    rw [tiedPowerGlobalBudgetNegativeNodes, tiedPowerScaleNodes,
      tiedPowerNegativeNodes_three]
    norm_num
  rw [tiedPowerMultiplicityThreeOrientationEnergy, Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  norm_num

/-- Both clouds meet the exact scalar budgets available for the completed central Xi source. -/
theorem tiedPowerGlobalBudget_bounds :
    (1 / 25 : ℝ) <
        tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 0 ∧
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 0 < 29 / 625 ∧
    tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 1 < 1 / 5000 ∧
    tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetPositiveNodes <
      1 / 150000 ∧
    tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetNegativeNodes <
      1 / 150000 := by
  rw [tiedPowerGlobalBudgetPositiveMoment_zero,
    tiedPowerGlobalBudgetPositiveMoment_one,
    tiedPowerGlobalBudgetPositiveOrientationEnergy,
    tiedPowerGlobalBudgetNegativeOrientationEnergy]
  norm_num

def tiedPowerGlobalBudgetNoGoKernel : Fin 2 → ℝ := ![-1 / 288, 1]

theorem tiedPowerGlobalBudgetPositive_head_posDef :
    (momentHankelMatrix
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 1).PosDef := by
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
    rw [tiedPowerGlobalBudgetPositiveMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

theorem tiedPowerGlobalBudgetPositive_kernel :
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 2 *ᵥ
      tiedPowerGlobalBudgetNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix,
      tiedPowerGlobalBudgetNoGoKernel] <;> norm_num

theorem tiedPowerGlobalBudgetNegative_kernel :
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes) 2 *ᵥ
      tiedPowerGlobalBudgetNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix,
      tiedPowerGlobalBudgetNoGoKernel] <;> norm_num

theorem tiedPowerGlobalBudget_sameFace :
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 2 =
      momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [momentHankelMatrix]

theorem tiedPowerGlobalBudgetPositive_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes)
      tiedPowerGlobalBudgetNoGoKernel = 1 / 5733089280000 := by
  have hraw : finiteHankelNullPolynomial tiedPowerGlobalBudgetNoGoKernel =
      X - C (1 / 288) := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [tiedPowerGlobalBudgetNoGoKernel, monomial_one_right_eq_X_pow]
    rw [show (-1 / 288 : ℝ) = -(1 / 288) by ring, map_neg]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerGlobalBudgetNoGoKernel =
      X - C (1 / 288) := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ 2 * (X - C (1 / 288)) =
      X ^ 3 - C (1 / 288) * X ^ 2 := by ring
  calc
    momentFunctional
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes)
        (X ^ 2 * (X - C (1 / 288))) =
      momentFunctional
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes)
        (X ^ 3 - C (1 / 288) * X ^ 2) := congrArg _ hpoly
    _ = 1 / 5733089280000 := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C (1 / 288) * X ^ 2 : Polynomial ℝ)) =
          (-1 : ℝ) • (C (1 / 288) * X ^ 2 : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C (1 / 288) * X ^ 2 : Polynomial ℝ) =
          (1 / 288 : ℝ) • X ^ 2 by rw [Polynomial.smul_eq_C_mul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [tiedPowerGlobalBudgetPositiveMoment_three,
        tiedPowerGlobalBudgetPositiveMoment_two]
      norm_num

theorem tiedPowerGlobalBudgetNegative_monicRemainder :
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes)
      tiedPowerGlobalBudgetNoGoKernel = -(1 / 1433272320000) := by
  have hraw : finiteHankelNullPolynomial tiedPowerGlobalBudgetNoGoKernel =
      X - C (1 / 288) := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [tiedPowerGlobalBudgetNoGoKernel, monomial_one_right_eq_X_pow]
    rw [show (-1 / 288 : ℝ) = -(1 / 288) by ring, map_neg]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerGlobalBudgetNoGoKernel =
      X - C (1 / 288) := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ 2 * (X - C (1 / 288)) =
      X ^ 3 - C (1 / 288) * X ^ 2 := by ring
  calc
    momentFunctional
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes)
        (X ^ 2 * (X - C (1 / 288))) =
      momentFunctional
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes)
        (X ^ 3 - C (1 / 288) * X ^ 2) := congrArg _ hpoly
    _ = -(1 / 1433272320000) := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C (1 / 288) * X ^ 2 : Polynomial ℝ)) =
          (-1 : ℝ) • (C (1 / 288) * X ^ 2 : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C (1 / 288) * X ^ 2 : Polynomial ℝ) =
          (1 / 288 : ℝ) • X ^ 2 by rw [Polynomial.smul_eq_C_mul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [tiedPowerGlobalBudgetNegativeMoment_three,
        tiedPowerGlobalBudgetNegativeMoment_two]
      norm_num

/-- **Global-scalar-budget no-go.**  Exact central scalar constraints, local atom geometry, and
full tied-power transport remain jointly insufficient to orient the next Hankel/Krein extension. -/
theorem tiedPowerGlobalBudgetOrientationNoGo :
    (∀ i, ∃ j, conj (tiedPowerGlobalBudgetPositiveNodes i) =
      tiedPowerGlobalBudgetPositiveNodes j) ∧
    (∀ i, ∃ j, conj (tiedPowerGlobalBudgetNegativeNodes i) =
      tiedPowerGlobalBudgetNegativeNodes j) ∧
    (∀ i, 0 < (tiedPowerGlobalBudgetPositiveNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetPositiveNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerGlobalBudgetPositiveNodes i).re ^ 2 ∧
      (41 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetPositiveNodes i) < 4) ∧
    (∀ i, 0 < (tiedPowerGlobalBudgetNegativeNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetNegativeNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerGlobalBudgetNegativeNodes i).re ^ 2 ∧
      (41 : ℝ) ^ 2 * Complex.normSq (tiedPowerGlobalBudgetNegativeNodes i) < 4) ∧
    ((1 / 25 : ℝ) <
        tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 0 ∧
      tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 0 < 29 / 625 ∧
      tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes 1 < 1 / 5000 ∧
      tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetPositiveNodes <
        1 / 150000 ∧
      tiedPowerMultiplicityThreeOrientationEnergy tiedPowerGlobalBudgetNegativeNodes <
        1 / 150000) ∧
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 2 =
      momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes) 2 ∧
    (momentHankelMatrix
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 1).PosDef ∧
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes) 2 *ᵥ
      tiedPowerGlobalBudgetNoGoKernel = 0 ∧
    momentHankelMatrix
        (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes) 2 *ᵥ
      tiedPowerGlobalBudgetNoGoKernel = 0 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetPositiveNodes)
      tiedPowerGlobalBudgetNoGoKernel = 1 / 5733089280000 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMultiplicityThreeMoment tiedPowerGlobalBudgetNegativeNodes)
      tiedPowerGlobalBudgetNoGoKernel = -(1 / 1433272320000) ∧
    (∀ k, HasDerivAt
      (tiedPowerMultiplicityThreeTrajectory tiedPowerGlobalBudgetPositiveNodes k)
      (3 * (-((k + 1 : ℕ) : ℂ) *
        ∑ i, tiedPowerGlobalBudgetPositiveNodes i ^ (k + 2))) 0) ∧
    (∀ k, HasDerivAt
      (tiedPowerMultiplicityThreeTrajectory tiedPowerGlobalBudgetNegativeNodes k)
      (3 * (-((k + 1 : ℕ) : ℂ) *
        ∑ i, tiedPowerGlobalBudgetNegativeNodes i ^ (k + 2))) 0) := by
  exact ⟨tiedPowerGlobalBudgetPositiveNodes_conjugationClosed,
    tiedPowerGlobalBudgetNegativeNodes_conjugationClosed,
    tiedPowerGlobalBudgetPositiveNodes_geometry,
    tiedPowerGlobalBudgetNegativeNodes_geometry,
    tiedPowerGlobalBudget_bounds,
    tiedPowerGlobalBudget_sameFace,
    tiedPowerGlobalBudgetPositive_head_posDef,
    tiedPowerGlobalBudgetPositive_kernel,
    tiedPowerGlobalBudgetNegative_kernel,
    tiedPowerGlobalBudgetPositive_monicRemainder,
    tiedPowerGlobalBudgetNegative_monicRemainder,
    fun k => tiedPowerMultiplicityThreeTrajectory_hasDerivAt
      tiedPowerGlobalBudgetPositiveNodes k,
    fun k => tiedPowerMultiplicityThreeTrajectory_hasDerivAt
      tiedPowerGlobalBudgetNegativeNodes k⟩

end

end HTGeometry
