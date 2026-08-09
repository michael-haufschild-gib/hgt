import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass

/-!
# Narrow-sector tied-power orientation no-go

Local Xi-style source marginals do not orient the first unseen extension of a positive singular
Hankel face.  This file gives two exact conjugation-stable, narrow-sector, tied-power sources with
the same current face and opposite projective remainders, while proving their full Möbius moment
transport law.
-/

open Matrix Polynomial
open scoped ComplexConjugate

namespace HTGeometry

noncomputable section

def tiedPowerMoment (nodes : Fin 4 → ℂ) (k : ℕ) : ℝ :=
  (∑ i, nodes i ^ (k + 1)).re

def tiedPowerPositiveNodes : Fin 4 → ℂ :=
  ![(11 : ℂ), (9 : ℂ), (10 : ℂ) + Complex.I, (10 : ℂ) - Complex.I]

def tiedPowerNegativeNodes : Fin 4 → ℂ :=
  ![(11 : ℂ) + Complex.I, (9 : ℂ) + Complex.I,
    (9 : ℂ) - Complex.I, (11 : ℂ) - Complex.I]

@[simp] theorem tiedPowerPositiveNodes_zero : tiedPowerPositiveNodes 0 = 11 := rfl
@[simp] theorem tiedPowerPositiveNodes_one : tiedPowerPositiveNodes 1 = 9 := rfl
@[simp] theorem tiedPowerPositiveNodes_two :
    tiedPowerPositiveNodes 2 = 10 + Complex.I := rfl
@[simp] theorem tiedPowerPositiveNodes_three :
    tiedPowerPositiveNodes 3 = 10 - Complex.I := rfl

@[simp] theorem tiedPowerNegativeNodes_zero :
    tiedPowerNegativeNodes 0 = 11 + Complex.I := rfl
@[simp] theorem tiedPowerNegativeNodes_one :
    tiedPowerNegativeNodes 1 = 9 + Complex.I := rfl
@[simp] theorem tiedPowerNegativeNodes_two :
    tiedPowerNegativeNodes 2 = 9 - Complex.I := rfl
@[simp] theorem tiedPowerNegativeNodes_three :
    tiedPowerNegativeNodes 3 = 11 - Complex.I := rfl

theorem tiedPowerPositiveNodes_narrowRightSector :
    ∀ i, 0 < (tiedPowerPositiveNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerPositiveNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerPositiveNodes i).re ^ 2 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerPositiveNodes, Complex.normSq_apply]

theorem tiedPowerNegativeNodes_narrowRightSector :
    ∀ i, 0 < (tiedPowerNegativeNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerNegativeNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerNegativeNodes i).re ^ 2 := by
  intro i
  fin_cases i <;>
    norm_num [tiedPowerNegativeNodes, Complex.normSq_apply]

theorem tiedPowerPositiveNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerPositiveNodes i) = tiedPowerPositiveNodes j := by
  have hten : (starRingEnd ℂ) (10 : ℂ) = 10 := Complex.conj_ofReal 10
  intro i
  fin_cases i
  · refine ⟨0, ?_⟩
    change conj (11 : ℂ) = 11
    exact Complex.conj_ofReal 11
  · refine ⟨1, ?_⟩
    change conj (9 : ℂ) = 9
    exact Complex.conj_ofReal 9
  · refine ⟨3, ?_⟩
    simp
    rw [hten]
    ring
  · refine ⟨2, ?_⟩
    simp
    rw [hten]

theorem tiedPowerNegativeNodes_conjugationClosed :
    ∀ i, ∃ j, conj (tiedPowerNegativeNodes i) = tiedPowerNegativeNodes j := by
  have hnine : (starRingEnd ℂ) (9 : ℂ) = 9 := Complex.conj_ofReal 9
  have heleven : (starRingEnd ℂ) (11 : ℂ) = 11 := Complex.conj_ofReal 11
  intro i
  fin_cases i
  · refine ⟨3, ?_⟩
    simp
    rw [heleven]
    ring
  · refine ⟨2, ?_⟩
    simp
    rw [hnine]
    ring
  · refine ⟨1, ?_⟩
    simp
    rw [hnine]
  · refine ⟨0, ?_⟩
    simp
    rw [heleven]

theorem tiedPowerPositiveMoment_zero :
    tiedPowerMoment tiedPowerPositiveNodes 0 = 40 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerPositiveNodes_zero, tiedPowerPositiveNodes_one,
    tiedPowerPositiveNodes_two, tiedPowerPositiveNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerPositiveMoment_one :
    tiedPowerMoment tiedPowerPositiveNodes 1 = 400 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerPositiveNodes_zero, tiedPowerPositiveNodes_one,
    tiedPowerPositiveNodes_two, tiedPowerPositiveNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerPositiveMoment_two :
    tiedPowerMoment tiedPowerPositiveNodes 2 = 4000 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerPositiveNodes_zero, tiedPowerPositiveNodes_one,
    tiedPowerPositiveNodes_two, tiedPowerPositiveNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerPositiveMoment_three :
    tiedPowerMoment tiedPowerPositiveNodes 3 = 40004 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerPositiveNodes_zero, tiedPowerPositiveNodes_one,
    tiedPowerPositiveNodes_two, tiedPowerPositiveNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerNegativeMoment_zero :
    tiedPowerMoment tiedPowerNegativeNodes 0 = 40 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerNegativeNodes_zero, tiedPowerNegativeNodes_one,
    tiedPowerNegativeNodes_two, tiedPowerNegativeNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerNegativeMoment_one :
    tiedPowerMoment tiedPowerNegativeNodes 1 = 400 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerNegativeNodes_zero, tiedPowerNegativeNodes_one,
    tiedPowerNegativeNodes_two, tiedPowerNegativeNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerNegativeMoment_two :
    tiedPowerMoment tiedPowerNegativeNodes 2 = 4000 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerNegativeNodes_zero, tiedPowerNegativeNodes_one,
    tiedPowerNegativeNodes_two, tiedPowerNegativeNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

theorem tiedPowerNegativeMoment_three :
    tiedPowerMoment tiedPowerNegativeNodes 3 = 39984 := by
  rw [tiedPowerMoment, Fin.sum_univ_four]
  simp only [tiedPowerNegativeNodes_zero, tiedPowerNegativeNodes_one,
    tiedPowerNegativeNodes_two, tiedPowerNegativeNodes_three]
  ring_nf
  norm_num [Complex.I_sq]

def tiedPowerSectorNoGoKernel : Fin 2 → ℝ := ![-10, 1]

theorem tiedPowerPositiveMoment_head_posDef :
    (momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i
    fin_cases j
    simp [momentHankelMatrix]
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    simp only [momentHankelMatrix]
    norm_num only [Fin.val_zero, zero_add]
    rw [tiedPowerPositiveMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

theorem tiedPowerNegativeMoment_head_posDef :
    (momentHankelMatrix (tiedPowerMoment tiedPowerNegativeNodes) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i
    fin_cases j
    simp [momentHankelMatrix]
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    simp only [momentHankelMatrix]
    norm_num only [Fin.val_zero, zero_add]
    rw [tiedPowerNegativeMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

theorem tiedPowerPositiveMoment_kernel :
    momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 2 *ᵥ
      tiedPowerSectorNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix, tiedPowerSectorNoGoKernel,
      tiedPowerPositiveMoment_zero, tiedPowerPositiveMoment_one,
      tiedPowerPositiveMoment_two] <;> norm_num

theorem tiedPowerNegativeMoment_kernel :
    momentHankelMatrix (tiedPowerMoment tiedPowerNegativeNodes) 2 *ᵥ
      tiedPowerSectorNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix, tiedPowerSectorNoGoKernel,
      tiedPowerNegativeMoment_zero, tiedPowerNegativeMoment_one,
      tiedPowerNegativeMoment_two] <;> norm_num

theorem tiedPowerSectorNoGo_sameFace :
    momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 2 =
      momentHankelMatrix (tiedPowerMoment tiedPowerNegativeNodes) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentHankelMatrix, tiedPowerPositiveMoment_zero,
      tiedPowerPositiveMoment_one, tiedPowerPositiveMoment_two,
      tiedPowerNegativeMoment_zero, tiedPowerNegativeMoment_one,
      tiedPowerNegativeMoment_two]

theorem tiedPowerPositive_monicRemainder :
    finiteHankelBoundaryMonicRemainder
        (tiedPowerMoment tiedPowerPositiveNodes) tiedPowerSectorNoGoKernel = 4 := by
  have hraw : finiteHankelNullPolynomial tiedPowerSectorNoGoKernel = X - C 10 := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_two]
    simp [tiedPowerSectorNoGoKernel, monomial_one_right_eq_X_pow]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerSectorNoGoKernel = X - C 10 := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ 2 * (X - C 10) = X ^ 3 - C 10 * X ^ 2 := by ring
  calc
    momentFunctional (tiedPowerMoment tiedPowerPositiveNodes) (X ^ 2 * (X - C 10)) =
        momentFunctional (tiedPowerMoment tiedPowerPositiveNodes)
          (X ^ 3 - C 10 * X ^ 2) := congrArg _ hpoly
    _ = 4 := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C 10 * X ^ 2 : Polynomial ℝ)) =
          (-1 : ℝ) • (C 10 * X ^ 2 : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C 10 * X ^ 2 : Polynomial ℝ) = (10 : ℝ) • X ^ 2 by
        rw [Polynomial.smul_eq_C_mul], momentFunctional_smul,
        momentFunctional_X_pow, tiedPowerPositiveMoment_three,
        tiedPowerPositiveMoment_two]
      norm_num

theorem tiedPowerNegative_monicRemainder :
    finiteHankelBoundaryMonicRemainder
        (tiedPowerMoment tiedPowerNegativeNodes) tiedPowerSectorNoGoKernel = -16 := by
  have hraw : finiteHankelNullPolynomial tiedPowerSectorNoGoKernel = X - C 10 := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_two]
    simp [tiedPowerSectorNoGoKernel, monomial_one_right_eq_X_pow]
    ring
  have hmonic : finiteHankelNullMonicPolynomial tiedPowerSectorNoGoKernel = X - C 10 := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  norm_num only [Nat.reduceAdd]
  have hpoly : (X : Polynomial ℝ) ^ 2 * (X - C 10) = X ^ 3 - C 10 * X ^ 2 := by ring
  calc
    momentFunctional (tiedPowerMoment tiedPowerNegativeNodes) (X ^ 2 * (X - C 10)) =
        momentFunctional (tiedPowerMoment tiedPowerNegativeNodes)
          (X ^ 3 - C 10 * X ^ 2) := congrArg _ hpoly
    _ = -16 := by
      rw [sub_eq_add_neg, momentFunctional_add]
      rw [show -((C 10 * X ^ 2 : Polynomial ℝ)) =
          (-1 : ℝ) • (C 10 * X ^ 2 : Polynomial ℝ) by rw [neg_one_smul],
        momentFunctional_smul, momentFunctional_X_pow]
      rw [show (C 10 * X ^ 2 : Polynomial ℝ) = (10 : ℝ) • X ^ 2 by
        rw [Polynomial.smul_eq_C_mul], momentFunctional_smul,
        momentFunctional_X_pow, tiedPowerNegativeMoment_three,
        tiedPowerNegativeMoment_two]
      norm_num

def complexAtomicMobiusPowerTrajectory (z : ℂ) (k : ℕ) (h : ℂ) : ℂ :=
  (z / (1 + h * z)) ^ (k + 1)

theorem complexAtomicMobiusPowerTrajectory_hasDerivAt (z : ℂ) (k : ℕ) :
    HasDerivAt (complexAtomicMobiusPowerTrajectory z k)
      (-((k + 1 : ℕ) : ℂ) * z ^ (k + 2)) 0 := by
  have hden : HasDerivAt (fun h : ℂ => 1 + h * z) z 0 := by
    simpa [add_comm] using ((hasDerivAt_id (0 : ℂ)).mul_const z).const_add 1
  have hquot : HasDerivAt (fun h : ℂ => z / (1 + h * z)) (-z ^ 2) 0 := by
    have hraw := (hasDerivAt_const (x := (0 : ℂ)) z).div hden (by norm_num)
    convert! hraw using 1
    ring
  have hpow := hquot.pow (k + 1)
  apply hpow.congr_deriv
  push_cast
  rw [show k + 2 = k + 1 + 1 by omega, pow_add]
  ring

def tiedPowerMobiusTrajectory (nodes : Fin 4 → ℂ) (k : ℕ) (h : ℂ) : ℂ :=
  ∑ i, complexAtomicMobiusPowerTrajectory (nodes i) k h

theorem tiedPowerMobiusTrajectory_hasDerivAt (nodes : Fin 4 → ℂ) (k : ℕ) :
    HasDerivAt (tiedPowerMobiusTrajectory nodes k)
      (-((k + 1 : ℕ) : ℂ) * ∑ i, nodes i ^ (k + 2)) 0 := by
  have hsum : HasDerivAt
      (fun h : ℂ => ∑ i, complexAtomicMobiusPowerTrajectory (nodes i) k h)
      (∑ i, -((k + 1 : ℕ) : ℂ) * nodes i ^ (k + 2)) 0 := by
    exact HasDerivAt.fun_sum (fun i _ => complexAtomicMobiusPowerTrajectory_hasDerivAt (nodes i) k)
  change HasDerivAt (tiedPowerMobiusTrajectory nodes k) _ 0
  convert! hsum using 1
  rw [Finset.mul_sum]

/-- **Closed local-Xi-marginal no-go.**  Two finite tied-power sources are conjugation-stable,
lie in the strict squared `85/84` right-sector cone, obey the complete complex Möbius moment
hierarchy, and determine the same positive singular Hankel face, yet their first unseen projective
remainders have opposite signs. -/
theorem tiedPowerNarrowSectorOrientationNoGo :
    (∀ i, ∃ j, conj (tiedPowerPositiveNodes i) = tiedPowerPositiveNodes j) ∧
    (∀ i, ∃ j, conj (tiedPowerNegativeNodes i) = tiedPowerNegativeNodes j) ∧
    (∀ i, 0 < (tiedPowerPositiveNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerPositiveNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerPositiveNodes i).re ^ 2) ∧
    (∀ i, 0 < (tiedPowerNegativeNodes i).re ∧
      (84 : ℝ) ^ 2 * Complex.normSq (tiedPowerNegativeNodes i) <
        (85 : ℝ) ^ 2 * (tiedPowerNegativeNodes i).re ^ 2) ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 2 =
      momentHankelMatrix (tiedPowerMoment tiedPowerNegativeNodes) 2 ∧
    (momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 1).PosDef ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerPositiveNodes) 2 *ᵥ
      tiedPowerSectorNoGoKernel = 0 ∧
    momentHankelMatrix (tiedPowerMoment tiedPowerNegativeNodes) 2 *ᵥ
      tiedPowerSectorNoGoKernel = 0 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerPositiveNodes) tiedPowerSectorNoGoKernel = 4 ∧
    finiteHankelBoundaryMonicRemainder
      (tiedPowerMoment tiedPowerNegativeNodes) tiedPowerSectorNoGoKernel = -16 ∧
    (∀ k, HasDerivAt (tiedPowerMobiusTrajectory tiedPowerPositiveNodes k)
      (-((k + 1 : ℕ) : ℂ) * ∑ i, tiedPowerPositiveNodes i ^ (k + 2)) 0) ∧
    (∀ k, HasDerivAt (tiedPowerMobiusTrajectory tiedPowerNegativeNodes k)
      (-((k + 1 : ℕ) : ℂ) * ∑ i, tiedPowerNegativeNodes i ^ (k + 2)) 0) := by
  exact ⟨tiedPowerPositiveNodes_conjugationClosed,
    tiedPowerNegativeNodes_conjugationClosed,
    tiedPowerPositiveNodes_narrowRightSector,
    tiedPowerNegativeNodes_narrowRightSector,
    tiedPowerSectorNoGo_sameFace,
    tiedPowerPositiveMoment_head_posDef,
    tiedPowerPositiveMoment_kernel,
    tiedPowerNegativeMoment_kernel,
    tiedPowerPositive_monicRemainder,
    tiedPowerNegative_monicRemainder,
    fun k => tiedPowerMobiusTrajectory_hasDerivAt tiedPowerPositiveNodes k,
    fun k => tiedPowerMobiusTrajectory_hasDerivAt tiedPowerNegativeNodes k⟩

end

end HTGeometry
