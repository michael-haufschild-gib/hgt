import GaloisForLFunctions.EisensteinDegeneration.MatrixRegularity
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FinCases

/-!
# Branch contact is the obstruction to detecting poles

The coefficient-to-value matrix for a linear polynomial on `0,a` is
`[[1,0],[1,a]]`. It is injective exactly when the branches differ, but
reflects every parameter-divisibility condition exactly when their contact
order is zero. This applies the contact factor in Du, Theorem 8.12, to
the existing matrix criterion for regular specialization.
-/

namespace GaloisForLFunctions.EisensteinDegeneration
open Matrix PowerSeries
noncomputable section

def branchEvaluationMatrix {R : Type*} [CommRing R] (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 1, a]

theorem branchEvaluationMatrix_mulVec {R : Type*} [CommRing R] (a : R) (x : Fin 2 → R) :
    branchEvaluationMatrix a *ᵥ x = ![x 0, x 0 + a * x 1] := by
  ext i
  fin_cases i <;> simp [branchEvaluationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Generic injectivity detects distinct branches, without controlling contact order. -/
theorem branchEvaluationMatrix_injective_iff {R : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (a : R) :
    Function.Injective (branchEvaluationMatrix a).mulVec ↔ a ≠ 0 := by
  constructor
  · intro hinj ha
    have heq : branchEvaluationMatrix a *ᵥ ![0, 1] = branchEvaluationMatrix a *ᵥ 0 := by
      rw [ha, branchEvaluationMatrix_mulVec, branchEvaluationMatrix_mulVec]
      simp
    have hz := congrFun (hinj heq) 1
    simpa using hz
  · intro ha x y hxy
    rw [branchEvaluationMatrix_mulVec, branchEvaluationMatrix_mulVec] at hxy
    have h0 : x 0 = y 0 := congrFun hxy 0
    have h1 : a * x 1 = a * y 1 := by
      have h := congrFun hxy 1
      change x 0 + a * x 1 = y 0 + a * y 1 at h
      rw [h0] at h
      exact add_left_cancel h
    have hx1 := mul_left_cancel₀ ha h1
    ext i
    fin_cases i
    · exact h0
    · exact hx1

variable {K : Type*} [Field K]

theorem branchEvaluationMatrix_reduction (a : PowerSeries K) :
    (branchEvaluationMatrix a).map constantCoeff = branchEvaluationMatrix (constantCoeff a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [branchEvaluationMatrix]

/-- All orders of pole detection hold exactly at contact order zero. -/
theorem branchEvaluationMatrix_detects_divisibility_iff (a : PowerSeries K) :
    (∀ (m : ℕ) (f : Fin 2 → PowerSeries K),
      (∀ i, X ^ m ∣ (branchEvaluationMatrix a *ᵥ f) i) ↔ ∀ j, X ^ m ∣ f j) ↔
        a.order = 0 := by
  rw [← matrix_specialization_injective_iff, branchEvaluationMatrix_reduction,
    branchEvaluationMatrix_injective_iff]
  exact (not_congr PowerSeries.order_ne_zero_iff_constCoeff_eq_zero).symm.trans not_not

/-- The same contact criterion detects regularity after any common Laurent shift. -/
theorem branchEvaluationMatrix_detects_regular_iff (a : PowerSeries K) :
    (∀ (m : ℕ) (f : Fin 2 → PowerSeries K),
      (∀ i, Regular (HahnSeries.single (-(m : ℤ)) (1 : K) *
        (((branchEvaluationMatrix a *ᵥ f) i : PowerSeries K) : LaurentSeries K))) ↔
      ∀ j, Regular (HahnSeries.single (-(m : ℤ)) (1 : K) *
        ((f j : PowerSeries K) : LaurentSeries K))) ↔ a.order = 0 := by
  rw [← matrix_regular_specialization_iff, branchEvaluationMatrix_reduction,
    branchEvaluationMatrix_injective_iff]
  exact (not_congr PowerSeries.order_ne_zero_iff_constCoeff_eq_zero).symm.trans not_not

#print axioms branchEvaluationMatrix_injective_iff
#print axioms branchEvaluationMatrix_detects_divisibility_iff
#print axioms branchEvaluationMatrix_detects_regular_iff

end
end GaloisForLFunctions.EisensteinDegeneration
