import GaloisForLFunctions.HTGeometry.BesselOrderRiccatiBaseField
import GaloisForLFunctions.HTGeometry.DifferentialJacobiFormula
import GaloisForLFunctions.HTGeometry.RatFuncShiftDerivationCommute
import Mathlib.Data.Matrix.Basic

/-!
# Bessel order isomonodromy obstruction after constant-field extension

The degree-at-infinity obstruction to a rational connection uses only characteristic zero. It
therefore persists over the differential closure of the constant field required by parameterized
difference Galois theory.
-/

namespace GaloisForLFunctions.HTGeometry.FieldShift

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

/-- Shift coefficient `c (X + 1)` over an arbitrary constant field. -/
def orderShiftCoeff (c : F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (Polynomial.C c * (Polynomial.X + Polynomial.C 1))

theorem orderShiftCoeff_ne_zero {c : F} (hc : c ≠ 0) : orderShiftCoeff c ≠ 0 := by
  refine algebraMap_poly_ne_zero (mul_ne_zero ?_ ?_)
  · simpa using hc
  · exact (Polynomial.monic_X_add_C (1 : F)).ne_zero

theorem intDegree_orderShiftCoeff {c : F} (hc : c ≠ 0) :
    (orderShiftCoeff c).intDegree = 1 := by
  rw [orderShiftCoeff, RatFunc.intDegree_polynomial]
  have h : (Polynomial.C c * (Polynomial.X + Polynomial.C 1)).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X_add_C]
  rw [h]
  rfl

variable [CharZero F]

/-- The Bessel order recurrence has no rational compatible derivation after arbitrary
characteristic-zero constant-field extension. -/
theorem besselOrder_no_rational_delta_structure {c : F} (hc : c ≠ 0) (P Q : RatFunc F)
    (hA : ratShift (ratShift P) + ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = P + orderShiftCoeff c * ratShift Q)
    (hB : ratShift (ratShift Q) + orderShiftCoeff c * ratShift (ratShift P)
          + orderShiftCoeff c * ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = Q + algebraMap F (RatFunc F) c + orderShiftCoeff c * ratShift P
          + orderShiftCoeff c * orderShiftCoeff c * ratShift Q) : False := by
  set b := orderShiftCoeff c with hbdef
  have hb0 : b ≠ 0 := orderShiftCoeff_ne_zero hc
  have hbdeg : b.intDegree = 1 := intDegree_orderShiftCoeff hc
  have hcne : algebraMap F (RatFunc F) c ≠ 0 := by
    intro h
    exact hc ((algebraMap F (RatFunc F)).injective (by rw [h, map_zero]))
  have hcdeg : (algebraMap F (RatFunc F) c).intDegree = 0 := intDegree_algebraMap_const c
  have hI : ratShift (ratShift Q) - Q + b * (P - ratShift P)
      = algebraMap F (RatFunc F) c := by linear_combination hB - b * hA
  have hT : ratShift (P + ratShift P + b * ratShift Q) = P + ratShift P + b * ratShift Q := by
    simp only [map_add, map_mul]
    linear_combination hA
  obtain ⟨κ, hκ⟩ := ratShift_fixed_eq_const hT
  have hTQ : b * ratShift Q
      = (algebraMap F (RatFunc F) κ + (-P)) + (-(ratShift P)) := by
    linear_combination hκ
  have hbQbound : b * ratShift Q = 0 ∨
      (b * ratShift Q).intDegree ≤ max 0 P.intDegree := by
    rw [hTQ]
    refine intDegree_add_le_of_le (intDegree_add_le_of_le (Or.inr ?_) (Or.inr ?_)) (Or.inr ?_)
    · rw [intDegree_algebraMap_const]
      exact le_max_left _ _
    · rw [RatFunc.intDegree_neg]
      exact le_max_right _ _
    · rw [RatFunc.intDegree_neg, intDegree_ratShift]
      exact le_max_right _ _
  set U := ratShift (ratShift Q) - Q with hUdef
  set V := b * (P - ratShift P) with hVdef
  have hUbound : U = 0 ∨ U.intDegree ≤ Q.intDegree - 1 := ratShift_two_sub_le Q
  by_cases hd : P.intDegree = 0
  · have hVsmall : V = 0 ∨ V.intDegree ≤ -1 := by
      by_cases hPfix : ratShift P = P
      · left
        rw [hVdef, hPfix, sub_self, mul_zero]
      · obtain ⟨-, hb2⟩ := intDegree_ratShift_sub_le_of_intDegree_zero hd hPfix
        have hneg : (P - ratShift P).intDegree ≤ -2 := by
          have hrw : P - ratShift P = -(ratShift P - P) := by ring
          rw [hrw, RatFunc.intDegree_neg]
          exact hb2
        rcases intDegree_mul_le_of_le (b := b) (x := P - ratShift P) hb0 (Or.inr hneg) with h | h
        · left
          rw [← hVdef] at h
          exact h
        · right
          rw [← hVdef, hbdeg] at h
          omega
    have hUsmall : U = 0 ∨ U.intDegree ≤ -1 := by
      by_cases hQ0 : Q = 0
      · left
        rw [hUdef, hQ0, map_zero, map_zero, sub_zero]
      · have hsq : ratShift Q ≠ 0 := fun h0 => hQ0 (ratShift_injective (by rw [h0, map_zero]))
        have hqdeg : (b * ratShift Q).intDegree = 1 + Q.intDegree := by
          rw [RatFunc.intDegree_mul hb0 hsq, hbdeg, intDegree_ratShift]
        have hbound : 1 + Q.intDegree ≤ 0 := by
          rcases hbQbound with h | h
          · exact absurd h (mul_ne_zero hb0 hsq)
          · rw [hqdeg, hd, max_self] at h
            exact h
        rcases hUbound with h1 | h1
        · left
          exact h1
        · right
          omega
    rcases intDegree_add_le_of_le hUsmall hVsmall with h | h
    · rw [hI] at h
      exact hcne h
    · rw [hI, hcdeg] at h
      omega
  · have hP0 : P ≠ 0 := by
      intro h0
      rw [h0, RatFunc.intDegree_zero] at hd
      exact hd rfl
    obtain ⟨hsne, hsdeg⟩ := intDegree_ratShift_sub hP0 hd
    have hPdne : P - ratShift P ≠ 0 := by
      intro h0
      exact hsne (by rw [← neg_eq_zero, ← h0]; ring)
    have hPddeg : (P - ratShift P).intDegree = P.intDegree - 1 := by
      have hrw : P - ratShift P = -(ratShift P - P) := by ring
      rw [hrw, RatFunc.intDegree_neg]
      exact hsdeg
    have hVne : V ≠ 0 := mul_ne_zero hb0 hPdne
    have hVdeg : V.intDegree = P.intDegree := by
      rw [hVdef, RatFunc.intDegree_mul hb0 hPdne, hbdeg, hPddeg]
      omega
    by_cases hQ0 : Q = 0
    · have hU0 : U = 0 := by rw [hUdef, hQ0, map_zero, map_zero, sub_zero]
      rw [hU0, zero_add] at hI
      rw [hI, hcdeg] at hVdeg
      exact hd hVdeg.symm
    · have hsq : ratShift Q ≠ 0 := fun h0 => hQ0 (ratShift_injective (by rw [h0, map_zero]))
      have hqdeg : (b * ratShift Q).intDegree = 1 + Q.intDegree := by
        rw [RatFunc.intDegree_mul hb0 hsq, hbdeg, intDegree_ratShift]
      have hbound : 1 + Q.intDegree ≤ max 0 P.intDegree := by
        rcases hbQbound with h | h
        · exact absurd h (mul_ne_zero hb0 hsq)
        · rw [hqdeg] at h
          exact h
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · have hmax : max 0 P.intDegree = 0 := max_eq_left (le_of_lt hneg)
        rw [hmax] at hbound
        have hUsmall : U = 0 ∨ U.intDegree ≤ -1 := by
          rcases hUbound with h1 | h1
          · left
            exact h1
          · right
            omega
        have hVsmall : V = 0 ∨ V.intDegree ≤ -1 := by
          right
          rw [hVdeg]
          omega
        rcases intDegree_add_le_of_le hUsmall hVsmall with h2 | h2
        · rw [hI] at h2
          exact hcne h2
        · rw [hI, hcdeg] at h2
          omega
      · have hmax : max 0 P.intDegree = P.intDegree := max_eq_right (le_of_lt hpos)
        rw [hmax] at hbound
        have hUlt : U = 0 ∨ U.intDegree < V.intDegree := by
          rcases hUbound with h1 | h1
          · left
            exact h1
          · right
            rw [hVdeg]
            omega
        obtain ⟨-, hVU⟩ := intDegree_add_eq_left hVne hUlt
        have hcomm : V + U = U + V := by ring
        rw [hcomm, hI, hcdeg] at hVU
        omega

/-- Companion matrix of the Bessel order recurrence over an arbitrary constant field. -/
def besselOrderCompanion (c : F) : Matrix (Fin 2) (Fin 2) (RatFunc F) :=
  !![0, 1; 1, orderShiftCoeff c]

/-- Entrywise coordinate derivative of the Bessel companion when `c` is a differential
constant. -/
def besselOrderCompanionDeriv (c : F) : Matrix (Fin 2) (Fin 2) (RatFunc F) :=
  !![0, 0; 0, algebraMap F (RatFunc F) c]

/-- Matrix connection obstruction after arbitrary characteristic-zero constant-field extension. -/
theorem besselOrder_no_matrix_delta_structure {c : F} (hc : c ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) (RatFunc F))
    (hB : B.map ratShift * besselOrderCompanion c - besselOrderCompanion c * B
      = besselOrderCompanionDeriv c) : False := by
  have hentry : ∀ i j : Fin 2,
      (B.map ratShift * besselOrderCompanion c - besselOrderCompanion c * B) i j
        = besselOrderCompanionDeriv c i j := fun i j => by rw [hB]
  have h00 := hentry 0 0
  have h01 := hentry 0 1
  have h10 := hentry 1 0
  have h11 := hentry 1 1
  simp [besselOrderCompanion, besselOrderCompanionDeriv, Matrix.sub_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul, dotProduct]
    at h00 h01 h10 h11
  have hr : ratShift (B 0 1) = B 1 0 := by linear_combination h00
  have ht : ratShift (B 0 0) + orderShiftCoeff c * ratShift (B 0 1) = B 1 1 := by
    linear_combination h01
  have h3 : ratShift (B 1 1) = B 0 0 + orderShiftCoeff c * B 1 0 := by
    linear_combination h10
  have hCeq : algebraMap F (RatFunc F) c = RatFunc.C c := rfl
  have h4 : ratShift (B 1 0) + orderShiftCoeff c * ratShift (B 1 1) - B 0 1
      - orderShiftCoeff c * B 1 1 = algebraMap F (RatFunc F) c := by
    rw [hCeq]
    linear_combination h11
  rw [← hr, ← ht] at h3 h4
  simp only [map_add, map_mul] at h3 h4
  exact besselOrder_no_rational_delta_structure hc (B 0 0) (B 0 1)
    (by linear_combination h3) (by linear_combination h4)

variable [Differential F]

/-- The total derivative of the Bessel companion, when its slope is a differential constant. -/
theorem matrixDeriv_besselOrderCompanion {c : F} (hc : Differential.deriv c = 0) :
    letI := coordinateTotalDifferential (K := F)
    matrixDeriv (besselOrderCompanion c) = besselOrderCompanionDeriv c := by
  letI := coordinateTotalDifferential (K := F)
  have hd : Differential.deriv (orderShiftCoeff c) = algebraMap F (RatFunc F) c := by
    change coordinateTotalDerivation (orderShiftCoeff c) = algebraMap F (RatFunc F) c
    rw [orderShiftCoeff, coordinateTotalDerivation_algebraMap, polyTotalDeriv_apply]
    simp [Polynomial.derivative_mul, coeffDeriv_mul, coeffDeriv_add, coeffDeriv_X,
      coeffDeriv_C, hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixDeriv, besselOrderCompanion, besselOrderCompanionDeriv, hd]

/-- No parameterized connection is created by extending the constant field. -/
theorem besselOrder_no_matrix_isomonodromy {c : F} (hc : c ≠ 0)
    (hcδ : Differential.deriv c = 0) :
    letI := coordinateTotalDifferential (K := F)
    ¬ ∃ B : Matrix (Fin 2) (Fin 2) (RatFunc F),
      B.map ratShift * besselOrderCompanion c =
        matrixDeriv (besselOrderCompanion c) + besselOrderCompanion c * B := by
  letI := coordinateTotalDifferential (K := F)
  rintro ⟨B, hB⟩
  apply besselOrder_no_matrix_delta_structure hc B
  rw [← matrixDeriv_besselOrderCompanion hcδ, hB]
  abel

end

end GaloisForLFunctions.HTGeometry.FieldShift
