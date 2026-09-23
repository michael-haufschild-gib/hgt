import GaloisForLFunctions.HTGeometry.RatFuncTotalDerivation
import GaloisForLFunctions.HTGeometry.RatFuncFieldShiftEquiv
import GaloisForLFunctions.HTGeometry.FractionRingDerivationExt
import GaloisForLFunctions.HTGeometry.SemilinearFractionField

/-!
# The unit shift commutes with the total derivation

Translating the variable commutes with differentiating: on polynomials the chain rule contributes
the factor one and the coefficientwise part is untouched, and two derivations of a rational function
field agreeing on the polynomial ring agree everywhere.  Conjugating the total derivation by the
shift therefore returns it, which is the compatibility a difference-differential base field needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Differential

variable {K : Type*} [Field K] [CharZero K] [Differential K]

omit [CharZero K] in
@[simp] theorem coeffDeriv_C_ratFuncShiftDerivationCommute (a : K) : coeffDeriv (Polynomial.C a) = Polynomial.C (a′) := by
  have hC : (Polynomial.C a : K[X]) = Polynomial.monomial 0 a := by
    rw [Polynomial.monomial_zero_left]
  rw [hC, coeffDeriv_monomial]
  simp

omit [CharZero K] in
@[simp] theorem coeffDeriv_X_ratFuncShiftDerivationCommute : coeffDeriv (Polynomial.X : K[X]) = 0 := by
  have hX : (Polynomial.X : K[X]) = Polynomial.monomial 1 (1 : K) :=
    (Polynomial.monomial_one_one_eq_X).symm
  rw [hX, coeffDeriv_monomial]
  simp

omit [CharZero K] in
theorem coeffDeriv_pow_X_add_C {c : K} (hc : (c : K)′ = 0) (k : ℕ) :
    coeffDeriv ((Polynomial.X + Polynomial.C c) ^ k) = 0 := by
  have hbase : coeffDeriv (Polynomial.X + Polynomial.C c : K[X]) = 0 := by
    rw [coeffDeriv_add, coeffDeriv_X_ratFuncShiftDerivationCommute, coeffDeriv_C_ratFuncShiftDerivationCommute, hc, map_zero, add_zero]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, coeffDeriv_mul, ih, hbase]
      simp

omit [CharZero K] in
theorem coeffDeriv_comp_X_add_C {c : K} (hc : (c : K)′ = 0) (p : K[X]) :
    coeffDeriv (p.comp (Polynomial.X + Polynomial.C c))
      = (coeffDeriv p).comp (Polynomial.X + Polynomial.C c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, coeffDeriv_add, coeffDeriv_add, hp, hq, Polynomial.add_comp]
  | monomial k a =>
      rw [Polynomial.monomial_comp, coeffDeriv_mul, coeffDeriv_C_ratFuncShiftDerivationCommute,
        coeffDeriv_pow_X_add_C hc, mul_zero, add_zero, coeffDeriv_monomial,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]

theorem polyTotalDeriv_comp_X_add_C {c : K} (hc : (c : K)′ = 0) (p : K[X]) :
    polyTotalDeriv (p.comp (Polynomial.X + Polynomial.C c))
      = (polyTotalDeriv p).comp (Polynomial.X + Polynomial.C c) := by
  rw [polyTotalDeriv_apply, polyTotalDeriv_apply, Polynomial.derivative_comp,
    coeffDeriv_comp_X_add_C hc, Polynomial.add_comp]
  simp

/-- The unit shift as a `ℚ`-algebra automorphism of the rational-function field. -/
def ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K :=
  { (FieldShift.ratShiftEquiv : RatFunc K ≃+* RatFunc K) with
    commutes' := fun q => by
      have hq : algebraMap ℚ (RatFunc K) q = (q : RatFunc K) := by
        simp
      rw [hq]
      exact map_ratCast (FieldShift.ratShiftEquiv : RatFunc K ≃+* RatFunc K) q }

omit [Differential K] in
@[simp] theorem ratShiftAlgEquiv_apply (r : RatFunc K) :
    (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K) r = FieldShift.ratShift r := rfl

omit [Differential K] in
@[simp] theorem ratShiftAlgEquiv_symm_apply (r : RatFunc K) :
    (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm r = FieldShift.ratShiftOf (-1) r := rfl

/-- **The shift commutes with the total derivation.** -/
theorem ratShift_coordinateTotalDerivation (r : RatFunc K) :
    FieldShift.ratShift (coordinateTotalDerivation r)
      = coordinateTotalDerivation (FieldShift.ratShift r) := by
  have hone : ((1 : K))′ = 0 := Derivation.map_one_eq_zero _
  have hneg : ((-1 : K))′ = 0 := by
    rw [show (-1 : K) = -(1 : K) from rfl, map_neg, hone, neg_zero]
  have hconj : GaloisForLFunctions.conjDerivation
        (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm coordinateTotalDerivation
      = coordinateTotalDerivation := by
    refine derivation_ext_of_fractionRing (R := K[X]) ?_
    intro p
    have hsymm : (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm
        (algebraMap K[X] (RatFunc K) p)
        = algebraMap K[X] (RatFunc K) (p.comp (Polynomial.X + Polynomial.C (-1 : K))) := by
      rw [ratShiftAlgEquiv_symm_apply, FieldShift.ratShiftOf_algebraMap]
    rw [GaloisForLFunctions.conjDerivation_apply, AlgEquiv.symm_symm, hsymm,
      coordinateTotalDerivation_algebraMap, polyTotalDeriv_comp_X_add_C hneg,
      ratShiftAlgEquiv_apply, FieldShift.ratShift_algebraMap,
      coordinateTotalDerivation_algebraMap]
    congr 1
    rw [Polynomial.comp_assoc]
    have hcancel : (Polynomial.X + Polynomial.C (-1 : K)).comp
        (Polynomial.X + Polynomial.C (1 : K)) = Polynomial.X := by
      simp
    rw [hcancel, Polynomial.comp_X]
  have happ : FieldShift.ratShift (coordinateTotalDerivation
      ((ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm (FieldShift.ratShift r)))
      = coordinateTotalDerivation (FieldShift.ratShift r) :=
    congrArg (fun D : Derivation ℚ (RatFunc K) (RatFunc K) => D (FieldShift.ratShift r)) hconj
  have hinv : (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm
      (FieldShift.ratShift r) = r := by
    have h := (ratShiftAlgEquiv : RatFunc K ≃ₐ[ℚ] RatFunc K).symm_apply_apply r
    simpa using h
  rw [hinv] at happ
  exact happ

end

end GaloisForLFunctions.HTGeometry
