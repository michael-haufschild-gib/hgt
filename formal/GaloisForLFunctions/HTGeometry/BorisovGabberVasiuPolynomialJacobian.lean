import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.HTGeometry.KaehlerJacobianTopForm
import Mathlib.Algebra.CharP.Basic

open scoped BigOperators Matrix
open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Coordinatewise polynomial responses to one shared polynomial source. -/
def bgvSharedSourceMap (f : ι → Polynomial R) (w : MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval fun i => X i * Polynomial.aeval w (f i)

omit [Fintype ι] in
/-- The shared source contributes a rank-one correction to the diagonal Jacobian. -/
theorem bgv_jacobian_sharedSource (f : ι → Polynomial R) (w : MvPolynomial ι R) :
    jacobian R ι (bgvSharedSourceMap f w) =
      Matrix.diagonal (fun i => Polynomial.aeval w (f i)) +
        Matrix.vecMulVec (fun i => X i * Polynomial.aeval w (f i).derivative)
          (fun j => pderiv j w) := by
  ext i j
  simp only [jacobian, bgvSharedSourceMap, Matrix.of_apply, MvPolynomial.aeval_X,
    pderiv_mul, Derivation.map_aeval, smul_eq_mul, Matrix.add_apply, Matrix.vecMulVec_apply]
  by_cases h : i = j
  · subst j
    simp only [pderiv_X_self, one_mul, Matrix.diagonal_apply_eq]
    rw [mul_assoc]
  · rw [pderiv_X_of_ne h, zero_mul, zero_add, Matrix.diagonal_apply_ne _ h, zero_add,
      mul_assoc]

/-- The division-free shared-source Jacobian identity works over every commutative ring. -/
theorem bgv_det_jacobian_sharedSource (f : ι → Polynomial R) (w : MvPolynomial ι R) :
    (jacobian R ι (bgvSharedSourceMap f w)).det =
      (∏ i, Polynomial.aeval w (f i)) +
        ∑ i, (X i * pderiv i w) * Polynomial.aeval w (f i).derivative *
          ∏ j ∈ Finset.univ.erase i, Polynomial.aeval w (f j) := by
  rw [bgv_jacobian_sharedSource, bgv_det_diagonal_add_vecMulVec]
  apply congrArg (fun t : MvPolynomial ι R => (∏ i, Polynomial.aeval w (f i)) + t)
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Euler differentiation of a coordinate monomial, including exponent zero. -/
theorem bgv_coordinateEuler_power (i : ι) (e : ℕ) :
    X i * pderiv i ((X i : MvPolynomial ι R) ^ e) = (e : MvPolynomial ι R) * X i ^ e := by
  cases e with
  | zero => simp
  | succ e =>
    simp only [pderiv_pow, pderiv_X_self, mul_one, Nat.add_sub_cancel]
    rw [show X i * (((e + 1 : ℕ) : MvPolynomial ι R) * X i ^ e) =
      ((e + 1 : ℕ) : MvPolynomial ι R) * (X i ^ e * X i) by ac_rfl, ← pow_succ]

omit [Fintype ι] in
/-- Euler differentiation records the exact coordinate exponent in a finite product. -/
theorem bgv_coordinateEuler_product (e : ι → ℕ) (i : ι) (s : Finset ι) :
    X i * pderiv i (∏ j ∈ s, (X j : MvPolynomial ι R) ^ e j) =
      (if i ∈ s then (e i : MvPolynomial ι R) else 0) * ∏ j ∈ s, X j ^ e j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, mul_add]
    by_cases hia : i = a
    · subst a
      simp only [Finset.mem_insert_self, if_true]
      have hiz : X i * pderiv i (∏ j ∈ s, (X j : MvPolynomial ι R) ^ e j) = 0 := by
        simpa only [if_neg ha, zero_mul] using ih
      calc
        _ = (X i * pderiv i (X i ^ e i)) * (∏ j ∈ s, X j ^ e j) +
            X i ^ e i * (X i * pderiv i (∏ j ∈ s, X j ^ e j)) := by ring
        _ = _ := by rw [bgv_coordinateEuler_power, hiz, mul_zero, add_zero, mul_assoc]
    · have hp : pderiv i ((X a : MvPolynomial ι R) ^ e a) = 0 := by
        rw [pderiv_pow, pderiv_X_of_ne (Ne.symm hia), mul_zero]
      rw [hp, zero_mul, mul_zero, zero_add]
      rw [show X i * (X a ^ e a * pderiv i (∏ j ∈ s, X j ^ e j)) =
        X a ^ e a * (X i * pderiv i (∏ j ∈ s, X j ^ e j)) by ac_rfl, ih]
      simp only [Finset.mem_insert, hia, false_or]
      ac_rfl

/-- A characteristic-power factor is invisible to every coordinate Euler derivative. -/
theorem bgv_coordinateEuler_source (p : ℕ) [CharP R p]
    (L : MvPolynomial ι R) (e : ι → ℕ) (i : ι) :
    X i * pderiv i (L ^ p * ∏ j, (X j : MvPolynomial ι R) ^ e j) =
      (e i : MvPolynomial ι R) * (L ^ p * ∏ j, X j ^ e j) := by
  have hp0 : (p : MvPolynomial ι R) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (C : R → MvPolynomial ι R) (CharP.cast_eq_zero R p)
  have hL : pderiv i (L ^ p) = 0 := by
    rw [pderiv_pow, hp0, zero_mul, zero_mul]
  rw [pderiv_mul, hL, zero_mul, zero_add]
  rw [show X i * (L ^ p * pderiv i (∏ j, X j ^ e j)) =
    L ^ p * (X i * pderiv i (∏ j, X j ^ e j)) by ac_rfl,
    bgv_coordinateEuler_product]
  simp only [Finset.mem_univ, if_true]
  ac_rfl

/-- Corollary 21.2 for a characteristic-power factor; zero weights are also allowed. -/
theorem bgv_det_jacobian_weightedSource (p : ℕ) [CharP R p]
    (L : MvPolynomial ι R) (e : ι → ℕ) (f : ι → Polynomial R) :
    let w := L ^ p * ∏ j, (X j : MvPolynomial ι R) ^ e j
    (jacobian R ι (bgvSharedSourceMap f w)).det =
      (∏ i, Polynomial.aeval w (f i)) +
        ∑ i, (e i : MvPolynomial ι R) * w * Polynomial.aeval w (f i).derivative *
          ∏ j ∈ Finset.univ.erase i, Polynomial.aeval w (f j) := by
  dsimp only
  rw [bgv_det_jacobian_sharedSource]
  simp_rw [bgv_coordinateEuler_source]

/-- The top differential form scales by the same explicit shared-source determinant. -/
theorem bgv_det_pullback_sharedSource (f : ι → Polynomial R) (w : MvPolynomial ι R) :
    LinearMap.det (pullbackDifferential R ι (bgvSharedSourceMap f w)) =
      (∏ i, Polynomial.aeval w (f i)) +
        ∑ i, (X i * pderiv i w) * Polynomial.aeval w (f i).derivative *
          ∏ j ∈ Finset.univ.erase i, Polynomial.aeval w (f j) := by
  rw [det_pullbackDifferential, bgv_det_jacobian_sharedSource]

/-- The scalar polynomial controlling a weighted shared-source Jacobian. -/
def bgvJacobianResponse (e : ι → ℕ) (f : ι → Polynomial R) : Polynomial R :=
  (∏ i, f i) + ∑ i, (e i : Polynomial R) * Polynomial.X * (f i).derivative *
    ∏ j ∈ Finset.univ.erase i, f j

/-- In every characteristic the monomial-source determinant factors through one scalar polynomial. -/
theorem bgv_det_jacobian_monomialSource (e : ι → ℕ) (f : ι → Polynomial R) :
    let w := ∏ j, (X j : MvPolynomial ι R) ^ e j
    (jacobian R ι (bgvSharedSourceMap f w)).det =
      Polynomial.aeval w (bgvJacobianResponse e f) := by
  dsimp only
  rw [bgv_det_jacobian_sharedSource]
  simp_rw [bgv_coordinateEuler_product, if_pos (Finset.mem_univ _)]
  simp only [bgvJacobianResponse, map_add, map_prod, map_sum, map_mul, map_natCast,
    Polynomial.aeval_X]

/-- Characteristic-power twists preserve the same scalar response polynomial. -/
theorem bgv_det_jacobian_twistedSource_response (p : ℕ) [CharP R p]
    (L : MvPolynomial ι R) (e : ι → ℕ) (f : ι → Polynomial R) :
    let w := L ^ p * ∏ j, (X j : MvPolynomial ι R) ^ e j
    (jacobian R ι (bgvSharedSourceMap f w)).det =
      Polynomial.aeval w (bgvJacobianResponse e f) := by
  dsimp only
  rw [bgv_det_jacobian_weightedSource]
  simp only [bgvJacobianResponse, map_add, map_prod, map_sum, map_mul, map_natCast,
    Polynomial.aeval_X]

end
end GaloisForLFunctions.HTGeometry
