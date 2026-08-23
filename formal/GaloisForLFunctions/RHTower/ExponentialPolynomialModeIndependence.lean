import GaloisForLFunctions.HTGeometry.GammaShiftConfluentCasoratian
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Independence of exponential-polynomial residue modes

For pairwise distinct complex nodes and arbitrary finite multiplicities, the functions
`z^q exp(lambda*z)` are linearly independent.  Their derivative-at-zero matrix is exactly the
transpose of the confluent polynomial-jet matrix already available in the corpus, so its determinant
is the confluent Vandermonde product.  This is the distinct-pole assembly needed by finite residue
mode expansions.
-/

namespace RHTower

open scoped BigOperators
open Complex Polynomial Matrix

noncomputable section

/-- Polynomial-exponential mode attached to one node and one multiplicity slot. -/
def exponentialPolynomialMode {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ)
    (k : Fin (∑ i, mult i)) (z : ℂ) : ℂ :=
  z ^ GaloisForLFunctions.gammaJetSlotOrder mult k *
    Complex.exp (lambda (GaloisForLFunctions.gammaJetSlotNode mult k) * z)

theorem contDiff_exponentialPolynomialMode {r : ℕ} (lambda : Fin r → ℂ)
    (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) (n : ℕ) :
    ContDiff ℂ n (exponentialPolynomialMode lambda mult k) := by
  exact (contDiff_id.pow _).mul
    (HurwitzExp.contDiff_expLin (lambda (GaloisForLFunctions.gammaJetSlotNode mult k)))

/-- Analytic mode jets are entries of the corresponding confluent polynomial-jet matrix. -/
theorem iteratedDeriv_exponentialPolynomialMode_zero
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ)
    (k : Fin (∑ i, mult i)) (n : ℕ) :
    iteratedDeriv n (exponentialPolynomialMode lambda mult k) 0 =
      ((Polynomial.derivative^[GaloisForLFunctions.gammaJetSlotOrder mult k])
        (Polynomial.X ^ n : Polynomial ℂ)).eval
          (lambda (GaloisForLFunctions.gammaJetSlotNode mult k)) := by
  let o := GaloisForLFunctions.gammaJetSlotOrder mult k
  let beta := lambda (GaloisForLFunctions.gammaJetSlotNode mult k)
  change iteratedDeriv n
      ((fun z : ℂ => z ^ o) * fun z : ℂ => Complex.exp (beta * z)) 0 =
    ((Polynomial.derivative^[o]) (Polynomial.X ^ n : Polynomial ℂ)).eval beta
  rw [iteratedDeriv_mul
    (n := n) (x := (0 : ℂ)) (by fun_prop)
      (HurwitzExp.contDiff_expLin beta).contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero, HurwitzExp.iteratedDeriv_expLin,
    mul_zero, Complex.exp_zero, mul_one]
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hon : o ≤ n
  · rw [Finset.sum_eq_single o]
    · rw [if_pos rfl, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      ring
    · intro i hi hio
      simp [hio]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hon))).elim
  · have hno : n < o := Nat.lt_of_not_ge hon
    rw [Finset.sum_eq_zero]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hno]
      simp
    · intro i hi
      have hio : i ≠ o := by
        have hi : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        omega
      simp [hio]

/-- Derivative-at-zero matrix of the complete polynomial-exponential mode family. -/
def exponentialPolynomialJetMatrix {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) ℂ :=
  fun n k => iteratedDeriv n.val (exponentialPolynomialMode lambda mult k) 0

theorem exponentialPolynomialJetMatrix_eq_transpose_confluent
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ) :
    exponentialPolynomialJetMatrix lambda mult =
      (GaloisForLFunctions.confluentPolynomialJetMatrix lambda mult
        (fun n => Polynomial.X ^ n.val)).transpose := by
  ext n k
  rw [exponentialPolynomialJetMatrix, Matrix.transpose_apply,
    GaloisForLFunctions.confluentPolynomialJetMatrix,
    GaloisForLFunctions.polynomialJetEvalMatrix,
    iteratedDeriv_exponentialPolynomialMode_zero]

theorem exponentialPolynomialJetMatrix_det_ne_zero
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (mult : Fin r → ℕ) : (exponentialPolynomialJetMatrix lambda mult).det ≠ 0 := by
  rw [exponentialPolynomialJetMatrix_eq_transpose_confluent, Matrix.det_transpose]
  rw [GaloisForLFunctions.det_confluentPolynomialJetMatrix]
  · refine mul_ne_zero ?_ ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun q _ => by
          exact_mod_cast Nat.factorial_ne_zero q.val
    · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j hj =>
          pow_ne_zero _ (sub_ne_zero.mpr fun h =>
            (ne_of_lt (Finset.mem_Ioi.mp hj)) (hlambda h).symm)
  · intro n
    simp
  · intro n
    simp

/-- Polynomial-exponential modes at distinct nodes are linearly independent, with every prescribed
multiplicity block included. -/
theorem exponentialPolynomialMode_linearIndependent
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (mult : Fin r → ℕ) :
    LinearIndependent ℂ (fun k : Fin (∑ i, mult i) =>
      exponentialPolynomialMode lambda mult k) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzero :
      (fun z : ℂ => ∑ k, c k * exponentialPolynomialMode lambda mult k z) = 0 := by
    funext z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc z
  have hjet : exponentialPolynomialJetMatrix lambda mult *ᵥ c = 0 := by
    funext n
    have key : iteratedDeriv n.val
        (fun z : ℂ => ∑ k, c k * exponentialPolynomialMode lambda mult k z) 0 = 0 := by
      rw [hzero]
      simp [iteratedDeriv]
    rw [HurwitzExp.iteratedDeriv_finset_sum _ n.val
      (fun k _ => contDiff_const.mul
        (contDiff_exponentialPolynomialMode lambda mult k n.val)) 0] at key
    simp only [iteratedDeriv_const_mul_field] at key
    simpa [exponentialPolynomialJetMatrix, Matrix.mulVec, dotProduct, mul_comm] using key
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero
    (exponentialPolynomialJetMatrix_det_ne_zero hlambda mult) hjet
  exact fun k => congrFun hc0 k

end

end RHTower
