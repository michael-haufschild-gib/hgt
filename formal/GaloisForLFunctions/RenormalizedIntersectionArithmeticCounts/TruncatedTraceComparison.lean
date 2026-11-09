import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import GaloisForLFunctions.RHTower.ExteriorSatake
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverOfACurveIsAdmittedAboveTheZeroWidth

/-!
# Finite trace data and signed reciprocal coefficients

Positive power sums through degree n determine elementary symmetric
functions through n, without requiring equal cardinalities. Schur
triangulation supplies one multiset for both an actual matrix determinant
and all its trace powers. Adding the curve-root multiset identifies the
product coefficients with the two polar factors through n. Multiplication
by the reciprocal root series preserves this finite-degree comparison.
The final estimate records the resulting root-radius coefficient bound.
-/

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Polynomial

/-- Positive power sums through a finite order determine elementary functions through that order. -/
theorem esymm_eq_of_powerSums_through {S : Type*} [Field S] [CharZero S]
    (M N : Multiset S) (n : ℕ)
    (h : ∀ d, 0 < d → d ≤ n → (M.map (· ^ d)).sum = (N.map (· ^ d)).sum) :
    ∀ k, k ≤ n → M.esymm k = N.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [Multiset.esymm]
    · rw [multiset_esymm_eq_of_powerSum M k hk, multiset_esymm_eq_of_powerSum N k hk,
        h k hk hkn]
      congr 2
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 := ((Finset.mem_filter.mp ha).2)
      have haLt : a.1 < k := ha1.2
      have ha2 : a.1 + a.2 = k := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
      rw [ih a.1 haLt (Nat.le_trans haLt.le hkn), h a.2 (by omega) (by omega)]

/-- The elementary polynomial retains repeated entries of its multiset. -/
def elementaryPolynomial (M : Multiset ℂ) : ℂ[X] :=
  (M.map fun a => 1 + C a * X).prod

/-- Coefficients of the actual product are elementary symmetric functions. -/
theorem elementaryPolynomial_coeff (M : Multiset ℂ) (k : ℕ) :
    (elementaryPolynomial M).coeff k = M.esymm k := by
  induction M using Multiset.induction generalizing k with
  | empty =>
    cases k <;> simp [elementaryPolynomial, Multiset.esymm, Polynomial.coeff_one]
  | cons a M ih =>
    have he : elementaryPolynomial (a ::ₘ M) = (1 + C a * X) * elementaryPolynomial M := by
      simp only [elementaryPolynomial, Multiset.map_cons, Multiset.prod_cons]
    rw [he]
    cases k with
    | zero =>
      have h0 : ((1 + C a * X) * elementaryPolynomial M).coeff 0 =
          (elementaryPolynomial M).coeff 0 := by simp [Polynomial.coeff_zero_eq_eval_zero]
      rw [h0, ih]
      simp [Multiset.esymm]
    | succ k =>
      rw [add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih, ih, multiset_esymm_cons]

/-- Adjoining a root multiset multiplies its actual elementary polynomial. -/
theorem elementaryPolynomial_add (M N : Multiset ℂ) :
    elementaryPolynomial (M + N) = elementaryPolynomial M * elementaryPolynomial N := by
  simp only [elementaryPolynomial, Multiset.map_add, Multiset.prod_add]

/-- Power sums through a finite order determine the product coefficients through that order. -/
theorem elementaryPolynomial_coeff_eq_through (M N : Multiset ℂ) (n : ℕ)
    (h : ∀ d, 0 < d → d ≤ n → (M.map (· ^ d)).sum = (N.map (· ^ d)).sum)
    (k : ℕ) (hk : k ≤ n) :
    (elementaryPolynomial M).coeff k = (elementaryPolynomial N).coeff k := by
  rw [elementaryPolynomial_coeff, elementaryPolynomial_coeff]
  exact esymm_eq_of_powerSums_through M N n h k hk

#print axioms esymm_eq_of_powerSums_through
#print axioms elementaryPolynomial_coeff
#print axioms elementaryPolynomial_add
#print axioms elementaryPolynomial_coeff_eq_through
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Polynomial Matrix
open GaloisForLFunctions.HTGeometry


/-- The polynomial determinant of the actual complex matrix. -/
def matrixOrientationPolynomial {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) : ℂ[X] :=
  Matrix.det (1 + (Polynomial.X : ℂ[X]) • M.map Polynomial.C)

/-- Evaluation commutes with the actual determinant. -/
theorem matrixOrientationPolynomial_eval {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (z : ℂ) :
    (matrixOrientationPolynomial M).eval z = (1 + z • M).det := by
  change (Polynomial.evalRingHom z) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (Polynomial.evalRingHom z)
      ((if i = j then 1 else 0) + Polynomial.X * Polynomial.C (M i j)) =
    (if i = j then 1 else 0) + z * M i j
  have hx : (Polynomial.evalRingHom z) Polynomial.X = z := by
    change Polynomial.eval z Polynomial.X = z
    rw [Polynomial.eval_X]
  have hc (c : ℂ) : (Polynomial.evalRingHom z) (Polynomial.C c) = c := by
    change Polynomial.eval z (Polynomial.C c) = c
    rw [Polynomial.eval_C]
  by_cases hij : i = j <;> simp only [hij, if_true, if_false, map_add, map_mul,
    map_one, map_zero, hx, hc]

/-- Enumerating a multiset by a finite family gives the same polynomial product. -/
theorem elementaryPolynomial_univ {I : Type*} [Fintype I] (a : I → ℂ) :
    elementaryPolynomial (univ.val.map a) = ∏ i, (1 + C (a i) * X) := by
  simp only [elementaryPolynomial, Multiset.map_map, Function.comp_def,
    ← Finset.prod_eq_multiset_prod]

/-- Schur diagonal entries retain multiplicities in the determinant factorization. -/
theorem matrixOrientationPolynomial_schur {r : ℕ} (M U T : Matrix (Fin r) (Fin r) ℂ)
    (hU : U * Uᴴ = 1) (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) :
    matrixOrientationPolynomial M = elementaryPolynomial (univ.val.map fun i => T i i) := by
  apply Polynomial.funext
  intro z
  rw [matrixOrientationPolynomial_eval, elementaryPolynomial_univ,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simpa only [mul_comm z] using det_one_add_smul_eq_prod hU hT hMT z

/-- The same Schur diagonal also has every actual matrix trace as its power sum. -/
theorem schur_powerSum_eq_trace {r : ℕ} (M U T : Matrix (Fin r) (Fin r) ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id)
    (hMT : Uᴴ * M * U = T) (d : ℕ) :
    ((univ.val.map fun i => T i i).map (· ^ d)).sum = (M ^ d).trace := by
  rw [Multiset.map_map]
  exact (trace_pow_eq_sum_diag hU1 hU2 hT hMT d).symm

#print axioms matrixOrientationPolynomial_eval
#print axioms elementaryPolynomial_univ
#print axioms matrixOrientationPolynomial_schur
#print axioms schur_powerSum_eq_trace
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Polynomial Matrix
open GaloisForLFunctions.HTGeometry

/-- Simultaneous row and column reindexing preserves the actual determinant polynomial. -/
theorem matrixOrientationPolynomial_submatrix {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : J ≃ I) (M : Matrix I I ℂ) :
    matrixOrientationPolynomial (M.submatrix e e) = matrixOrientationPolynomial M := by
  have hm : 1 + (Polynomial.X : ℂ[X]) • (M.submatrix e e).map C =
      (1 + (Polynomial.X : ℂ[X]) • M.map C).submatrix e e := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, e.injective.eq_iff]
  rw [matrixOrientationPolynomial, hm, Matrix.det_submatrix_equiv_self]
  rfl

/-- Every actual matrix has one multiset simultaneously realizing its determinant and trace powers. -/
theorem exists_matrix_root_multiset {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) :
    ∃ Λ : Multiset ℂ, matrixOrientationPolynomial M = elementaryPolynomial Λ ∧
      ∀ d : ℕ, (Λ.map (· ^ d)).sum = (M ^ d).trace := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ :=
    exists_schur_triangulation (Fintype.card I) (M.submatrix e e)
  refine ⟨univ.val.map (fun i => T i i), ?_, fun d => ?_⟩
  · rw [← matrixOrientationPolynomial_submatrix e M]
    exact matrixOrientationPolynomial_schur _ U T hU2 hT hMT
  · rw [schur_powerSum_eq_trace _ U T hU1 hU2 hT hMT, trace_pow_submatrix]

/-- Exact traces through degree n determine the product with the actual root polynomial through n. -/
theorem matrix_root_product_coeff_through {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (Α : Multiset ℂ) (q : ℂ) (n : ℕ)
    (h : ∀ d, 0 < d → d ≤ n → (M ^ d).trace = q ^ d + 1 - (Α.map (· ^ d)).sum)
    (k : ℕ) (hk : k ≤ n) :
    (matrixOrientationPolynomial M * elementaryPolynomial Α).coeff k =
      ((1 + C 1 * X) * (1 + C q * X)).coeff k := by
  obtain ⟨Λ, hdet, htrace⟩ := exists_matrix_root_multiset M
  have hp : ∀ d, 0 < d → d ≤ n →
      ((Λ + Α).map (· ^ d)).sum = ((1 ::ₘ q ::ₘ (0 : Multiset ℂ)).map (· ^ d)).sum := by
    intro d hd hdn
    rw [Multiset.map_add, Multiset.sum_add, htrace, h d hd hdn]
    simp only [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons,
      Multiset.sum_zero, add_zero, one_pow]
    ring
  rw [hdet, ← elementaryPolynomial_add]
  have he := elementaryPolynomial_coeff_eq_through (Λ + Α) (1 ::ₘ q ::ₘ 0) n hp k hk
  simpa only [elementaryPolynomial, Multiset.map_cons, Multiset.map_zero,
    Multiset.prod_cons, Multiset.prod_zero, mul_one] using he

#print axioms matrixOrientationPolynomial_submatrix
#print axioms exists_matrix_root_multiset
#print axioms matrix_root_product_coeff_through
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset PowerSeries
open GaloisForLFunctions.ArithmeticCompensationTheory


/-- Multiplication preserves equality of coefficients through any fixed degree. -/
theorem coeff_mul_eq_through (A B C : PowerSeries ℂ) (n : ℕ)
    (h : ∀ k, k ≤ n → coeff k A = coeff k B) (k : ℕ) (hk : k ≤ n) :
    coeff k (A * C) = coeff k (B * C) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have haSum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha
  rw [h a.1 (by omega)]

/-- The elementary root polynomial is the curve numerator under sign reversal. -/
theorem elementaryPolynomial_coe_curveP {m : ℕ} (α : Fin m → ℂ) :
    (elementaryPolynomial (univ.val.map α) : PowerSeries ℂ) =
      rescale (-1) (curveP α) := by
  rw [elementaryPolynomial_univ]
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
    (∏ i, (1 + Polynomial.C (α i) * Polynomial.X)) = _
  rw [map_prod, curveP, map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, rescale_one_sub_C_mul_X,
    map_neg, neg_mul, sub_neg_eq_add, one_mul]

/-- The root polynomial and its actual product of geometric series are reciprocal. -/
theorem curveP_mul_curvePinv (α : Fin m → ℂ) : curveP α * curvePinv α = 1 := by
  rw [curveP, curvePinv, ← Finset.prod_mul_distrib]
  exact prod_eq_one fun i _ => one_sub_mul_geomSeries (α i)

/-- Finite trace data determine the signed reciprocal-zeta coefficient, not a whole series. -/
theorem matrixOrientationPolynomial_coeff_curveZinv {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (α : Fin m → ℂ) (q n : ℕ)
    (h : ∀ d, 0 < d → d ≤ n →
      (M ^ d).trace = (q : ℂ) ^ d + 1 - ∑ i, α i ^ d) :
    (matrixOrientationPolynomial M).coeff n =
      coeff n (rescale (-1) (curveZinv q α)) := by
  let P : PowerSeries ℂ := rescale (-1) (curveP α)
  let V : PowerSeries ℂ := rescale (-1) (curvePinv α)
  let D : PowerSeries ℂ := matrixOrientationPolynomial M
  let B : PowerSeries ℂ := rescale (-1) (curveZinv q α)
  have hPV : P * V = 1 := by
    rw [← map_mul, curveP_mul_curvePinv, map_one]
  have hBP : B * P =
      (1 + C 1 * X) * (1 + C (q : ℂ) * X) := by
    rw [mul_comm, ← map_mul, curveP_mul_curveZinv, map_mul,
      rescale_one_sub_C_mul_X, rescale_one_sub_C_mul_X]
    simp only [map_neg, neg_mul, sub_neg_eq_add, one_mul]
  have hp : ∀ k, k ≤ n → coeff k (D * P) = coeff k (B * P) := by
    intro k hk
    rw [hBP]
    have he := matrix_root_product_coeff_through M (univ.val.map α) (q : ℂ) n
      (fun d hd hdn => by
        rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
        exact h d hd hdn) k hk
    have hn : (((1 + Polynomial.C (1 : ℂ) * Polynomial.X) *
        (1 + Polynomial.C (q : ℂ) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
        (1 + C 1 * X) * (1 + C (q : ℂ) * X) := by
      simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_one,
        Polynomial.coe_C, Polynomial.coe_X]
    change coeff k ((matrixOrientationPolynomial M : PowerSeries ℂ) *
      rescale (-1) (curveP α)) = _
    rw [← hn, ← elementaryPolynomial_coe_curveP α, ← Polynomial.coe_mul,
      Polynomial.coeff_coe, Polynomial.coeff_coe]
    exact he
  have he := coeff_mul_eq_through (D * P) (B * P) V n hp n le_rfl
  rw [mul_assoc, hPV, mul_one, mul_assoc, hPV, mul_one] at he
  simpa only [D, B, Polynomial.coeff_coe] using he

#print axioms coeff_mul_eq_through
#print axioms elementaryPolynomial_coe_curveP
#print axioms curveP_mul_curvePinv
#print axioms matrixOrientationPolynomial_coeff_curveZinv
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open PowerSeries
open GaloisForLFunctions.ArithmeticCompensationTheory

/-- The signed reciprocal coefficient has the same root-radius bound as the ordinary coefficient. -/
theorem norm_coeff_signed_curveZinv_le {m : ℕ} (q : ℕ) (α : Fin m → ℂ)
    {t : ℝ} (ht : 1 ≤ t) (hα : ∀ i, ‖α i‖ ≤ t) (n : ℕ) :
    ‖coeff n (rescale (-1) (curveZinv q α))‖ ≤
      (2 * (q : ℝ) + 2) * ((n : ℝ) + 1) ^ m * t ^ n := by
  rw [coeff_rescale, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hp (k : ℕ) : ‖coeff k (curvePinv α)‖ ≤
      1 * ((k : ℝ) + 1) ^ m * t ^ k := by
    simpa only [one_mul] using norm_coeff_curvePinv_le α (by linarith) hα k
  have hq (k : ℕ) : ‖coeff k ((1 - C (q : ℂ) * X) * curvePinv α)‖ ≤
      (1 + (q : ℝ)) * ((k : ℝ) + 1) ^ m * t ^ k := by
    simpa only [Complex.ofReal_natCast, mul_one] using
      norm_coeff_one_sub_mul_le (m := m) (K := 1) (c := (q : ℝ))
        zero_le_one ht (Nat.cast_nonneg q) hp k
  have h1 := norm_coeff_one_sub_mul_le (m := m) (K := 1 + (q : ℝ)) (c := 1)
    (by positivity) ht zero_le_one hq n
  rw [curveZinv, mul_assoc]
  have hc : (1 + (1 : ℝ)) * (1 + (q : ℝ)) = 2 * q + 2 := by ring
  simpa only [Complex.ofReal_one, hc] using h1

#print axioms norm_coeff_signed_curveZinv_le
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
