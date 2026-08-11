import Mathlib
import GaloisForLFunctions.HTGeometry.VandermondeSign

/-!
# Vandermonde divisibility of polynomial evaluation determinants

For any family `v : Fin n → R` and any family of polynomials `p : Fin n → R[X]`, the Vandermonde
product `∏_{i<j} (v j − v i)` divides the determinant of the evaluation matrix
`(p j).eval (v i)`.

The proof is a row reduction: subtracting the top row from every other row makes the entry in row
`i` divisible by `v i − v 0`, with cofactor the evaluation of the divided difference of `p j`;
pulling those factors out and expanding along the top row reduces to the same statement one size
down.

Taking `p j = X ^ m j` gives the classical fact that the Vandermonde product divides every
alternant, without developing Schur polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {R : Type*} [CommRing R]

/-! ## Splitting the Vandermonde product -/

theorem prod_Ioi_zero_eq_prod_succ {M : Type*} [CommMonoid M] {m : ℕ} (g : Fin (m + 1) → M) :
    ∏ j ∈ Finset.Ioi (0 : Fin (m + 1)), g j = ∏ b : Fin m, g b.succ := by
  have hmap : (Finset.univ : Finset (Fin m)).map (Fin.succEmb m)
      = Finset.Ioi (0 : Fin (m + 1)) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Ioi]
    constructor
    · rintro ⟨b, rfl⟩
      exact Fin.succ_pos b
    · intro hj
      exact ⟨j.pred (Fin.pos_iff_ne_zero.mp hj), Fin.succ_pred j (Fin.pos_iff_ne_zero.mp hj)⟩
  rw [← hmap, Finset.prod_map]
  rfl

theorem prod_Ioi_succ_eq_prod_Ioi {M : Type*} [CommMonoid M] {m : ℕ} (g : Fin (m + 1) → M)
    (a : Fin m) : ∏ j ∈ Finset.Ioi a.succ, g j = ∏ b ∈ Finset.Ioi a, g b.succ := by
  rw [← Fin.map_succEmb_Ioi a, Finset.prod_map]
  rfl

/-- The Vandermonde product splits off its first row of differences. -/
theorem vandermondeProd_succ {m : ℕ} (v : Fin (m + 1) → R) :
    vandermondeProd v
      = (∏ b : Fin m, (v b.succ - v 0)) * vandermondeProd (v ∘ Fin.succ) := by
  rw [vandermondeProd, vandermondeProd, Fin.prod_univ_succ]
  congr 1
  · exact prod_Ioi_zero_eq_prod_succ fun j => v j - v 0
  · refine Finset.prod_congr rfl fun a _ => ?_
    exact prod_Ioi_succ_eq_prod_Ioi (fun j => v j - v a.succ) a

/-! ## Divided differences -/

/-- A divided difference of a polynomial: `p − p(c)` factors through `X − c`. -/
noncomputable def dividedDifference (p : Polynomial R) (c : R) : Polynomial R :=
  (Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := p)).choose

theorem dividedDifference_spec (p : Polynomial R) (c : R) :
    p - Polynomial.C (p.eval c) = (Polynomial.X - Polynomial.C c) * dividedDifference p c :=
  (Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := p)).choose_spec

/-- The defining identity of the divided difference, read off by evaluation. -/
theorem eval_sub_eval (p : Polynomial R) (c u : R) :
    p.eval u - p.eval c = (u - c) * (dividedDifference p c).eval u := by
  have h := congrArg (Polynomial.eval u) (dividedDifference_spec p c)
  simpa using h

/-! ## The divisibility theorem -/

/-- **Vandermonde divides every polynomial evaluation determinant.**  For any points `v` and any
polynomials `p`, `∏_{i<j}(v j − v i)` divides `det ((p j).eval (v i))`. -/
theorem vandermondeProd_dvd_det_eval :
    ∀ {n : ℕ} (v : Fin n → R) (p : Fin n → Polynomial R),
      vandermondeProd v ∣ (Matrix.of fun i j => (p j).eval (v i)).det := by
  intro n
  induction n with
  | zero =>
    intro v p
    simp [vandermondeProd]
  | succ m ih =>
    intro v p
    classical
    set dd : Fin (m + 1) → Polynomial R := fun j => dividedDifference (p j) (v 0) with hdd
    set M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
      Matrix.of fun i j => (p j).eval (v i) with hM
    set M' : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
      Matrix.of (Fin.cons (fun j => (p j).eval (v 0))
        (fun (a : Fin m) (j : Fin (m + 1)) => (dd j).eval (v a.succ))) with hM'
    set D : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
      Matrix.diagonal (Fin.cons 1 (fun b : Fin m => v b.succ - v 0)) with hD
    have hDM : ∀ (i j : Fin (m + 1)), (D * M') i j
        = (Fin.cons (1 : R) (fun b : Fin m => v b.succ - v 0) : Fin (m + 1) → R) i
          * M' i j := by
      intro i j
      rw [hD, Matrix.diagonal_mul]
    have hrow : ∀ i j, M i j
        = (D * M') i j
          + (Fin.cons (0 : R) (fun _ : Fin m => (1 : R)) : Fin (m + 1) → R) i * (D * M') 0 j := by
      intro i j
      rw [hDM i j, hDM 0 j, hM']
      refine Fin.cases ?_ ?_ i
      · rw [Fin.cons_zero, Fin.cons_zero, one_mul, zero_mul, add_zero, hM,
          Matrix.of_apply, Matrix.of_apply, Fin.cons_zero]
      · intro a
        rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_zero, one_mul, one_mul, hM,
          Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero, hdd]
        linear_combination eval_sub_eval (p j) (v 0) (v a.succ)
    have hdetM : M.det = (D * M').det :=
      Matrix.det_eq_of_forall_row_eq_smul_add_const (A := M) (B := D * M')
        ((Fin.cons (0 : R) fun _ : Fin m => (1 : R)) : Fin (m + 1) → R) 0
        (Fin.cons_zero _ _) hrow
    have hdetD : D.det = ∏ b : Fin m, (v b.succ - v 0) := by
      rw [hD, Matrix.det_diagonal, Fin.prod_univ_succ, Fin.cons_zero, one_mul]
      exact Finset.prod_congr rfl fun b _ => Fin.cons_succ _ _ b
    have hsub : ∀ j : Fin (m + 1),
        (M'.submatrix Fin.succ j.succAbove)
          = Matrix.of fun a b => ((dd ∘ j.succAbove) b).eval ((v ∘ Fin.succ) a) := by
      intro j
      ext a b
      rw [Matrix.submatrix_apply, hM', Matrix.of_apply, Matrix.of_apply, Fin.cons_succ]
      rfl
    have hdvd' : vandermondeProd (v ∘ Fin.succ) ∣ M'.det := by
      rw [Matrix.det_succ_row_zero]
      refine Finset.dvd_sum fun j _ => ?_
      refine Dvd.dvd.mul_left ?_ _
      rw [hsub j]
      exact ih (v ∘ Fin.succ) (dd ∘ j.succAbove)
    rw [hdetM, Matrix.det_mul, hdetD, vandermondeProd_succ]
    exact mul_dvd_mul_left _ hdvd'

/-- **Every alternant is divisible by the Vandermonde product.**  Taking the polynomials to be
monomials recovers the classical statement, which is the special case used to bound the valuation
of a minor of a Vandermonde matrix. -/
theorem vandermondeProd_dvd_det_pow {n : ℕ} (v : Fin n → R) (e : Fin n → ℕ) :
    vandermondeProd v ∣ (Matrix.of fun i j => v i ^ e j).det := by
  have h := vandermondeProd_dvd_det_eval v (fun j => Polynomial.X ^ e j)
  simpa using h

end GaloisForLFunctions.HTGeometry
