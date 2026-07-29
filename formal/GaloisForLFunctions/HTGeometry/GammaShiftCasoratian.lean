import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Consecutive-shift Casoratians of Gamma translates

For distinct shifts `shift i`, the matrix of consecutive values

`Gamma (s + shift i + k)`,  `0 ≤ k < n`,

has determinant

`(∏ i, Gamma (s + shift i)) * ∏ i<j, (shift j - shift i)`.

The proof separates each Gamma column by the functional equation and identifies the remaining
ascending-Pochhammer evaluation determinant with the ordinary Vandermonde determinant.  This is
the algebraic certificate underlying the finite Gamma-shift Dirichlet residual law.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Matrix Polynomial

noncomputable section

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]

/-- The ascending-factorial evaluation matrix, with shift order on rows and evaluation points on
columns. -/
def ascPochhammerEvalMatrix {n : ℕ} (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun k i ↦ (ascPochhammer R (k : ℕ)).eval (x i)

/-- Ascending factorials are monic of successive degrees, so their evaluation determinant is the
ordinary Vandermonde product. -/
theorem det_ascPochhammerEvalMatrix {n : ℕ} (x : Fin n → R) :
    (ascPochhammerEvalMatrix x).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  let p : Fin n → R[X] := fun k ↦ ascPochhammer R (k : ℕ)
  have hdeg : ∀ k, (p k).natDegree = k := by
    intro k
    exact ascPochhammer_natDegree R (k : ℕ)
  have hmonic : ∀ k, (p k).Monic := by
    intro k
    exact monic_ascPochhammer R (k : ℕ)
  calc
    (ascPochhammerEvalMatrix x).det =
        (Matrix.of fun i k ↦ (p k).eval (x i)).det := by
          rw [← Matrix.det_transpose]
          congr 1
    _ = (Matrix.vandermonde x).det :=
      (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p hdeg hmonic).symm
    _ = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) := Matrix.det_vandermonde x

/-- Iterating `Gamma (z + 1) = z * Gamma z` gives the ascending-Pochhammer multiplier away from
the intervening poles. -/
theorem Complex.Gamma_add_nat_eq_ascPochhammer_mul (z : ℂ) (n : ℕ)
    (hz : ∀ k < n, z + k ≠ 0) :
    Complex.Gamma (z + n) = (ascPochhammer ℂ n).eval z * Complex.Gamma z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show z + (n + 1 : ℕ) = (z + n) + 1 by push_cast; ring,
        Complex.Gamma_add_one (z + n) (hz n (Nat.lt_succ_self n)), ih]
      · rw [ascPochhammer_succ_eval]
        ring
      · intro k hk
        exact hz k (Nat.lt_trans hk (Nat.lt_succ_self n))

/-- The consecutive unit-shift value matrix of a finite family of Gamma translates. -/
def gammaShiftValueMatrix {n : ℕ} (s : ℂ) (shift : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun k i ↦ Complex.Gamma (s + shift i + (k : ℕ))

/-- **Exact Gamma-shift Casoratian.** Consecutive values of finitely many Gamma translates have
determinant equal to their value product times the Vandermonde of the shifts. -/
theorem det_gammaShiftValueMatrix {n : ℕ} (s : ℂ) (shift : Fin n → ℂ)
    (hpole : ∀ i (k : ℕ), k < n → s + shift i + k ≠ 0) :
    (gammaShiftValueMatrix s shift).det =
      (∏ i, Complex.Gamma (s + shift i)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (shift j - shift i) := by
  let x : Fin n → ℂ := fun i ↦ s + shift i
  have hmatrix : gammaShiftValueMatrix s shift =
      Matrix.of fun k i ↦ Complex.Gamma (x i) * ascPochhammerEvalMatrix x k i := by
    ext k i
    rw [gammaShiftValueMatrix, Matrix.of_apply, ascPochhammerEvalMatrix]
    rw [Complex.Gamma_add_nat_eq_ascPochhammer_mul (x i) (k : ℕ)]
    · ring
    · intro m hm
      exact hpole i m (Nat.lt_trans hm k.isLt)
  rw [hmatrix, Matrix.det_mul_row, det_ascPochhammerEvalMatrix]
  simp only [x, add_sub_add_left_eq_sub]

/-- Distinct shifts give an invertible consecutive-value matrix at every common regular point. -/
theorem det_gammaShiftValueMatrix_ne_zero {n : ℕ} (s : ℂ) (shift : Fin n → ℂ)
    (hshift : Function.Injective shift)
    (hpole : ∀ i (m : ℕ), s + shift i ≠ -(m : ℂ)) :
    (gammaShiftValueMatrix s shift).det ≠ 0 := by
  have hstep : ∀ i (k : ℕ), k < n → s + shift i + k ≠ 0 := by
    intro i k _ hzero
    apply hpole i k
    linear_combination hzero
  rw [det_gammaShiftValueMatrix s shift hstep]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Complex.Gamma_ne_zero (hpole i)
  · simpa only [Matrix.det_vandermonde] using
      (Matrix.det_vandermonde_ne_zero_iff.mpr hshift)

/-- At a common regular point, there is a unique monic order-`n` consecutive-value relation for
the `n` Gamma translates.  The vector `a` consists of the lower-order coefficients; matrix
multiplication states
`Gamma (s + shift i + n) + ∑ k, a k * Gamma (s + shift i + k) = 0` for every `i`. -/
theorem existsUnique_gammaShiftAnnihilatorValues {n : ℕ} (s : ℂ)
    (shift : Fin n → ℂ) (hshift : Function.Injective shift)
    (hpole : ∀ i (m : ℕ), s + shift i ≠ -(m : ℂ)) :
    ∃! a : Fin n → ℂ,
      (gammaShiftValueMatrix s shift)ᵀ.mulVec a =
        fun i ↦ -Complex.Gamma (s + shift i + (n : ℕ)) := by
  let M := gammaShiftValueMatrix s shift
  let b : Fin n → ℂ := fun i ↦ Complex.Gamma (s + shift i + (n : ℕ))
  have hM : M.det ≠ 0 := det_gammaShiftValueMatrix_ne_zero s shift hshift hpole
  have hMT : Mᵀ.det ≠ 0 := by simpa only [Matrix.det_transpose] using hM
  have hunit : IsUnit Mᵀ.det := isUnit_iff_ne_zero.mpr hMT
  let a : Fin n → ℂ := Mᵀ⁻¹.mulVec (-b)
  have ha : Mᵀ.mulVec a = -b := by
    dsimp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Mᵀ hunit, Matrix.one_mulVec]
  refine ⟨a, ?_, ?_⟩
  · change Mᵀ.mulVec a = fun i ↦ -Complex.Gamma (s + shift i + (n : ℕ))
    apply _root_.funext
    intro i
    exact congrFun ha i
  · intro a' ha'
    have ha'M : Mᵀ.mulVec a' = -b := by
      apply _root_.funext
      intro i
      exact congrFun ha' i
    have hsub : Mᵀ.mulVec (a' - a) = 0 := by
      rw [Matrix.mulVec_sub, ha'M, ha, sub_self]
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hMT hsub)

/-! ## The two Vandermonde values in the initial Dirichlet flag -/

/-- Reciprocal Dirichlet nodes `1, 1/2, ..., 1/q`. -/
def dirichletReciprocalNode {q : ℕ} (i : Fin q) : ℝ :=
  (((i : ℕ) + 1 : ℕ) : ℝ)⁻¹

/-- Logarithmic Dirichlet nodes `0, -log 2, ..., -log q`. -/
def dirichletLogNode {q : ℕ} (i : Fin q) : ℝ :=
  -Real.log (((i : ℕ) + 1 : ℕ) : ℝ)

theorem dirichletReciprocalNode_injective {q : ℕ} :
    Function.Injective (dirichletReciprocalNode (q := q)) := by
  intro i j h
  have hcast : ((((i : ℕ) + 1 : ℕ) : ℝ)) = (((j : ℕ) + 1 : ℕ) : ℝ) :=
    inv_injective h
  have hnat : (i : ℕ) + 1 = (j : ℕ) + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

theorem dirichletLogNode_injective {q : ℕ} :
    Function.Injective (dirichletLogNode (q := q)) := by
  intro i j h
  have hlog : Real.log ((((i : ℕ) + 1 : ℕ) : ℝ)) =
      Real.log (((j : ℕ) + 1 : ℕ) : ℝ) := neg_injective h
  have hcast : ((((i : ℕ) + 1 : ℕ) : ℝ)) = (((j : ℕ) + 1 : ℕ) : ℝ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hlog
  have hnat : (i : ℕ) + 1 = (j : ℕ) + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

/-- Product of the reciprocal-node and negative-log-node Vandermonde determinants. This is the
algebraic value `V_q` in the simultaneous zeta-jet residual asymptotic. -/
def dirichletFlagVandermonde (q : ℕ) : ℝ :=
  (Matrix.vandermonde (dirichletReciprocalNode (q := q))).det *
    (Matrix.vandermonde (dirichletLogNode (q := q))).det

/-- The initial Dirichlet packet has two noncolliding value signatures: its reciprocals and its
negative logarithms are both pairwise distinct. -/
theorem dirichletFlagVandermonde_ne_zero (q : ℕ) :
    dirichletFlagVandermonde q ≠ 0 := by
  exact mul_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr dirichletReciprocalNode_injective)
    (Matrix.det_vandermonde_ne_zero_iff.mpr dirichletLogNode_injective)

end

end GaloisForLFunctions
