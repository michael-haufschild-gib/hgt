import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The leading coefficient of a determinant with linear columns

A matrix whose last column is constant and whose other columns are linear in a parameter has a
determinant of degree at most the number of linear columns, and the coefficient at that degree is the
determinant obtained by keeping only the linear parts.

This is the extraction step of a Jacobian induction: the top coefficient of the determinant in the
newest variable is again a determinant, of the same shape one size down.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R : Type*} [CommRing R]

/-- The matrix with `n` columns linear in the parameter and a constant last column. -/
noncomputable def columnPencil {n : ℕ} (a b : Fin n → Fin (n + 1) → R) (w : Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial R) :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => Polynomial R) (Polynomial.C (w i))
      (fun j' : Fin n => Polynomial.C (a j' i) + Polynomial.X * Polynomial.C (b j' i)) j

/-- The matrix of leading parts. -/
def columnLeading {n : ℕ} (b : Fin n → Fin (n + 1) → R) (w : Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => R) (w i) (fun j' : Fin n => b j' i) j

/-- **The top coefficient of a column pencil determinant.** -/
theorem coeff_det_columnPencil {n : ℕ} (a b : Fin n → Fin (n + 1) → R) (w : Fin (n + 1) → R) :
    (columnPencil a b w).det.coeff n = (columnLeading b w).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  -- split off the constant last column
  have hsplit : ∏ i : Fin (n + 1), (columnPencil a b w) (σ i) i
      = (∏ i : Fin n, (columnPencil a b w) (σ i.castSucc) i.castSucc)
        * (columnPencil a b w) (σ (Fin.last n)) (Fin.last n) :=
    Fin.prod_univ_castSucc _
  have hlast : (columnPencil a b w) (σ (Fin.last n)) (Fin.last n)
      = Polynomial.C (w (σ (Fin.last n))) := by
    simp [columnPencil]
  have hcast : ∀ i : Fin n, (columnPencil a b w) (σ i.castSucc) i.castSucc
      = Polynomial.C (a i (σ i.castSucc)) + Polynomial.X * Polynomial.C (b i (σ i.castSucc)) := by
    intro i
    simp [columnPencil]
  rw [hsplit, hlast, Polynomial.coeff_mul_C]
  have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ((columnPencil a b w) (σ i.castSucc) i.castSucc).natDegree ≤ 1 := by
    intro i _
    rw [hcast i]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [max_le_iff]
    constructor
    · simp
    · refine le_trans (Polynomial.natDegree_mul_le) ?_
      simp only [Polynomial.natDegree_C, add_zero]
      exact Polynomial.natDegree_X_le
  have hprod := Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => (columnPencil a b w) (σ i.castSucc) i.castSucc) 1 hdeg
  simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hprod
  rw [hprod]
  have hcoeff : ∀ i : Fin n,
      ((columnPencil a b w) (σ i.castSucc) i.castSucc).coeff 1 = b i (σ i.castSucc) := by
    intro i
    rw [hcast i]
    simp [Polynomial.coeff_add, Polynomial.coeff_C]
  have hsplit2 : ∏ i : Fin (n + 1), (columnLeading b w) (σ i) i
      = (∏ i : Fin n, (columnLeading b w) (σ i.castSucc) i.castSucc)
        * (columnLeading b w) (σ (Fin.last n)) (Fin.last n) :=
    Fin.prod_univ_castSucc _
  rw [hsplit2]
  have hlast2 : (columnLeading b w) (σ (Fin.last n)) (Fin.last n) = w (σ (Fin.last n)) := by
    simp [columnLeading]
  have hcast2 : ∀ i : Fin n, (columnLeading b w) (σ i.castSucc) i.castSucc = b i (σ i.castSucc) := by
    intro i
    simp [columnLeading]
  rw [hlast2]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [hcoeff i, hcast2 i]


/-- **A nonzero leading determinant makes the pencil determinant nonzero.** -/
theorem det_columnPencil_ne_zero {n : ℕ} (a b : Fin n → Fin (n + 1) → R) (w : Fin (n + 1) → R)
    (h : (columnLeading b w).det ≠ 0) : (columnPencil a b w).det ≠ 0 := by
  intro h0
  refine h ?_
  rw [← coeff_det_columnPencil a b w, h0, Polynomial.coeff_zero]


/-! ## Dropping multiples of the constant column -/

/-- The transition matrix expressing a rescaled-and-shifted column family in the original one. -/
noncomputable def leadingTransition {n : ℕ} (c : Fin n → R) (p : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun k j =>
    Fin.lastCases (motive := fun _ => R)
      (Fin.lastCases (motive := fun _ => R) p (fun _ : Fin n => 0) k)
      (fun j' : Fin n =>
        Fin.lastCases (motive := fun _ => R) (c j')
          (fun k' : Fin n => if k' = j' then p else 0) k) j

theorem columnLeading_eq_mul {n : ℕ} (v : Fin n → Fin (n + 1) → R) (u : Fin (n + 1) → R)
    (c : Fin n → R) (p : R) :
    columnLeading (fun j i => c j * u i + p * v j i) (fun i => p * u i)
      = (columnLeading v u) * (leadingTransition c p) := by
  classical
  funext i j
  induction j using Fin.lastCases with
  | last =>
    simp [columnLeading, leadingTransition, Matrix.mul_apply, Fin.sum_univ_castSucc, mul_comm]
  | cast j' =>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [columnLeading, leadingTransition, Matrix.of_apply, Fin.lastCases_castSucc,
      Fin.lastCases_last]
    rw [Finset.sum_congr rfl (fun k' _ => by
      simp [mul_ite] : ∀ k' ∈ Finset.univ, v k' i * (if k' = j' then p else 0)
        = if k' = j' then v k' i * p else 0)]
    rw [Finset.sum_ite_eq' Finset.univ j' (fun k' => v k' i * p)]
    simp [mul_comm, add_comm]

theorem det_leadingTransition {n : ℕ} (c : Fin n → R) (p : R) :
    (leadingTransition c p).det = p ^ (n + 1) := by
  classical
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    have hdiag : ∀ k' : Fin n,
        (leadingTransition c p) k'.castSucc k'.castSucc = p := by
      intro k'
      simp [leadingTransition]
    have hlast : (leadingTransition c p) (Fin.last n) (Fin.last n) = p := by
      simp [leadingTransition]
    rw [Finset.prod_congr rfl (fun k' _ => hdiag k'), hlast, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  · intro i j hij
    have hlt : i < j := hij
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · have hne : i' ≠ j' := by
          intro h
          rw [h] at hlt
          exact absurd hlt (lt_irrefl _)
        simp [leadingTransition, hne]
      · exact absurd hlt (lt_asymm (Fin.castSucc_lt_last j'))
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp [leadingTransition]
      · exact absurd hlt (lt_irrefl _)

/-- **Multiples of the constant column drop out.**  Adding a multiple of the constant column to each
other column and rescaling all of them multiplies the determinant by a power of the scale. -/
theorem det_columnLeading_smul_add {n : ℕ} (v : Fin n → Fin (n + 1) → R) (u : Fin (n + 1) → R)
    (c : Fin n → R) (p : R) :
    (columnLeading (fun j i => c j * u i + p * v j i) (fun i => p * u i)).det
      = p ^ (n + 1) * (columnLeading v u).det := by
  rw [columnLeading_eq_mul, Matrix.det_mul, det_leadingTransition]
  ring


/-! ## Expansion along a unit first row -/

/-- **A unit first row drops the constant column.**  If the first row of a leading matrix is the last
unit vector, the determinant is, up to sign, the determinant of the linear part with that row
removed. -/
theorem det_columnLeading_of_row_zero {n : ℕ} (v : Fin n → Fin (n + 1) → R) (u : Fin (n + 1) → R)
    (hu : u 0 = 1) (hv : ∀ j, v j 0 = 0) :
    (columnLeading v u).det = (-1) ^ n * (Matrix.of fun i j : Fin n => v j i.succ).det := by
  classical
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have h1 : (columnLeading v u) 0 (Fin.last n) = 1 := by
      simp [columnLeading, hu]
    have h2 : ((columnLeading v u).submatrix Fin.succ (Fin.last n).succAbove)
        = Matrix.of fun i j : Fin n => v j i.succ := by
      funext i j
      simp [columnLeading, Fin.succAbove_last]
    rw [h1, h2]
    simp
  · intro j _ hj
    obtain ⟨j', rfl⟩ : ∃ j' : Fin n, j = j'.castSucc := by
      rcases Fin.eq_castSucc_or_eq_last j with h | h
      · exact h
      · exact absurd h hj
    have : (columnLeading v u) 0 j'.castSucc = 0 := by
      simp [columnLeading, hv j']
    rw [this]
    ring
  · intro h
    exact absurd (Finset.mem_univ (Fin.last n)) h

end GaloisForLFunctions.HTGeometry
