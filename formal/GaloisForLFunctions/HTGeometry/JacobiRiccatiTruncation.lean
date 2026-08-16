import GaloisForLFunctions.HTGeometry.SkewConjugatedRiccatiGramian
import Mathlib.Algebra.BigOperators.Fin

/-!
# Truncating a tridiagonal Riccati flow

The Jacobi matrix of an orthonormal polynomial family and the skew connection matrix of its moving
frame are both tridiagonal.  Compressing their commutator and the Jacobi square to the first `n`
levels therefore loses exactly the three terms that pass through level `n`, and those three terms
combine into a single rank-one boundary source at the last diagonal entry with the exact
coefficient `2n a_n²`.

This is the finite algebraic identity behind the boundary-source law of a finite Jacobi flow: the
bulk is gauge and Riccati, and the whole admission is one corner.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Tridiagonal data -/

/-- The symmetric tridiagonal Jacobi entry of a coefficient pair. -/
def jacobiEntry (a b : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = j then b i else if i + 1 = j then a j else if j + 1 = i then a i else 0

/-- The skew tridiagonal connection entry of a moving orthonormal frame. -/
def connectionEntry (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i + 1 = j then ((i : ℝ) + 1 / 2) * a j
  else if j + 1 = i then -(((j : ℝ) + 1 / 2) * a i)
  else 0

/-- The Jacobi compression to the first `n` levels. -/
def jacobiCompression (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => jacobiEntry a b i j

/-- The connection compression to the first `n` levels. -/
def connectionCompression (a : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => connectionEntry a i j

theorem connectionEntry_skew (a : ℕ → ℝ) (i j : ℕ) :
    connectionEntry a j i = -connectionEntry a i j := by
  rw [connectionEntry, connectionEntry]
  by_cases h1 : i + 1 = j
  · have h2 : ¬ (j + 1 = i) := by omega
    simp [h1, h2]
  · by_cases h2 : j + 1 = i
    · simp [h1, h2]
    · simp [h1, h2]

theorem connectionCompression_skew (a : ℕ → ℝ) (n : ℕ) :
    (connectionCompression a n)ᵀ = -connectionCompression a n := by
  ext i j
  simp only [Matrix.transpose_apply, connectionCompression, Matrix.of_apply, Matrix.neg_apply]
  exact connectionEntry_skew a i j

/-! ## The last row and column -/

theorem jacobiEntry_last_col (a b : ℕ → ℝ) (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    jacobiEntry a b j (m + 1) = if j = m then a (m + 1) else 0 := by
  rw [jacobiEntry]
  by_cases h : j = m
  · subst h
    simp
  · have h1 : ¬ (j = m + 1) := by omega
    have h3 : ¬ (m + 1 + 1 = j) := by omega
    simp [h1, h3, h]

theorem jacobiEntry_last_row (a b : ℕ → ℝ) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    jacobiEntry a b (m + 1) k = if k = m then a (m + 1) else 0 := by
  rw [jacobiEntry]
  by_cases h : k = m
  · subst h
    have h2 : ¬ (k + 1 + 1 = k) := by omega
    simp [h2]
  · have h1 : ¬ (m + 1 = k) := by omega
    have h2 : ¬ (m + 1 + 1 = k) := by omega
    simp [h1, h2, h]

theorem connectionEntry_last_col (a : ℕ → ℝ) (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    connectionEntry a j (m + 1) = if j = m then ((m : ℝ) + 1 / 2) * a (m + 1) else 0 := by
  rw [connectionEntry]
  by_cases h : j = m
  · subst h
    simp
  · have h2 : ¬ (m + 1 + 1 = j) := by omega
    simp [h2, h]

theorem connectionEntry_last_row (a : ℕ → ℝ) (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    connectionEntry a (m + 1) k = if k = m then -(((m : ℝ) + 1 / 2) * a (m + 1)) else 0 := by
  rw [connectionEntry]
  by_cases h : k = m
  · subst h
    have h1 : ¬ (k + 1 + 1 = k) := by omega
    simp [h1]
  · have h1 : ¬ (m + 1 + 1 = k) := by omega
    simp [h1, h]

/-! ## The truncation identity -/

/-- The last-level correction of a product of two compressions. -/
theorem mul_castSucc_split (M N : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    (j k : Fin (m + 1)) :
    (M * N) (j.castSucc) (k.castSucc)
      = (∑ l : Fin (m + 1), M (j.castSucc) (l.castSucc) * N (l.castSucc) (k.castSucc))
        + M (j.castSucc) (Fin.last (m + 1)) * N (Fin.last (m + 1)) (k.castSucc) := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]

/-- **The finite Jacobi Riccati truncation.**  Compressing the tridiagonal commutator and square
to one level fewer loses exactly `2n a_n²` at the last diagonal entry. -/
theorem jacobiCompression_riccati_truncation (a b : ℕ → ℝ) (m : ℕ) (j k : Fin (m + 1)) :
    (jacobiCompression a b (m + 2) * connectionCompression a (m + 2)
        - connectionCompression a (m + 2) * jacobiCompression a b (m + 2)
        - jacobiCompression a b (m + 2) * jacobiCompression a b (m + 2))
        (j.castSucc) (k.castSucc)
      = (jacobiCompression a b (m + 1) * connectionCompression a (m + 1)
          - connectionCompression a (m + 1) * jacobiCompression a b (m + 1)
          - jacobiCompression a b (m + 1) * jacobiCompression a b (m + 1)) j k
        - 2 * ((m : ℝ) + 1) * a (m + 1) ^ 2 *
            (if (j : ℕ) = m ∧ (k : ℕ) = m then 1 else 0) := by
  have hjle : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
  have hkle : (k : ℕ) ≤ m := Nat.lt_succ_iff.mp k.isLt
  simp only [Matrix.sub_apply]
  rw [mul_castSucc_split, mul_castSucc_split, mul_castSucc_split]
  simp only [jacobiCompression, connectionCompression, Matrix.of_apply, Fin.val_castSucc,
    Fin.val_last, Matrix.mul_apply]
  rw [jacobiEntry_last_col a b m hjle, connectionEntry_last_row a m hkle,
    connectionEntry_last_col a m hjle, jacobiEntry_last_row a b m hkle]
  by_cases hj : (j : ℕ) = m
  · by_cases hk : (k : ℕ) = m
    · simp only [hj, hk, if_true, and_true]
      ring
    · simp only [hj, hk, if_true, and_false, if_false]
      ring
  · simp only [hj, false_and, if_false]
    ring

/-- The same identity in matrix form: the truncated flow acquires one rank-one boundary source. -/
theorem jacobiCompression_riccati_matrix (a b : ℕ → ℝ) (m : ℕ) :
    Matrix.of (fun j k : Fin (m + 1) =>
        (jacobiCompression a b (m + 2) * connectionCompression a (m + 2)
          - connectionCompression a (m + 2) * jacobiCompression a b (m + 2)
          - jacobiCompression a b (m + 2) * jacobiCompression a b (m + 2))
          (j.castSucc) (k.castSucc))
      = jacobiCompression a b (m + 1) * connectionCompression a (m + 1)
        - connectionCompression a (m + 1) * jacobiCompression a b (m + 1)
        - jacobiCompression a b (m + 1) * jacobiCompression a b (m + 1)
        - (2 * ((m : ℝ) + 1) * a (m + 1) ^ 2) •
            Matrix.vecMulVec (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0)
              (fun i : Fin (m + 1) => if (i : ℕ) = m then (1 : ℝ) else 0) := by
  ext j k
  rw [Matrix.of_apply, jacobiCompression_riccati_truncation a b m j k]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) = m
  · by_cases hk : (k : ℕ) = m
    · simp [hj, hk]
    · simp [hj, hk]
  · simp [hj]

end GaloisForLFunctions.HTGeometry
