import GaloisForLFunctions.HTGeometry.DifferentialOperatorConstantMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact degree growth along a chain of operator matrices

The leading matrix is multiplicative, so along an ordered product `B₀ B₁ ⋯ B_{n-1}` of matrices of
operators the leading matrix of the product is the ordered product of the leading matrices, and the
degree bound `∑ eₖ` is attained exactly when that product of leading matrices is nonzero.

This is the generic branch of the slope dichotomy for a twisted product: as long as no leading
matrix annihilates the accumulated one, the degree grows exactly additively; a drop can only happen
when the accumulated leading matrix is killed.

* `chainProd`, `chainProdK` — the ordered products;
* `degree_matrix_mul_le`, `topCoeffMatrix_chainProd`;
* `exists_degree_chainProd_eq` — exact growth when the leading product survives;
* `matDeg_chainProd_eq` — the exact matrix degree `n · e` of such a chain;
* `chainProdK_eq_zero_of_le`, `rank_chainProdK_antitone`, `chainProdK_dichotomy` — the accumulated
  leading matrices either never vanish or vanish from some index on.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem degree_matrix_mul_le (A B : Matrix ι ι (DiffOp K)) (d e : ℕ)
    (hA : ∀ i j, degree (A i j) ≤ d) (hB : ∀ i j, degree (B i j) ≤ e) (i j : ι) :
    degree ((A * B) i j) ≤ d + e := by
  have hentry : (A * B) i j = ∑ k, A i k * B k j := Matrix.mul_apply
  rw [hentry]
  refine le_trans (degree_sum_le _ _) (Finset.sup_le fun k _ => ?_)
  exact le_trans (degree_mul_le _ _) (Nat.add_le_add (hA i k) (hB k j))

/-- The ordered product `B₀ B₁ ⋯ B_{n-1}` of operator matrices. -/
def chainProd (B : ℕ → Matrix ι ι (DiffOp K)) : ℕ → Matrix ι ι (DiffOp K)
  | 0 => 1
  | n + 1 => chainProd B n * B n

/-- The ordered product of coefficient matrices. -/
def chainProdK (C : ℕ → Matrix ι ι K) : ℕ → Matrix ι ι K
  | 0 => 1
  | n + 1 => chainProdK C n * C n

@[simp] theorem chainProd_zero (B : ℕ → Matrix ι ι (DiffOp K)) : chainProd B 0 = 1 := rfl

@[simp] theorem chainProd_succ (B : ℕ → Matrix ι ι (DiffOp K)) (n : ℕ) :
    chainProd B (n + 1) = chainProd B n * B n := rfl

omit [Differential K] in
@[simp] theorem chainProdK_zero (C : ℕ → Matrix ι ι K) : chainProdK C 0 = 1 := rfl

omit [Differential K] in
@[simp] theorem chainProdK_succ (C : ℕ → Matrix ι ι K) (n : ℕ) :
    chainProdK C (n + 1) = chainProdK C n * C n := rfl

omit [Fintype ι] in
theorem topCoeffMatrix_one_zero : topCoeffMatrix (1 : Matrix ι ι (DiffOp K)) 0 = 1 := by
  ext i j
  show coeff ((1 : Matrix ι ι (DiffOp K)) i j) 0 = (1 : Matrix ι ι K) i j
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
    show coeff (mono 0 1 : DiffOp K) 0 = 1
    rw [coeff_mono_self]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, coeff_zero]

omit [Fintype ι] in
theorem degree_one_le (i j : ι) : degree ((1 : Matrix ι ι (DiffOp K)) i j) ≤ 0 := by
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq]
    exact le_trans (degree_mono_le 0 (1 : K)) le_rfl
  · rw [Matrix.one_apply_ne hij, degree_zero]

/-- **The leading matrix of an ordered product is the ordered product of the leading matrices.** -/
theorem topCoeffMatrix_chainProd (B : ℕ → Matrix ι ι (DiffOp K)) (e : ℕ → ℕ)
    (hB : ∀ n i j, degree (B n i j) ≤ e n) (n : ℕ) :
    (∀ i j, degree (chainProd B n i j) ≤ ∑ k ∈ Finset.range n, e k) ∧
      topCoeffMatrix (chainProd B n) (∑ k ∈ Finset.range n, e k)
        = chainProdK (fun k => topCoeffMatrix (B k) (e k)) n := by
  induction n with
  | zero =>
      refine ⟨fun i j => ?_, ?_⟩
      · rw [Finset.range_zero, Finset.sum_empty, chainProd_zero]
        exact degree_one_le i j
      · rw [Finset.range_zero, Finset.sum_empty, chainProd_zero, chainProdK_zero]
        exact topCoeffMatrix_one_zero
  | succ n ih =>
      obtain ⟨hdeg, htop⟩ := ih
      have hsum : ∑ k ∈ Finset.range (n + 1), e k = (∑ k ∈ Finset.range n, e k) + e n :=
        Finset.sum_range_succ e n
      refine ⟨fun i j => ?_, ?_⟩
      · rw [hsum, chainProd_succ]
        exact degree_matrix_mul_le _ _ _ _ hdeg (hB n) i j
      · rw [hsum, chainProd_succ, chainProdK_succ,
          topCoeffMatrix_mul _ _ _ _ hdeg (hB n), htop]

/-- **Exact degree growth when the leading product survives.** -/
theorem exists_degree_chainProd_eq (B : ℕ → Matrix ι ι (DiffOp K)) (e : ℕ → ℕ)
    (hB : ∀ n i j, degree (B n i j) ≤ e n) (n : ℕ)
    (hne : chainProdK (fun k => topCoeffMatrix (B k) (e k)) n ≠ 0) :
    ∃ i j, degree (chainProd B n i j) = ∑ k ∈ Finset.range n, e k := by
  obtain ⟨hdeg, htop⟩ := topCoeffMatrix_chainProd B e hB n
  have hne' : topCoeffMatrix (chainProd B n) (∑ k ∈ Finset.range n, e k) ≠ 0 := by
    rw [htop]
    exact hne
  obtain ⟨i, j, hij⟩ : ∃ i j, coeff (chainProd B n i j) (∑ k ∈ Finset.range n, e k) ≠ 0 := by
    by_contra hcon
    refine hne' ?_
    ext i j
    by_contra hij
    exact hcon ⟨i, j, hij⟩
  exact ⟨i, j, le_antisymm (hdeg i j) (le_degree hij)⟩

omit [DecidableEq ι] in
theorem matDeg_le {P : Matrix ι ι (DiffOp K)} {m : ℕ} (h : ∀ i j, degree (P i j) ≤ m) :
    matDeg P ≤ m :=
  Finset.sup_le fun i _ => degVec_le_iff.mpr fun j => h i j

/-- **Exact degree of a chain of equal-degree factors whose leading products never vanish.** -/
theorem matDeg_chainProd_eq (B : ℕ → Matrix ι ι (DiffOp K)) (e : ℕ)
    (hB : ∀ n i j, degree (B n i j) ≤ e)
    (hne : ∀ n, chainProdK (fun k => topCoeffMatrix (B k) e) n ≠ 0) (n : ℕ) :
    matDeg (chainProd B n) = n * e := by
  have hsum : ∑ _k ∈ Finset.range n, e = n * e := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  obtain ⟨hdeg, _⟩ := topCoeffMatrix_chainProd B (fun _ => e) hB n
  obtain ⟨i, j, hij⟩ := exists_degree_chainProd_eq B (fun _ => e) hB n (hne n)
  refine le_antisymm ?_ ?_
  · refine matDeg_le fun i j => ?_
    rw [← hsum]
    exact hdeg i j
  · rw [← hsum, ← hij]
    exact degree_le_matDeg _ i j


omit [Differential K] in
/-- Once the accumulated leading matrix vanishes it stays zero. -/
theorem chainProdK_eq_zero_of_le (C : ℕ → Matrix ι ι K) {N : ℕ} (h : chainProdK C N = 0)
    {n : ℕ} (hn : N ≤ n) : chainProdK C n = 0 := by
  induction n with
  | zero =>
      have : N = 0 := Nat.le_zero.mp hn
      rw [← this]
      exact h
  | succ n ih =>
      rcases Nat.lt_or_ge N (n + 1) with hlt | hge
      · rw [chainProdK_succ, ih (by omega), zero_mul]
      · have : N = n + 1 := by omega
        rw [← this]
        exact h

omit [Differential K] in
/-- The ranks of the accumulated leading matrices are non-increasing. -/
theorem rank_chainProdK_antitone (C : ℕ → Matrix ι ι K) (n : ℕ) :
    Matrix.rank (chainProdK C (n + 1)) ≤ Matrix.rank (chainProdK C n) := by
  rw [chainProdK_succ]
  exact Matrix.rank_mul_le_left _ _

omit [Differential K] in
/-- **The accumulated leading matrices either never vanish or vanish from some index on.** -/
theorem chainProdK_dichotomy (C : ℕ → Matrix ι ι K) :
    (∀ n, chainProdK C n ≠ 0) ∨ ∃ N, ∀ n, N ≤ n → chainProdK C n = 0 := by
  by_cases h : ∀ n, chainProdK C n ≠ 0
  · exact Or.inl h
  · refine Or.inr ?_
    push Not at h
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => chainProdK_eq_zero_of_le C hN hn⟩


end

end DiffOp

end GaloisForLFunctions.HTGeometry
