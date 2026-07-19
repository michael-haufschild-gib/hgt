import GaloisForLFunctions.HilbertMetric.GradedPartition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Quadratic graph completion in finite Fock coordinates

This module formalizes the two finite-dimensional algebraic layers of the quadratic graph
completion law.

* A graph from a quadratic channel to an orthogonal linear channel has scaled Gram matrix
  `t ^ 2 I + t LᵀL`, hence determinant `t ^ n det (t I + LᵀL)`.
* A deterministic degree baseline plus independent Bernoulli channels has Fano margin equal to
  the baseline plus the sum of the squared channel probabilities.

The connector identifying these coordinates with the annihilation-invariant subspace
`ℝΩ ⊕ V ⊕ {q + Lq}` in symmetric Fock space is kept separate.  The results here are
unconditional finite matrix and finite-sum infrastructure.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

section GraphGram

variable {κ : Type*} [Fintype κ]

/-- Orthogonal feature rows for a graph: the left channel is a scaled canonical basis, while
the right channel is a scaled row of the graph map. -/
def graphFeatureRow {n : ℕ} (L : Matrix κ (Fin n) ℝ) (a b : ℝ)
    (i : Fin n) : Fin n ⊕ κ → ℝ
  | Sum.inl j => if i = j then a else 0
  | Sum.inr k => b * L k i

/-- The graph feature Gram matrix is the sum of the two orthogonal channel Gram matrices. -/
theorem standardFeatureGram_graphFeatureRow {n : ℕ}
    (L : Matrix κ (Fin n) ℝ) (a b : ℝ) :
    standardFeatureGram (graphFeatureRow L a b) =
      a ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) +
        b ^ 2 • (L.transpose * L) := by
  ext i j
  simp only [standardFeatureGram, Fintype.sum_sum_type, graphFeatureRow,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    simp
    rw [Finset.mul_sum]
    ring_nf
  · simp [hij]
    rw [Finset.mul_sum]
    ring_nf

/-- Gram matrix of a quadratic-to-linear graph after degree dilation by `sqrt t`.  Quadratic
coordinates scale by `t`, while linear correction coordinates scale by `sqrt t`. -/
def quadraticGraphGram {n : ℕ} (L : Matrix κ (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  standardFeatureGram (graphFeatureRow L t (Real.sqrt t))

/-- Exact quadratic graph Gram law. -/
theorem quadraticGraphGram_eq {n : ℕ} (L : Matrix κ (Fin n) ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    quadraticGraphGram L t =
      t ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ) +
        t • (L.transpose * L) := by
  rw [quadraticGraphGram, standardFeatureGram_graphFeatureRow, Real.sq_sqrt ht]

/-- Factoring the universal linear-scale contribution from the graph Gram matrix. -/
theorem quadraticGraphGram_eq_smul {n : ℕ} (L : Matrix κ (Fin n) ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    quadraticGraphGram L t =
      t • (t • (1 : Matrix (Fin n) (Fin n) ℝ) + L.transpose * L) := by
  rw [quadraticGraphGram_eq L t ht]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Quadratic graph determinant factorization.**  An `n`-dimensional graph contributes one
forced linear degree per graph direction and the residual determinant `det (t I + LᵀL)`. -/
theorem det_quadraticGraphGram {n : ℕ} (L : Matrix κ (Fin n) ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    (quadraticGraphGram L t).det =
      t ^ n *
        (t • (1 : Matrix (Fin n) (Fin n) ℝ) + L.transpose * L).det := by
  rw [quadraticGraphGram_eq_smul L t ht, Matrix.det_smul]
  simp

end GraphGram

section BernoulliFano

variable {ι : Type*} [Fintype ι]

/-- Mean of a deterministic degree baseline plus finitely many Bernoulli channels. -/
def bernoulliCompletionMean (baseline : ℝ) (p : ι → ℝ) : ℝ :=
  baseline + ∑ i, p i

/-- Variance of finitely many independent Bernoulli channels. -/
def bernoulliCompletionVariance (p : ι → ℝ) : ℝ :=
  ∑ i, p i * (1 - p i)

/-- **Bernoulli completion Fano identity.**  The mean-minus-variance margin is exactly the
deterministic baseline plus the squared channel probabilities. -/
theorem bernoulliCompletion_fano_identity (baseline : ℝ) (p : ι → ℝ) :
    bernoulliCompletionMean baseline p - bernoulliCompletionVariance p =
      baseline + ∑ i, (p i) ^ 2 := by
  unfold bernoulliCompletionMean bernoulliCompletionVariance
  rw [show baseline + (∑ i, p i) - ∑ i, p i * (1 - p i) =
      baseline + ((∑ i, p i) - ∑ i, p i * (1 - p i)) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (baseline + ·)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A nonnegative deterministic baseline makes every finite Bernoulli completion sub-Poisson. -/
theorem bernoulliCompletion_variance_le_mean (baseline : ℝ) (p : ι → ℝ)
    (hbaseline : 0 ≤ baseline) :
    bernoulliCompletionVariance p ≤ bernoulliCompletionMean baseline p := by
  rw [← sub_nonneg, bernoulliCompletion_fano_identity]
  exact add_nonneg hbaseline (Finset.sum_nonneg fun i _ => sq_nonneg (p i))

/-- A positive deterministic baseline makes every finite Bernoulli completion strictly
sub-Poisson. -/
theorem bernoulliCompletion_variance_lt_mean (baseline : ℝ) (p : ι → ℝ)
    (hbaseline : 0 < baseline) :
    bernoulliCompletionVariance p < bernoulliCompletionMean baseline p := by
  rw [← sub_pos, bernoulliCompletion_fano_identity]
  exact add_pos_of_pos_of_nonneg hbaseline
    (Finset.sum_nonneg fun i _ => sq_nonneg (p i))

end BernoulliFano

end


end GaloisForLFunctions.HilbertMetric
