import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition

/-!
# Coupling invisible to both matrix marginals

For a bipartite matrix `X`, the homogeneous separability defect is
`trace X • X - partialTraceRight X ⊗ partialTraceLeft X`. Both partial traces vanish.
For two product clusters it factors as a tensor product of the differences of their
trace-weighted marginals. This gives an exact separability test for the cluster model
of Rivetti–Fodor–Björnson–Skoglund, Proposition 2, arXiv:2611.08007. Without
positive covariance normalization, a trace-zero degeneracy must also be included.
-/

noncomputable section

open Matrix HTGeometry.ConstraintRelativity
open scoped BigOperators Kronecker

namespace HilbertMetric.Correlation

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Homogeneous discrepancy from the product of the two partial traces. -/
def kroneckerDefect (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  X.trace • X - partialTraceRight X ⊗ₖ partialTraceLeft X

/-- Marginal observations cannot detect the separability defect. -/
theorem kroneckerDefect_mem_crossFibre (X : Matrix (m × n) (m × n) ℂ) :
    kroneckerDefect X ∈ matrixCrossFibre := by
  rw [mem_matrixCrossFibre]
  simp only [kroneckerDefect, partialTraceRight_sub, partialTraceLeft_sub,
    partialTraceRight_smul, partialTraceLeft_smul, partialTraceRight_kronecker,
    partialTraceLeft_kronecker, trace_partialTraceRight, trace_partialTraceLeft, sub_self,
    and_self]

/-- Every product matrix has zero separability defect, without normalization. -/
theorem kroneckerDefect_product (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    kroneckerDefect (A ⊗ₖ B) = 0 := by
  rw [kroneckerDefect, trace_kronecker, partialTraceRight_kronecker,
    partialTraceLeft_kronecker]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul, Matrix.zero_apply]
  ring

/-- Two product clusters interact only through simultaneous changes of both marginals. -/
theorem kroneckerDefect_two_clusters
    (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    kroneckerDefect (A ⊗ₖ B + C ⊗ₖ D) =
      (C.trace • A - A.trace • C) ⊗ₖ (D.trace • B - B.trace • D) := by
  simp only [kroneckerDefect, trace_add, trace_kronecker,
    partialTraceRight_add, partialTraceLeft_add, partialTraceRight_kronecker,
    partialTraceLeft_kronecker]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  ring

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
/-- A tensor vanishes exactly when one of its factors vanishes. -/
theorem product_eq_zero_iff (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    A ⊗ₖ B = 0 ↔ A = 0 ∨ B = 0 := by
  classical
  constructor
  · intro h
    by_cases hA : A = 0
    · exact Or.inl hA
    · right
      obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hA (Matrix.ext hn)
      ext k l
      have hentry := congrArg (fun M : Matrix (m × n) (m × n) ℂ => M (i, k) (j, l)) h
      exact (mul_eq_zero.mp hentry).resolve_left hij
  · rintro (rfl | rfl) <;> simp

/-- Zero defect means a product matrix, or exactly the trace-zero degeneracy
where at least one marginal vanishes. -/
theorem kroneckerDefect_eq_zero_iff (X : Matrix (m × n) (m × n) ℂ) :
    kroneckerDefect X = 0 ↔
      (∃ A : Matrix m m ℂ, ∃ B : Matrix n n ℂ, X = A ⊗ₖ B) ∨
        (X.trace = 0 ∧ (partialTraceRight X = 0 ∨ partialTraceLeft X = 0)) := by
  constructor
  · intro h
    have he : X.trace • X = partialTraceRight X ⊗ₖ partialTraceLeft X :=
      sub_eq_zero.mp h
    by_cases ht : X.trace = 0
    · right
      refine ⟨ht, (product_eq_zero_iff _ _).mp ?_⟩
      rw [← he, ht, zero_smul]
    · left
      refine ⟨X.trace⁻¹ • partialTraceRight X, partialTraceLeft X, ?_⟩
      calc
        X = X.trace⁻¹ • (X.trace • X) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [he, smul_kronecker]
  · rintro (⟨A, B, rfl⟩ | ⟨ht, hm⟩)
    · exact kroneckerDefect_product A B
    · rw [kroneckerDefect, ht, zero_smul, (product_eq_zero_iff _ _).mpr hm, sub_self]

/-- Exact two-cluster rigidity: the defect vanishes precisely when a marginal pair
is proportional with its trace as normalization. -/
theorem kroneckerDefect_two_clusters_eq_zero_iff
    (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    kroneckerDefect (A ⊗ₖ B + C ⊗ₖ D) = 0 ↔
      C.trace • A = A.trace • C ∨ D.trace • B = B.trace • D := by
  rw [kroneckerDefect_two_clusters, product_eq_zero_iff, sub_eq_zero, sub_eq_zero]

private theorem pairwise_scalar_identity {ι : Type*} [Fintype ι]
    (a b x y : ι → ℂ) :
    (2 : ℂ) * ((∑ i, a i * b i) * (∑ i, x i * y i) -
      (∑ i, b i * x i) * (∑ i, a i * y i)) =
      ∑ i, ∑ j, (a j * x i - a i * x j) * (b j * y i - b i * y j) := by
  symm
  calc
    _ = ∑ i, ∑ j, ((a j * b j) * (x i * y i) +
        (a i * b i) * (x j * y j) - (b i * x i) * (a j * y j) -
        (a i * y i) * (b j * x j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => (a j * b j) * (x i * y i))]
      simp only [← Finset.sum_mul_sum]
      ring

/-- All cluster interactions are pairwise: the homogeneous defect is half the sum
of tensor products of trace-weighted marginal differences. -/
theorem kroneckerDefect_clusters {ι : Type*} [Fintype ι]
    (A : ι → Matrix m m ℂ) (B : ι → Matrix n n ℂ) :
    (2 : ℂ) • kroneckerDefect (∑ i, A i ⊗ₖ B i) =
      ∑ i, ∑ j, ((A j).trace • A i - (A i).trace • A j) ⊗ₖ
        ((B j).trace • B i - (B i).trace • B j) := by
  have hR : partialTraceRight (∑ i, A i ⊗ₖ B i) =
      ∑ i, (B i).trace • A i := by
    exact (map_sum partialTraceRightLinear _ _).trans
      (Finset.sum_congr rfl fun i _ => partialTraceRight_kronecker (A i) (B i))
  have hL : partialTraceLeft (∑ i, A i ⊗ₖ B i) =
      ∑ i, (A i).trace • B i := by
    exact (map_sum partialTraceLeftLinear _ _).trans
      (Finset.sum_congr rfl fun i _ => partialTraceLeft_kronecker (A i) (B i))
  simp only [kroneckerDefect, hR, hL, trace_sum, trace_kronecker]
  ext u v
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  exact pairwise_scalar_identity (fun i => (A i).trace) (fun i => (B i).trace)
    (fun i => A i u.1 v.1) (fun i => B i u.2 v.2)

end HilbertMetric.Correlation
