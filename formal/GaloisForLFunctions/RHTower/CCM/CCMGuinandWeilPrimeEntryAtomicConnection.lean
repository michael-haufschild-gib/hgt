import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryRankOneTangent

/-!
# Finite atomic prime-entry connection

All prime-entry event tangents found in the preceding module lie on the same constant-boundary
outer-product direction.  This file sums arbitrary finite event sets and proves that the entire
atomic connection still factors as one scalar cumulative rate times that fixed rank-one matrix.

For the literal visible cutoff set, every index is at least two.  Von Mangoldt nonnegativity makes
each event rate nonpositive, including zero-weight composite indices.  The cumulative atomic
connection is therefore negative semidefinite for every aperture and every centered packet.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Scalar cumulative event rate of a finite index set. -/
def ccmGuinandWeilPrimeEntryAtomicRate (S : Finset ℕ) : ℝ :=
  ∑ k ∈ S, ccmGuinandWeilPrimeEntryMatrixRate k

/-- Matrix-valued cumulative event tangent of a finite index set. -/
def ccmGuinandWeilPrimeEntryAtomicTangent (S : Finset ℕ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ k ∈ S, ccmGuinandWeilPrimeEntryRankOneTangent k N

/-- Every finite atomic connection factors through the fixed constant-boundary outer product. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne
    (S : Finset ℕ) (N : ℕ) :
    ccmGuinandWeilPrimeEntryAtomicTangent S N =
      ccmGuinandWeilPrimeEntryAtomicRate S •
        Matrix.vecMulVec
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
          ccmConstantBoundary := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent, ccmGuinandWeilPrimeEntryAtomicRate]
  simp_rw [ccmGuinandWeilPrimeEntryRankOneTangent]
  rw [Finset.sum_smul]

/-- Every index above one has nonpositive entry rate; composites may have rate zero. -/
theorem ccmGuinandWeilPrimeEntryMatrixRate_nonpos
    {k : ℕ} (hk : 1 < k) :
    ccmGuinandWeilPrimeEntryMatrixRate k ≤ 0 := by
  rw [ccmGuinandWeilPrimeEntryMatrixRate]
  have hw : 0 ≤ criticalMellinAtomWeight k := by
    rw [criticalMellinAtomWeight]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hw) hlog.le

/-- A finite collection of nontrivial indices has nonpositive cumulative rate. -/
theorem ccmGuinandWeilPrimeEntryAtomicRate_nonpos
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k) :
    ccmGuinandWeilPrimeEntryAtomicRate S ≤ 0 := by
  rw [ccmGuinandWeilPrimeEntryAtomicRate]
  exact Finset.sum_nonpos fun k hk => ccmGuinandWeilPrimeEntryMatrixRate_nonpos (hS k hk)

/-- Exact quadratic form of the finite atomic connection. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_quadratic
    (S : Finset ℕ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    dotProduct v (ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ v) =
      ccmGuinandWeilPrimeEntryAtomicRate S * (∑ i, v i) ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply,
    Matrix.vecMulVec_apply, ccmConstantBoundary, smul_eq_mul, one_mul]
  rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

/-- Every finite atomic connection supported above index one is negative semidefinite. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_quadratic_nonpos
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    dotProduct v (ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ v) ≤ 0 := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_quadratic]
  exact mul_nonpos_of_nonpos_of_nonneg
    (ccmGuinandWeilPrimeEntryAtomicRate_nonpos hS) (sq_nonneg _)

/-- Cumulative atomic connection over the literal indices visible at aperture `a`. -/
def ccmGuinandWeilVisiblePrimeEntryAtomicTangent (a : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmGuinandWeilPrimeEntryAtomicTangent
    (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) N

/-- Literal visible atomic connection is negative semidefinite for every aperture. -/
theorem ccmGuinandWeilVisiblePrimeEntryAtomicTangent_quadratic_nonpos
    (a : ℝ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    dotProduct v (ccmGuinandWeilVisiblePrimeEntryAtomicTangent a N *ᵥ v) ≤ 0 := by
  apply ccmGuinandWeilPrimeEntryAtomicTangent_quadratic_nonpos
  intro k hk
  have := (Finset.mem_Icc.mp hk).1
  omega

/-- Summing arbitrarily many finite prime-entry tangents never raises matrix rank above one. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_rank_le_one
    (S : Finset ℕ) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryAtomicTangent S N).rank ≤ 1 := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne]
  have heq : (ccmGuinandWeilPrimeEntryAtomicRate S •
      Matrix.vecMulVec
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ) =
      Matrix.vecMulVec
        (ccmGuinandWeilPrimeEntryAtomicRate S •
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ))
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) := by
    ext i j
    simp [Matrix.vecMulVec_apply, ccmConstantBoundary]
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

end RHTower
