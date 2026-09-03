import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Matrix.Rank
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationSampling

/-!
# Full inner rank of nonzero-shift affine free pencils

This module closes the algebraic-fullness half of the all-replica matrix-atom
obstruction.  A nonsingular field specialization rules out every factorization
through a smaller free module.  Augmenting all free variables to zero specializes
`sum_s A_s x_s - a I` to `-a I`, so every nonzero scalar shift is full.

No evaluation-rank or Strong-Atiyah statement is asserted here: identifying
free-Fock evaluation-kernel mass with this algebraic inner rank remains separate.
-/

namespace GaloisForLFunctions.HTGeometry

namespace Matrix

/-- A square matrix factors through an `r`-dimensional free module. -/
def HasInnerFactorizationAtMost
    {R ι : Type*} [Semiring R] (A : Matrix ι ι R) (r : ℕ) : Prop :=
  ∃ B : Matrix ι (Fin r) R, ∃ C : Matrix (Fin r) ι R, A = B * C

/-- Full noncommutative inner rank: no factorization through a smaller free module. -/
def HasFullInnerRank
    {R ι : Type*} [Semiring R] [Fintype ι] (A : Matrix ι ι R) : Prop :=
  ∀ r, r < Fintype.card ι → ¬ HasInnerFactorizationAtMost A r

/-- One nonsingular field specialization certifies full inner rank over the source ring. -/
theorem hasFullInnerRank_of_map_det_ne_zero
    {R K ι : Type*} [Semiring R] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : R →+* K) (A : Matrix ι ι R)
    (hdet : (A.map φ).det ≠ 0) : HasFullInnerRank A := by
  intro r hr
  rintro ⟨B, C, hA⟩
  have hmap : A.map φ = B.map φ * C.map φ := by
    rw [hA, Matrix.map_mul]
  have hinjA : Function.Injective (A.map φ).mulVec :=
    mulVec_injective_of_det_ne_zero hdet
  have hinjC : Function.Injective (C.map φ).mulVec := by
    intro x y hxy
    apply hinjA
    rw [hmap]
    simpa only [Matrix.mulVec_mulVec] using congrArg (B.map φ).mulVec hxy
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (f := (C.map φ).mulVecLin) hinjC
  have hnr : Fintype.card ι ≤ r := by simpa using hdim
  omega

end Matrix

namespace FreeAffinePencil

variable {K σ : Type*} [Field K]

/-- Augmentation of free algebra sending every noncommuting variable to zero. -/
def augmentation : FreeAlgebra K σ →ₐ[K] K :=
  FreeAlgebra.lift K (fun _ => 0)

@[simp] theorem augmentation_ι (s : σ) :
    augmentation (K := K) (FreeAlgebra.ι K s) = 0 := by
  exact FreeAlgebra.lift_ι_apply _ _

/-- Linear affine pencil `sum_s A_s x_s - a I` over free algebra. -/
def matrix
    [Fintype σ] {ι : Type*} [DecidableEq ι] (A : σ → Matrix ι ι K) (a : K) :
    Matrix ι ι (FreeAlgebra K σ) :=
  fun i j =>
    (∑ s, algebraMap K (FreeAlgebra K σ) (A s i j) * FreeAlgebra.ι K s) -
      if i = j then algebraMap K (FreeAlgebra K σ) a else 0

/-- Zero-variable specialization of affine free pencil is the scalar matrix `-a I`. -/
theorem map_augmentation
    [Fintype σ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : σ → Matrix ι ι K) (a : K) :
    (matrix A a).map (augmentation (K := K) (σ := σ)).toRingHom =
      (-a) • (1 : Matrix ι ι K) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matrix, augmentation]
  · simp [matrix, augmentation, hij]

/-- Nonzero scalar shift makes affine free pencil full in noncommutative inner rank. -/
theorem hasFullInnerRank
    [Fintype σ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : σ → Matrix ι ι K)
    {a : K} (ha : a ≠ 0) : Matrix.HasFullInnerRank (matrix A a) := by
  apply Matrix.hasFullInnerRank_of_map_det_ne_zero
    (augmentation (K := K) (σ := σ)).toRingHom
  rw [map_augmentation]
  rw [Matrix.det_smul]
  simpa using pow_ne_zero (Fintype.card ι) (neg_ne_zero.mpr ha)

/-- Real nonzero spectral shift makes every complex affine free pencil full. -/
theorem complex_hasFullInnerRank_of_ne_zero
    [Fintype σ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : σ → Matrix ι ι ℂ) {a : ℝ} (ha : a ≠ 0) :
    Matrix.HasFullInnerRank (matrix A (a : ℂ)) :=
  hasFullInnerRank A (Complex.ofReal_ne_zero.mpr ha)

end FreeAffinePencil

end GaloisForLFunctions.HTGeometry
