import GaloisForLFunctions.HTGeometry.ContinuousCircuitMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.ConormNormDetLaw
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Real coordinates and norm comparison for finite C*-matrices

Finite complex C*-matrices are flattened into complete real entry coordinates.
For a pair of matrices, the Euclidean coordinate norm dominates the product
C*-operator norm.  Thus an operator-norm conorm estimate can be transferred
without dimension loss to the Euclidean target required by norm determinants
and coarea.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable instance cstarMatrixFiniteDimensionalReal
    (ι : Type*) [Fintype ι] :
    FiniteDimensional ℝ (CStarMatrix ι ι ℂ) := by
  let e : Matrix ι ι ℂ ≃ₗ[ℝ] CStarMatrix ι ι ℂ :=
    CStarMatrix.ofMatrixₗ (R := ℝ)
  exact e.finiteDimensional

/-- Finite complex C*-module columns and Euclidean columns are isometric. -/
def withCStarComplexEuclideanEquiv
    (ι : Type*) [Fintype ι] :
    WithCStarModule ℂ (ι → ℂ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toLinearEquiv :=
    (WithCStarModule.linearEquiv ℂ ℂ (ι → ℂ)).trans
      (EuclideanSpace.equiv ι ℂ).symm.toLinearEquiv
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithCStarModule.pi_norm_sq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖x i‖ ^ 2) = ‖∑ i, inner ℂ (x i) (x i)‖
    simp only [RCLike.inner_apply]
    simp_rw [RCLike.mul_conj]
    have hcast :
        (∑ i, ((‖x i‖ : ℝ) : ℂ) ^ 2) =
          ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by norm_cast
    calc
      (∑ i, ‖x i‖ ^ 2) =
          ‖((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg ‖x i‖)]
      _ = ‖∑ i, ((‖x i‖ : ℝ) : ℂ) ^ 2‖ := congrArg norm hcast.symm

theorem withCStarComplexEuclideanEquiv_apply_ofLp
    {ι : Type*} [Fintype ι]
    (x : WithCStarModule ℂ (ι → ℂ)) (i : ι) :
    ((withCStarComplexEuclideanEquiv ι x).ofLp i) = x i := rfl

theorem withCStarComplexEuclideanEquiv_toCLM
    {ι : Type*} [Fintype ι]
    (M : CStarMatrix ι ι ℂ) (x : WithCStarModule ℂ (ι → ℂ)) :
    withCStarComplexEuclideanEquiv ι (CStarMatrix.toCLM M x) =
      (EuclideanSpace.equiv ι ℂ).symm
        ((CStarMatrix.ofMatrix.symm M).transpose *ᵥ
          (withCStarComplexEuclideanEquiv ι x).ofLp) := by
  apply (EuclideanSpace.equiv ι ℂ).injective
  ext j
  change (∑ i, x i * M i j) = ∑ i, M i j * x i
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem hsNorm_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    hsNorm M.transpose = hsNorm M := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hsNorm_sq, hsNorm_sq]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- C*-matrix operator norm is dominated by Hilbert--Schmidt entry norm. -/
theorem cstarMatrix_norm_le_hsNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι ℂ) :
    ‖M‖ ≤ hsNorm (CStarMatrix.ofMatrix.symm M) := by
  rw [CStarMatrix.norm_def]
  apply (CStarMatrix.toCLM M).opNorm_le_bound (hsNorm_nonneg _)
  intro x
  have h := Matrix.l2_opNorm_mulVec
    (CStarMatrix.ofMatrix.symm M).transpose
    (withCStarComplexEuclideanEquiv ι x)
  rw [← withCStarComplexEuclideanEquiv_toCLM M x,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  exact h.trans (by
    gcongr
    exact (l2_opNorm_le_hsNorm _).trans_eq (hsNorm_transpose _))

/-- Real and imaginary entry-coordinate index for a finite complex matrix. -/
abbrev MatrixRealCoordinateIndex (ι : Type*) := (ι × ι) × Bool

/-- Complete real entry coordinates of a finite complex matrix. -/
def matrixRealCoordinates
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) : EuclideanSpace ℝ (MatrixRealCoordinateIndex ι) :=
  (EuclideanSpace.equiv (MatrixRealCoordinateIndex ι) ℝ).symm fun p =>
    if p.2 then (M p.1.1 p.1.2).im else (M p.1.1 p.1.2).re

@[simp] theorem matrixRealCoordinates_apply
    {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ)
    (p : MatrixRealCoordinateIndex ι) :
    (matrixRealCoordinates M).ofLp p =
      if p.2 then (M p.1.1 p.1.2).im else (M p.1.1 p.1.2).re := rfl

/-- Complete real entry coordinates are isometric for Hilbert--Schmidt norm. -/
theorem norm_matrixRealCoordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ‖matrixRealCoordinates M‖ = hsNorm M := by
  refine (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg M)).mp ?_
  change ‖matrixRealCoordinates M‖ ^ 2 = ‖matVec M‖ ^ 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc
    ∑ p : MatrixRealCoordinateIndex ι,
        ‖(matrixRealCoordinates M).ofLp p‖ ^ 2 =
        ∑ ij : ι × ι, ((M ij.1 ij.2).re ^ 2 + (M ij.1 ij.2).im ^ 2) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Fintype.sum_bool]
      simp [Real.norm_eq_abs, sq_abs, add_comm]
    _ = ∑ ij : ι × ι, ‖M ij.1 ij.2‖ ^ 2 := by
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    _ = ∑ p : ι × ι,
        ‖((EuclideanSpace.equiv (ι × ι) ℂ).symm
          (fun p => M p.1 p.2)).ofLp p‖ ^ 2 := by rfl

/-- Both time slices flattened into one Euclidean real coordinate vector. -/
def twoTimeCStarMatrixRealCoordinates
    {ι : Type*} [Fintype ι]
    (p : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) :
    EuclideanSpace ℝ (Bool × MatrixRealCoordinateIndex ι) :=
  (EuclideanSpace.equiv (Bool × MatrixRealCoordinateIndex ι) ℝ).symm fun q =>
    if q.1 then
      (matrixRealCoordinates (CStarMatrix.ofMatrix.symm p.2)).ofLp q.2
    else
      (matrixRealCoordinates (CStarMatrix.ofMatrix.symm p.1)).ofLp q.2

theorem norm_twoTimeCStarMatrixRealCoordinates_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : CStarMatrix ι ι ℂ) :
    ‖twoTimeCStarMatrixRealCoordinates (M, N)‖ ^ 2 =
      hsNorm (CStarMatrix.ofMatrix.symm M) ^ 2 +
        hsNorm (CStarMatrix.ofMatrix.symm N) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ q : Bool × MatrixRealCoordinateIndex ι,
    ‖if q.1 then
      (matrixRealCoordinates (CStarMatrix.ofMatrix.symm N)).ofLp q.2
    else
      (matrixRealCoordinates (CStarMatrix.ofMatrix.symm M)).ofLp q.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  change
    (∑ q : MatrixRealCoordinateIndex ι,
        ‖(matrixRealCoordinates (CStarMatrix.ofMatrix.symm N)).ofLp q‖ ^ 2) +
      (∑ q : MatrixRealCoordinateIndex ι,
        ‖(matrixRealCoordinates (CStarMatrix.ofMatrix.symm M)).ofLp q‖ ^ 2) = _
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
    norm_matrixRealCoordinates, norm_matrixRealCoordinates]
  ring

/-- Real-linear paired entry-coordinate map. -/
def twoTimeCStarMatrixRealCoordinatesLinear
    (ι : Type*) [Fintype ι] :
    (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →ₗ[ℝ]
      EuclideanSpace ℝ (Bool × MatrixRealCoordinateIndex ι) where
  toFun := twoTimeCStarMatrixRealCoordinates
  map_add' := by
    intro M N
    apply (EuclideanSpace.equiv (Bool × MatrixRealCoordinateIndex ι) ℝ).injective
    ext q
    rcases q with ⟨b, ⟨ij, c⟩⟩
    cases b <;> cases c <;>
      simp [twoTimeCStarMatrixRealCoordinates, matrixRealCoordinates]
  map_smul' := by
    intro r M
    apply (EuclideanSpace.equiv (Bool × MatrixRealCoordinateIndex ι) ℝ).injective
    ext q
    rcases q with ⟨b, ⟨ij, c⟩⟩
    cases b <;> cases c <;>
      simp [twoTimeCStarMatrixRealCoordinates, matrixRealCoordinates, smul_eq_mul]

/-- Continuous paired entry-coordinate map. -/
def twoTimeCStarMatrixRealCoordinatesCLM
    (ι : Type*) [Fintype ι] :
    (CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) →L[ℝ]
      EuclideanSpace ℝ (Bool × MatrixRealCoordinateIndex ι) :=
  LinearMap.toContinuousLinearMap (twoTimeCStarMatrixRealCoordinatesLinear ι)

@[simp] theorem twoTimeCStarMatrixRealCoordinatesCLM_apply
    {ι : Type*} [Fintype ι]
    (p : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) :
    twoTimeCStarMatrixRealCoordinatesCLM ι p =
      twoTimeCStarMatrixRealCoordinates p := rfl

/-- Euclidean paired entry coordinates dominate the product C*-operator norm. -/
theorem norm_le_twoTimeCStarMatrixRealCoordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : CStarMatrix ι ι ℂ × CStarMatrix ι ι ℂ) :
    ‖p‖ ≤ ‖twoTimeCStarMatrixRealCoordinates p‖ := by
  rw [Prod.norm_def]
  apply max_le
  · refine (cstarMatrix_norm_le_hsNorm p.1).trans ?_
    apply (sq_le_sq₀ (hsNorm_nonneg _) (norm_nonneg _)).mp
    rw [norm_twoTimeCStarMatrixRealCoordinates_sq]
    nlinarith [sq_nonneg (hsNorm (CStarMatrix.ofMatrix.symm p.2))]
  · refine (cstarMatrix_norm_le_hsNorm p.2).trans ?_
    apply (sq_le_sq₀ (hsNorm_nonneg _) (norm_nonneg _)).mp
    rw [norm_twoTimeCStarMatrixRealCoordinates_sq]
    nlinarith [sq_nonneg (hsNorm (CStarMatrix.ofMatrix.symm p.1))]

end

end GaloisForLFunctions.HTGeometry
