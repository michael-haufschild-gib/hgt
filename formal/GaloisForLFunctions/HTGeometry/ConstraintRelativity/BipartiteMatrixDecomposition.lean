import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Bipartite matrix decomposition

Partial traces and Hilbert--Schmidt identities needed for finite bipartite observer/cross-fibre
decompositions.  Definitions use matrix coordinates and work for arbitrary finite factor indices.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix
open scoped BigOperators Kronecker

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Partial trace over the right tensor factor. -/
def partialTraceRight (X : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k : n, X (i, k) (j, k)

/-- Partial trace over the left tensor factor. -/
def partialTraceLeft (X : Matrix (m × n) (m × n) ℂ) : Matrix n n ℂ :=
  fun i j => ∑ k : m, X (k, i) (k, j)

@[simp] theorem partialTraceRight_zero :
    partialTraceRight (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext i j
  simp [partialTraceRight]

@[simp] theorem partialTraceLeft_zero :
    partialTraceLeft (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext i j
  simp [partialTraceLeft]

@[simp] theorem partialTraceRight_add (X Y : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (X + Y) = partialTraceRight X + partialTraceRight Y := by
  ext i j
  simp [partialTraceRight, Finset.sum_add_distrib]

@[simp] theorem partialTraceLeft_add (X Y : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (X + Y) = partialTraceLeft X + partialTraceLeft Y := by
  ext i j
  simp [partialTraceLeft, Finset.sum_add_distrib]

@[simp] theorem partialTraceRight_sub (X Y : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (X - Y) = partialTraceRight X - partialTraceRight Y := by
  ext i j
  simp [partialTraceRight, ← Finset.sum_sub_distrib]

@[simp] theorem partialTraceLeft_sub (X Y : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (X - Y) = partialTraceLeft X - partialTraceLeft Y := by
  ext i j
  simp [partialTraceLeft, ← Finset.sum_sub_distrib]

@[simp] theorem partialTraceRight_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (c • X) = c • partialTraceRight X := by
  ext i j
  simp [partialTraceRight, Finset.mul_sum]

@[simp] theorem partialTraceLeft_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (c • X) = c • partialTraceLeft X := by
  ext i j
  simp [partialTraceLeft, Finset.mul_sum]

/-- Partial trace of a Kronecker product over the right factor. -/
theorem partialTraceRight_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    partialTraceRight (A ⊗ₖ B) = B.trace • A := by
  ext i j
  simp [partialTraceRight, Matrix.kroneckerMap_apply, Matrix.trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Partial trace of a Kronecker product over the left factor. -/
theorem partialTraceLeft_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    partialTraceLeft (A ⊗ₖ B) = A.trace • B := by
  ext i j
  simp [partialTraceLeft, Matrix.kroneckerMap_apply, Matrix.trace, Finset.sum_mul]

theorem trace_partialTraceRight (X : Matrix (m × n) (m × n) ℂ) :
    (partialTraceRight X).trace = X.trace := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

theorem trace_partialTraceLeft (X : Matrix (m × n) (m × n) ℂ) :
    (partialTraceLeft X).trace = X.trace := by
  simp [partialTraceLeft, Matrix.trace, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Partial trace over the right factor as a complex-linear map. -/
def partialTraceRightLinear :
    Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' := partialTraceRight_smul

/-- Partial trace over the left factor as a complex-linear map. -/
def partialTraceLeftLinear :
    Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' := partialTraceLeft_smul

/-- Matrices invisible to both boundary partial traces. -/
def matrixCrossFibre : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  LinearMap.ker (partialTraceRightLinear (m := m) (n := n)) ⊓
    LinearMap.ker (partialTraceLeftLinear (m := m) (n := n))

theorem mem_matrixCrossFibre {X : Matrix (m × n) (m × n) ℂ} :
    X ∈ matrixCrossFibre (m := m) (n := n) ↔
      partialTraceRight X = 0 ∧ partialTraceLeft X = 0 := by
  rfl

/-- Traceless matrices on one factor. -/
def tracelessMatrices (m : Type*) [Fintype m] [DecidableEq m] :
    Submodule ℂ (Matrix m m ℂ) := LinearMap.ker (Matrix.traceLinearMap m ℂ ℂ)

theorem mem_tracelessMatrices {A : Matrix m m ℂ} :
    A ∈ tracelessMatrices m ↔ A.trace = 0 := by
  rfl

/-- Every Kronecker product of traceless factor matrices lies in the cross fibre. -/
theorem kronecker_mem_matrixCrossFibre
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A ∈ tracelessMatrices m) (hB : B ∈ tracelessMatrices n) :
    A ⊗ₖ B ∈ matrixCrossFibre (m := m) (n := n) := by
  rw [mem_matrixCrossFibre, partialTraceRight_kronecker, partialTraceLeft_kronecker]
  simp [mem_tracelessMatrices.mp hA, mem_tracelessMatrices.mp hB]

/-- The span of traceless pure tensors. -/
def tracelessKroneckerSpan : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  Submodule.map₂
    (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (l := m) (m := m) (n := n) (p := n))
    (tracelessMatrices m) (tracelessMatrices n)

theorem tracelessKroneckerSpan_le_matrixCrossFibre :
    tracelessKroneckerSpan (m := m) (n := n) ≤ matrixCrossFibre := by
  rw [tracelessKroneckerSpan, Submodule.map₂_le]
  intro A hA B hB
  exact kronecker_mem_matrixCrossFibre hA hB

section Decomposition

variable [Nonempty m] [Nonempty n]

/-- Remove the scalar trace component of a square matrix. -/
noncomputable def traceCenter (A : Matrix m m ℂ) : Matrix m m ℂ :=
  A - (((Fintype.card m : ℂ)⁻¹ * A.trace) • (1 : Matrix m m ℂ))

theorem trace_traceCenter (A : Matrix m m ℂ) : (traceCenter A).trace = 0 := by
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [traceCenter, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  field_simp
  ring

/-- Scalar coefficient in the bipartite trace decomposition. -/
noncomputable def bipartiteScalarCoeff (X : Matrix (m × n) (m × n) ℂ) : ℂ :=
  X.trace / ((Fintype.card m : ℂ) * (Fintype.card n : ℂ))

/-- Traceless left factor extracted by the normalized right partial trace. -/
noncomputable def leftReducedComponent (X : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  traceCenter (((Fintype.card n : ℂ)⁻¹) • partialTraceRight X)

/-- Traceless right factor extracted by the normalized left partial trace. -/
noncomputable def rightReducedComponent (X : Matrix (m × n) (m × n) ℂ) : Matrix n n ℂ :=
  traceCenter (((Fintype.card m : ℂ)⁻¹) • partialTraceLeft X)

theorem leftReducedComponent_trace (X : Matrix (m × n) (m × n) ℂ) :
    (leftReducedComponent X).trace = 0 := trace_traceCenter _

theorem rightReducedComponent_trace (X : Matrix (m × n) (m × n) ℂ) :
    (rightReducedComponent X).trace = 0 := trace_traceCenter _

/-- Left-local summand `H_A ⊗ I`. -/
noncomputable def leftLocalPart (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  leftReducedComponent X ⊗ₖ (1 : Matrix n n ℂ)

/-- Right-local summand `I ⊗ H_B`. -/
noncomputable def rightLocalPart (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  (1 : Matrix m m ℂ) ⊗ₖ rightReducedComponent X

/-- Scalar summand `cI`. -/
noncomputable def scalarMatrixPart (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  bipartiteScalarCoeff X • ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ))

/-- Cross component after removing left-local, right-local, and scalar parts. -/
noncomputable def crossMatrixPart (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  X - leftLocalPart X - rightLocalPart X - scalarMatrixPart X

/-- Exact four-sector decomposition. -/
theorem bipartite_decomposition (X : Matrix (m × n) (m × n) ℂ) :
    X = leftLocalPart X + rightLocalPart X + scalarMatrixPart X + crossMatrixPart X := by
  simp [crossMatrixPart]

theorem partialTraceRight_leftLocalPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (leftLocalPart X) =
      partialTraceRight X -
        (((Fintype.card m : ℂ)⁻¹ * X.trace) • (1 : Matrix m m ℂ)) := by
  have hn : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [leftLocalPart, partialTraceRight_kronecker, Matrix.trace_one]
  simp only [leftReducedComponent, traceCenter, smul_sub, smul_smul]
  rw [Matrix.trace_smul, trace_partialTraceRight, mul_inv_cancel₀ hn, one_smul]
  congr 1
  apply congrArg (fun c : ℂ => c • (1 : Matrix m m ℂ))
  calc
    (Fintype.card n : ℂ) * X.trace * (Fintype.card n : ℂ)⁻¹ =
        X.trace * ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)⁻¹) := by ring
    _ = X.trace := by rw [mul_inv_cancel₀ hn, mul_one]

theorem partialTraceRight_rightLocalPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (rightLocalPart X) = 0 := by
  rw [rightLocalPart, partialTraceRight_kronecker, rightReducedComponent_trace, zero_smul]

theorem partialTraceRight_scalarMatrixPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (scalarMatrixPart X) =
      (((Fintype.card m : ℂ)⁻¹ * X.trace) • (1 : Matrix m m ℂ)) := by
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [scalarMatrixPart, partialTraceRight_smul, partialTraceRight_kronecker,
    Matrix.trace_one, smul_smul]
  congr 1
  simp only [bipartiteScalarCoeff]
  field_simp

theorem partialTraceLeft_rightLocalPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (rightLocalPart X) =
      partialTraceLeft X -
        (((Fintype.card n : ℂ)⁻¹ * X.trace) • (1 : Matrix n n ℂ)) := by
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [rightLocalPart, partialTraceLeft_kronecker, Matrix.trace_one]
  simp only [rightReducedComponent, traceCenter, smul_sub, smul_smul]
  rw [Matrix.trace_smul, trace_partialTraceLeft, mul_inv_cancel₀ hm, one_smul]
  congr 1
  apply congrArg (fun c : ℂ => c • (1 : Matrix n n ℂ))
  calc
    (Fintype.card m : ℂ) * X.trace * (Fintype.card m : ℂ)⁻¹ =
        X.trace * ((Fintype.card m : ℂ) * (Fintype.card m : ℂ)⁻¹) := by ring
    _ = X.trace := by rw [mul_inv_cancel₀ hm, mul_one]

theorem partialTraceLeft_leftLocalPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (leftLocalPart X) = 0 := by
  rw [leftLocalPart, partialTraceLeft_kronecker, leftReducedComponent_trace, zero_smul]

theorem partialTraceLeft_scalarMatrixPart (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (scalarMatrixPart X) =
      (((Fintype.card n : ℂ)⁻¹ * X.trace) • (1 : Matrix n n ℂ)) := by
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [scalarMatrixPart, partialTraceLeft_smul, partialTraceLeft_kronecker,
    Matrix.trace_one, smul_smul]
  congr 1
  simp only [bipartiteScalarCoeff]
  field_simp

/-- The residual component is invisible to both partial traces. -/
theorem crossMatrixPart_mem (X : Matrix (m × n) (m × n) ℂ) :
    crossMatrixPart X ∈ matrixCrossFibre (m := m) (n := n) := by
  rw [mem_matrixCrossFibre]
  constructor
  · rw [crossMatrixPart, partialTraceRight_sub, partialTraceRight_sub, partialTraceRight_sub,
      partialTraceRight_leftLocalPart, partialTraceRight_rightLocalPart,
      partialTraceRight_scalarMatrixPart]
    abel
  · rw [crossMatrixPart, partialTraceLeft_sub, partialTraceLeft_sub, partialTraceLeft_sub,
      partialTraceLeft_leftLocalPart, partialTraceLeft_rightLocalPart,
      partialTraceLeft_scalarMatrixPart]
    abel

end Decomposition

end HTGeometry.ConstraintRelativity
