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

@[simp] theorem traceCenter_add (A B : Matrix m m ℂ) :
    traceCenter (A + B) = traceCenter A + traceCenter B := by
  simp only [traceCenter, Matrix.trace_add, mul_add, add_smul]
  abel

@[simp] theorem traceCenter_smul (c : ℂ) (A : Matrix m m ℂ) :
    traceCenter (c • A) = c • traceCenter A := by
  ext i j
  simp [traceCenter, Matrix.trace_smul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Scalar coefficient in the bipartite trace decomposition. -/
noncomputable def bipartiteScalarCoeff (X : Matrix (m × n) (m × n) ℂ) : ℂ :=
  X.trace / ((Fintype.card m : ℂ) * (Fintype.card n : ℂ))

@[simp] theorem bipartiteScalarCoeff_add (X Y : Matrix (m × n) (m × n) ℂ) :
    bipartiteScalarCoeff (X + Y) = bipartiteScalarCoeff X + bipartiteScalarCoeff Y := by
  simp [bipartiteScalarCoeff, Matrix.trace_add, add_div]

@[simp] theorem bipartiteScalarCoeff_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    bipartiteScalarCoeff (c • X) = c * bipartiteScalarCoeff X := by
  simp [bipartiteScalarCoeff, Matrix.trace_smul]
  ring

/-- Traceless left factor extracted by the normalized right partial trace. -/
noncomputable def leftReducedComponent (X : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  traceCenter (((Fintype.card n : ℂ)⁻¹) • partialTraceRight X)

/-- Traceless right factor extracted by the normalized left partial trace. -/
noncomputable def rightReducedComponent (X : Matrix (m × n) (m × n) ℂ) : Matrix n n ℂ :=
  traceCenter (((Fintype.card m : ℂ)⁻¹) • partialTraceLeft X)

@[simp] theorem leftReducedComponent_add (X Y : Matrix (m × n) (m × n) ℂ) :
    leftReducedComponent (X + Y) = leftReducedComponent X + leftReducedComponent Y := by
  simp [leftReducedComponent, smul_add]

@[simp] theorem rightReducedComponent_add (X Y : Matrix (m × n) (m × n) ℂ) :
    rightReducedComponent (X + Y) = rightReducedComponent X + rightReducedComponent Y := by
  simp [rightReducedComponent, smul_add]

@[simp] theorem leftReducedComponent_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    leftReducedComponent (c • X) = c • leftReducedComponent X := by
  simp [leftReducedComponent, smul_smul, mul_comm]

@[simp] theorem rightReducedComponent_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    rightReducedComponent (c • X) = c • rightReducedComponent X := by
  simp [rightReducedComponent, smul_smul, mul_comm]

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

@[simp] theorem leftLocalPart_add (X Y : Matrix (m × n) (m × n) ℂ) :
    leftLocalPart (X + Y) = leftLocalPart X + leftLocalPart Y := by
  simp [leftLocalPart, Matrix.add_kronecker]

@[simp] theorem rightLocalPart_add (X Y : Matrix (m × n) (m × n) ℂ) :
    rightLocalPart (X + Y) = rightLocalPart X + rightLocalPart Y := by
  simp [rightLocalPart, Matrix.kronecker_add]

@[simp] theorem scalarMatrixPart_add (X Y : Matrix (m × n) (m × n) ℂ) :
    scalarMatrixPart (X + Y) = scalarMatrixPart X + scalarMatrixPart Y := by
  simp [scalarMatrixPart, add_smul]

@[simp] theorem leftLocalPart_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    leftLocalPart (c • X) = c • leftLocalPart X := by
  simp [leftLocalPart, Matrix.smul_kronecker]

@[simp] theorem rightLocalPart_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    rightLocalPart (c • X) = c • rightLocalPart X := by
  simp [rightLocalPart, Matrix.kronecker_smul]

@[simp] theorem scalarMatrixPart_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    scalarMatrixPart (c • X) = c • scalarMatrixPart X := by
  simp [scalarMatrixPart, smul_smul]

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
  rw [smul_eq_mul]
  change (Fintype.card n : ℂ) *
      ((Fintype.card m : ℂ)⁻¹ * ((Fintype.card n : ℂ)⁻¹ * X.trace)) =
    (Fintype.card m : ℂ)⁻¹ * X.trace
  calc
    (Fintype.card n : ℂ) *
        ((Fintype.card m : ℂ)⁻¹ * ((Fintype.card n : ℂ)⁻¹ * X.trace)) =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)⁻¹) *
          ((Fintype.card m : ℂ)⁻¹ * X.trace) := by ring
    _ = (Fintype.card m : ℂ)⁻¹ * X.trace := by rw [mul_inv_cancel₀ hn, one_mul]

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
  rw [smul_eq_mul]
  change (Fintype.card m : ℂ) *
      ((Fintype.card n : ℂ)⁻¹ * ((Fintype.card m : ℂ)⁻¹ * X.trace)) =
    (Fintype.card n : ℂ)⁻¹ * X.trace
  calc
    (Fintype.card m : ℂ) *
        ((Fintype.card n : ℂ)⁻¹ * ((Fintype.card m : ℂ)⁻¹ * X.trace)) =
        ((Fintype.card m : ℂ) * (Fintype.card m : ℂ)⁻¹) *
          ((Fintype.card n : ℂ)⁻¹ * X.trace) := by ring
    _ = (Fintype.card n : ℂ)⁻¹ * X.trace := by rw [mul_inv_cancel₀ hm, one_mul]

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

@[simp] theorem crossMatrixPart_zero :
    crossMatrixPart (0 : Matrix (m × n) (m × n) ℂ) = 0 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [crossMatrixPart, leftLocalPart, rightLocalPart, scalarMatrixPart,
    leftReducedComponent, rightReducedComponent, bipartiteScalarCoeff, traceCenter,
    partialTraceRight, partialTraceLeft, Matrix.kroneckerMap_apply]

@[simp] theorem crossMatrixPart_add (X Y : Matrix (m × n) (m × n) ℂ) :
    crossMatrixPart (X + Y) = crossMatrixPart X + crossMatrixPart Y := by
  simp only [crossMatrixPart, leftLocalPart_add, rightLocalPart_add,
    scalarMatrixPart_add]
  abel

@[simp] theorem crossMatrixPart_smul (c : ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    crossMatrixPart (c • X) = c • crossMatrixPart X := by
  simp only [crossMatrixPart, leftLocalPart_smul, rightLocalPart_smul,
    scalarMatrixPart_smul, smul_sub]

/-- Projection onto the component invisible to both partial traces. -/
noncomputable def crossMatrixPartLinear :
    Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun := crossMatrixPart
  map_add' := crossMatrixPart_add
  map_smul' := crossMatrixPart_smul

/-- On a pure tensor, the cross projection removes the scalar trace component of each factor. -/
theorem crossMatrixPart_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    crossMatrixPart (A ⊗ₖ B) = traceCenter A ⊗ₖ traceCenter B := by
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [crossMatrixPart, leftLocalPart, rightLocalPart, scalarMatrixPart,
    leftReducedComponent, rightReducedComponent, bipartiteScalarCoeff, traceCenter,
    partialTraceRight_kronecker, partialTraceLeft_kronecker, Matrix.trace_kronecker,
    Matrix.trace_smul, Matrix.trace_one, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  field_simp
  ring

/-- Standard matrix units on a product index are Kronecker products of factor matrix units. -/
theorem single_kronecker_single (i k : m) (j l : n) :
    (Matrix.single i k (1 : ℂ)) ⊗ₖ (Matrix.single j l (1 : ℂ)) =
      Matrix.single (i, j) (k, l) (1 : ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Kronecker products span the full matrix algebra on a product index. -/
theorem map₂_kroneckerBilinear_top_top :
    Submodule.map₂
        (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (l := m) (m := m) (n := n) (p := n))
        ⊤ ⊤ = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← (Matrix.stdBasis ℂ (m × n) (m × n)).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro X ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single, ← single_kronecker_single]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top Submodule.mem_top

/-- Every cross projection is a linear combination of traceless pure tensors. -/
theorem crossMatrixPart_mem_tracelessKroneckerSpan
    (X : Matrix (m × n) (m × n) ℂ) :
    crossMatrixPart X ∈ tracelessKroneckerSpan (m := m) (n := n) := by
  let P : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
    (tracelessKroneckerSpan (m := m) (n := n)).comap crossMatrixPartLinear
  have htop : (⊤ : Submodule ℂ (Matrix (m × n) (m × n) ℂ)) ≤ P := by
    rw [← map₂_kroneckerBilinear_top_top]
    rw [Submodule.map₂_le]
    intro A _ B _
    change crossMatrixPart (A ⊗ₖ B) ∈ tracelessKroneckerSpan
    rw [crossMatrixPart_kronecker]
    exact Submodule.apply_mem_map₂ _
      (trace_traceCenter A) (trace_traceCenter B)
  exact htop Submodule.mem_top

/-- **Card Theorem 5.1, complexified form.** The joint kernel of both partial traces is exactly
the span of pure tensors with traceless factors. -/
theorem matrixCrossFibre_eq_tracelessKroneckerSpan :
    matrixCrossFibre (m := m) (n := n) = tracelessKroneckerSpan := by
  apply le_antisymm
  · intro X hX
    rw [mem_matrixCrossFibre] at hX
    have htrace : X.trace = 0 := by
      rw [← trace_partialTraceRight X, hX.1, Matrix.trace_zero]
    have hleft : leftLocalPart X = 0 := by
      rw [leftLocalPart]
      congr 1
      simp [leftReducedComponent, traceCenter, hX.1]
    have hright : rightLocalPart X = 0 := by
      rw [rightLocalPart]
      congr 1
      simp [rightReducedComponent, traceCenter, hX.2]
    have hscalar : scalarMatrixPart X = 0 := by
      simp [scalarMatrixPart, bipartiteScalarCoeff, htrace]
    have hcross : crossMatrixPart X = X := by
      simp [crossMatrixPart, hleft, hright, hscalar]
    rw [← hcross]
    exact crossMatrixPart_mem_tracelessKroneckerSpan X
  · exact tracelessKroneckerSpan_le_matrixCrossFibre

/-! ## Local reporters and first-order locality -/

/-- Embed a left-factor matrix as `A ⊗ I`. -/
def leftMatrixEmbedding :
    Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_add' A B := by simp [Matrix.add_kronecker]
  map_smul' c A := by simp [Matrix.smul_kronecker]

/-- Embed a right-factor matrix as `I ⊗ B`. -/
def rightMatrixEmbedding :
    Matrix n n ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun B := (1 : Matrix m m ℂ) ⊗ₖ B
  map_add' A B := by simp [Matrix.kronecker_add]
  map_smul' c A := by simp [Matrix.kronecker_smul]

/-- Complexification of the traceless Hermitian local reporter sector. -/
def matrixLocalReporter : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  (tracelessMatrices m).map (leftMatrixEmbedding (m := m) (n := n)) ⊔
    (tracelessMatrices n).map (rightMatrixEmbedding (m := m) (n := n))

theorem mem_matrixLocalReporter_iff {X : Matrix (m × n) (m × n) ℂ} :
    X ∈ matrixLocalReporter (m := m) (n := n) ↔
      ∃ A : Matrix m m ℂ, A.trace = 0 ∧
        ∃ B : Matrix n n ℂ, B.trace = 0 ∧
          X = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B := by
  rw [matrixLocalReporter, Submodule.mem_sup]
  constructor
  · rintro ⟨XL, ⟨A, hA, rfl⟩, XR, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨A, hA, B, hB, rfl⟩
  · rintro ⟨A, hA, B, hB, rfl⟩
    exact ⟨A ⊗ₖ (1 : Matrix n n ℂ), ⟨A, hA, rfl⟩,
      (1 : Matrix m m ℂ) ⊗ₖ B, ⟨B, hB, rfl⟩, rfl⟩

/-- Local reporters and the cross fibre meet only at zero. -/
theorem matrixLocalReporter_inf_matrixCrossFibre_eq_bot :
    matrixLocalReporter (m := m) (n := n) ⊓ matrixCrossFibre = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  rw [Submodule.mem_inf, mem_matrixLocalReporter_iff, mem_matrixCrossFibre] at hX
  obtain ⟨⟨A, hA, B, hB, rfl⟩, hR, hL⟩ := hX
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hAzero : A = 0 := by
    rw [partialTraceRight_add, partialTraceRight_kronecker, partialTraceRight_kronecker,
      Matrix.trace_one, hB, zero_smul, add_zero] at hR
    exact (smul_eq_zero.mp hR).resolve_left hn
  have hBzero : B = 0 := by
    rw [partialTraceLeft_add, partialTraceLeft_kronecker, partialTraceLeft_kronecker,
      hA, Matrix.trace_one, zero_smul, zero_add] at hL
    exact (smul_eq_zero.mp hL).resolve_left hm
  simp [hAzero, hBzero]

/-- Matrix commutator, without the harmless scalar factor `i`. -/
def matrixCommutator (H X : Matrix (m × n) (m × n) ℂ) := H * X - X * H

theorem mul_leftLocal_apply
    (X : Matrix (m × n) (m × n) ℂ) (A : Matrix m m ℂ)
    (i j : m) (k l : n) :
    (X * (A ⊗ₖ (1 : Matrix n n ℂ))) (i, k) (j, l) =
      ∑ p : m, X (i, k) (p, l) * A p j := by
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

theorem leftLocal_mul_apply
    (A : Matrix m m ℂ) (X : Matrix (m × n) (m × n) ℂ)
    (i j : m) (k l : n) :
    ((A ⊗ₖ (1 : Matrix n n ℂ)) * X) (i, k) (j, l) =
      ∑ p : m, A i p * X (p, k) (j, l) := by
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

theorem partialTraceRight_mul_leftLocal
    (X : Matrix (m × n) (m × n) ℂ) (A : Matrix m m ℂ) :
    partialTraceRight (X * (A ⊗ₖ (1 : Matrix n n ℂ))) = partialTraceRight X * A := by
  ext i j
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_mul]
  simp
  rw [Finset.sum_comm]

theorem partialTraceRight_leftLocal_mul
    (A : Matrix m m ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix n n ℂ)) * X) = A * partialTraceRight X := by
  ext i j
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.mul_sum]
  simp
  rw [Finset.sum_comm]

theorem partialTraceLeft_commutator_leftLocal
    (X : Matrix (m × n) (m × n) ℂ) (A : Matrix m m ℂ) :
    partialTraceLeft (matrixCommutator X (A ⊗ₖ (1 : Matrix n n ℂ))) = 0 := by
  ext k l
  simp only [matrixCommutator, Matrix.sub_apply, Matrix.zero_apply, partialTraceLeft,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- A cross operator commuted with a left reporter remains in the cross fibre. -/
theorem matrixCommutator_leftLocal_mem_cross
    {X : Matrix (m × n) (m × n) ℂ} (hX : X ∈ matrixCrossFibre)
    (A : Matrix m m ℂ) :
    matrixCommutator X (A ⊗ₖ (1 : Matrix n n ℂ)) ∈ matrixCrossFibre := by
  rw [mem_matrixCrossFibre] at hX ⊢
  constructor
  · rw [matrixCommutator, partialTraceRight_sub, partialTraceRight_mul_leftLocal,
      partialTraceRight_leftLocal_mul, hX.1]
    simp
  · exact partialTraceLeft_commutator_leftLocal X A

theorem partialTraceLeft_mul_rightLocal
    (X : Matrix (m × n) (m × n) ℂ) (B : Matrix n n ℂ) :
    partialTraceLeft (X * ((1 : Matrix m m ℂ) ⊗ₖ B)) = partialTraceLeft X * B := by
  ext i j
  simp only [partialTraceLeft, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_mul]
  simp
  rw [Finset.sum_comm]

theorem partialTraceLeft_rightLocal_mul
    (B : Matrix n n ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft (((1 : Matrix m m ℂ) ⊗ₖ B) * X) = B * partialTraceLeft X := by
  ext i j
  simp only [partialTraceLeft, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.mul_sum]
  simp
  rw [Finset.sum_comm]

theorem partialTraceRight_commutator_rightLocal
    (X : Matrix (m × n) (m × n) ℂ) (B : Matrix n n ℂ) :
    partialTraceRight (matrixCommutator X ((1 : Matrix m m ℂ) ⊗ₖ B)) = 0 := by
  ext k l
  simp only [matrixCommutator, Matrix.sub_apply, Matrix.zero_apply, partialTraceRight,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel]
  simp
  rw [sub_eq_zero]
  conv_lhs => rw [Finset.sum_comm]
  simp [mul_comm]

/-- A cross operator commuted with a right reporter remains in the cross fibre. -/
theorem matrixCommutator_rightLocal_mem_cross
    {X : Matrix (m × n) (m × n) ℂ} (hX : X ∈ matrixCrossFibre)
    (B : Matrix n n ℂ) :
    matrixCommutator X ((1 : Matrix m m ℂ) ⊗ₖ B) ∈ matrixCrossFibre := by
  rw [mem_matrixCrossFibre] at hX ⊢
  constructor
  · exact partialTraceRight_commutator_rightLocal X B
  · rw [matrixCommutator, partialTraceLeft_sub, partialTraceLeft_mul_rightLocal,
      partialTraceLeft_rightLocal_mul, hX.2]
    simp

/-- Commutators of local reporters remain local. -/
theorem matrixCommutator_local_mem
    {H L : Matrix (m × n) (m × n) ℂ}
    (hH : H ∈ matrixLocalReporter) (hL : L ∈ matrixLocalReporter) :
    matrixCommutator H L ∈ matrixLocalReporter := by
  rw [mem_matrixLocalReporter_iff] at hH hL ⊢
  obtain ⟨A, hA, B, hB, rfl⟩ := hH
  obtain ⟨C, hC, D, hD, rfl⟩ := hL
  refine ⟨A * C - C * A, ?_, B * D - D * B, ?_, ?_⟩
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    simp
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    simp
  · ext ⟨i, k⟩ ⟨j, l⟩
    simp only [matrixCommutator, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply]
    ring

/-- Commuting with every left-factor matrix forces block-scalar form `I ⊗ B`. -/
theorem eq_one_kronecker_of_commutes_left
    (X : Matrix (m × n) (m × n) ℂ)
    (hX : ∀ A : Matrix m m ℂ,
      X * (A ⊗ₖ (1 : Matrix n n ℂ)) = (A ⊗ₖ (1 : Matrix n n ℂ)) * X) :
    ∃ B : Matrix n n ℂ, X = (1 : Matrix m m ℂ) ⊗ₖ B := by
  classical
  let i₀ : m := Classical.choice (inferInstance : Nonempty m)
  let B : Matrix n n ℂ := fun k l => X (i₀, k) (i₀, l)
  refine ⟨B, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    have h := congrFun (congrFun (hX (Matrix.single i i₀ 1)) (i, k)) (i₀, l)
    rw [mul_leftLocal_apply, leftLocal_mul_apply] at h
    simpa [Matrix.single, B] using h
  · have h := congrFun (congrFun (hX (Matrix.single i i 1)) (i, k)) (j, l)
    rw [mul_leftLocal_apply, leftLocal_mul_apply] at h
    have hzero : X (i, k) (j, l) = 0 := by
      simpa [Matrix.single, hij] using h.symm
    simp [Matrix.kroneckerMap_apply, hij, hzero]

/-- A cross operator commuting with every left-factor matrix vanishes. -/
theorem eq_zero_of_mem_cross_of_commutes_left
    {X : Matrix (m × n) (m × n) ℂ} (hmem : X ∈ matrixCrossFibre)
    (hX : ∀ A : Matrix m m ℂ,
      X * (A ⊗ₖ (1 : Matrix n n ℂ)) = (A ⊗ₖ (1 : Matrix n n ℂ)) * X) :
    X = 0 := by
  obtain ⟨B, rfl⟩ := eq_one_kronecker_of_commutes_left X hX
  rw [mem_matrixCrossFibre] at hmem
  have hm : (Fintype.card m : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [partialTraceLeft_kronecker, Matrix.trace_one] at hmem
  have hB : B = 0 := (smul_eq_zero.mp hmem.2).resolve_left hm
  simp [hB]

@[simp] theorem matrixCommutator_sub_left
    (X Y Z : Matrix (m × n) (m × n) ℂ) :
    matrixCommutator (X - Y) Z = matrixCommutator X Z - matrixCommutator Y Z := by
  simp only [matrixCommutator, Matrix.sub_mul, Matrix.mul_sub]
  abel

@[simp] theorem matrixCommutator_add_left
    (X Y Z : Matrix (m × n) (m × n) ℂ) :
    matrixCommutator (X + Y) Z = matrixCommutator X Z + matrixCommutator Y Z := by
  simp only [matrixCommutator, Matrix.add_mul, Matrix.mul_add]
  abel

theorem one_kronecker_one :
    (1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ) = 1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rcases eq_or_ne i j with rfl | hi
  · rcases eq_or_ne k l with rfl | hk
    · simp [Matrix.kroneckerMap_apply]
    · simp [Matrix.kroneckerMap_apply, hk]
  · simp [Matrix.kroneckerMap_apply, hi]

@[simp] theorem matrixCommutator_scalarMatrixPart
    (X L : Matrix (m × n) (m × n) ℂ) :
    matrixCommutator (scalarMatrixPart X) L = 0 := by
  rw [scalarMatrixPart, one_kronecker_one]
  simp [matrixCommutator, Matrix.smul_mul, Matrix.mul_smul]

/-- Any local-plus-scalar Hamiltonian preserves the local reporter sector. -/
theorem matrixCommutator_localForm_mem
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (c : ℂ)
    {L : Matrix (m × n) (m × n) ℂ} (hL : L ∈ matrixLocalReporter) :
    matrixCommutator
        (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B +
          c • ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ))) L ∈
      matrixLocalReporter := by
  rw [mem_matrixLocalReporter_iff] at hL ⊢
  obtain ⟨C, hC, D, hD, rfl⟩ := hL
  refine ⟨A * C - C * A, ?_, B * D - D * B, ?_, ?_⟩
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    simp
  · rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    simp
  · ext ⟨i, k⟩ ⟨j, l⟩
    simp only [matrixCommutator, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.kroneckerMap_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring

/-- The cross projection vanishes exactly when every local reporter remains local to first order.
This is the complexified algebraic core of Card Theorem 5.2. -/
theorem crossMatrixPart_eq_zero_iff_preserves_local
    (H : Matrix (m × n) (m × n) ℂ) :
    crossMatrixPart H = 0 ↔
      ∀ L : Matrix (m × n) (m × n) ℂ,
        L ∈ matrixLocalReporter → matrixCommutator H L ∈ matrixLocalReporter := by
  constructor
  · intro hcross L hL
    have hdecomp := bipartite_decomposition H
    rw [hcross, add_zero] at hdecomp
    rw [hdecomp]
    exact matrixCommutator_localForm_mem
      (leftReducedComponent H) (rightReducedComponent H) (bipartiteScalarCoeff H) hL
  · intro hpres
    let Hlocal := leftLocalPart H + rightLocalPart H
    have hHlocal : Hlocal ∈ matrixLocalReporter (m := m) (n := n) := by
      rw [mem_matrixLocalReporter_iff]
      exact ⟨leftReducedComponent H, leftReducedComponent_trace H,
        rightReducedComponent H, rightReducedComponent_trace H, rfl⟩
    have hcrossmem := crossMatrixPart_mem H
    have hcommTraceCenter : ∀ A : Matrix m m ℂ,
        matrixCommutator (crossMatrixPart H)
            (traceCenter A ⊗ₖ (1 : Matrix n n ℂ)) = 0 := by
      intro A
      let L := traceCenter A ⊗ₖ (1 : Matrix n n ℂ)
      have hL : L ∈ matrixLocalReporter (m := m) (n := n) := by
        rw [mem_matrixLocalReporter_iff]
        exact ⟨traceCenter A, trace_traceCenter A, 0, by simp, by simp [L]⟩
      have hHL := hpres L hL
      have hlocalL := matrixCommutator_local_mem hHlocal hL
      have hcrossLocal : matrixCommutator (crossMatrixPart H) L ∈ matrixLocalReporter := by
        have heq : matrixCommutator (crossMatrixPart H) L =
            matrixCommutator H L - matrixCommutator Hlocal L := by
          rw [show crossMatrixPart H = (H - Hlocal) - scalarMatrixPart H by
            simp only [crossMatrixPart, Hlocal]
            abel]
          simp
        rw [heq]
        exact (matrixLocalReporter (m := m) (n := n)).sub_mem hHL hlocalL
      have hcrossCross : matrixCommutator (crossMatrixPart H) L ∈ matrixCrossFibre :=
        matrixCommutator_leftLocal_mem_cross hcrossmem (traceCenter A)
      have hinf : matrixCommutator (crossMatrixPart H) L ∈
          matrixLocalReporter (m := m) (n := n) ⊓ matrixCrossFibre :=
        ⟨hcrossLocal, hcrossCross⟩
      rw [matrixLocalReporter_inf_matrixCrossFibre_eq_bot] at hinf
      simpa using hinf
    have hcommAll : ∀ A : Matrix m m ℂ,
        crossMatrixPart H * (A ⊗ₖ (1 : Matrix n n ℂ)) =
          (A ⊗ₖ (1 : Matrix n n ℂ)) * crossMatrixPart H := by
      intro A
      have hsplit : A = traceCenter A +
          (((Fintype.card m : ℂ)⁻¹ * A.trace) • (1 : Matrix m m ℂ)) := by
        simp [traceCenter]
      have hcenter := hcommTraceCenter A
      rw [matrixCommutator] at hcenter
      rw [hsplit, Matrix.add_kronecker, Matrix.smul_kronecker,
        one_kronecker_one]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul]
      rw [sub_eq_zero] at hcenter
      rw [hcenter]
    exact eq_zero_of_mem_cross_of_commutes_left hcrossmem hcommAll

/-- **Card Theorem 5.2.** First-order preservation of all local reporters is equivalent to a
local-plus-scalar Hamiltonian. -/
theorem preserves_matrixLocalReporter_iff_localForm
    (H : Matrix (m × n) (m × n) ℂ) :
    (∀ L : Matrix (m × n) (m × n) ℂ,
        L ∈ matrixLocalReporter → matrixCommutator H L ∈ matrixLocalReporter) ↔
      ∃ A : Matrix m m ℂ, ∃ B : Matrix n n ℂ, ∃ c : ℂ,
        H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B +
          c • ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)) := by
  rw [← crossMatrixPart_eq_zero_iff_preserves_local]
  constructor
  · intro hcross
    refine ⟨leftReducedComponent H, rightReducedComponent H, bipartiteScalarCoeff H, ?_⟩
    simpa [leftLocalPart, rightLocalPart, scalarMatrixPart, hcross] using
      bipartite_decomposition H
  · rintro ⟨A, B, c, rfl⟩
    apply (crossMatrixPart_eq_zero_iff_preserves_local _).2
    intro L hL
    exact matrixCommutator_localForm_mem A B c hL

/-- The cross projection vanishes on every local reporter. -/
theorem crossMatrixPart_eq_zero_of_mem_matrixLocalReporter
    {X : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ matrixLocalReporter (m := m) (n := n)) :
    crossMatrixPart X = 0 := by
  exact (crossMatrixPart_eq_zero_iff_preserves_local X).2 fun L hL =>
    matrixCommutator_local_mem hX hL

/-! ## Exact boundary/cross direct sum on the traceless joint sector -/

/-- Joint traceless matrix sector, the complexification of `Herm₀(A ⊗ B)`. -/
abbrev jointTracelessMatrices : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  tracelessMatrices (m × n)

theorem matrixLocalReporter_le_jointTraceless :
    matrixLocalReporter (m := m) (n := n) ≤ jointTracelessMatrices := by
  intro X hX
  rw [mem_matrixLocalReporter_iff] at hX
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  change (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B).trace = 0
  rw [Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker, hA, hB]
  simp

theorem matrixCrossFibre_le_jointTraceless :
    matrixCrossFibre (m := m) (n := n) ≤ jointTracelessMatrices := by
  intro X hX
  rw [mem_matrixCrossFibre] at hX
  change X.trace = 0
  rw [← trace_partialTraceRight X, hX.1, Matrix.trace_zero]

/-- **Card Theorem 5.1, direct-sum form.** Every traceless joint matrix splits uniquely into a
local reporter and a cross component. -/
theorem jointTracelessMatrices_eq_local_sup_cross :
    jointTracelessMatrices (m := m) (n := n) =
      matrixLocalReporter ⊔ matrixCrossFibre := by
  apply le_antisymm
  · intro X hX
    have htrace : X.trace = 0 := hX
    have hscalar : scalarMatrixPart X = 0 := by
      simp [scalarMatrixPart, bipartiteScalarCoeff, htrace]
    have hlocal : leftLocalPart X + rightLocalPart X ∈
        matrixLocalReporter (m := m) (n := n) := by
      rw [mem_matrixLocalReporter_iff]
      exact ⟨leftReducedComponent X, leftReducedComponent_trace X,
        rightReducedComponent X, rightReducedComponent_trace X, rfl⟩
    have hcross := crossMatrixPart_mem X
    rw [Submodule.mem_sup]
    refine ⟨leftLocalPart X + rightLocalPart X, hlocal, crossMatrixPart X, hcross, ?_⟩
    simpa [hscalar, add_assoc] using (bipartite_decomposition X).symm
  · exact sup_le matrixLocalReporter_le_jointTraceless matrixCrossFibre_le_jointTraceless

/-- On the traceless joint sector, zero cross projection is exactly local membership. -/
theorem crossMatrixPart_eq_zero_iff_mem_matrixLocalReporter_of_trace_zero
    {X : Matrix (m × n) (m × n) ℂ} (htrace : X.trace = 0) :
    crossMatrixPart X = 0 ↔ X ∈ matrixLocalReporter (m := m) (n := n) := by
  constructor
  · intro hcross
    rw [mem_matrixLocalReporter_iff]
    refine ⟨leftReducedComponent X, leftReducedComponent_trace X,
      rightReducedComponent X, rightReducedComponent_trace X, ?_⟩
    have hscalar : scalarMatrixPart X = 0 := by
      simp [scalarMatrixPart, bipartiteScalarCoeff, htrace]
    simpa [leftLocalPart, rightLocalPart, hscalar, hcross] using bipartite_decomposition X
  · exact crossMatrixPart_eq_zero_of_mem_matrixLocalReporter


end Decomposition

end HTGeometry.ConstraintRelativity
