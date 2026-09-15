import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity

/-!
# Reduced-density-matrix applications

Finite-dimensional transfers of Fredheim--Kvaal, arXiv:2510.12242, Theorem 5.1.  Partial trace has
an explicit positive right inverse, hence is surjective both on the full matrix space and on the
positive cone.  The construction embeds a reduced state by tensoring with the normalized identity.
-/

noncomputable section

namespace HTGeometry.ConstraintRelativity

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Canonical section of the right partial trace: tensor with the normalized identity state. -/
def partialTraceRightSection [Nonempty n] (A : Matrix m m ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  A ⊗ₖ ((Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ))

/-- The normalized-identity embedding is an exact right inverse to partial trace. -/
@[simp] theorem partialTraceRight_section [Nonempty n] (A : Matrix m m ℂ) :
    partialTraceRight (partialTraceRightSection (n := n) A) = A := by
  rw [partialTraceRightSection, partialTraceRight_kronecker, Matrix.trace_smul,
    Matrix.trace_one]
  simp [Fintype.card_ne_zero]

/-- Partial trace is surjective whenever the traced factor is inhabited. -/
theorem partialTraceRight_surjective [Nonempty n] :
    Function.Surjective
      (partialTraceRight : Matrix (m × n) (m × n) ℂ → Matrix m m ℂ) :=
  fun A => ⟨partialTraceRightSection (n := n) A, partialTraceRight_section A⟩

omit [DecidableEq m] in
/-- The canonical section preserves positive semidefiniteness. -/
theorem partialTraceRightSection_posSemidef [Nonempty n]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (partialTraceRightSection (n := n) A).PosSemidef := by
  apply hA.kronecker
  exact Matrix.PosSemidef.one.smul (by positivity)

/-- Partial trace is surjective on the positive cone, with a positive preimage chosen canonically. -/
theorem partialTraceRight_positive_surjective [Nonempty n] (A : Matrix m m ℂ) :
    A.PosSemidef →
      ∃ X : Matrix (m × n) (m × n) ℂ,
        X.PosSemidef ∧ partialTraceRight X = A := by
  intro hA
  exact ⟨partialTraceRightSection (n := n) A,
    partialTraceRightSection_posSemidef hA, partialTraceRight_section A⟩

/-- Positive semidefinite matrices as a closed positive-cone carrier. -/
def PositiveMatrix (m : Type*) [Fintype m] :=
  {A : Matrix m m ℂ // A.PosSemidef}

/-- Right partial trace as a map of positive cones. -/
def partialTraceRightPositive [Nonempty n] :
    PositiveMatrix (m × n) → PositiveMatrix m :=
  fun X => ⟨partialTraceRight X.1,
    GaloisForLFunctions.HTGeometry.posSemidef_partialTraceRight X.2⟩

/-- Canonical normalized-identity section on the positive cone. -/
def partialTraceRightPositiveSection [Nonempty n] :
    PositiveMatrix m → PositiveMatrix (m × n) :=
  fun A => ⟨partialTraceRightSection (n := n) A.1,
    partialTraceRightSection_posSemidef A.2⟩

@[simp] theorem partialTraceRightPositive_section [Nonempty n] (A : PositiveMatrix m) :
    partialTraceRightPositive (partialTraceRightPositiveSection (n := n) A) = A := by
  exact Subtype.ext (partialTraceRight_section A.1)

/-- **Positive-cone surjectivity.**  Partial trace reaches every positive subsystem state. -/
theorem partialTraceRightPositive_surjective [Nonempty n] :
    Function.Surjective (partialTraceRightPositive (m := m) (n := n)) :=
  fun A => ⟨partialTraceRightPositiveSection (n := n) A,
    partialTraceRightPositive_section A⟩

/-- Unit-trace positive matrices, the finite density-matrix state space. -/
def DensityMatrix (m : Type*) [Fintype m] :=
  {A : Matrix m m ℂ // A.PosSemidef ∧ A.trace = 1}

/-- Right partial trace as a state-space map. -/
def partialTraceRightDensity [Nonempty n] :
    DensityMatrix (m × n) → DensityMatrix m :=
  fun X => ⟨partialTraceRight X.1,
    GaloisForLFunctions.HTGeometry.posSemidef_partialTraceRight X.2.1,
    (trace_partialTraceRight X.1).trans X.2.2⟩

/-- Canonical product-state section of right partial trace. -/
def partialTraceRightDensitySection [Nonempty n] :
    DensityMatrix m → DensityMatrix (m × n) :=
  fun A => ⟨partialTraceRightSection (n := n) A.1,
    partialTraceRightSection_posSemidef A.2.1, by
      rw [← trace_partialTraceRight, partialTraceRight_section]
      exact A.2.2⟩

@[simp] theorem partialTraceRightDensity_section [Nonempty n] (A : DensityMatrix m) :
    partialTraceRightDensity (partialTraceRightDensitySection (n := n) A) = A := by
  exact Subtype.ext (partialTraceRight_section A.1)

/-- **State-space surjectivity.**  Every reduced density matrix has a canonical product-state
extension with a maximally mixed ancillary factor. -/
theorem partialTraceRightDensity_surjective [Nonempty n] :
    Function.Surjective (partialTraceRightDensity (m := m) (n := n)) :=
  fun A => ⟨partialTraceRightDensitySection (n := n) A,
    partialTraceRightDensity_section A⟩

/-- Canonical section of the left partial trace. -/
def partialTraceLeftSection [Nonempty m] (B : Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  ((Fintype.card m : ℂ)⁻¹ • (1 : Matrix m m ℂ)) ⊗ₖ B

/-- The normalized-identity embedding is an exact right inverse to left partial trace. -/
@[simp] theorem partialTraceLeft_section [Nonempty m] (B : Matrix n n ℂ) :
    partialTraceLeft (partialTraceLeftSection (m := m) B) = B := by
  rw [partialTraceLeftSection, partialTraceLeft_kronecker, Matrix.trace_smul,
    Matrix.trace_one]
  simp [Fintype.card_ne_zero]

/-- Left partial trace is surjective whenever the traced factor is inhabited. -/
theorem partialTraceLeft_surjective [Nonempty m] :
    Function.Surjective
      (partialTraceLeft : Matrix (m × n) (m × n) ℂ → Matrix n n ℂ) :=
  fun B => ⟨partialTraceLeftSection (m := m) B, partialTraceLeft_section B⟩

omit [DecidableEq n] in
/-- The canonical left section preserves positive semidefiniteness. -/
theorem partialTraceLeftSection_posSemidef [Nonempty m]
    {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    (partialTraceLeftSection (m := m) B).PosSemidef := by
  apply Matrix.PosSemidef.kronecker
  · exact Matrix.PosSemidef.one.smul (by positivity)
  · exact hB

/-- Left partial trace is likewise surjective on the positive cone. -/
theorem partialTraceLeft_positive_surjective [Nonempty m] (B : Matrix n n ℂ) :
    B.PosSemidef →
      ∃ X : Matrix (m × n) (m × n) ℂ,
        X.PosSemidef ∧ partialTraceLeft X = B := by
  intro hB
  exact ⟨partialTraceLeftSection (m := m) B,
    partialTraceLeftSection_posSemidef hB, partialTraceLeft_section B⟩

/-! The corpus previously carried positivity only for the right partial trace.  The symmetric
left-hand infrastructure below closes the second subsystem without changing index order. -/

/-- Embed a vector from the right subsystem into one fixed left-coordinate slice. -/
def leftLiftSlice (x : n → ℂ) (k : m) : m × n → ℂ :=
  fun z => if z.1 = k then x z.2 else 0

omit [DecidableEq n] in
theorem matSesq_leftLiftSlice (A : Matrix (m × n) (m × n) ℂ) (x : n → ℂ) (k : m) :
    GaloisForLFunctions.HTGeometry.matSesq A (leftLiftSlice x k) (leftLiftSlice x k) =
      ∑ i, ∑ j, (starRingEnd ℂ) (x i) * A (k, i) (k, j) * x j := by
  classical
  simp [GaloisForLFunctions.HTGeometry.matSesq, leftLiftSlice, Fintype.sum_prod_type,
    apply_ite, ite_mul, Finset.sum_ite_eq']

private theorem sum3_rotate {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (F : ι₁ → ι₂ → ι₃ → ℂ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  rw [show (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c from
    Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

omit [DecidableEq n] in
/-- Quadratic forms of the left partial trace split as a sum over left-coordinate slices. -/
theorem matSesq_partialTraceLeft (A : Matrix (m × n) (m × n) ℂ) (x : n → ℂ) :
    GaloisForLFunctions.HTGeometry.matSesq (partialTraceLeft A) x x =
      ∑ k, GaloisForLFunctions.HTGeometry.matSesq A (leftLiftSlice x k) (leftLiftSlice x k) := by
  classical
  rw [show (∑ k, GaloisForLFunctions.HTGeometry.matSesq A
      (leftLiftSlice x k) (leftLiftSlice x k)) =
      ∑ k, ∑ i, ∑ j, (starRingEnd ℂ) (x i) * A (k, i) (k, j) * x j from
    Finset.sum_congr rfl fun k _ => matSesq_leftLiftSlice A x k]
  simp only [GaloisForLFunctions.HTGeometry.matSesq, partialTraceLeft,
    Finset.mul_sum, Finset.sum_mul]
  exact sum3_rotate
    (fun i j k => (starRingEnd ℂ) (x i) * A (k, i) (k, j) * x j)

omit [DecidableEq n] in
/-- Positive semidefiniteness is preserved by the left partial trace. -/
theorem posSemidef_partialTraceLeft {A : Matrix (m × n) (m × n) ℂ}
    (hA : A.PosSemidef) : (partialTraceLeft A).PosSemidef := by
  refine GaloisForLFunctions.HTGeometry.posSemidef_of_matSesq_re_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, partialTraceLeft, star_sum]
    exact Finset.sum_congr rfl fun k _ =>
      congrFun (congrFun hA.isHermitian (k, i)) (k, j)
  · rw [matSesq_partialTraceLeft, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ =>
      GaloisForLFunctions.HTGeometry.matSesq_self_re_nonneg hA _

/-- Left partial trace as a map of positive cones. -/
def partialTraceLeftPositive [Nonempty m] :
    PositiveMatrix (m × n) → PositiveMatrix n :=
  fun X => ⟨partialTraceLeft X.1, posSemidef_partialTraceLeft X.2⟩

/-- Canonical normalized-identity section for the left positive cone. -/
def partialTraceLeftPositiveSection [Nonempty m] :
    PositiveMatrix n → PositiveMatrix (m × n) :=
  fun B => ⟨partialTraceLeftSection (m := m) B.1,
    partialTraceLeftSection_posSemidef B.2⟩

@[simp] theorem partialTraceLeftPositive_section [Nonempty m] (B : PositiveMatrix n) :
    partialTraceLeftPositive (partialTraceLeftPositiveSection (m := m) B) = B := by
  exact Subtype.ext (partialTraceLeft_section B.1)

/-- Positive-cone surjectivity for the left subsystem. -/
theorem partialTraceLeftPositive_surjective [Nonempty m] :
    Function.Surjective (partialTraceLeftPositive (m := m) (n := n)) :=
  fun B => ⟨partialTraceLeftPositiveSection (m := m) B,
    partialTraceLeftPositive_section B⟩

/-- Left partial trace as a density-state map. -/
def partialTraceLeftDensity [Nonempty m] :
    DensityMatrix (m × n) → DensityMatrix n :=
  fun X => ⟨partialTraceLeft X.1, posSemidef_partialTraceLeft X.2.1,
    (trace_partialTraceLeft X.1).trans X.2.2⟩

/-- Canonical product-state section for the left density-state map. -/
def partialTraceLeftDensitySection [Nonempty m] :
    DensityMatrix n → DensityMatrix (m × n) :=
  fun B => ⟨partialTraceLeftSection (m := m) B.1,
    partialTraceLeftSection_posSemidef B.2.1, by
      rw [← trace_partialTraceLeft, partialTraceLeft_section]
      exact B.2.2⟩

@[simp] theorem partialTraceLeftDensity_section [Nonempty m] (B : DensityMatrix n) :
    partialTraceLeftDensity (partialTraceLeftDensitySection (m := m) B) = B := by
  exact Subtype.ext (partialTraceLeft_section B.1)

/-- **Left state-space surjectivity.** Every right-subsystem density matrix has a canonical
product-state extension with maximally mixed left factor. -/
theorem partialTraceLeftDensity_surjective [Nonempty m] :
    Function.Surjective (partialTraceLeftDensity (m := m) (n := n)) :=
  fun B => ⟨partialTraceLeftDensitySection (m := m) B,
    partialTraceLeftDensity_section B⟩

end HTGeometry.ConstraintRelativity
