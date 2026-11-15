import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryQuadraticRefinement
import Mathlib.RingTheory.Discriminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField

/-!
# Canonical alternating trace forms over the binary field

For every finite commutative binary algebra, squaring preserves trace. The
pairing `Tr(xy) + Tr(x)Tr(y)` is therefore alternating. In every basis its matrix
is the canonical diagonal outer-product correction of the trace matrix, so its
rank rounds down to even and its determinant is the discriminant in even
dimension. The trace shear `x ↦ x + Tr(x)·1` gives a basis-free description.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable (A : Type*) [CommRing A] [Algebra (ZMod 2) A] [Module.Finite (ZMod 2) A]

/-- Squaring does not change the trace of an element of a finite binary algebra. -/
theorem binary_trace_sq (x : A) :
    Algebra.trace (ZMod 2) A (x ^ 2) = Algebra.trace (ZMod 2) A x := by
  classical
  let b := Module.finBasis (ZMod 2) A
  rw [Algebra.trace_eq_matrix_trace b, map_pow, ZMod.trace_pow_card, ZMod.pow_card,
    ← Algebra.trace_eq_matrix_trace b]

/-- The trace of one is the dimension reduced modulo two. -/
theorem binary_trace_one :
    Algebra.trace (ZMod 2) A 1 = (finrank (ZMod 2) A : ZMod 2) := by
  simpa using (Algebra.trace_algebraMap (R := ZMod 2) (S := A) (1 : ZMod 2))

/-- Every binary Artin–Schreier difference has trace zero. -/
theorem binary_trace_artinSchreier (x : A) :
    Algebra.trace (ZMod 2) A (x ^ 2 + x) = 0 := by
  rw [map_add, binary_trace_sq, CharTwo.add_self_eq_zero]

/-- The canonical alternating correction of the algebra trace pairing. -/
noncomputable def binaryTraceForm : LinearMap.BilinForm (ZMod 2) A :=
  Algebra.traceForm (ZMod 2) A +
    (Algebra.trace (ZMod 2) A).smulRight (Algebra.trace (ZMod 2) A)

omit [Module.Finite (ZMod 2) A] in
@[simp]
theorem binaryTraceForm_apply (x y : A) :
    binaryTraceForm A x y = Algebra.trace (ZMod 2) A (x * y) +
      Algebra.trace (ZMod 2) A x * Algebra.trace (ZMod 2) A y := rfl

/-- The corrected trace pairing is alternating, including nonreduced algebras. -/
theorem binaryTraceForm_isAlt : (binaryTraceForm A).IsAlt := by
  intro x
  rw [binaryTraceForm_apply, ← sq, binary_trace_sq, ← sq, ZMod.pow_card,
    CharTwo.add_self_eq_zero]

/-- The rank-one endomorphism producing the corrected trace pairing. -/
noncomputable def binaryTraceShear : A →ₗ[ZMod 2] A :=
  LinearMap.id + (Algebra.trace (ZMod 2) A).smulRight (1 : A)

omit [Module.Finite (ZMod 2) A] in
@[simp]
theorem binaryTraceShear_apply (x : A) :
    binaryTraceShear A x = x + Algebra.trace (ZMod 2) A x • (1 : A) := rfl

omit [Module.Finite (ZMod 2) A] in
/-- Correcting the trace pairing is precomposition by the trace shear. -/
theorem binaryTraceForm_eq_trace_comp :
    binaryTraceForm A = LinearMap.comp (Algebra.traceForm (ZMod 2) A) (binaryTraceShear A) := by
  ext x y
  change Algebra.trace (ZMod 2) A (x * y) +
      Algebra.trace (ZMod 2) A x * Algebra.trace (ZMod 2) A y =
    Algebra.trace (ZMod 2) A ((x + Algebra.trace (ZMod 2) A x • (1 : A)) * y)
  rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul, smul_eq_mul]

/-- The square of the trace shear is controlled by the dimension parity. -/
theorem binaryTraceShear_square (x : A) :
    binaryTraceShear A (binaryTraceShear A x) =
      x + (Algebra.trace (ZMod 2) A x * (finrank (ZMod 2) A : ZMod 2)) • (1 : A) := by
  have hz : Algebra.trace (ZMod 2) A x • (1 : A) +
      Algebra.trace (ZMod 2) A x • (1 : A) = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  simp only [binaryTraceShear_apply, map_add, map_smul, binary_trace_one, smul_add, smul_smul]
  rw [add_assoc, ← add_assoc (Algebra.trace (ZMod 2) A x • (1 : A)), hz, zero_add]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The diagonal of the trace matrix is the trace covector in every basis. -/
theorem diagonal_binaryTraceMatrix (b : Basis ι (ZMod 2) A) :
    (fun i => Algebra.traceMatrix (ZMod 2) b i i) =
      fun i => Algebra.trace (ZMod 2) A (b i) := by
  funext i
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, ← sq, binary_trace_sq]

/-- The corrected trace matrix is the canonical binary alternating repair. -/
theorem binaryTraceForm_toMatrix (b : Basis ι (ZMod 2) A) :
    (binaryTraceForm A).toMatrix b =
      binaryAlternatingRepair (Algebra.traceMatrix (ZMod 2) b) := by
  rw [binaryAlternatingRepair, diagonal_binaryTraceMatrix]
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, binaryTraceForm_apply, Matrix.add_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, vecMulVec, Matrix.of_apply]

/-- Correction rounds the trace-matrix rank down to the nearest even integer. -/
theorem rank_binaryTraceForm_toMatrix (b : Basis ι (ZMod 2) A) :
    ((binaryTraceForm A).toMatrix b).rank =
      (Algebra.traceMatrix (ZMod 2) b).rank - (Algebra.traceMatrix (ZMod 2) b).rank % 2 := by
  rw [binaryTraceForm_toMatrix, rank_binaryAlternatingRepair]
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]

/-- The corrected determinant equals the discriminant in even dimension and zero in odd dimension. -/
theorem det_binaryTraceForm_toMatrix (b : Basis ι (ZMod 2) A) :
    ((binaryTraceForm A).toMatrix b).det =
      if Fintype.card ι % 2 = 0 then Algebra.discr (ZMod 2) b else 0 := by
  rw [binaryTraceForm_toMatrix, det_binaryAlternatingRepair, Algebra.discr_def]
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]

/-- Nondegeneracy of the corrected trace pairing requires exactly nondegeneracy of
the original pairing and even algebra dimension. -/
theorem binaryTraceForm_nondegenerate_iff :
    (binaryTraceForm A).Nondegenerate ↔
      (Algebra.traceForm (ZMod 2) A).Nondegenerate ∧ finrank (ZMod 2) A % 2 = 0 := by
  classical
  let b := Module.finBasis (ZMod 2) A
  have hs : (Algebra.traceMatrix (ZMod 2) b).IsSymm := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, binaryTraceForm_toMatrix,
    binaryAlternatingRepair_det_ne_zero_iff _ hs,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, ← Algebra.traceMatrix_of_basis]
  simp only [Fintype.card_fin]

#print axioms binaryTraceForm_nondegenerate_iff

#print axioms binary_trace_sq
#print axioms binary_trace_artinSchreier
#print axioms binaryTraceForm_eq_trace_comp
#print axioms binaryTraceForm_isAlt
#print axioms binaryTraceShear_square
#print axioms rank_binaryTraceForm_toMatrix
#print axioms det_binaryTraceForm_toMatrix
end GaloisForLFunctions.HTGeometry.LinearAlgebra
