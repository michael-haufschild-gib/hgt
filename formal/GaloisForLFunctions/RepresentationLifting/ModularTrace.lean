import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Trace on regular and free dual-number modules

An endomorphism of a free regular representation has a unique matrix of convolution kernels.
Its scalar trace is the group order times the sum of the diagonal identity coefficients.
The centralizer of the standard square-zero shift consists exactly of blocks `[A B; 0 A]`,
whose trace is twice the trace of `A`.

These are the two trace mechanisms used in Scavia's Lemma 6.3. The classification identifies
the complete surviving matrix data even when the scalar trace vanishes in modular characteristic.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open scoped BigOperators

variable {ι G R : Type*} [Group G] [CommRing R]

/-- The matrix of a family of right-convolution kernels on copies of the regular module. -/
def regularKernelMatrix (K : ι → ι → G → R) : Matrix (ι × G) (ι × G) R :=
  fun x y => K x.1 y.1 (x.2⁻¹ * y.2)

omit [CommRing R] in
theorem regularKernelMatrix_translate (K : ι → ι → G → R)
    (g x y : G) (i j : ι) :
    regularKernelMatrix K (i, g * x) (j, g * y) = regularKernelMatrix K (i, x) (j, y) := by
  simp [regularKernelMatrix, mul_assoc]

omit [CommRing R] in
/-- Simultaneous left-translation invariance is equivalent to a unique convolution kernel. -/
theorem regularKernelMatrix_classification (A : Matrix (ι × G) (ι × G) R) :
    (∀ (g x y : G) (i j : ι), A (i, g * x) (j, g * y) = A (i, x) (j, y)) ↔
      ∃! K : ι → ι → G → R, regularKernelMatrix K = A := by
  constructor
  · intro h
    refine ⟨fun i j g => A (i, 1) (j, g), ?_, ?_⟩
    · funext x y
      simpa [regularKernelMatrix] using h x.2⁻¹ x.2 y.2 x.1 y.1
    · intro K hK
      funext i j g
      simpa [regularKernelMatrix] using congrFun (congrFun hK (i, 1)) (j, g)
  · rintro ⟨K, rfl, _⟩
    exact regularKernelMatrix_translate K

/-- The regular-module trace only retains the identity coefficient. -/
theorem trace_regularKernelMatrix [Fintype ι] [Fintype G] (K : ι → ι → G → R) :
    Matrix.trace (regularKernelMatrix K) = (Fintype.card G : R) * ∑ i, K i i 1 := by
  simp [Matrix.trace, Matrix.diag, regularKernelMatrix, Fintype.sum_prod_type,
    nsmul_eq_mul, Finset.mul_sum]

/-- In characteristic equal to the group order, every regular-module trace vanishes. -/
theorem trace_regularKernelMatrix_modular [Fintype ι] [Fintype G]
    [CharP R (Fintype.card G)] (K : ι → ι → G → R) :
    Matrix.trace (regularKernelMatrix K) = 0 := by
  rw [trace_regularKernelMatrix, CharP.cast_eq_zero R (Fintype.card G), zero_mul]

section DualNumber

variable [Fintype ι] [DecidableEq ι]

/-- Multiplication by the nilpotent parameter on a free dual-number module. -/
def dualNumberShift : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks 0 1 0 0

theorem dualNumberShift_sq : (dualNumberShift (ι := ι) (R := R)) ^ 2 = 0 := by
  rw [pow_two, dualNumberShift, Matrix.fromBlocks_multiply]
  simp

/-- The full centralizer of a free square-zero operator is a repeated upper-triangular block. -/
theorem commute_dualNumberShift_iff (T : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    T * dualNumberShift = dualNumberShift * T ↔
      ∃ A B : Matrix ι ι R, T = Matrix.fromBlocks A B 0 A := by
  constructor
  · intro h
    have hleft : T * dualNumberShift = Matrix.fromBlocks 0 T.toBlocks₁₁ 0 T.toBlocks₂₁ := by
      conv_lhs => lhs; rw [← Matrix.fromBlocks_toBlocks T]
      simp [dualNumberShift, Matrix.fromBlocks_multiply]
    have hright : dualNumberShift * T = Matrix.fromBlocks T.toBlocks₂₁ T.toBlocks₂₂ 0 0 := by
      conv_lhs => rhs; rw [← Matrix.fromBlocks_toBlocks T]
      simp [dualNumberShift, Matrix.fromBlocks_multiply]
    rw [hleft, hright] at h
    have hzero : T.toBlocks₂₁ = 0 := by
      have := congrArg Matrix.toBlocks₁₁ h
      simpa using this.symm
    have heq : T.toBlocks₁₁ = T.toBlocks₂₂ := by
      simpa using congrArg Matrix.toBlocks₁₂ h
    refine ⟨T.toBlocks₁₁, T.toBlocks₁₂, ?_⟩
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks T]
    rw [hzero, ← heq]
  · rintro ⟨A, B, rfl⟩
    simp [dualNumberShift, Matrix.fromBlocks_multiply]

omit [DecidableEq ι] in
theorem trace_dualNumberBlock (A B : Matrix ι ι R) :
    Matrix.trace (Matrix.fromBlocks A B 0 A) = 2 * Matrix.trace A := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, two_mul]

/-- Characteristic two makes every endomorphism of a free dual-number module traceless. -/
theorem dualNumberShift_trace_zero [CharP R 2] (T : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    T * dualNumberShift = dualNumberShift * T → Matrix.trace T = 0 := by
  intro h
  obtain ⟨A, B, rfl⟩ := (commute_dualNumberShift_iff T).mp h
  rw [trace_dualNumberBlock, two_mul, CharTwo.add_self_eq_zero]

end DualNumber

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.regularKernelMatrix_classification
#print axioms GaloisForLFunctions.RepresentationLifting.trace_regularKernelMatrix_modular
#print axioms GaloisForLFunctions.RepresentationLifting.commute_dualNumberShift_iff
#print axioms GaloisForLFunctions.RepresentationLifting.dualNumberShift_trace_zero
