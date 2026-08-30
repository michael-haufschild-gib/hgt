import GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone

/-!
# Positive-definite Hermitian realification

The standard doubled-real block representation carries the real part of a complex Hermitian
quadratic form to its ordinary real quadratic form.  In particular, positive-definite Hermitian
matrices realify to positive-definite real matrices.  This supplies the complex local block needed
for a single unconditional archimedean quadratic form over a number field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical ComplexOrder Matrix

noncomputable section

variable {n : Type*} [Fintype n]

/-- Recombine the two real channels of a doubled vector into a complex vector. -/
def complexOfDoubledReal (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

/-- Realification preserves the Hermitian quadratic value, after taking real part. -/
theorem complexMatrixRealification_quadratic
    (A : Matrix n n ℂ) (x : n ⊕ n → ℝ) :
    x ⬝ᵥ (complexMatrixRealification A).mulVec x =
      ((star (complexOfDoubledReal x)) ⬝ᵥ
        A.mulVec (complexOfDoubledReal x)).re := by
  simp [dotProduct, mulVec, complexMatrixRealification,
    complexMatrixRealPart, complexMatrixImagPart, complexOfDoubledReal,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib]
  ring_nf
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Positive-definite Hermitian matrices have positive-definite doubled-real models. -/
theorem complexMatrixRealification_posDef
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    (complexMatrixRealification A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext i j
    change complexMatrixRealification A j i = complexMatrixRealification A i j
    have h := congrArg complexMatrixRealification hA.1
    rw [complexMatrixRealification_conjTranspose] at h
    exact congrFun (congrFun h i) j
  · intro x hx
    have hz : complexOfDoubledReal x ≠ 0 := by
      intro hz
      apply hx
      funext i
      rcases i with i | i
      · have hi := congrFun hz i
        exact Complex.ext_iff.mp hi |>.1
      · have hi := congrFun hz i
        exact Complex.ext_iff.mp hi |>.2
    rw [Matrix.posDef_iff_dotProduct_mulVec] at hA
    have hpos := hA.2 hz
    have hre := (Complex.lt_def.1 hpos).1
    change @LT.lt ℝ Real.instLT 0
      (x ⬝ᵥ (complexMatrixRealification A).mulVec x)
    simpa [complexMatrixRealification_quadratic] using hre

end

end GaloisForLFunctions.HTGeometry
