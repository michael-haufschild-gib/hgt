import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Prime-log Vandermonde defects are scalar Schur residuals

The first `k` moment equations form a transposed Vandermonde sampling matrix.  Border that matrix
by the archimedean derivation target and the next moment row.  This file proves that the canonical
next-order interpolation defect is exactly the negative of the resulting scalar Schur complement.

For distinct positive prime labels the Schur residual is the positive number `Qₖ'(0)`, where
`Qₖ(X) = ∏ i, (X + log (p i))`.  Thus the signed defect `-Qₖ'(0)` already proved in
`PinnedAffinePrimeJetRigidity` is not a positive Gram residual: it is the negative Schur residual
of a non-Hermitian bordered moment system.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial Complex
open scoped BigOperators

/-- The finite moment-sampling map, with moments indexing rows and frequencies indexing columns. -/
def finiteMomentSamplingMatrix {k : ℕ} (f : Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  (Matrix.vandermonde f)ᵀ

/-- The first `k` moments of coefficient extraction at derivative order one. -/
def finiteDerivationTarget {k : ℕ} : Fin k → ℂ :=
  fun j => archimedeanDerivationMoment (j : ℕ)

/-- The canonical finite interpolation packet obtained from the nonsingular inverse. -/
def canonicalFiniteDerivationPacket {k : ℕ} (f : Fin k → ℂ) : Fin k → ℂ :=
  (finiteMomentSamplingMatrix f)⁻¹ *ᵥ finiteDerivationTarget

/-- The finite derivation target as a block column. -/
def finiteDerivationTargetColumn {k : ℕ} : Matrix (Fin k) (Fin 1) ℂ :=
  fun j _ => finiteDerivationTarget j

/-- The first omitted moment as a block row. -/
def finiteNextMomentRow {k : ℕ} (f : Fin k → ℂ) : Matrix (Fin 1) (Fin k) ℂ :=
  fun _ i => f i ^ k

/-- The derivation's value at the first omitted order as a scalar block. -/
def finiteNextDerivationBlock (k : ℕ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => archimedeanDerivationMoment k

/-- The scalar Schur complement of the finite moment-sampling block. -/
def finiteDerivationSchurResidual {k : ℕ} (f : Fin k → ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  finiteNextDerivationBlock k -
    finiteNextMomentRow f * (finiteMomentSamplingMatrix f)⁻¹ * finiteDerivationTargetColumn

/-- The moment-sampling matrix bordered by the derivation target and first omitted moment. -/
def finiteDerivationBorderedMatrix {k : ℕ} (f : Fin k → ℂ) :
    Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (finiteMomentSamplingMatrix f) finiteDerivationTargetColumn
    (finiteNextMomentRow f) (finiteNextDerivationBlock k)

/-- Distinct frequencies make the finite moment-sampling matrix nonsingular. -/
theorem finiteMomentSamplingMatrix_det_ne_zero {k : ℕ} {f : Fin k → ℂ}
    (hf : Function.Injective f) : (finiteMomentSamplingMatrix f).det ≠ 0 := by
  rw [finiteMomentSamplingMatrix, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hf

/-- The inverse-defined canonical packet matches every moment below the truncation order. -/
theorem canonicalFiniteDerivationPacket_matches {k : ℕ} {f : Fin k → ℂ}
    (hf : Function.Injective f) (j : Fin k) :
    (∑ i : Fin k, canonicalFiniteDerivationPacket f i * f i ^ (j : ℕ)) =
      archimedeanDerivationMoment (j : ℕ) := by
  let A := finiteMomentSamplingMatrix f
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (finiteMomentSamplingMatrix_det_ne_zero hf)
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have happ : (A *ᵥ (A⁻¹ *ᵥ finiteDerivationTarget)) j = finiteDerivationTarget j := by
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  simpa [A, finiteMomentSamplingMatrix, canonicalFiniteDerivationPacket,
    finiteDerivationTarget, Matrix.mulVec, mul_comm] using happ

/-- The scalar Schur complement is the target's first omitted moment minus the interpolated one. -/
theorem finiteDerivationSchurResidual_apply {k : ℕ} (f : Fin k → ℂ) :
    finiteDerivationSchurResidual f 0 0 =
      archimedeanDerivationMoment k -
        ∑ i : Fin k, canonicalFiniteDerivationPacket f i * f i ^ k := by
  simp [finiteDerivationSchurResidual, finiteNextDerivationBlock,
    finiteNextMomentRow, finiteDerivationTargetColumn, canonicalFiniteDerivationPacket,
    finiteDerivationTarget, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The next-order interpolation defect is exactly the negative scalar Schur residual. -/
theorem canonicalFiniteDerivationNextDefect_eq_neg_schurResidual {k : ℕ}
    (f : Fin k → ℂ) :
    (∑ i : Fin k, canonicalFiniteDerivationPacket f i * f i ^ k) -
        archimedeanDerivationMoment k =
      -finiteDerivationSchurResidual f 0 0 := by
  rw [finiteDerivationSchurResidual_apply]
  ring

/-- The bordered moment determinant factors by the finite sampling determinant and its scalar
Schur residual. -/
theorem finiteDerivationBorderedMatrix_det_eq_sampling_det_mul_schur {k : ℕ}
    {f : Fin k → ℂ} (hf : Function.Injective f) :
    (finiteDerivationBorderedMatrix f).det =
      (finiteMomentSamplingMatrix f).det * finiteDerivationSchurResidual f 0 0 := by
  let A := finiteMomentSamplingMatrix f
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (finiteMomentSamplingMatrix_det_ne_zero hf)
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  letI : Invertible A := hA.invertible
  have hfactor := Matrix.det_fromBlocks₁₁ A finiteDerivationTargetColumn
    (finiteNextMomentRow f) (finiteNextDerivationBlock k)
  rw [Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one] at hfactor
  simpa [A, finiteDerivationBorderedMatrix, finiteDerivationSchurResidual] using hfactor

/-- For distinct real nodes, the scalar Schur residual is the derivative at zero of their node
polynomial. -/
theorem finiteNegativeDerivationSchurResidual_eq_nodePolynomialDerivative {k : ℕ}
    (hk : 0 < k) (f : Fin k → ℝ) (hf : Function.Injective f) :
    finiteDerivationSchurResidual (fun i => (f i : ℂ)) 0 0 =
      (((negativeNodePolynomial f).derivative.eval (0 : ℝ) : ℝ) : ℂ) := by
  let fc : Fin k → ℂ := fun i => (f i : ℂ)
  let a := canonicalFiniteDerivationPacket fc
  have hfc : Function.Injective fc := fun i j hij => hf (Complex.ofReal_injective hij)
  have hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (f i : ℂ) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ) := by
    intro j
    exact canonicalFiniteDerivationPacket_matches hfc j
  have hdefect := finiteNegativeDerivationInterpolation_nextOrderDefect_eq hk f a hmatch
  rw [finiteDerivationSchurResidual_apply]
  linear_combination -hdefect

/-- For distinct positive prime labels, the scalar Schur residual is the positive derivative of
the prime-log node polynomial.  Hence the previously computed signed defect is its negative. -/
theorem finitePrimeDerivationSchurResidual_eq_nodePolynomialDerivative {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 0 < p i)
    (hpinj : Function.Injective p) :
    finiteDerivationSchurResidual (fun i => -(Real.log (p i) : ℂ)) 0 0 =
      (((negativeNodePolynomial (fun i => -Real.log (p i))).derivative.eval
        (0 : ℝ) : ℝ) : ℂ) := by
  have hfR : Function.Injective (fun i => -Real.log (p i)) := by
    intro i j hij
    apply neg_log_nat_injective p hp hpinj
    simpa using congrArg Complex.ofReal hij
  simpa using finiteNegativeDerivationSchurResidual_eq_nodePolynomialDerivative hk
    (fun i => -Real.log (p i)) hfR

/-- Every nonempty distinct packet of labels greater than one has a strictly positive scalar Schur
residual; equivalently, its canonical next-order interpolation defect is strictly negative. -/
theorem finitePrimeDerivationSchurResidual_re_pos {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) :
    0 < (finiteDerivationSchurResidual (fun i => -(Real.log (p i) : ℂ)) 0 0).re := by
  rw [finitePrimeDerivationSchurResidual_eq_nodePolynomialDerivative hk p
    (fun i => Nat.zero_lt_one.trans (hp i)) hpinj]
  simpa using negativeNodePolynomial_derivative_eval_zero_pos hk
    (fun i => -Real.log (p i))
    (fun i => neg_lt_zero.mpr (Real.log_pos (by exact_mod_cast hp i)))

end RHTower
