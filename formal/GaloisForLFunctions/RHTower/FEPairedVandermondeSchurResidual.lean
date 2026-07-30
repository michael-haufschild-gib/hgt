import GaloisForLFunctions.RHTower.PrimeVandermondeSchurResidual
import GaloisForLFunctions.RHTower.FEPairedPrimeJetBarycentricRigidity

/-!
# Functional-equation-paired Vandermonde defects are scalar Schur residuals

Antisymmetric reflection reduces the odd prime-log moments to ordinary moments at the squared nodes
`(log p)^2`.  The target becomes evaluation at the origin.  This file proves that the first omitted
FE-paired defect is again the negative scalar Schur complement of a bordered moment matrix.

The algebraic invariant changes under reflection: the one-sided derivation residual is `Q'(0)`,
whereas the paired residual is `Q(0) = ∏ i, (-(log p_i)^2)`.  Its sign therefore alternates with the
number of reflected pairs.  Functional-equation symmetry does not turn the finite defect into a
positive Gram Schur complement.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial Complex
open scoped BigOperators

/-- The first `k` moments of evaluation at the origin. -/
def finiteOriginTarget {k : ℕ} : Fin k → ℂ :=
  fun j => originValueMoment (j : ℕ)

/-- The canonical finite packet interpolating evaluation at the origin. -/
def canonicalFiniteOriginPacket {k : ℕ} (f : Fin k → ℂ) : Fin k → ℂ :=
  (finiteMomentSamplingMatrix f)⁻¹ *ᵥ finiteOriginTarget

/-- The origin-evaluation target as a block column. -/
def finiteOriginTargetColumn {k : ℕ} : Matrix (Fin k) (Fin 1) ℂ :=
  fun j _ => finiteOriginTarget j

/-- The first omitted origin-evaluation moment as a scalar block. -/
def finiteNextOriginBlock (k : ℕ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => originValueMoment k

/-- The scalar Schur complement for origin-value interpolation. -/
def finiteOriginSchurResidual {k : ℕ} (f : Fin k → ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  finiteNextOriginBlock k -
    finiteNextMomentRow f * (finiteMomentSamplingMatrix f)⁻¹ * finiteOriginTargetColumn

/-- The squared-node moment matrix bordered by the origin target and first omitted moment. -/
def finiteOriginBorderedMatrix {k : ℕ} (f : Fin k → ℂ) :
    Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (finiteMomentSamplingMatrix f) finiteOriginTargetColumn
    (finiteNextMomentRow f) (finiteNextOriginBlock k)

/-- The inverse-defined packet matches every origin-value moment below the truncation order. -/
theorem canonicalFiniteOriginPacket_matches {k : ℕ} {f : Fin k → ℂ}
    (hf : Function.Injective f) (j : Fin k) :
    (∑ i : Fin k, canonicalFiniteOriginPacket f i * f i ^ (j : ℕ)) =
      originValueMoment (j : ℕ) := by
  let A := finiteMomentSamplingMatrix f
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (finiteMomentSamplingMatrix_det_ne_zero hf)
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have happ : (A *ᵥ (A⁻¹ *ᵥ finiteOriginTarget)) j = finiteOriginTarget j := by
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  simpa [A, finiteMomentSamplingMatrix, canonicalFiniteOriginPacket,
    finiteOriginTarget, Matrix.mulVec, mul_comm] using! happ

/-- The scalar Schur complement is the first omitted origin target minus its interpolated value. -/
theorem finiteOriginSchurResidual_apply {k : ℕ} (f : Fin k → ℂ) :
    finiteOriginSchurResidual f 0 0 =
      originValueMoment k -
        ∑ i : Fin k, canonicalFiniteOriginPacket f i * f i ^ k := by
  simp [finiteOriginSchurResidual, finiteNextOriginBlock,
    finiteNextMomentRow, finiteOriginTargetColumn, canonicalFiniteOriginPacket,
    finiteOriginTarget, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The first omitted origin-value defect is exactly the negative scalar Schur residual. -/
theorem canonicalFiniteOriginNextDefect_eq_neg_schurResidual {k : ℕ}
    (f : Fin k → ℂ) :
    (∑ i : Fin k, canonicalFiniteOriginPacket f i * f i ^ k) -
        originValueMoment k =
      -finiteOriginSchurResidual f 0 0 := by
  rw [finiteOriginSchurResidual_apply]
  ring

/-- The FE-paired bordered determinant factors through its scalar Schur residual. -/
theorem finiteOriginBorderedMatrix_det_eq_sampling_det_mul_schur {k : ℕ}
    {f : Fin k → ℂ} (hf : Function.Injective f) :
    (finiteOriginBorderedMatrix f).det =
      (finiteMomentSamplingMatrix f).det * finiteOriginSchurResidual f 0 0 := by
  let A := finiteMomentSamplingMatrix f
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr
    (finiteMomentSamplingMatrix_det_ne_zero hf)
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  letI : Invertible A := hA.invertible
  have hfactor := Matrix.det_fromBlocks₁₁ A finiteOriginTargetColumn
    (finiteNextMomentRow f) (finiteNextOriginBlock k)
  rw [Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one] at hfactor
  simpa [A, finiteOriginBorderedMatrix, finiteOriginSchurResidual] using hfactor

/-- For distinct real nodes, the origin-value Schur residual is the node polynomial's constant
term. -/
theorem finiteOriginSchurResidual_eq_nodePolynomialEvalZero {k : ℕ}
    (hk : 0 < k) (f : Fin k → ℝ) (hf : Function.Injective f) :
    finiteOriginSchurResidual (fun i => (f i : ℂ)) 0 0 =
      (((negativeNodePolynomial f).eval (0 : ℝ) : ℝ) : ℂ) := by
  let fc : Fin k → ℂ := fun i => (f i : ℂ)
  let a := canonicalFiniteOriginPacket fc
  have hfc : Function.Injective fc := fun i j hij => hf (Complex.ofReal_injective hij)
  have hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (f i : ℂ) ^ (j : ℕ)) =
        originValueMoment (j : ℕ) := by
    intro j
    exact canonicalFiniteOriginPacket_matches hfc j
  have hdefect := finiteOriginValueInterpolation_nextOrderDefect_eq hk f a hmatch
  rw [finiteOriginSchurResidual_apply]
  simp [originValueMoment, hk.ne']
  linear_combination -hdefect

/-- At squared prime-log nodes, the FE-paired Schur residual is the corresponding node
polynomial's constant term. -/
theorem finiteFEPairedPrimeSchurResidual_eq_nodePolynomialEvalZero {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) :
    finiteOriginSchurResidual (fun i => ((Real.log (p i) ^ 2 : ℝ) : ℂ)) 0 0 =
      (((negativeNodePolynomial (fun i => Real.log (p i) ^ 2)).eval
        (0 : ℝ) : ℝ) : ℂ) := by
  have hfR : Function.Injective (fun i => Real.log (p i) ^ 2) := by
    intro i j hij
    apply log_sq_nat_injective p hp hpinj
    simpa using congrArg Complex.ofReal hij
  simpa using finiteOriginSchurResidual_eq_nodePolynomialEvalZero hk
    (fun i => Real.log (p i) ^ 2) hfR

/-- The canonical FE-paired barycentric first-omitted defect is the negative squared-node Schur
residual. -/
theorem fePairedPrimeBarycentricFirstOmitted_eq_neg_schurResidual {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) :
    fePairedMoment (fun i => (Real.log (p i) : ℂ))
        (fePairedPrimeBarycentricCoefficient p) (2 * k + 1) -
      archimedeanDerivationMoment (2 * k + 1) =
        -finiteOriginSchurResidual
          (fun i => ((Real.log (p i) ^ 2 : ℝ) : ℂ)) 0 0 := by
  rw [finiteFEPairedPrimeSchurResidual_eq_nodePolynomialEvalZero hk p hp hpinj]
  exact fePairedPrimeDerivationInterpolation_firstOmitted_eq hk p
    (fePairedPrimeBarycentricCoefficient p)
    (fePairedPrimeBarycentricCoefficient_odd_match p hp hpinj)

/-- The FE-paired Schur residual is the alternating signed product of squared prime logarithms. -/
theorem finiteFEPairedPrimeSchurResidual_eq_signedLogSqProduct {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) :
    finiteOriginSchurResidual (fun i => ((Real.log (p i) ^ 2 : ℝ) : ℂ)) 0 0 =
      (((∏ i : Fin k, -(Real.log (p i) ^ 2)) : ℝ) : ℂ) := by
  rw [finiteFEPairedPrimeSchurResidual_eq_nodePolynomialEvalZero hk p hp hpinj,
    negativeNodePolynomial_eval_zero_eq_prod_neg]

end RHTower
