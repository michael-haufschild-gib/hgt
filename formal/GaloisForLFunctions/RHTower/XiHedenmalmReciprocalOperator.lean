import GaloisForLFunctions.RHTower.XiHedenmalmEigenbasis
import GaloisForLFunctions.FredholmDeterminantZeta
import GaloisForLFunctions.HilbertSchmidtTrace
import GaloisForLFunctions.HilbertSchmidtCompact

/-!
# The reciprocal Xi divisor operator and the Hedenmalm eigenbasis

The diagonal Hilbert--Schmidt kernel with entries `xiSpectralPoint q` inverse is defined on the
actual multiplicity-copy Xi divisor. Its represented operator is compact unconditionally, its
regularized determinant is the exact Xi canonical product on the determinant convergence disk,
and it is self-adjoint exactly when RH holds.

Under simplicity, the evaluated Hedenmalm theta eigenfunctions are its complete eigenfamily by
`XiHedenmalmEigenbasis`. The construction is divisor-indexed and therefore is a terminal
Hilbert--Polya model, not a source-side proof of RH. All route-bearing assertions below are closed
theorems over concrete objects; no spectral or positivity interface is assumed.
-/

open Complex
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- The multiplicity-exact reciprocal Xi diagonal kernel. -/
def xiReciprocalDiagonalKernel : XiZeroCopy × XiZeroCopy → ℂ :=
  diagMul (fun q => (xiSpectralPoint q)⁻¹)

theorem summable_norm_xiSpectralPoint_inv_sq :
    Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖ ^ 2) := by
  simpa [norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable

theorem isHS_xiReciprocalDiagonalKernel : IsHS xiReciprocalDiagonalKernel :=
  isHS_diagMul_infinite _ summable_norm_xiSpectralPoint_inv_sq

/-- The bounded reciprocal Xi operator on the complete multiplicity-copy evaluation carrier. -/
def xiReciprocalOperator :
    lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 :=
  toOperator isHS_xiReciprocalDiagonalKernel

theorem hsAdjoint_xiReciprocalDiagonalKernel_eq
    (hRH : RiemannHypothesis) :
    hsAdjoint xiReciprocalDiagonalKernel = xiReciprocalDiagonalKernel := by
  funext p
  rcases p with ⟨q, r⟩
  by_cases hqr : q = r
  · subst r
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    simp [hsAdjoint, xiReciprocalDiagonalKernel, diagMul, ht]
  · have hrq : r ≠ q := Ne.symm hqr
    simp [hsAdjoint, xiReciprocalDiagonalKernel, diagMul, hqr, hrq]

theorem xiReciprocalOperator_isSelfAdjoint_of_rh
    (hRH : RiemannHypothesis) : IsSelfAdjoint xiReciprocalOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [xiReciprocalOperator, adjoint_toOperator]
  exact toOperator_congr _ _ (hsAdjoint_xiReciprocalDiagonalKernel_eq hRH)

/-- The reciprocal Xi operator is compact without RH. -/
theorem xiReciprocalOperator_isCompact :
    IsCompactOperator xiReciprocalOperator := by
  exact (isHilbertSchmidt_toOperator isHS_xiReciprocalDiagonalKernel).isCompactOperator

theorem riemannHypothesis_of_xiReciprocalOperator_isSelfAdjoint
    (hself : IsSelfAdjoint xiReciprocalOperator) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hop : ContinuousLinearMap.adjoint xiReciprocalOperator = xiReciprocalOperator :=
    hself.adjoint_eq
  have hmatrix := congrArg matrixOf hop
  rw [matrixOf_adjoint, xiReciprocalOperator, matrixOf_toOperator] at hmatrix
  have hdiag := congrFun hmatrix (q, q)
  simp [hsAdjoint, xiReciprocalDiagonalKernel, diagMul] at hdiag
  have hstar : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
    have hinv := congrArg Inv.inv hdiag
    simpa [map_inv₀, xiSpectralPoint_ne_zero q] using hinv
  have him := congrArg Complex.im hstar
  have him0 : (xiSpectralPoint q).im = 0 := by
    have him' : -(xiSpectralPoint q).im = (xiSpectralPoint q).im := by
      simpa using him
    linarith
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simp [him0]

/-- Exact terminal Hilbert--Polya equivalence: the reciprocal Xi divisor operator is self-adjoint
if and only if RH holds. -/
theorem xiReciprocalOperator_isSelfAdjoint_iff_rh :
    IsSelfAdjoint xiReciprocalOperator ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiReciprocalOperator_isSelfAdjoint,
    xiReciprocalOperator_isSelfAdjoint_of_rh⟩

theorem xiReciprocalOperator_single (q : XiZeroCopy) :
    xiReciprocalOperator (lp.single 2 q (1 : ℂ)) =
      (xiSpectralPoint q)⁻¹ • lp.single 2 q (1 : ℂ) := by
  apply Subtype.ext
  funext r
  rw [xiReciprocalOperator, toOperator_single]
  by_cases hrq : r = q
  · subst r
    simp [xiReciprocalDiagonalKernel, diagMul]
  · simp [xiReciprocalDiagonalKernel, diagMul, hrq]

/-- Under simplicity, every evaluated Hedenmalm theta eigenfunction is an eigenvector of the
reciprocal Xi operator with the corresponding reciprocal spectral coordinate. -/
theorem xiReciprocalOperator_thetaEigen
    (hsimple : XiZerosSimple) (q : XiZeroCopy) :
    xiReciprocalOperator (xiThetaEigenEvaluationLp q) =
      (xiSpectralPoint q)⁻¹ • xiThetaEigenEvaluationLp q := by
  rw [xiThetaEigenEvaluationLp_eq_smul_single hsimple q,
    map_smul, xiReciprocalOperator_single, smul_smul, smul_smul]
  congr 1
  ring

/-- On its convergence disk, the regularized determinant of the reciprocal operator is exactly
the multiplicity-exact Xi canonical product. -/
theorem fredholmDet_xiReciprocalDiagonalKernel_eq_xiCanonicalProduct
    (r : ℝ) (hr : r * hsNorm xiReciprocalDiagonalKernel < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet xiReciprocalDiagonalKernel z = xiCanonicalProduct z := by
  rw [xiReciprocalDiagonalKernel,
    fredholmDet_tprod_diagMul _ summable_norm_xiSpectralPoint_inv_sq r hr z hz,
    xiCanonicalProduct, canonicalProductE1Indexed]
  apply tprod_congr
  intro q
  simp [weierstrassE1, div_eq_mul_inv]

end

end RHTower
