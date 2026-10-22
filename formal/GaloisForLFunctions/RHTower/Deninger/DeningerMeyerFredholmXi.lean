import GaloisForLFunctions.RHTower.Deninger.DeningerHasseResolventTriangular
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerClosedHasseGenerator
import GaloisForLFunctions.RHTower.XiOrderedPrimeDeterminantNormalForm
import GaloisForLFunctions.RHTower.XiDeterminantLogarithmicSingularValueLaw

/-! # Exact Xi determinant of the closed original Meyer generator

The compact operator is the inverse of the graph closure of the literal
centered source generator. Its entire determinant is XiC normalized at zero.
The proof retains all Jordan orders and gives full algebraic multiplicity;
no self-adjointness, simplicity, or RH premise occurs.
-/

noncomputable section
open Complex HilbertSchmidt Set
open GaloisForLFunctions.HTGeometry

namespace RHTower
open scoped Classical

private def xiInverseDiagonalKernel : XiZeroCopy × XiZeroCopy → ℂ :=
  diagMul fun q => (xiSpectralPoint q)⁻¹

private theorem xiInverseDiagonalKernel_isHS : IsHS xiInverseDiagonalKernel :=
  isHS_diagMul_infinite _ summable_norm_inv_xiSpectralPoint_sq

private theorem xiInverseDiagonalKernel_local (r : ℝ)
    (hr : r * hsNorm xiInverseDiagonalKernel < 1) (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
    fredholmDet xiInverseDiagonalKernel z = XiC z / XiC 0 := by
  rw [xiInverseDiagonalKernel,
    fredholmDet_tprod_diagMul _ summable_norm_inv_xiSpectralPoint_sq r hr z hz]
  have hp := xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd (mem_univ z)
  rw [← xiCanonicalProduct_eq_XiC_div_zero]
  simpa only [weierstrassE1, div_eq_mul_inv] using hp.tprod_eq

private theorem xiInverseDiagonalKernel_normalized :
    IsRegularizedDet xiInverseDiagonalKernel (fun z => XiC z / XiC 0) := by
  refine ⟨?_, detRadius xiInverseDiagonalKernel, detRadius_pos _, detRadius_mul_hsNorm_lt _, ?_⟩
  · have hXi : Differentiable ℂ XiC := by
      rw [← differentiableOn_univ]
      exact XiC_analytic.differentiableOn
    exact hXi.div_const _
  · intro z hz
    exact (xiInverseDiagonalKernel_local _ (detRadius_mul_hsNorm_lt _) z hz).symm

/-- The entire source determinant, defined from the actual source resolvent matrix. -/
def deningerMeyerFredholmXi : ℂ → ℂ := entireDet2 deningerMeyerHasseResolventKernel

theorem differentiable_deningerMeyerFredholmXi : Differentiable ℂ deningerMeyerFredholmXi :=
  differentiable_entireDet2 deningerMeyerHasseResolventKernel_isHS

/-- **Exact source determinant identity on the entire complex plane.** -/
theorem deningerMeyerFredholmXi_eq (z : ℂ) :
    deningerMeyerFredholmXi z = XiC z / XiC 0 := by
  have htri := deningerMeyerHasseResolventKernel_triangular.entireDet2_eq_diagonal
  have hdiag : (fun q => deningerMeyerHasseResolventKernel (q, q)) =
      fun q => (xiSpectralPoint q)⁻¹ := funext deningerMeyerHasseResolventKernel_diagonal
  rw [hdiag] at htri
  have hD := (isRegularizedDet_entireDet2 xiInverseDiagonalKernel_isHS).unique
    xiInverseDiagonalKernel_normalized
  exact (congrFun htri z).trans (congrFun hD z)

/-- Every zero and its multiplicity belong to the genuine source resolvent. -/
theorem deningerMeyerFredholmXi_zero_iff (z : ℂ) :
    deningerMeyerFredholmXi z = 0 ↔ XiC z = 0 := by
  rw [deningerMeyerFredholmXi_eq, div_eq_zero_iff]
  simp only [XiC_zero_ne_zero, or_false]

/-- Full Xi analytic multiplicity is the algebraic multiplicity of the
inverse of the original closed generator, including nontrivial Jordan blocks. -/
theorem deningerMeyerHasseResolvent_algebraicMultiplicity (rho : XiDivisorSupport) :
    analyticOrderAt XiC (xiSpectralPointSupport rho) =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (deningerMeyerHasseResolvent : DeningerArithmeticJetHilbert →ₗ[ℂ]
          DeningerArithmeticJetHilbert) (xiSpectralPointSupport rho)⁻¹) : ℕ∞) := by
  have hXi (z : ℂ) : XiC z = XiC 0 * entireDet2 deningerMeyerHasseResolventKernel z := by
    change XiC z = XiC 0 * deningerMeyerFredholmXi z
    rw [deningerMeyerFredholmXi_eq]
    field_simp [XiC_zero_ne_zero]
  have h := analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_of_exactDeterminant
    deningerMeyerHasseResolventKernel_isHS (fun _ => XiC 0) (by fun_prop)
    (fun _ => XiC_zero_ne_zero) hXi (XiC_xiSpectralPointSupport_eq_zero rho)
  rw [toOperator_deningerMeyerHasseResolventKernel] at h
  exact h

end RHTower
