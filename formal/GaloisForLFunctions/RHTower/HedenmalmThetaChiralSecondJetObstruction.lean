import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.RHTower.HedenmalmThetaEscapingNonlocalChiralPolarization
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDeterminantIdentity
import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux

/-!
# Unconditional quadratic-jet no-go for positive theta-source chiralization

The escaping nonlocal positive polarizations have a forced compact-open limit: the regularized
determinant of the Hermitian dilation of the fixed signed theta kernel.  This file proves that
forced limit is not centered `XiC`.

The obstruction is source-side and occurs before any zero location.  The original theta determinant
has quadratic jet `-tr(K²)/2`; positive Hermitian dilation has jet `-‖K‖²_HS`.  Cauchy--Schwarz
bounds the first trace by one copy of the source energy, while dilation demands two.  Since the
theta source is nonzero (forced by strict central Xi curvature), the jets are strictly separated.
Consequently the real-divisor finite family unconditionally fails to converge to `XiC`.
-/

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt
open Filter

noncomputable section

/-- The fixed signed theta kernel is nonzero, detected without using any Xi zero: otherwise the
exact determinant identity would make Xi constant, contradicting its strict central curvature. -/
theorem neg_thetaKernelMatrix_ne_zero : (-thetaKernelMatrix) ≠ 0 := by
  intro hzero
  have hXi : XiC = fun _ => XiC 0 := by
    funext z
    have h := thetaSourceEntireDet2_eq_XiC_normalized z
    rw [thetaSourceEntireDet2, hzero, entireDet2_zero_kernel] at h
    field_simp [XiC_zero_ne] at h
    exact h.symm
  have hsecond : deriv (deriv XiC) 0 = 0 := by
    rw [hXi]
    simp
  have hneg := RHTower.XiC_secondDeriv_div_center_re_neg
  rw [hsecond] at hneg
  simp at hneg

/-- The forced positive dilation has a strictly separated quadratic determinant jet. -/
theorem thetaSourceChiral_quadraticTaylorGap_pos :
    0 < ‖taylorCoeff (entireDet2 thetaSourceChiralLimitKernel) 2 -
      taylorCoeff thetaSourceEntireDet2 2‖ := by
  have henergy0 : hsNormSq (-thetaKernelMatrix) ≠ 0 := by
    intro hzero
    exact neg_thetaKernelMatrix_ne_zero
      ((hsNormSq_eq_zero_iff isHS_neg_thetaKernelMatrix).mp hzero)
  have henergy : 0 < hsNormSq (-thetaKernelMatrix) :=
    lt_of_le_of_ne (hsNormSq_nonneg _) (Ne.symm henergy0)
  have hfloor := half_hsNormSq_le_norm_taylorCoeff_dilation_sub
    isHS_neg_thetaKernelMatrix
  rw [thetaSourceChiralLimitKernel, thetaSourceEntireDet2]
  exact lt_of_lt_of_le (half_pos henergy) hfloor

/-- The forced positive Hermitian-dilation limit cannot be centered Xi. -/
theorem thetaSourceChiralEntireLimit_ne_XiC :
    thetaSourceChiralEntireLimit ≠ XiC := by
  intro hlimit
  have hdet :
      entireDet2 thetaSourceChiralLimitKernel =
        entireDet2 (-thetaKernelMatrix) := by
    funext z
    have hD := congrFun hlimit z
    have hK := thetaSourceEntireDet2_eq_XiC_normalized z
    rw [thetaSourceChiralEntireLimit] at hD
    rw [thetaSourceEntireDet2] at hK
    have hKscaled : XiC 0 * entireDet2 (-thetaKernelMatrix) z = XiC z := by
      rw [hK]
      field_simp [XiC_zero_ne]
    exact mul_left_cancel₀ XiC_zero_ne (hD.trans hKscaled.symm)
  rw [thetaSourceChiralLimitKernel] at hdet
  exact neg_thetaKernelMatrix_ne_zero
    ((entireDet2_sourceHermitianDilationKernel_eq_iff
      isHS_neg_thetaKernelMatrix).mp hdet)

/-- The real-divisor positive chiral family unconditionally misses Xi in compact-open topology. -/
theorem not_thetaSourceChiralXiCandidate_tendstoLocallyUniformly_XiC :
    ¬ TendstoLocallyUniformly thetaSourceChiralXiCandidate XiC atTop := by
  intro h
  exact thetaSourceChiralEntireLimit_ne_XiC
    (thetaSourceChiralXiCandidate_tendstoLocallyUniformly_XiC_iff_limit_eq.mp h)

end

end RHTower.HedenmalmThetaSource
