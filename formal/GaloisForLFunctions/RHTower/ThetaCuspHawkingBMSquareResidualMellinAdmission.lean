import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareResidualModularBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularStripPowerAdmission

/-! The actual modular source has an absolutely convergent Mellin seed in the full right half-plane. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMJointSource
open D4BMModularCore
noncomputable section

def residualMellinSeed (q : XiZeroCopy) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im:ℂ)^s*globalSquareResidual q z

theorem residualMellinSeed_periodic (q : XiZeroCopy) (s : ℂ) (n : ℤ) (z : UpperHalfPlane) :
    residualMellinSeed q s (T^n • z) = residualMellinSeed q s z := by
  unfold residualMellinSeed
  rw [ModularGroup.im_T_zpow_smul]
  congr 1
  exact globalSquareResidual_invariant q (cuspTranslation n) z

/-- All strip convergence obligations are discharged for every original Xi residual. -/
theorem residualMellinSeed_integrable (q : XiZeroCopy) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    IntegrableOn (residualMellinSeed q P.s) modularStrip volume := by
  obtain ⟨C,hC,hb⟩ := globalSquareResidual_bounded q
  obtain ⟨D,hD,hd⟩ := globalSquareResidual_strip_weighted_bound q P.s
  have hc : Continuous (residualMellinSeed q P.s) :=
    ((Complex.continuous_ofReal_cpow_const (by linarith [P.re_gt_one])).comp
      UpperHalfPlane.continuous_im).mul (globalSquareResidual_smooth q).continuous
  apply modularStrip_integrable_of_two_bounds _ hc P.s.re C D P.re_gt_one
  · intro z _ _
    rw [residualMellinSeed,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos]
    exact (mul_le_mul_of_nonneg_left (hb z) (Real.rpow_nonneg z.im_pos.le _)).trans_eq (mul_comm _ _)
  · intro z hz hy
    exact hd z hz (by linarith)

end
end RHTower.D4BMJointSource
