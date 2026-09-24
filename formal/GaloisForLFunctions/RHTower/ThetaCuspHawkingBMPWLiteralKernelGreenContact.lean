import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularPhysicalAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformalCoordinateLines
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWFullNativeAdjointSymmetrizer

/-!
# Literal full/native kernel angular contact

The original direct-minus-image full-circle kernel obeys the forced physical
angular equation with the original native causal kernel. Pairing that exact
equation with the source vertex exposes the mixed full/native Green bulk term.
No angular boundary, cap limit, or oriented incidence cancellation is assumed.
-/

namespace RHTower.D4BMPWLiteralKernelGreenContact

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMFullAngularCircleJointJets
open D4BMFullAngularPhysicalAction D4BMAngularSeries D4BMJointConformal
open D4BMFullAngularReconstruction D4BMNativeCircle
open D4BMGlobalAngularResponse D4BMCausalKernel
open D4BMPWFullNativeAdjointSymmetrizer
open scoped ContDiff

noncomputable section
set_option autoImplicit false

private theorem physicalMean_scalarLaplacian (q : XiZeroCopy) (branch : Bool) (d : ℝ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    scalarLaplacian (physicalMean q branch d) z =
      physicalMeanAction q branch d (z 0) (z 1) := by
  rw [scalarLaplacian_eq _ z hz]
  unfold physicalMeanAction
  have hs : ContDiffAt ℝ 2 (physicalMean q branch d) z :=
    (physicalMean_contDiffAt q branch d z hz).of_le (by decide)
  rw [coordinate_secondDerivative _ z 0 hs,
    coordinate_secondDerivative _ z 1 hs]
  rfl

private theorem physicalMean_hyperbolicLaplacian (q : XiZeroCopy)
    (branch : Bool) (d : ℝ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (physicalMean q branch d) z =
      parameter q branch *
        (physicalMean q branch d z + physicalNativeMean q d (z 0) (z 1)) := by
  have he := physicalMean_action_equation q branch d (z 0) (z 1) hz
  have hzv : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
  rw [hzv] at he
  rw [← he]
  rw [← physicalMean_scalarLaplacian q branch d z hz]
  rw [scalarLaplacian_eq _ z hz]
  rfl

private def directCoeff (h x y : ℝ) : ℂ :=
  if |x-y| ≤ h then 1/2 else 0

private def imageCoeff (h x y : ℝ) : ℂ :=
  if |x+y| ≤ h then -(1/2) else 0

/-- The unaltered direct-minus-image full-circle kernel in physical height. -/
def physicalKernel (q : XiZeroCopy) (branch : Bool)
    (h x y : ℝ) (z : Fin 2 → ℝ) : ℂ :=
  angularDirichletKernel q branch h x y (z 0) (Real.log (z 1))

private theorem physicalKernel_decomp (q : XiZeroCopy) (branch : Bool)
    (h x y : ℝ) :
    physicalKernel q branch h x y =
      fun z => directCoeff h x y *
          physicalMean q branch (Real.arcosh (invariant h x y)) z +
        imageCoeff h x y *
          physicalMean q branch (Real.arcosh (invariant h x (-y))) z := by
  funext z
  by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h <;>
    simp [physicalKernel,angularDirichletKernel,directCoeff,imageCoeff,
      physicalMean,hd,hi,div_eq_mul_inv] <;> ring

private theorem nativeKernel_decomp (q : XiZeroCopy) (h x y : ℝ)
    (z : Fin 2 → ℝ) :
    nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1)) =
      directCoeff h x y *
          physicalNativeMean q (Real.arcosh (invariant h x y)) (z 0) (z 1) +
        imageCoeff h x y *
          physicalNativeMean q (Real.arcosh (invariant h x (-y))) (z 0) (z 1) := by
  by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h <;>
    simp [nativeDirichletCausalKernel,nativeRiemannKernel,angularKernel,
      physicalNativeMean,directCoeff,imageCoeff,hd,hi,div_eq_mul_inv] <;> ring

/-- The original causal gates do not impair angular smoothness. -/
theorem physicalKernel_smooth (q : XiZeroCopy) (branch : Bool)
    (h x y : ℝ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (physicalKernel q branch h x y) z := by
  rw [physicalKernel_decomp]
  exact (contDiffAt_const.mul
    (physicalMean_contDiffAt q branch _ z hz)).add
      (contDiffAt_const.mul (physicalMean_contDiffAt q branch _ z hz))

/-- The literal direct/image full kernel has exactly the actual native causal
kernel as its angular forcing, with no mode or gate replacement. -/
theorem physicalKernel_hyperbolicLaplacian (q : XiZeroCopy)
    (branch : Bool) (h x y : ℝ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (physicalKernel q branch h x y) z =
      parameter q branch *
        (physicalKernel q branch h x y z +
          nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1))) := by
  let d₁ := Real.arcosh (invariant h x y)
  let d₂ := Real.arcosh (invariant h x (-y))
  have hs₁ : ContDiffAt ℝ 2 (physicalMean q branch d₁) z :=
    (physicalMean_contDiffAt q branch d₁ z hz).of_le (by decide)
  have hs₂ : ContDiffAt ℝ 2 (physicalMean q branch d₂) z :=
    (physicalMean_contDiffAt q branch d₂ z hz).of_le (by decide)
  calc
    hyperbolicLaplacian (physicalKernel q branch h x y) z =
        directCoeff h x y * hyperbolicLaplacian (physicalMean q branch d₁) z +
          imageCoeff h x y * hyperbolicLaplacian (physicalMean q branch d₂) z := by
      rw [physicalKernel_decomp]
      rw [hyperbolicLaplacian_add (contDiffAt_const.mul hs₁)
        (contDiffAt_const.mul hs₂), hyperbolicLaplacian_const_mul hs₁,
        hyperbolicLaplacian_const_mul hs₂]
    _ = parameter q branch *
          (physicalKernel q branch h x y z +
            nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1))) := by
      rw [physicalMean_hyperbolicLaplacian q branch d₁ z hz,
        physicalMean_hyperbolicLaplacian q branch d₂ z hz,
        show physicalKernel q branch h x y z = _ from congrFun
          (physicalKernel_decomp q branch h x y) z,
        nativeKernel_decomp]
      ring

theorem physicalKernel_scalarLaplacian (q : XiZeroCopy)
    (branch : Bool) (h x y : ℝ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    scalarLaplacian (physicalKernel q branch h x y) z =
      parameter q branch *
        (physicalKernel q branch h x y z +
          nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1))) := by
  rw [scalarLaplacian_eq _ z hz]
  exact physicalKernel_hyperbolicLaplacian q branch h x y z hz

/-- Exact local Green bulk for the actual source vertex and the unaltered
causal kernel. This mixed full/native contact is what any finite-domain
angular boundary or incidence argument must transport. -/
theorem physicalKernel_source_green_contact (q : XiZeroCopy) (branch : Bool)
    (h x y : ℝ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    fullAngularField q branch z *
        scalarLaplacian (physicalKernel q branch h x y) z -
      physicalKernel q branch h x y z *
        scalarLaplacian (fullAngularField q branch) z =
      parameter q branch *
        (fullAngularField q branch z *
            nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1)) -
          fullSquarePotential q z * physicalKernel q branch h x y z) := by
  have hK : scalarLaplacian (physicalKernel q branch h x y) z -
      parameter q branch * (physicalKernel q branch h x y z +
        nativeDirichletCausalKernel q h x y (z 0) (Real.log (z 1))) = 0 := by
    rw [physicalKernel_scalarLaplacian q branch h x y z hz]
    ring
  have hH := physical_source_full_dual_zero q branch z hz
  linear_combination (fullAngularField q branch z) * hK -
    (physicalKernel q branch h x y z) * hH

end
end RHTower.D4BMPWLiteralKernelGreenContact
