import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularSpacetimeCoordinates
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCovectorModular

/-! The actual reconstructed mixed metric and its complete source transform by both tensor indices. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMGlobalAngularResponse D4BMMetricReconstruction
noncomputable section

/-- Symmetric mixed metric blocks built from the actual angular covector. -/
def covectorBlock (T R : ℂ) (V : Covector) (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,T*V 0 z,T*V 1 z; 0,0,R*V 0 z,R*V 1 z;
    T*V 0 z,R*V 0 z,0,0; T*V 1 z,R*V 1 z,0,0]

/-- The covector pullback law supplies every component of the full mixed tensor law. -/
theorem covectorBlock_modular (A : SL(2,ℤ)) (z : UpperHalfPlane) (V : Covector)
    (hV : ∀ v, covectorAction V (coordinates (A • z)) ((1/(denom A z)^(2 : ℕ))*v) =
      covectorAction V (coordinates z) v) (T R : ℂ) :
    modularTensorPullback A z (covectorBlock T R V (coordinates (A • z))) =
      covectorBlock T R V (coordinates z) := by
  have h0 := hV 1
  have h1 := hV Complex.I
  simp only [covectorAction,mul_one,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero,zero_add,
    Complex.mul_I_re,Complex.mul_I_im,Complex.ofReal_neg] at h0 h1
  simp only [modularTensorPullback,modularJacobian]
  generalize 1/(denom A z)^(2 : ℕ) = c at h0 h1 ⊢
  simp only [sl_moeb] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [covectorBlock,Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals first | linear_combination T*h0 | linear_combination T*h1 |
    linear_combination R*h0 | linear_combination R*h1

/-- Actual tensor pullback preserves subtraction and fixed complex scaling. -/
theorem modularTensorPullback_combination (A : SL(2,ℤ)) (z : UpperHalfPlane) (c : ℂ)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    modularTensorPullback A z (fun i j => M i j-c*N i j) =
      fun i j => modularTensorPullback A z M i j-c*modularTensorPullback A z N i j := by
  change (modularJacobian A z).transpose*(M-c • N)*modularJacobian A z =
    (modularJacobian A z).transpose*M*modularJacobian A z-
      c • ((modularJacobian A z).transpose*N*modularJacobian A z)
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]

/-- Actual tensor pullback preserves the full sum of mixed source channels. -/
theorem modularTensorPullback_add (A : SL(2,ℤ)) (z : UpperHalfPlane)
    (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    modularTensorPullback A z (M+N) = modularTensorPullback A z M+modularTensorPullback A z N := by
  simp only [modularTensorPullback,Matrix.mul_add,Matrix.add_mul]

/-- The actual radial stream metric has the original modular tensor transformation law. -/
theorem streamMetricField_modular (A : SL(2,ℤ)) (z : UpperHalfPlane) (V : Covector)
    (hV : ∀ v, covectorAction V (coordinates (A • z)) ((1/(denom A z)^(2 : ℕ))*v) =
      covectorAction V (coordinates z) v) (w a : ℂ) (square : Bool) (t r : ℝ) :
    modularTensorPullback A z (streamMetricField w a square V (spacetimePoint t r (A • z))) =
      streamMetricField w a square V (spacetimePoint t r z) := by
  change modularTensorPullback A z
    (covectorBlock (streamTimeBlock w a square (spacetimePoint t r z))
      (streamRadiusBlock w a square (spacetimePoint t r z)) V (coordinates (A • z))) =
    covectorBlock (streamTimeBlock w a square (spacetimePoint t r z))
      (streamRadiusBlock w a square (spacetimePoint t r z)) V (coordinates z)
  exact covectorBlock_modular A z V hV _ _

/-- The complete constructed forced metric transforms as an actual tensor on the modular geometry. -/
theorem forcedMetricField_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (A : SL(2,ℤ)) (t r : ℝ) (z : UpperHalfPlane) :
    modularTensorPullback A z (forcedMetricField q branch a (spacetimePoint t r (A • z))) =
      forcedMetricField q branch a (spacetimePoint t r z) := by
  unfold forcedMetricField
  rw [modularTensorPullback_combination,
    streamMetricField_modular A z _ (fullAngularCovector_modular q branch A z),
    streamMetricField_modular A z _ (fullSquareCovector_modular q A z)]

private theorem source_blocks (q : XiZeroCopy) (branch : Bool) (r B : ℂ) (z : Point) :
    literalMixedSource q branch r B z =
      covectorBlock (B^(2 : ℕ)*D4BMQuadraticMixedSource.timeSquare (physicalRate q branch) r)
        (B^(2 : ℕ)*D4BMQuadraticMixedSource.radialSquare (physicalRate q branch) r) (fullSquareCovector q) z+
      covectorBlock (B^(2 : ℕ)*D4BMQuadraticMixedSource.timeGradient (physicalRate q branch) r)
        (B^(2 : ℕ)*D4BMQuadraticMixedSource.radialGradient (physicalRate q branch) r) (fullGradientCovector q branch) z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [literalMixedSource,covectorBlock] <;> ring

/-- The complete original mixed Einstein source has the same actual tensor transformation law. -/
theorem literalMixedSource_modular (q : XiZeroCopy) (branch : Bool) (r B : ℂ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (literalMixedSource q branch r B (coordinates (A • z))) =
      literalMixedSource q branch r B (coordinates z) := by
  rw [source_blocks,modularTensorPullback_add,
    covectorBlock_modular A z _ (fullSquareCovector_modular q A z),
    covectorBlock_modular A z _ (fullGradientCovector_modular q branch A z),← source_blocks]

end
end RHTower.D4BMModularCore
