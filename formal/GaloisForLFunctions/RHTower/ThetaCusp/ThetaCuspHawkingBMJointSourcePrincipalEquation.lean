import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGreenTortoiseJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceResidualCoefficients

/-! Actual radial jets and reduced equations for the three principal cusp corrections. -/
open Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMModularCore
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def principalDifferenceFirst (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (i : Fin 3) (t : ℝ) : ℂ :=
  tortoiseGreenFirst w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) T t-
    radialLiftFirst (physicalRate q branch) w a T t*principalAmplitude q i

def principalDifferenceSecond (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (i : Fin 3) (t : ℝ) : ℂ :=
  tortoiseGreenSecond w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) T t-
    radialLiftSecond (physicalRate q branch) w a T t*principalAmplitude q i

theorem principalDifference_hasDerivAt (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    HasDerivAt (principalDifference q branch w a T i)
        (principalDifferenceFirst q branch w a T i t) t ∧
      HasDerivAt (principalDifferenceFirst q branch w a T i)
        (principalDifferenceSecond q branch w a T i t) t := by
  have hg := tortoiseGreen_hasDerivAt (hw i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) T t ht
  exact ⟨hg.1.sub ((radialLift_hasDerivAt _ _ _ _ t).mul_const _),
    hg.2.sub ((radialLiftFirst_hasDerivAt _ _ _ _ t).mul_const _)⟩

theorem principalDifference_secondDerivative (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    deriv (deriv (principalDifference q branch w a T i)) t =
      principalDifferenceSecond q branch w a T i t := by
  have he : deriv (principalDifference q branch w a T i) =ᶠ[𝓝 t]
      principalDifferenceFirst q branch w a T i := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (principalDifference_hasDerivAt q branch w a T hw i x hx).1.deriv
  rw [he.deriv_eq]
  exact (principalDifference_hasDerivAt q branch w a T hw i t ht).2.deriv

/-- The actual principal differences solve the squared-source radial equations. -/
theorem principalDifference_equation (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*principalDifference q branch w a T i t-
        deriv (deriv (principalDifference q branch w a T i)) t-
        (horizonCoordinate t:ℂ)*principalExponent q i*(principalExponent q i-1)*
          principalDifference q branch w a T i t =
      reducedCoefficient (physicalRate q branch) w a T t*principalAmplitude q i := by
  have he := tortoiseGreen_equation (hw i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) T t ht
  rw [principalFrequency_parameter] at he
  rw [principalDifference_secondDerivative q branch w a T hw i t ht]
  dsimp only [principalDifference,principalDifferenceSecond]
  dsimp [originalForcing,principalGradient,reducedCoefficient,reducedPolynomial,
    radialLift,radialLiftSecond,horizonCoordinate] at he ⊢
  push_cast at he ⊢
  linear_combination he

end
end RHTower.D4BMJointSource
