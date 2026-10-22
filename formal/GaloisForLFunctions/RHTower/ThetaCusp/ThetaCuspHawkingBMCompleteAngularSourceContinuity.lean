import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteAngularProjectionMeromorphy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalLaplaceClassical

/-! The complete physical angular source has its actual continuous interior radial density. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All continued cutoff channels are continuous on the original radial interior, even at connection zeros. -/
theorem continuedCutoffRadialCoefficient_continuousOn (q : XiZeroCopy) (branch : Bool)
    (w a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re) (i : Fin 3) :
    ContinuousOn (continuedCutoffRadialCoefficient q branch w a i) (Iio (0:ℝ)) := by
  intro t ht
  exact ((Complex.continuous_ofReal.comp horizonCoordinate_continuous).continuousAt.mul
    (continuedPrincipalDifference_hasDerivAt q branch w a hw hwr i t ht).1.continuousAt).continuousWithinAt

/-- The literal complete angular integral has a continuous radial density with all four channels retained. -/
theorem continuedAngularSourceProjection_continuousOn (q : XiZeroCopy) (branch : Bool)
    (u a w : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re) :
    ContinuousOn (continuedAngularSourceProjection q branch u a w) (Iio (0:ℝ)) := by
  have he : continuedAngularSourceProjection q branch u a w = fun t =>
      reducedCoefficient (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
        scalarResidualPeriod q u+
      ∑ i : Fin 3, continuedCutoffRadialCoefficient q branch w a i t*
        scalarCutoffPeriod u (principalExponent q i) :=
    funext (continuedAngularSourceProjection_eq q branch u a w)
  rw [he]
  exact ((reducedCoefficient_continuous _ _ _ _).continuousOn.mul continuousOn_const).add
    (continuousOn_finsetSum _ (fun i _ =>
      (continuedCutoffRadialCoefficient_continuousOn q branch w a hw hwr i).mul continuousOn_const))

/-- The original radial source class is represented by that same complete angular integral. -/
theorem continuedAngularSourceL2_ae (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    continuedAngularSourceL2 q branch u a w =ᵐ[radialMeasure]
      continuedAngularSourceProjection q branch u a w := by
  unfold continuedAngularSourceL2
  rw [l2Family_eq_toLp _ _ w (continuedAngularSourceProjection_memLp q branch u a w hw hwr)]
  exact (continuedAngularSourceProjection_memLp q branch u a w hw hwr).coeFn_toLp

end
end RHTower.D4BMJointSource
