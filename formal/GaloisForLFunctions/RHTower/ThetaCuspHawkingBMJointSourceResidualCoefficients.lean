import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGradientReduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalData

/-! Every radial coefficient of the exact cusp-subtracted source is admitted on the full tortoise half-line. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMLaplaceRadial
noncomputable section

/-- The explicit full-square lift has an actual L² radial coefficient. -/
theorem radialLift_memLp (s w a T : ℂ) (hw : 0 < w.re) :
    MemLp (radialLift s w a T) 2 radialMeasure := by
  have h := sourceAmplitude_profile_memLp s w a T hw (fun u => (-s*(s-1)/4)*(u:ℂ)^(3 : ℕ))
    (by fun_prop)
  convert! h using 1
  ext t
  dsimp [radialLift]
  ring

/-- The exact reduced source coefficient, with all differentiated amplitude terms, is in L². -/
theorem reducedCoefficient_memLp (s w a T : ℂ) (hw : 0 < w.re) :
    MemLp (reducedCoefficient s w a T) 2 radialMeasure :=
  sourceAmplitude_profile_memLp s w a T hw (fun u => reducedPolynomial s w u)
    (by unfold reducedPolynomial liftSecondPolynomial amplitudeRate; fun_prop)

def principalDifference (q : XiZeroCopy) (branch : Bool) (w a T : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  tortoiseGreen w (principalFrequency q i) (physicalRate q branch) a
      (principalAmplitude q i) (principalGradient q branch i) T t-
    radialLift (physicalRate q branch) w a T t*principalAmplitude q i

/-- The radial coefficient multiplying the entire angular cutoff commutator. -/
def cutoffRadialCoefficient (q : XiZeroCopy) (branch : Bool) (w a T : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  (horizonCoordinate t:ℂ)*principalDifference q branch w a T i t

/-- Genuine endpoint Green response minus the exact full-square lift is admitted before cutoff assembly. -/
theorem principalDifference_memLp (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) :
    MemLp (principalDifference q branch w a T i) 2 radialMeasure :=
  (tortoiseGreen_memLp (hw i) _ _ _ _ _).sub
    ((radialLift_memLp _ _ _ _ (principalChamber_re_pos hw)).mul_const _)

/-- Every complete cutoff coefficient is in the actual radial L² space. -/
theorem cutoffRadialCoefficient_memLp (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) :
    MemLp (cutoffRadialCoefficient q branch w a T i) 2 radialMeasure := by
  have hd := principalDifference_memLp q branch w a T hw i
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hz : Continuous (fun t => (horizonCoordinate t:ℂ)) := by unfold horizonCoordinate; fun_prop
  apply MemLp.of_le hd (hz.aestronglyMeasurable.mul hd.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  have hb := horizonCoordinate_interior t ht
  change ‖(horizonCoordinate t:ℂ)*principalDifference q branch w a T i t‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hb.2.le

end
end RHTower.D4BMJointSource
