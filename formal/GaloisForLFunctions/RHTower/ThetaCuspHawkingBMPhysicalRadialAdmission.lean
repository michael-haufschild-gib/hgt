import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightGraphBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseRadialEquation

/-! Height admission of the original response's actual radial derivative. -/
open Complex MeasureTheory
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The radial component of the original completed response inherits the full source's height admission. -/
theorem jointWaveResponse_radial_height_memLp (w : ℂ) (hw : 0 < w.re)
    (hd : 3/2 < w.re) (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*
      ((jointWaveResponse w hw F : JointEnergySpace) 1) p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  obtain ⟨C,_,hC⟩ := jointWaveResponse_cuspGraph_uniform w hw hd F (cuspWeight_memLp_of_height F hF)
  apply height_memLp_of_cuspWeight
  apply cuspWeightLimit_memLp_of_uniform _ C
  intro N hN
  have hc := PiLp.norm_apply_le (jointCuspWeight N hN (jointWaveResponse w hw F) : JointEnergySpace) 1
  exact hc.trans (hC N hN)

end
end RHTower.D4BMJointWave

namespace RHTower.D4BMJointSource
open D4BMJointWave
noncomputable section
set_option autoImplicit false

/-- The actual complete cusp response has a height-admitted radial derivative, with no derivative-norm premise. -/
theorem completeCuspResponse_radial_height_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*
      ((jointWaveResponse w hw (continuedCuspResidualL2 q branch a w) : JointEnergySpace) 1) p)
      2 (radialMeasure.prod D4BMModularCore.measure) :=
  jointWaveResponse_radial_height_memLp w hw hd _ (continuedCuspResidualL2_height_memLp q branch w a hwi hwr)

end
end RHTower.D4BMJointSource
