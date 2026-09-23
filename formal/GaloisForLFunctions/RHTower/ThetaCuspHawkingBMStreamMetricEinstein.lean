import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamMetricField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamForcedCurrent

/-! The full cosmological Einstein image of the actual stream metric. -/

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMVectorStream
noncomputable section

/-- Complete source tensor of the actual stream metric, with both current components retained. -/
def streamMetricTensor (w r B : ℂ) (square : Bool) (V : Covector) (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let T0 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*streamMasterFirst w r B square V 0 z
  let T1 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*streamMasterFirst w r B square V 1 z
  let R0 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*streamMaster w r B square V 0 z
  let R1 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*streamMaster w r B square V 1 z
  !![0,0,T0,T1; 0,0,R0,R1; T0,R0,0,0; T1,R1,0,0]

/-- All sixteen Einstein components are the actual master current curl of the reconstructed field. -/
theorem streamMetricField_einstein (w a : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (streamMetricField w a square V) p.val) (-3) i j =
      streamMetricTensor w (p.val 1) (D4BMFundamentalScalarMetric.envelope w a p.val) square V
        (angularPoint p.val) i j := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  rw [streamMetricField_jet w a square V p hV hD]
  unfold streamActualMetricJet
  rw [D4BMVectorStream.cosmological_component _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf i j]
  rfl

end
end RHTower.D4BMModularCore
