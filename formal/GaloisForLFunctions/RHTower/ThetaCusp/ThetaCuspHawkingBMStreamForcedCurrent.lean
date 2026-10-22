import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamAngularJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamRadialProfiles

/-! The retained forced master current and its actual radial derivative. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMVectorStream D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section

/-- The full master expression with its actual angular and radial slots. -/
def streamMaster (w r B : ℂ) (square : Bool) (V : Covector) (k : Fin 2) (z : Point) : ℂ :=
  master w r (streamRadialValue w r B square) (streamRadialFirst w r B square)
    (streamRadialSecond w r B square) (V k z) (streamAngularOperator V k z)

/-- Its complete radial derivative, including the third derivative required by the metric. -/
def streamMasterFirst (w r B : ℂ) (square : Bool) (V : Covector) (k : Fin 2) (z : Point) : ℂ :=
  masterFirst w r (streamRadialValue w r B square) (streamRadialFirst w r B square)
    (streamRadialSecond w r B square) (streamRadialThird w r B square) (V k z) (streamAngularOperator V k z)

/-- Differentiating the full two-factor master defect retains exactly the original current derivative. -/
theorem masterFirst_resolvent_defect (s r B J K A D : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    masterFirst (2*s) r (streamRadialValue (2*s) r (B^(2 : ℕ)) false)
      (streamRadialFirst (2*s) r (B^(2 : ℕ)) false) (streamRadialSecond (2*s) r (B^(2 : ℕ)) false)
      (streamRadialThird (2*s) r (B^(2 : ℕ)) false) A D -
    (s*(s-1)/4)*masterFirst (2*s) r (streamRadialValue (2*s) r (B^(2 : ℕ)) true)
      (streamRadialFirst (2*s) r (B^(2 : ℕ)) true) (streamRadialSecond (2*s) r (B^(2 : ℕ)) true)
      (streamRadialThird (2*s) r (B^(2 : ℕ)) true) J (2*(s+1)*(s+2)*J+2*K) -
    2*currentFirst s r B J K =
    (B^(2 : ℕ)*(2*s)/(r*(r^(2 : ℕ)-1)))*(D-(2*s+1)*(2*s+2)*A-2*(s+1)*(2*s+1)*J) := by
  dsimp [masterFirst,streamRadialValue,streamRadialFirst,streamRadialSecond,streamRadialThird,
    currentFirst,current]
  field_simp [hr,hf]
  ring

private theorem exterior_radius (p : D4BMBackground.ExteriorPoint) :
    (p.val 1 : ℂ) ≠ 0 ∧ (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
  constructor
  · exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  · exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)

/-- The original current is produced by the full actual angular fields and both radial factors. -/
theorem forced_stream_master (q : XiZeroCopy) (branch : Bool) (p : D4BMBackground.ExteriorPoint)
    (B : ℂ) (k : Fin 2) :
    let s := physicalRate q branch
    let z := angularPoint p.val
    streamMaster (2*s) (p.val 1) (B^(2 : ℕ)) false (fullAngularCovector q branch) k z -
      (s*(s-1)/4)*streamMaster (2*s) (p.val 1) (B^(2 : ℕ)) true (fullSquareCovector q) k z =
      2*current s (p.val 1) B (fullSquareCovector q k z) (fullGradientCovector q branch k z) := by
  dsimp only
  have h := master_resolvent_defect (physicalRate q branch) (p.val 1) B
    (fullSquareCovector q k (angularPoint p.val)) (fullGradientCovector q branch k (angularPoint p.val))
    (fullAngularCovector q branch k (angularPoint p.val))
    (streamAngularOperator (fullAngularCovector q branch) k (angularPoint p.val))
    (exterior_radius p).1 (exterior_radius p).2
  rw [streamAngularOperator_response q branch _ p.property.2 k,parameter_physicalRate] at h
  dsimp [resolventParameter] at h
  have hz := streamAngularOperator_square q branch (angularPoint p.val) p.property.2 k
  dsimp [streamMaster,streamRadialValue,streamRadialFirst,streamRadialSecond]
  rw [hz,streamAngularOperator_response q branch _ p.property.2 k,parameter_physicalRate]
  dsimp [resolventParameter]
  linear_combination h

/-- The temporal Einstein source uses the actual full radial derivative of the same current. -/
theorem forced_stream_masterFirst (q : XiZeroCopy) (branch : Bool) (p : D4BMBackground.ExteriorPoint)
    (B : ℂ) (k : Fin 2) :
    let s := physicalRate q branch
    let z := angularPoint p.val
    streamMasterFirst (2*s) (p.val 1) (B^(2 : ℕ)) false (fullAngularCovector q branch) k z -
      (s*(s-1)/4)*streamMasterFirst (2*s) (p.val 1) (B^(2 : ℕ)) true (fullSquareCovector q) k z =
      2*currentFirst s (p.val 1) B (fullSquareCovector q k z) (fullGradientCovector q branch k z) := by
  dsimp only
  have h := masterFirst_resolvent_defect (physicalRate q branch) (p.val 1) B
    (fullSquareCovector q k (angularPoint p.val)) (fullGradientCovector q branch k (angularPoint p.val))
    (fullAngularCovector q branch k (angularPoint p.val))
    (streamAngularOperator (fullAngularCovector q branch) k (angularPoint p.val))
    (exterior_radius p).1 (exterior_radius p).2
  rw [streamAngularOperator_response q branch _ p.property.2 k,parameter_physicalRate] at h
  dsimp [resolventParameter] at h
  unfold streamMasterFirst
  rw [streamAngularOperator_square q branch _ p.property.2 k,
    streamAngularOperator_response q branch _ p.property.2 k,parameter_physicalRate]
  dsimp [resolventParameter]
  linear_combination h

end
end RHTower.D4BMModularCore
