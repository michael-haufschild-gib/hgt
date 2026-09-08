import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMForcedMetricTensor

/-! Exact frequency transport of the original master, with both radial profiles
and the actual angular response held fixed. This is an operator identity, not a
construction of a retarded inverse or a prescription for switching the source. -/

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMVectorStream D4BMQuadraticMixedSource D4BMMetricReconstruction
set_option autoImplicit false
noncomputable section

/-- The time frequency and the radial-profile rate are independent slots. -/
def frozenStreamMaster (w v r B : ℂ) (square : Bool) (V : Covector)
    (k : Fin 2) (z : Point) : ℂ :=
  master w r (streamRadialValue v r B square) (streamRadialFirst v r B square)
    (streamRadialSecond v r B square) (V k z) (streamAngularOperator V k z)

/-- The complete radial derivative with the same frozen radial-profile rate. -/
def frozenStreamMasterFirst (w v r B : ℂ) (square : Bool) (V : Covector)
    (k : Fin 2) (z : Point) : ℂ :=
  masterFirst w r (streamRadialValue v r B square) (streamRadialFirst v r B square)
    (streamRadialSecond v r B square) (streamRadialThird v r B square)
    (V k z) (streamAngularOperator V k z)

/-- The original mixed stream value, including its inverse-square factor. -/
def forcedStreamValue (q : XiZeroCopy) (branch : Bool) (r B : ℂ)
    (k : Fin 2) (z : Point) : ℂ :=
  let s := physicalRate q branch
  streamRadialValue (2*s) r (B^2) false * fullAngularCovector q branch k z -
    (s*(s-1)/4)*streamRadialValue (2*s) r (B^2) true * fullSquareCovector q k z

/-- Its original first radial derivative; both differentiated profiles are retained. -/
def forcedStreamFirst (q : XiZeroCopy) (branch : Bool) (r B : ℂ)
    (k : Fin 2) (z : Point) : ℂ :=
  let s := physicalRate q branch
  streamRadialFirst (2*s) r (B^2) false * fullAngularCovector q branch k z -
    (s*(s-1)/4)*streamRadialFirst (2*s) r (B^2) true * fullSquareCovector q k z

private theorem master_frequency (w v r H H1 H2 A D : ℂ) :
    master w r H H1 H2 A D = master v r H H1 H2 A D -
      (w^2-v^2)*r^2/(r^2-1)*H*A := by
  unfold master
  ring

private theorem masterFirst_frequency (w v r H H1 H2 H3 A D : ℂ) :
    masterFirst w r H H1 H2 H3 A D = masterFirst v r H H1 H2 H3 A D -
      (w^2-v^2)*(r^2/(r^2-1)*H1-2*r/(r^2-1)^2*H)*A := by
  unfold masterFirst
  ring

/-- At arbitrary time frequency, the original response produces its original
master source plus this exact radial defect. The source is not silently retuned. -/
theorem forced_stream_frequency (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (k : Fin 2) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    frozenStreamMaster w (2*s) r (B^2) false (fullAngularCovector q branch) k z -
      (s*(s-1)/4)*frozenStreamMaster w (2*s) r (B^2) true (fullSquareCovector q) k z =
      2*current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) -
        (w^2-(2*s)^2)*r^2/(r^2-1)*forcedStreamValue q branch r B k z := by
  dsimp only
  have h := forced_stream_master q branch p B k
  dsimp only at h
  unfold frozenStreamMaster
  rw [master_frequency w (2*physicalRate q branch),master_frequency w (2*physicalRate q branch)]
  change streamMaster _ _ _ _ _ _ _ - _ -
    _*(streamMaster _ _ _ _ _ _ _ - _) = _
  rw [sub_mul, mul_sub]
  dsimp only [forcedStreamValue]
  linear_combination h

/-- The frequency defect's full radial derivative retains the derivative of
r²/(r²-1); omitting it changes the original temporal Einstein component. -/
theorem forced_streamFirst_frequency (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (k : Fin 2) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    frozenStreamMasterFirst w (2*s) r (B^2) false (fullAngularCovector q branch) k z -
      (s*(s-1)/4)*frozenStreamMasterFirst w (2*s) r (B^2) true (fullSquareCovector q) k z =
      2*currentFirst s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) -
        (w^2-(2*s)^2)*(r^2/(r^2-1)*forcedStreamFirst q branch r B k z -
          2*r/(r^2-1)^2*forcedStreamValue q branch r B k z) := by
  dsimp only
  have h := forced_stream_masterFirst q branch p B k
  dsimp only at h
  unfold frozenStreamMasterFirst
  rw [masterFirst_frequency w (2*physicalRate q branch),masterFirst_frequency w (2*physicalRate q branch)]
  change streamMasterFirst _ _ _ _ _ _ _ - _ -
    _*(streamMasterFirst _ _ _ _ _ _ _ - _) = _
  dsimp only [forcedStreamFirst,forcedStreamValue]
  linear_combination h

end
end RHTower.D4BMModularCore
