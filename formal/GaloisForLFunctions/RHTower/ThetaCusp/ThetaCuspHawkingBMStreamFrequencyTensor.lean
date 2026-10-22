import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamFrequencyTransport

/-! The complete frequency defect of the original Einstein stream pencil.
The time slot varies; original radial and angular jets and source stay visible.
No causal inverse, initial switching law or retarded field is asserted. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMVectorStream D4BMQuadraticMixedSource D4BMMetricReconstruction
set_option autoImplicit false
noncomputable section

/-- The original tensor curl with time frequency independent of the radial rate. -/
def frozenStreamMetricTensor (w v r B : ℂ) (square : Bool) (V : Covector)
    (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let T0 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*frozenStreamMasterFirst w v r B square V 0 z
  let T1 := -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*frozenStreamMasterFirst w v r B square V 1 z
  let R0 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*frozenStreamMaster w v r B square V 0 z
  let R1 := -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*frozenStreamMaster w v r B square V 1 z
  !![0,0,T0,T1; 0,0,R0,R1; T0,R0,0,0; T1,R1,0,0]

/-- Exact correction to all original source components at a different time
frequency. The radial block includes the unsquared frequency change. -/
def frequencyDefectTensor (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let v := 2*physicalRate q branch
  let f := r^(2 : ℕ)-1
  let D := w^(2 : ℕ)-v^(2 : ℕ)
  let P := forcedStreamValue q branch r B
  let P1 := forcedStreamFirst q branch r B
  let C := fun k => current (physicalRate q branch) r B
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)
  let T := fun k => f/(2*r^(2 : ℕ))*D*(r^(2 : ℕ)/f*P1 k z-2*r/f^(2 : ℕ)*P k z)
  let R := fun k => -(w-v)/(r^(2 : ℕ)*f)*C k+w/(2*r^(2 : ℕ)*f)*D*r^(2 : ℕ)/f*P k z
  !![0,0,T 0,T 1; 0,0,R 0,R 1; T 0,R 0,0,0; T 1,R 1,0,0]

private theorem unfactor {a c M N S Q : ℂ} (h : a*(M-c*N)+S=Q) :
    a*M-c*(a*N)+S=Q := by
  linear_combination h

set_option maxHeartbeats 600000 in
/-- All sixteen source components are retained in the exact frozen-profile
frequency transfer, including the radial frequency factor and current. -/
theorem frozen_stream_tensor_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    frozenStreamMetricTensor w (2*s) r (B^(2 : ℕ)) false (fullAngularCovector q branch) z i j -
      (s*(s-1)/4)*frozenStreamMetricTensor w (2*s) r (B^(2 : ℕ)) true (fullSquareCovector q) z i j +
      literalMixedSource q branch r B z i j = frequencyDefectTensor q branch w r B z i j := by
  let s := physicalRate q branch
  let r := (p.val 1 : ℂ)
  let z := angularPoint p.val
  have hnr : r ≠ 0 := by
    dsimp only [r]
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hnf : r^(2 : ℕ)-1 ≠ 0 := by
    dsimp only [r]
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  have htime (k : Fin 2) :
      -(r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*(frozenStreamMasterFirst w (2*s) r (B^(2 : ℕ)) false (fullAngularCovector q branch) k z -
        (s*(s-1)/4)*frozenStreamMasterFirst w (2*s) r (B^(2 : ℕ)) true (fullSquareCovector q) k z) +
      B^(2 : ℕ)*(timeSquare s r*fullSquareCovector q k z+timeGradient s r*fullGradientCovector q branch k z) =
      (r^(2 : ℕ)-1)/(2*r^(2 : ℕ))*(w^(2 : ℕ)-(2*s)^(2 : ℕ))*(r^(2 : ℕ)/(r^(2 : ℕ)-1)*forcedStreamFirst q branch r B k z -
        2*r/(r^(2 : ℕ)-1)^(2 : ℕ)*forcedStreamValue q branch r B k z) := by
    rw [forced_streamFirst_frequency q branch p B w k]
    rw [← temporal_current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) hnr hnf]
    dsimp only [s,r,z] at hnr hnf ⊢
    field_simp [hnr,hnf]
    ring
  have hradius (k : Fin 2) :
      -w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*(frozenStreamMaster w (2*s) r (B^(2 : ℕ)) false (fullAngularCovector q branch) k z -
        (s*(s-1)/4)*frozenStreamMaster w (2*s) r (B^(2 : ℕ)) true (fullSquareCovector q) k z) +
      B^(2 : ℕ)*(radialSquare s r*fullSquareCovector q k z+radialGradient s r*fullGradientCovector q branch k z) =
      -(w-2*s)/(r^(2 : ℕ)*(r^(2 : ℕ)-1))*current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) +
        w/(2*r^(2 : ℕ)*(r^(2 : ℕ)-1))*(w^(2 : ℕ)-(2*s)^(2 : ℕ))*r^(2 : ℕ)/(r^(2 : ℕ)-1)*forcedStreamValue q branch r B k z := by
    rw [forced_stream_frequency q branch p B w k]
    have hcur := radial_current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) hnr hnf
    dsimp only [s,r,z] at hnr hnf hcur ⊢
    field_simp [hnr,hnf]
    linear_combination (2*((p.val 1:ℂ)^(2 : ℕ)-1))*hcur
  dsimp only [s,r,z] at htime hradius
  dsimp only
  fin_cases i <;> fin_cases j
  all_goals dsimp only [frozenStreamMetricTensor,literalMixedSource,frequencyDefectTensor]
  all_goals first | exact unfactor (htime 0) | exact unfactor (htime 1) |
    exact unfactor (hradius 0) | exact unfactor (hradius 1) | norm_num

/-- The original metric-jet pencil with the time slot w independent of the
radial-profile slot v. The angular entries are actual coordinate derivatives. -/
def frozenStreamMetricJet (w v r B : ℂ) (square : Bool) (V : Covector)
    (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  D4BMVectorStream.metricJet w r (streamRadialValue v r B square) (streamRadialFirst v r B square)
    (streamRadialSecond v r B square) (streamRadialThird v r B square)
    (V 0 z) (V 1 z) (coordDeriv 0 (V 0) z) (coordDeriv 1 (V 0) z) (coordDeriv 0 (V 1) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 0 (coordDeriv 0 (V 1)) z) (coordDeriv 1 (coordDeriv 1 (V 0)) z)

private theorem frozenJet_einstein (w v B : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (frozenStreamMetricJet w v (p.val 1) B square V (angularPoint p.val)) (-3) i j =
      frozenStreamMetricTensor w v (p.val 1) B square V (angularPoint p.val) i j := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  unfold frozenStreamMetricJet
  rw [D4BMVectorStream.cosmological_component _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf i j]
  rfl

/-- The displayed frequency correction is the full original cosmological
Einstein pencil defect on the constructed mixed angular and radial data.
This does not supply an off-frequency causal field or its boundary domain. -/
theorem frozen_stream_cosmological_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    let E := fun K => CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet r (p.val 3)) K (-3) i j
    E (frozenStreamMetricJet w (2*s) r (B^(2 : ℕ)) false (fullAngularCovector q branch) z) -
      (s*(s-1)/4)*E (frozenStreamMetricJet w (2*s) r (B^(2 : ℕ)) true (fullSquareCovector q) z) +
      literalMixedSource q branch r B z i j = frequencyDefectTensor q branch w r B z i j := by
  dsimp only
  rw [frozenJet_einstein,frozenJet_einstein]
  exact frozen_stream_tensor_source q branch p B w i j

end
end RHTower.D4BMModularCore
