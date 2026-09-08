import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamRadialFields
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamForcedCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIngoingCoordinates
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-! The original stream equation as an actual time-evolution operator after
normalization by radius. No angular spectral model is substituted. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMVectorStream D4BMFundamentalScalarMetric D4BMHorizon D4BMMetricReconstruction D4BMQuadraticMixedSource D4BMScalarLinearEquation
set_option autoImplicit false
noncomputable section

private abbrev Field := (Fin 4 → ℝ) → ℂ

/-- The actual exterior radial factor. -/
def radialFactor (x : Fin 4 → ℝ) : ℂ := (x 1 : ℂ)*(x 1 : ℂ)+(-1)

private theorem radius_smooth (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) x :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt

private theorem factor_jet (x : Fin 4 → ℝ) :
    ofField radialFactor x = ((coord (x 1) 1).mul (coord (x 1) 1)).add (constant (-1)) := by
  unfold radialFactor
  rw [ofField_add ((radius_smooth x).mul (radius_smooth x)) contDiffAt_const,
    ofField_mul (radius_smooth x) (radius_smooth x),ofField_constant,coordinate_jet]
  rfl

/-- The time and tortoise-radial part of the wave operator, acting on actual jets. -/
def waveJet (r : ℂ) (J : ScalarTwoJet (Fin 4) ℂ) : ℂ :=
  J.second 0 0-(r^2-1)^2*J.second 1 1-2*r*(r^2-1)*J.first 1

/-- This expression is exactly ∂t² minus two applications of the original
tortoise vector field (r²-1)∂r, including its differentiated coefficient. -/
theorem waveJet_tortoise (F : Field) (x : Fin 4 → ℝ) (hF : ContDiffAt ℝ 2 F x) :
    waveJet (x 1) (ofField F x) = coordDeriv 0 (coordDeriv 0 F) x -
      radialFactor x*coordDeriv 1 (fun y => radialFactor y*coordDeriv 1 F y) x := by
  have hc : DifferentiableAt ℝ radialFactor x :=
    (((radius_smooth x).mul (radius_smooth x)).add (contDiffAt_const (c := (-1:ℂ)))).differentiableAt (by norm_num)
  have hd : coordDeriv 1 radialFactor x = 2*(x 1 : ℂ) := by
    have h := congrArg (fun J => J.first 1) (factor_jet x)
    simpa [ofField,ScalarTwoJet.add,ScalarTwoJet.mul,coord,constant,two_mul] using h
  rw [coordDeriv_mul hc (coordDeriv_hasFDerivAt hF 1).differentiableAt,hd]
  dsimp [waveJet,ofField,radialFactor]
  ring

/-- The actual original stream field normalized by radius. -/
def normalizedStream (w a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  streamRadialField w a square x*(x 1 : ℂ)⁻¹

/-- The normalized profile's complete coordinate jet is constructed from its
actual field, retaining all original time and radial derivatives. -/
theorem normalizedStream_jet (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ofField (normalizedStream w a square) p.val =
      (radialJet w (streamRadialValue w (p.val 1) (envelope w a p.val) square)
        (streamRadialFirst w (p.val 1) (envelope w a p.val) square)
        (streamRadialSecond w (p.val 1) (envelope w a p.val) square)).mul
        (coord (p.val 1) 1).inv := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  unfold normalizedStream
  rw [ofField_mul (g := fun x : Fin 4 → ℝ => (x 1 : ℂ)⁻¹)
    (streamRadialFields_smooth w a square p 2).1 ((radius_smooth p.val).inv hr),
    ofField_inv (radius_smooth p.val) hr,coordinate_jet,streamRadialField_jet]
  rfl

/-- The full wave component, with the actual original angular operator. -/
def normalizedStreamWave (w a : ℂ) (square : Bool) (V : Covector)
    (k : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  waveJet (x 1) (ofField (normalizedStream w a square) x)*V k (angularPoint x) -
    ((x 1 : ℂ)^2-1)/(x 1 : ℂ)^2*normalizedStream w a square x*
      streamAngularOperator V k (angularPoint x)

private theorem normalized_master (w r H H1 H2 A D : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    waveJet r ((radialJet w H H1 H2).mul (coord r 1).inv)*A-
      (r^2-1)/r^2*(H*r⁻¹)*D = -(r^2-1)/r^3*master w r H H1 H2 A D := by
  simp [waveJet,radialJet,ScalarTwoJet.mul,ScalarTwoJet.inv,coord,master]
  field_simp [hr,hf]
  ring

/-- The full actual wave expression is the original Einstein master with its
forced radius normalization. This fixes the operator and source together. -/
theorem normalizedStreamWave_master (w a : ℂ) (square : Bool) (V : Covector)
    (k : Fin 2) (p : D4BMBackground.ExteriorPoint) :
    normalizedStreamWave w a square V k p.val =
      -((p.val 1 : ℂ)^2-1)/(p.val 1 : ℂ)^3*
        streamMaster w (p.val 1) (envelope w a p.val) square V k (angularPoint p.val) := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hf : (p.val 1 : ℂ)^2-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^2-1 ≠ 0)
  have hv := congrArg (fun J => J.value) (streamRadialField_jet w a square p)
  change streamRadialField w a square p.val = streamRadialValue w (p.val 1) (envelope w a p.val) square at hv
  unfold normalizedStreamWave
  rw [normalizedStream_jet]
  unfold normalizedStream
  rw [hv]
  exact normalized_master _ _ _ _ _ _ _ hr hf

/-- The original constructed mixed response solves the full time-evolution
equation with the complete retained current and both radial factors. -/
theorem forced_normalized_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (k : Fin 2) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    normalizedStreamWave (2*s) (a^2) false (fullAngularCovector q branch) k p.val -
      (s*(s-1)/4)*normalizedStreamWave (2*s) (a^2) true (fullSquareCovector q) k p.val =
      -2*(r^2-1)/r^3*current s r (envelope s a p.val)
        (fullSquareCovector q k z) (fullGradientCovector q branch k z) := by
  dsimp only
  rw [normalizedStreamWave_master,normalizedStreamWave_master,envelope_double]
  have h := forced_stream_master q branch p (envelope (physicalRate q branch) a p.val) k
  dsimp only at h
  linear_combination -((p.val 1 : ℂ)^2-1)/(p.val 1 : ℂ)^3*h

end
end RHTower.D4BMModularCore
