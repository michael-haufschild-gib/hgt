import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceEndpointGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceRetainedSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceCoordinate

/-! The genuine endpoint response solves the original radial wave equation,
after the actual radius-coordinate derivatives and original source are restored. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions.HTGeometry D4BMModularCore D4BMHorizon
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem realCoordinate_derivatives {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => 1-r⁻¹^2) (2/r^3) r ∧
    HasDerivAt (fun r : ℝ => 2/r^3) (-6/r^4) r := by
  constructor
  · convert! (((hasDerivAt_id r).inv hr).pow 2).const_sub 1 using 1
    dsimp
    field_simp
  · convert! ((hasDerivAt_const r (2:ℝ)).div ((hasDerivAt_id r).pow 3) (pow_ne_zero 3 hr)) using 1
    dsimp
    field_simp
    ring

private theorem realCoordinate_interior {r : ℝ} (hr : 1 < r) : 1-r⁻¹^2 ∈ Ioo 0 1 := by
  have hi : 0 < r⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : r⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hr
  constructor <;> nlinarith

def radialResponse (w chi s a J K T : ℂ) (r : ℝ) : ℂ :=
  response w chi s a J K T (1-r⁻¹^2)

def radialResponseFirst (w chi s a J K T : ℂ) (r : ℝ) : ℂ :=
  (2/(r:ℂ)^3)*responseFirst w chi s a J K T (1-r⁻¹^2)

def radialResponseSecond (w chi s a J K T : ℂ) (r : ℝ) : ℂ :=
  (2/(r:ℂ)^3)^2*responseSecond w chi s a J K T (1-r⁻¹^2)-
    (6/(r:ℂ)^4)*responseFirst w chi s a J K T (1-r⁻¹^2)

/-- Both original-radius derivatives are actual derivatives of the constructed
endpoint integral response, including the differentiated coordinate factor. -/
theorem radialResponse_derivatives {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {r : ℝ} (hr : 1 < r) :
    HasDerivAt (radialResponse w chi s a J K T) (radialResponseFirst w chi s a J K T r) r ∧
    HasDerivAt (radialResponseFirst w chi s a J K T) (radialResponseSecond w chi s a J K T r) r := by
  obtain ⟨hz,hz1⟩ := realCoordinate_derivatives (ne_of_gt (show 0<r by linarith))
  obtain ⟨hF,hF1⟩ := response_derivatives h s a J K T (realCoordinate_interior hr)
  have hFR := hF.scomp r hz
  have hDR := hF1.scomp r hz
  constructor
  · simpa only [radialResponse,radialResponseFirst,Complex.real_smul,Complex.ofReal_div,
      Complex.ofReal_ofNat,Complex.ofReal_pow] using! hFR
  · have hd := hz1.ofReal_comp.mul hDR
    convert! hd using 1
    · funext t
      simp [radialResponseFirst,Function.comp_def]
    · dsimp [radialResponseSecond]
      push_cast
      ring

/-- The actual retained-profile response solves the original normalized radial
wave with exactly the factor -2*(r²-1)/r³ multiplying the original current. -/
theorem radialResponse_originalWave {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    {r : ℝ} (hr : 1 < r) :
    radialWave w (1/4+chi^2) r (radialResponse w chi s a J K T r)
      (radialResponseFirst w chi s a J K T r) (radialResponseSecond w chi s a J K T r) =
      -2*((r:ℂ)^2-1)/(r:ℂ)^3*
        (Complex.exp (w*(D4BMIngoingCoordinates.tortoise r:ℂ))*
          D4BMQuadraticMixedSource.current s r
            (D4BMIngoingCoordinates.compactEnvelope s a 0 (r:ℂ)⁻¹) J K*T) := by
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0<r by linarith))
  have hf : (r:ℂ)^2-1 ≠ 0 := by exact_mod_cast (ne_of_gt (show 0<r^2-1 by nlinarith))
  have hz := realCoordinate_interior hr
  unfold radialResponse radialResponseFirst radialResponseSecond
  rw [radialWave_physical _ _ _ _ _ _ hr0 hf]
  have hzcast : radialCoordinate (r:ℂ)=((1-r⁻¹^2:ℝ):ℂ) := by simp [radialCoordinate]
  rw [hzcast,response_equation h s a J K T hz]
  have hs : Real.sqrt (1-(1-r⁻¹^2))=r⁻¹ := by
    rw [sub_sub_cancel,Real.sqrt_sq (le_of_lt (inv_pos.mpr (by linarith)))]
  rw [hs,sourceProfile_original _ _ _ _ _ _ hr]
  push_cast
  field_simp
  ring

/-- The current on the right is the original half-line smooth-onset time
integral, at fixed Xi occurrence and fixed full angular fields. -/
theorem radialResponse_smoothCurrentWave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (ang : Point) (k : Fin 2) {w chi : ℂ} (h : Chamber w chi) :
    let s := physicalRate q branch
    let J := fullSquareCovector q k ang
    let K := fullGradientCovector q branch k ang
    let T := 1/(w-currentRate q branch)+onsetCorrection (currentRate q branch) w
    radialWave w (1/4+chi^2) r.val (radialResponse w chi s a J K T r.val)
      (radialResponseFirst w chi s a J K T r.val) (radialResponseSecond w chi s a J K T r.val) =
      -2*((r.val:ℂ)^2-1)/(r.val:ℂ)^3*smoothCurrentLaplace q branch a r ang k w := by
  dsimp only
  rw [radialResponse_originalWave h _ _ _ _ _ r.property,
    smoothCurrentLaplace_eq q branch a r ang k (chamber_re_pos h)]
  rfl

end
end RHTower.D4BMLaplaceRadial
