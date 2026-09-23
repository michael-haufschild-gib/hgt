import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceActionReduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricRadial

/-!
# Physical coefficients and QNM density of the original source action

Connects the source-derived Green reduction to the unchanged physical
metric coefficient and complete temporal corner. Native forcing is exactly
the source divided by the radial coordinate, with its original Jacobian.
At either physical QNM, the combined density has one elementary source core;
its canonical finite-part evaluation remains a separate theorem.
-/

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource
open D4BMOriginalHorizonGreenMatch D4BMOriginalMetricRadial D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

/-- The actual physical Green metric term and complete temporal corner reduce
 to the fixed-source derivative and the retained forcing temporal corner. -/
theorem physicalGreenMetric_corner_eq_source_below (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : Chamber w (physicalRadialFrequency q)) (hwi : w.im≠0) :
    let s := physicalRate q br
    let chi := physicalRadialFrequency q
    let K := reducedGreenGradient chi s 1
    let mu := physicalAngularParameter q^(2 : ℕ)-1/4
    let C := physicalSelfSourceCoefficient q
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      greenCoefficient q w*(normalizableHorizonPairingFinitePart s chi amp 1 K b w+
        (∫ z in b..1,mixedDensity s chi amp 1 K w w z))+physicalCornerCandidate q br amp w=
      -mu*(mu-2)*C*(∫ z in (0:ℝ)..1,normalizable w chi z*
        deriv (fun u => continuedSourceProfile s amp 1 K u z) w)+
        mu*connection w chi*C*deriv (continuedForcingTransform s amp 1 K) w/2 := by
  dsimp only
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  let mu := physicalAngularParameter q^(2 : ℕ)-1/4
  let C := physicalSelfSourceCoefficient q
  have hwr := chamber_re_pos hw
  have hs : (2*s).re<w.re := by
    have hr := currentRate_re_lt q br
    change (2*s).re < -2 at hr
    linarith
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  have hw0 : w≠0 := by intro he; exact hwi (by simp [he])
  have hE := greenHorizonAmplitude_analyticAt s chi amp 1 K w hwi (by linarith) hsp (connection_ne_zero hw)
  have hcorner : deriv (continuedCornerAmplitude q br amp) w=
      C*deriv (greenHorizonAmplitude s chi amp 1 K) w := by
    have hd := hE.differentiableAt.hasDerivAt.const_mul C
    exact hd.deriv
  obtain ⟨B,hB,hBh,h⟩ := originalMetricTemporal_eq_sourceDerivative_below s chi amp 1 K w hw hwi hs
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB
  have hI := h b hb hbB
  rw [physicalCornerCandidate,hcorner]
  dsimp only [greenCoefficient,continuedCornerAmplitude,D4BMLeftModeRadialEquation.eigenvalue] at ⊢
  change 2*mu*w*(mu-2)*C*(_+_)+mu*(connection w chi/(2*w))*
    ((mu-2)*(C*greenHorizonAmplitude s chi amp 1 K w)+
      2*w*(mu-2)*(C*deriv (greenHorizonAmplitude s chi amp 1 K) w)+
      w*C*deriv (continuedForcingTransform s amp 1 K) w)=_
  calc
    _ = mu*(mu-2)*C*(2*w*(normalizableHorizonPairingFinitePart s chi amp 1 K b w+
        (∫ z in b..1,mixedDensity s chi amp 1 K w w z))+
        connection w chi*(deriv (greenHorizonAmplitude s chi amp 1 K) w+
          greenHorizonAmplitude s chi amp 1 K w/(2*w)))+
        mu*connection w chi*C*deriv (continuedForcingTransform s amp 1 K) w/2 := by
      field_simp [hw0]
      ring
    _ = _ := by rw [hI]; ring

/-- Native forcing is exactly the unchanged source divided by the original
radial coordinate, including its coordinate Jacobian and sign. -/
theorem nativeForcing_pullback_eq_source (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    continuedOnset (physicalRate q br) w*D4BMOriginalMetricHorizon.pullback q br amp K w z=
      -(normalizable w (physicalRadialFrequency q) z*
        continuedSourceProfile (physicalRate q br) amp 1 K w z/(z:ℂ)) := by
  have hu := radialUnit_eq_sqrt (tortoiseOf z) (tortoiseOf_neg hz)
  rw [horizonCoordinate_tortoiseOf hz] at hu
  have hr : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=1-(z:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hz.2.le)
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hr0 : (Real.sqrt (1-z):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'
  change _=-(normalizable w (physicalRadialFrequency q) z*
    sourceProfile (physicalRate q br) w amp 1 K (continuedOnset (physicalRate q br) w) z/(z:ℂ))
  rw [sourceProfile_tortoiseFactor _ _ _ _ _ _ hz]
  dsimp only [D4BMOriginalMetricHorizon.pullback,D4BMOriginalMetricHorizon.forcingKernel]
  rw [horizonCoordinate_tortoiseOf hz,hu]
  simp only [forcingProfile,sourceRemainder,sub_zero,mul_one,hr]
  field_simp [hz0,hr0]

/-- At either actual QNM, the complete source-action density has one
 elementary radial core. The derivative still holds the angular data fixed;
 this identity makes no claim about an unsubtracted integral at the horizon. -/
theorem physicalQNM_sourceAction_density (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    let chi := physicalRadialFrequency q
    let K := reducedGreenGradient chi s 1
    let mu := physicalAngularParameter q^(2 : ℕ)-1/4
    normalizable w chi z*((mu-2)*deriv (fun u => continuedSourceProfile s amp 1 K u z) w+
      w*continuedSourceProfile s amp 1 K w z/(z:ℂ))=
    (z:ℂ)^w*fundamentalSourceCore w s amp z*
      ((mu-2)*((tortoiseOf z:ℂ)*continuedOnset s w+deriv (continuedOnset s) w)+
        w*continuedOnset s w/(z:ℂ)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  let mu := physicalAngularParameter q^(2 : ℕ)-1/4
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hM := normalizable_source_fundamental w chi s amp hf hz.1
  have hS : normalizable w chi z*continuedSourceProfile s amp 1 K w z=
      (z:ℂ)^w*fundamentalSourceCore w s amp z*continuedOnset s w := by
    have he : continuedSourceProfile s amp 1 K w z=
        sourceProfile s w amp 1 K 1 z*continuedOnset s w := by
      change sourceProfile s w amp 1 K (continuedOnset s w) z=_
      rw [sourceProfile_tortoiseFactor s w amp 1 K (continuedOnset s w) hz,
        sourceProfile_tortoiseFactor s w amp 1 K 1 hz]
      ring
    rw [he,← mul_assoc,hM]
  have hD : normalizable w chi z*deriv (fun u => continuedSourceProfile s amp 1 K u z) w=
      (z:ℂ)^w*fundamentalSourceCore w s amp z*
        ((tortoiseOf z:ℂ)*continuedOnset s w+deriv (continuedOnset s) w) := by
    rw [continuedSourceProfile_frequency_deriv s amp 1 K w
      (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side) hz,← mul_assoc,hM]
  change normalizable w chi z*((mu-2)*deriv (fun u => continuedSourceProfile s amp 1 K u z) w+
      w*continuedSourceProfile s amp 1 K w z/(z:ℂ))=_
  linear_combination (mu-2)*hD+w/(z:ℂ)*hS

end
end RHTower.D4BMOriginalSourceResolvent
