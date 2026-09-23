import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalNormJoin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalIncomingPairingResidue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOuterPairing

/-! The regular horizon branch and original outer pairing have a common-cutoff physical residue. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual interior Wronskian coefficient is analytic at every nonreal frequency. -/
theorem normalizable_horizonRegularCoefficient_analyticAt (w chi : ℂ) (hw : w.im ≠ 0) :
    AnalyticAt ℂ (fun u => horizonRegularCoefficient u chi
      (normalizable u chi) (normalizableFirst u chi)) w := by
  have hb : (1/2:ℝ) ∈ Ioo (0:ℝ) 1 := by constructor <;> norm_num
  have hm : (-w).im ≠ 0 := by simpa only [Complex.neg_im,neg_ne_zero] using hw
  have hw0 : w ≠ 0 := by intro he; exact hw (by simp [he])
  have hH := (horizon_frequency_analyticAt (-w) chi hm hb).comp analyticAt_id.neg
  have hD := (horizonFirst_frequency_analyticAt (-w) chi hm hb).comp analyticAt_id.neg
  have hN := (normalizable_frequency_entire chi hb).analyticAt w
  have hN1 := (normalizableFirst_frequency_entire chi hb).analyticAt w
  simpa only [horizonRegularCoefficient,radialBracket,Function.comp_def] using!
    ((show AnalyticAt ℂ (fun _ : ℂ => integratingFactor (1/2)) w from analyticAt_const).mul
      ((hN.mul hD).sub (hN1.mul hH))).div
      analyticAt_id.neg (neg_ne_zero.mpr hw0)

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Every admissible horizon cut corresponds to an actual negative tortoise coordinate. -/
theorem exists_matching_horizon_cutoff {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    ∃ T : ℝ, T < 0 ∧ horizonCoordinate T=b := by
  have hc : Continuous horizonCoordinate := continuous_iff_continuousAt.mpr
    (fun t => (horizonCoordinate_hasDerivAt t).continuousAt)
  have hsmall : ∀ᶠ t : ℝ in atBot, horizonCoordinate t < b :=
    horizonCoordinate_tendsto_horizon.eventually (Iio_mem_nhds hb.1)
  obtain ⟨L,hLb,hL⟩ := (hsmall.and (eventually_lt_atBot (0:ℝ))).exists
  have hzero : horizonCoordinate 0=1 := by norm_num [horizonCoordinate,radialUnit]
  obtain ⟨T,hT,he⟩ := intermediate_value_Icc hL.le hc.continuousOn
    (show b ∈ Icc (horizonCoordinate L) (horizonCoordinate 0) by rw [hzero]; exact ⟨hLb.le,hb.2.le⟩)
  refine ⟨T,lt_of_le_of_ne hT.2 ?_,he⟩
  intro h
  subst T
  rw [hzero] at he
  exact hb.2.ne he.symm

/-- The actual regular horizon coefficient multiplies the restored incoming branch before adding the original outer integral. -/
def regularOuterPairing (chi s a : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
    incomingPairingFinitePart s chi a 1 (reducedGreenGradient chi s 1) (horizonCoordinate T) w+
      continuedReducedOuterPairing chi s a T w

/-- Positive-cutoff expression with the original incoming integral and its derived counterterms. -/
def regularOuterPairingCutoff (chi s a : ℂ) (T : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  let K := reducedGreenGradient chi s 1
  let b := horizonCoordinate T
  horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
    ((∫ z in e..b, continuedResponse s chi a 1 K z w*horizon w chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
      (incomingResponseEndpoint s chi a 1 K w b/2)*(e:ℂ)^w/w+
      ((horizonGaussFirstCoefficient w chi+1/4)*incomingResponseEndpoint s chi a 1 K w b+
        incomingResponseSlope s a 1 K w/2)*(e:ℂ)^(w+1)/(w+1))+
    continuedReducedOuterPairing chi s a T w

/-- Restoring the incoming integral first gives the joined physical residue with its complete fixed source amplitude. -/
theorem physicalRegularOuterPairing_residue_and_restoration (q : XiZeroCopy)
    (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    ∃ T R : ℝ, T < 0 ∧ 0 < R ∧
      Tendsto (fun u => (u-w)*regularOuterPairing chi s a T u) (𝓝[≠] w)
        (𝓝 (physicalIncomingPoleAmplitude q branch side a*D4BMFundamentalNorm.normFinitePart w)) ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (regularOuterPairingCutoff chi s a T u) (𝓝[>] (0:ℝ))
          (𝓝 (regularOuterPairing chi s a T u)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  obtain ⟨R,b,hR,hb,hbhalf,_,hI,hcut⟩ :=
    physicalIncomingPairing_residue_and_restoration q branch side a
  obtain ⟨T,hT,hTb⟩ := exists_matching_horizon_cutoff ⟨hb,by linarith⟩
  have hw := physicalFundamentalFrequency_strip q side
  have hA := normalizable_horizonRegularCoefficient_analyticAt w chi hw.1
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hAv := fundamental_horizonRegularCoefficient w chi hw.1 hf
  have hAlim := hA.continuousAt.tendsto.mono_left (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  rw [hAv] at hAlim
  have hO := physicalReducedOuterPairing_residue q branch side a hT
  have hN := D4BMFundamentalNorm.physicalFundamentalNorm_join q side T hT
  have hlim := (hAlim.mul hI).add hO
  have hvalue :
      1*(physicalIncomingPoleAmplitude q branch side a*incomingNormFinitePart chi b w)+
      (fundamentalSourceMoment w s a*clearedOnset s w)*
        (∫ t in Ioo T (0:ℝ), normalizable w chi (horizonCoordinate t)^(2 : ℕ))/
          physicalFundamentalDenominatorSlope q branch side=
      physicalIncomingPoleAmplitude q branch side a*D4BMFundamentalNorm.normFinitePart w := by
    change incomingNormFinitePart chi (horizonCoordinate T) w+_=D4BMFundamentalNorm.normFinitePart w at hN
    rw [hTb] at hN
    rw [← hN,physicalIncomingPoleAmplitude_eq_cleared]
    ring
  change Tendsto _ _ (𝓝 (_+_)) at hlim
  rw [hvalue] at hlim
  refine ⟨T,R,hT,hR,?_,?_⟩
  · apply hlim.congr'
    filter_upwards [] with u
    dsimp only [regularOuterPairing]
    rw [hTb]
    ring
  · intro u hu hcu
    have hh := ((hcut u hu hcu).const_mul
      (horizonRegularCoefficient u chi (normalizable u chi) (normalizableFirst u chi))).add_const
        (continuedReducedOuterPairing chi s a T u)
    change Tendsto (fun e => regularOuterPairingCutoff chi s a T u e) _ _
    simpa only [regularOuterPairingCutoff,regularOuterPairing,hTb] using! hh

end
end RHTower.D4BMJointSource
