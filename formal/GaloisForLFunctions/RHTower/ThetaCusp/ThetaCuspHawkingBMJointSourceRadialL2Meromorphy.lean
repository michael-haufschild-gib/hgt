import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedNativeL2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedL2Holomorphy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceContinuedBandAdmission

/-! Restoration of the original source denominators in the actual radial L² space. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The native source has genuine radial L² holomorphy to the right of the physical onset pole. -/
theorem continuedReducedCoefficient_l2_analyticAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : -2 < w.re) : AnalyticAt ℂ
      (l2Family radialMeasure (fun u => reducedCoefficient (physicalRate q branch) u a
        (continuedOnset (physicalRate q branch) u))) w := by
  let s := physicalRate q branch
  have hs := physicalSourceDenominator_ne_zero q branch w hw
  have ha : AnalyticAt ℂ (fun u : ℂ => (u-2*s)⁻¹) w :=
    (analyticAt_id.sub analyticAt_const).inv hs
  apply (ha.smul (clearedReducedCoefficient_l2_analyticAt s a w hw)).congr
  have hn := Complex.continuous_re.continuousAt.eventually_const_lt hw
  filter_upwards [hn] with u hu
  have hsu := physicalSourceDenominator_ne_zero q branch u hu
  have he := l2Family_smul radialMeasure
    (fun v => reducedCoefficient s v a (continuedOnset s v)) (clearedReducedCoefficient s a) u (u-2*s)
    (reducedCoefficient_memLp_horizon s u a (continuedOnset s u) hu)
    (fun t => clearedReducedCoefficient_eq s a u hsu t)
  change (u-2*s)⁻¹ • l2Family radialMeasure (clearedReducedCoefficient s a) u = _
  rw [he,smul_smul,inv_mul_cancel₀ hsu,one_smul]

/-- Every original connection denominator is restored meromorphically in the actual L² norm,
throughout the nonreal band connecting the original source chamber to the fundamental QNMs. -/
theorem continuedCutoffRadialCoefficient_l2_meromorphicAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) (i : Fin 3) :
    MeromorphicAt (l2Family radialMeasure (fun u => continuedCutoffRadialCoefficient q branch u a i)) w := by
  have hwre : -2 < w.re := (abs_lt.mp hwr).1
  have hD : AnalyticAt ℂ (fun u => principalClearingFactor q branch u i) w :=
    (analyticAt_id.sub analyticAt_const).neg.mul (connection_frequency_analyticAt w (principalFrequency q i) hw)
  have ha := hD.meromorphicAt.inv.smul
    (clearedCutoffRadialCoefficient_l2_analyticAt q branch w a hw hwre hwr i).meromorphicAt
  apply ha.congr
  have hn : ∀ᶠ u in 𝓝[≠] w, u.im ≠ 0 ∧ |u.re| < 2 :=
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (Complex.continuous_re.continuousAt.abs.eventually_lt_const hwr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,principal_denominators_eventually_ne_zero q branch w hw i] with u hu hd
  have hd0 : principalClearingFactor q branch u i ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hd.1) hd.2
  have he := l2Family_smul radialMeasure
    (fun v => continuedCutoffRadialCoefficient q branch v a i)
    (fun v => clearedCutoffRadialCoefficient q branch v a i) u (principalClearingFactor q branch u i)
    (continuedCutoffRadialCoefficient_band_memLp q branch u a hu.1 hu.2 i)
    (fun t => clearedCutoffRadialCoefficient_eq q branch u a i hd.1 hd.2 t)
  change (principalClearingFactor q branch u i)⁻¹ •
    l2Family radialMeasure (fun v => clearedCutoffRadialCoefficient q branch v a i) u = _
  rw [he,smul_smul,inv_mul_cancel₀ hd0,one_smul]

end
end RHTower.D4BMJointSource
