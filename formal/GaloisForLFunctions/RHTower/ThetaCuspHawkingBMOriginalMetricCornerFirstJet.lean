import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerForcing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConnectionSecondJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConnectionCornerJetNonzero

/-! Rigidity of the finite first jet of the complete original temporal corner. -/
open Complex Set Filter Topology
namespace RHTower.D4BMOriginalMetricQNM
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalCornerForcing D4BMOriginalHorizonGreenMatch
noncomputable section
set_option autoImplicit false

private abbrev chi (q : XiZeroCopy) := physicalRadialFrequency q
private abbrev rate (q : XiZeroCopy) (br : Bool) := physicalRate q br
private abbrev grad (q : XiZeroCopy) (br : Bool) :=
  reducedGreenGradient (chi q) (rate q br) 1
private abbrev conn (q : XiZeroCopy) (w : ℂ) := connection w (chi q)
private abbrev mu (q : XiZeroCopy) := physicalAngularParameter q ^ (2 : ℕ) - 1 / 4

/-- The actual connection-cleared causal horizon amplitude, including its fixed QNM value. -/
def clearedCornerAmplitude (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ → ℂ :=
  Function.update (fun w => conn q w * continuedCornerAmplitude q br amp w)
    (physicalFundamentalFrequency q side)
    (connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side *
      cornerResidue q br side amp)

theorem clearedCornerAmplitude_analytic (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    AnalyticAt ℂ (clearedCornerAmplitude q br side amp)
      (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hC := connection_frequency_analyticAt w (chi q) hw.1
  have hM := hC.meromorphicAt.mul
    (continuedCornerAmplitude_meromorphic q br amp w hw.1 (abs_lt.mp hw.2).1)
  apply (hM.update w _).analyticAt
  apply continuousAt_update_same.mpr
  have hc := (physicalFundamental_connection_hasDerivAt q side).tendsto_slope
  have hlim := hc.mul (continuedCornerAmplitude_residue q br side amp)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [slope_def_field, physicalFundamentalFrequency_connection_zero, sub_zero]
  change conn q u / (u - w) * ((u - w) * continuedCornerAmplitude q br amp u) =
    conn q u * continuedCornerAmplitude q br amp u
  have hnot : u ∉ ({physicalFundamentalFrequency q side} : Set ℂ) := hu
  have huw : u ≠ w := by
    simpa only [Set.mem_singleton_iff, w] using hnot
  field_simp [sub_ne_zero.mpr huw]

/-- Clearing the actual temporal corner retains the derivative of its source amplitude. -/
def cornerNumerator (q : XiZeroCopy) (br side : Bool) (amp w : ℂ) : ℂ :=
  let H := clearedCornerAmplitude q br side amp
  mu q * ((mu q - 2) *
      (conn q w * H w / (2 * w) + conn q w * deriv H w - H w * deriv (conn q) w) +
    conn q w ^ (2 : ℕ) * physicalSelfSourceCoefficient q / 2 *
      deriv (continuedForcingTransform (rate q br) amp 1 (grad q br)) w)

theorem cornerNumerator_analytic (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    AnalyticAt ℂ (cornerNumerator q br side amp) (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hC := connection_frequency_analyticAt w (chi q) hw.1
  have hH := clearedCornerAmplitude_analytic q br side amp
  have hF := physical_forcing_analyticAt q br side amp 1 (grad q br)
  have hw0 : w ≠ 0 := by intro h; apply hw.1; change w.im = 0; rw [h]; rfl
  exact analyticAt_const.mul ((analyticAt_const.mul
    ((((hC.mul hH).div (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)).add
      (hC.mul hH.deriv)).sub (hH.mul hC.deriv))).add
    ((((hC.pow 2).mul analyticAt_const).div analyticAt_const (by norm_num)).mul hF.deriv))

/-- The finite first jet of the complete temporal corner is rigid. The unknown regular
Laurent coefficient of the continued horizon amplitude cancels from the antisymmetric
connection derivative, and the forcing contact is second order at the connection zero. -/
theorem cornerNumerator_firstJet (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    deriv (cornerNumerator q br side amp) (physicalFundamentalFrequency q side) /
        connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side =
      mu q * (mu q - 2) * cornerResidue q br side amp *
        (connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side /
            (2 * physicalFundamentalFrequency q side) -
          deriv (deriv (conn q)) (physicalFundamentalFrequency q side)) := by
  let w₀ := physicalFundamentalFrequency q side
  let C := conn q
  let H := clearedCornerAmplitude q br side amp
  let F := continuedForcingTransform (rate q br) amp 1 (grad q br)
  let s := connectionSimpleSlope w₀ (chi q) side
  let R := cornerResidue q br side amp
  let m := mu q
  have hw := physicalFundamentalFrequency_strip q side
  have hw₀ : w₀ ≠ 0 := by
    intro h
    apply hw.1
    change w₀.im = 0
    rw [h]
    rfl
  have hs : s ≠ 0 := physicalFundamental_connectionSlope_ne_zero q side
  have hC : AnalyticAt ℂ C w₀ := connection_frequency_analyticAt w₀ (chi q) hw.1
  have hH : AnalyticAt ℂ H w₀ := clearedCornerAmplitude_analytic q br side amp
  have hF : AnalyticAt ℂ F w₀ := physical_forcing_analyticAt q br side amp 1 (grad q br)
  have hCd : HasDerivAt C s w₀ := physicalFundamental_connection_hasDerivAt q side
  have hHd : HasDerivAt H (deriv H w₀) w₀ := hH.differentiableAt.hasDerivAt
  have hCdd : HasDerivAt (deriv C) (deriv (deriv C) w₀) w₀ :=
    hC.deriv.differentiableAt.hasDerivAt
  have hHdd : HasDerivAt (deriv H) (deriv (deriv H) w₀) w₀ :=
    hH.deriv.differentiableAt.hasDerivAt
  have hFdd : HasDerivAt (deriv F) (deriv (deriv F) w₀) w₀ :=
    hF.deriv.differentiableAt.hasDerivAt
  have hden : HasDerivAt (fun w : ℂ => 2 * w) 2 w₀ := by
    simpa using (hasDerivAt_id w₀).const_mul (2 : ℂ)
  have hA := (hCd.mul hHd).div hden (mul_ne_zero (by norm_num) hw₀)
  have hB := hCd.mul hHdd
  have hD := hHd.mul hCdd
  have hE := ((((hCd.pow 2).mul_const (physicalSelfSourceCoefficient q)).div_const 2).mul hFdd)
  have hTotal := (((hA.add hB).sub hD).const_mul (m - 2) |>.add hE).const_mul m
  change HasDerivAt (cornerNumerator q br side amp) _ w₀ at hTotal
  have hC₀ : C w₀ = 0 := physicalFundamentalFrequency_connection_zero q side
  have hCH₀ : (C * H) w₀ = 0 := by simp only [Pi.mul_apply, hC₀, zero_mul]
  have hCpow₀ : (C ^ (2 : ℕ)) w₀ = 0 := by
    rw [Pi.pow_apply, hC₀]
    norm_num
  have hH₀ : H w₀ = s * R := by
    change Function.update (fun w => conn q w * continuedCornerAmplitude q br amp w)
      (physicalFundamentalFrequency q side)
      (connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side *
        cornerResidue q br side amp) w₀ = s * R
    rw [show w₀ = physicalFundamentalFrequency q side from rfl, Function.update_self]
  have hderiv : deriv (cornerNumerator q br side amp) w₀ =
      m * (m - 2) * (s ^ (2 : ℕ) * R / (2 * w₀) - s * R * deriv (deriv C) w₀) := by
    rw [hTotal.deriv]
    rw [hC₀, hCd.deriv, hH₀, hCH₀, hCpow₀]
    norm_num
    field_simp [hw₀]
    ring
  change deriv (cornerNumerator q br side amp) w₀ / s = _
  rw [hderiv]
  change _ = m * (m - 2) * R * (s / (2 * w₀) - deriv (deriv C) w₀)
  field_simp [hw₀, hs]

/-- The rigid temporal-corner first jet with the connection two-jet eliminated completely. -/
theorem cornerNumerator_firstJet_explicit (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    deriv (cornerNumerator q br side amp) (physicalFundamentalFrequency q side) /
        connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side =
      mu q * (mu q - 2) * cornerResidue q br side amp *
        connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side *
          physicalConnectionCornerJetFactor q side := by
  rw [cornerNumerator_firstJet]
  rw [connection_fundamental_secondDerivative
    (physicalFundamentalFrequency q side) (chi q) side
    (physicalFundamentalFrequency_strip q side).1
    (physicalFundamental_zeroArgument q side)]
  unfold physicalConnectionCornerJetFactor
  ring

end
end RHTower.D4BMOriginalMetricQNM
