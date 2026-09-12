import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalGreenFactor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingFinitePart
import GaloisForLFunctions.HTGeometry.JetCoefficientUniqueness

/-! The complete cleared temporal current at the physical fundamental frequency. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The original source moment, fixed onset, physical self coefficient and angular current weight. -/
def physicalTemporalFundamentalAmplitude (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) : ℂ :=
  modeAngularSquare (physicalModeAngularJet q zang) *
    (-2 * physicalFundamentalFrequency q side * (physicalAngularParameter q ^ 2 - 1 / 4 - 2)) *
    physicalSelfSourceCoefficient q *
    fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a *
    clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)

private theorem physicalTemporal_fundamental_roots (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side = -3/2 - Complex.I * physicalRadialFrequency q ∨
    physicalFundamentalFrequency q side = -3/2 + Complex.I * physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

/-- The actual cleared self profile separates into its original Gauss mode and complete moment. -/
theorem selfClearedProfile_fundamental (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    selfClearedProfile q branch a (physicalFundamentalFrequency q side) z =
      gaussProfile q (physicalFundamentalFrequency q side) z *
        (fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a *
          clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hf := physicalTemporal_fundamental_roots q side
  have hp : (z : ℂ) ^ (physicalFundamentalFrequency q side / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
  unfold selfClearedProfile
  rw [clearedReducedGreen_fundamental_factor _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hf
    (tortoiseOf z) (tortoiseOf_neg hz), horizonCoordinate_tortoiseOf hz]
  rw [gaussProfile, gaussFactor_horizon_fundamental _ _ hw.1 hf ⟨hz.1.le, hz.2⟩]
  dsimp only [power]
  field_simp

/-- Every channel of the complete cleared current is evaluated before its pole is extracted. -/
theorem clearedDensityProfile_fundamental_factor (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z =
      physicalTemporalFundamentalAmplitude q branch side a zang *
        incomingPairingFactor (physicalFundamentalFrequency q side) (physicalRadialFrequency q) z := by
  have hD := physicalFundamental_clearingFactor_zero q branch side
  simp only [clearedDensityProfile, clearedDensityCore, selfPart, contactPart, hD,
    zero_mul, mul_zero, add_zero, sub_zero, selfClearedProfile_fundamental q branch side a hz,
    physicalTemporalFundamentalAmplitude, incomingPairingFactor, gaussProfile]
  ring

/-- A quadratic endpoint jet of the actual current has the source-derived fundamental coefficients. -/
theorem clearedDensityProfile_fundamental_jet_coefficients (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) (c₀ c₁ : ℂ) {b C : ℝ} (hb : 0 < b) (hbh : b ≤ 1/2)
    (hj : ∀ z ∈ Ioc (0:ℝ) b,
      ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z - c₀ -
        c₁ * z‖ ≤ C * z ^ 2) :
    c₀ = physicalTemporalFundamentalAmplitude q branch side a zang * (1/2) ∧
    c₁ = physicalTemporalFundamentalAmplitude q branch side a zang *
      (horizonGaussFirstCoefficient (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
        + 1/4) := by
  let K := physicalTemporalFundamentalAmplitude q branch side a zang
  let L := horizonGaussFirstCoefficient (physicalFundamentalFrequency q side)
    (physicalRadialFrequency q) + 1/4
  obtain ⟨R, D, _, hR, _, _, hN⟩ := incomingPairingFactor_uniform_second_bound
    (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
    (physicalFundamentalFrequency_strip q side).1
  have hjet (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :
      ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z - K*(1/2) -
        (K*L)*(z:ℂ)‖ ≤ (‖K‖*D)*z^2 := by
    rw [clearedDensityProfile_fundamental_factor q branch side a zang
      ⟨hz.1, by linarith [hz.2]⟩]
    calc
      _ = ‖K‖ * ‖incomingPairingFactor (physicalFundamentalFrequency q side)
        (physicalRadialFrequency q) z - 1/2 - L*(z:ℂ)‖ := by
          rw [← norm_mul]
          congr 1
          dsimp only [K]
          ring
      _ ≤ ‖K‖ * (D*z^2) := mul_le_mul_of_nonneg_left
        ((hN _ (mem_ball_self hR)).2 z ⟨hz.1.le, hz.2.trans hbh⟩) (norm_nonneg K)
      _ = _ := by ring
  have hcoeff := eq_zero_of_norm_add_mul_le_mul_sq (α := c₀-K*(1/2)) (β := c₁-K*L)
    (C := C+‖K‖*D) hb (fun z hz => by
      calc
        _ = ‖(clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z -
            K*(1/2) - (K*L)*(z:ℂ)) -
          (clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z -
            c₀ - c₁*(z:ℂ))‖ := by congr 1; ring
        _ ≤ ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z -
            K*(1/2) - (K*L)*(z:ℂ)‖ +
          ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z -
            c₀ - c₁*(z:ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖K‖*D)*z^2 + C*z^2 := add_le_add (hjet z hz) (hj z hz)
        _ = _ := by ring)
  exact ⟨sub_eq_zero.mp hcoeff.1, sub_eq_zero.mp hcoeff.2⟩

/-- The actual quadratic jet evaluates the integrated pole numerator, with its original norm. -/
theorem clearedDensityProfile_fundamental_finitePart (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) (c₀ c₁ : ℂ → ℂ) {b C : ℝ} (hb : 0 < b) (hbh : b ≤ 1/2)
    (hj : ∀ z ∈ Ioc (0:ℝ) b,
      ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z -
        c₀ (physicalFundamentalFrequency q side) -
        c₁ (physicalFundamentalFrequency q side) * z‖ ≤ C * z ^ 2) :
    QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
      (physicalFundamentalFrequency q side) =
      physicalTemporalFundamentalAmplitude q branch side a zang *
        incomingNormFinitePart (physicalRadialFrequency q) b (physicalFundamentalFrequency q side) := by
  have hc := clearedDensityProfile_fundamental_jet_coefficients q branch side a zang
    (c₀ (physicalFundamentalFrequency q side)) (c₁ (physicalFundamentalFrequency q side)) hb hbh hj
  unfold incomingNormFinitePart QuadraticEndpointMellin.finitePart
  simp only [hc.1, hc.2]
  have hi : QuadraticEndpointMellin.remainder (clearedDensityProfile q branch a zang) c₀ c₁ b
      (physicalFundamentalFrequency q side) =
    physicalTemporalFundamentalAmplitude q branch side a zang *
      QuadraticEndpointMellin.remainder (fun u => incomingPairingFactor u (physicalRadialFrequency q))
        (fun _ => 1/2) (fun u => horizonGaussFirstCoefficient u (physicalRadialFrequency q)+1/4) b
        (physicalFundamentalFrequency q side) := by
    unfold QuadraticEndpointMellin.remainder
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    simp only [hc.1, hc.2, clearedDensityProfile_fundamental_factor q branch side a zang
      ⟨hz.1, by linarith [hz.2]⟩]
    ring
  rw [hi]
  ring

end
end RHTower.D4BMJointSource
