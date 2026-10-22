import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalNormalizableOuterCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalNormalizableCurrentRestoration

/-! Restoration and residue of the complete original normalizable temporal radial current. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Both original radial intervals, with the complete normalizable left mode retained. -/
def normalizableTemporalRadialFinitePart (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (c₀ c₁ d : ℂ → ℂ) (b : ℝ) (u : ℂ) : ℂ :=
  normalizableTemporalHorizonFinitePart q branch a zang c₀ c₁ d b u +
    normalizableTemporalOuterIntegral q branch a zang (tortoiseOf b) u

/-- The original horizon cutoff with its three derived counterterms and original outer current. -/
def normalizableTemporalRadialCutoff (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (c₀ c₁ d : ℂ → ℂ) (b : ℝ) (u : ℂ) (e : ℝ) : ℂ :=
  normalizableTemporalHorizonCutoff q branch a zang c₀ c₁ d b u e +
    normalizableTemporalOuterIntegral q branch a zang (tortoiseOf b) u

/-- The full normalizable temporal current is restored before its radial residue is taken.
Both original radial intervals and all source, principal, lift and contact terms remain. -/
theorem physicalNormalizableTemporalCurrent_full_radial_restoration_and_residue
    (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ (B : ℝ) (c₀ c₁ d : ℂ → ℂ), 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) +
          compactPart q branch a zang b (physicalFundamentalFrequency q side) =
          physicalTemporalFundamentalAmplitude q branch side a zang *
            D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side)) ∧
        Tendsto (fun u => (u-physicalFundamentalFrequency q side) *
          normalizableTemporalRadialFinitePart q branch a zang c₀ c₁ d b u)
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (physicalTemporalFundamentalRadialResidue q branch side a zang)) ∧
        (∀ᶠ u in 𝓝[≠] (physicalFundamentalFrequency q side),
          IntegrableOn (fun t => ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*
            continuedPhysicalTimeAction q branch u a true t zang) (Ioo (tortoiseOf b) 0) ∧
          Tendsto (normalizableTemporalRadialCutoff q branch a zang c₀ c₁ d b u)
            (𝓝[>] (0:ℝ)) (𝓝 (normalizableTemporalRadialFinitePart q branch a zang c₀ c₁ d b u))) := by
  obtain ⟨R, B, c₀, c₁, d, hR, hB, hBh, hjet, hrest⟩ :=
    physicalNormalizableTemporalCurrent_horizon_restoration_data q branch side a zang
  obtain ⟨C, _, hJ⟩ := hjet
  refine ⟨B, c₀, c₁, d, hB, hBh, ?_⟩
  intro b hb hbB
  have hb1 : b < 1 := by linarith
  have ht : tortoiseOf b < 0 := tortoiseOf_neg ⟨hb, hb1⟩
  have hH := hrest b hb hbB
  have hO := normalizableTemporalOuterIntegral_residue q branch side a zang (tortoiseOf b) ht
  rw [horizonCoordinate_tortoiseOf ⟨hb, hb1⟩] at hO
  have hjb (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :=
    hJ (physicalFundamentalFrequency q side) (mem_closedBall_self hR.le) z ⟨hz.1, hz.2.trans hbB⟩
  have hvalue := clearedDensityProfile_fundamental_finitePart q branch side a zang c₀ c₁ hb
    (hbB.trans hBh) hjb
  have hjoin : QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
      (physicalFundamentalFrequency q side) + compactPart q branch a zang b (physicalFundamentalFrequency q side) =
      physicalTemporalFundamentalAmplitude q branch side a zang *
        D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side) := by
    rw [hvalue, compactPart_fundamental_factor, ← mul_add]
    have hn := D4BMFundamentalNorm.physicalFundamentalNorm_join q side (tortoiseOf b) ht
    rw [horizonCoordinate_tortoiseOf ⟨hb, hb1⟩] at hn
    exact congrArg (fun v => physicalTemporalFundamentalAmplitude q branch side a zang * v) hn
  refine ⟨hjoin, ?_, ?_⟩
  · have hlim := hH.1.add hO
    rw [← add_div, hjoin] at hlim
    apply hlim.congr'
    filter_upwards [] with u
    dsimp only [normalizableTemporalRadialFinitePart]
    ring
  have hball : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), u ∈ ball (physicalFundamentalFrequency q side) R :=
    ball_mem_nhds _ hR
  filter_upwards [normalizableTemporalOuterIntegral_decomposition q branch side a zang (tortoiseOf b) ht,
    hball.filter_mono nhdsWithin_le_nhds,
    connection_eventually_ne_zero _ (physicalRadialFrequency q) (physicalFundamentalFrequency_strip q side).1]
      with u hu hub hcu
  refine ⟨hu.1, ?_⟩
  exact (hH.2 u hub hcu).add_const (normalizableTemporalOuterIntegral q branch a zang (tortoiseOf b) u)

end
end RHTower.D4BMJointSource
