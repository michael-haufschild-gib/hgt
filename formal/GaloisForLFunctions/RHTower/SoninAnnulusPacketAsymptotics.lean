import GaloisForLFunctions.RHTower.SoninAnnulusPacket
import GaloisForLFunctions.HTGeometry.SoninCosineRiemannLebesgue

/-!
# High-frequency asymptotics of the annular wavepacket

Riemann--Lebesgue kills every oscillatory moment of the fixed profile, so the mean correction in
the wavepacket disappears and the squared `L²` norm settles at half the profile's energy.  In
particular the normalisation of the wavepacket stays bounded away from zero along the whole
frequency scale, which is what makes the family cofinal rather than degenerate.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- Anything vanishing wherever the profile vanishes has compact support. -/
theorem hasCompactSupport_of_soninAnnulusBump_eq_zero (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {f : ℝ → ℝ} (hf : ∀ x, soninAnnulusBump b c hbc x = 0 → f x = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (hf x h0)

/-- Riemann--Lebesgue with the frequency written directly. -/
theorem tendsto_integral_mul_cos_freq_atTop {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, g x * Real.cos (κ * x)) atTop (𝓝 0) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hscale : Tendsto (fun κ : ℝ => κ / (2 * Real.pi)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun d => ⟨d * (2 * Real.pi), fun a ha => ?_⟩
    rw [le_div_iff₀ hpi]
    exact ha
  have h := (tendsto_integral_mul_cos_atTop hg).comp hscale
  refine h.congr fun κ => ?_
  show (∫ x : ℝ, g x * Real.cos (2 * Real.pi * x * (κ / (2 * Real.pi)))) =
    ∫ x : ℝ, g x * Real.cos (κ * x)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hne : (2 * Real.pi) ≠ 0 := by positivity
  show g x * Real.cos (2 * Real.pi * x * (κ / (2 * Real.pi))) = g x * Real.cos (κ * x)
  rw [show 2 * Real.pi * x * (κ / (2 * Real.pi)) = κ * x by field_simp]

/-- The profile squared is continuous with compact support. -/
theorem integrable_soninAnnulusBump_sq_mul (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun x : ℝ => soninAnnulusBump b c hbc x ^ 2 * f x) := by
  refine Continuous.integrable_of_hasCompactSupport
    (((continuous_soninAnnulusBump b c hbc).pow 2).mul hf) ?_
  refine hasCompactSupport_of_soninAnnulusBump_eq_zero b c hb hbc fun x hx => ?_
  simp [hx]

theorem hasCompactSupport_soninAnnulusBump_sq (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    HasCompactSupport (fun x : ℝ => soninAnnulusBump b c hbc x ^ 2) := by
  refine hasCompactSupport_of_soninAnnulusBump_eq_zero b c hb hbc fun x hx => ?_
  simp [hx]

/-- **The mean correction disappears at high frequency.** -/
theorem tendsto_soninPacketMean_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Tendsto (fun κ : ℝ => soninPacketMean b c hbc κ) atTop (𝓝 0) := by
  have hnum := tendsto_integral_mul_cos_freq_atTop (integrable_soninAnnulusBump b c hb hbc)
  have hmass := (integral_soninAnnulusBump_pos b c hb hbc).ne'
  have := hnum.div_const (∫ x : ℝ, soninAnnulusBump b c hbc x)
  simpa [soninPacketMean] using this

/-- The oscillatory energy moment of the profile also disappears. -/
theorem tendsto_integral_soninAnnulusBump_sq_mul_cos_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x))
      atTop (𝓝 0) :=
  tendsto_integral_mul_cos_freq_atTop
    (Continuous.integrable_of_hasCompactSupport
      ((continuous_soninAnnulusBump b c hbc).pow 2)
      (hasCompactSupport_soninAnnulusBump_sq b c hb hbc))

/-- The doubled-frequency moment disappears as well. -/
theorem tendsto_integral_soninAnnulusBump_sq_mul_cos_two_atTop
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x))
      atTop (𝓝 0) := by
  have hbase := tendsto_integral_soninAnnulusBump_sq_mul_cos_atTop b c hb hbc
  have hscale : Tendsto (fun κ : ℝ => 2 * κ) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  exact hbase.comp hscale

/-- The squared `L²` norm of the wavepacket, expanded. -/
theorem integral_soninPacket_sq_eq (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ∫ x : ℝ, soninPacket b c hbc κ x ^ 2 =
      ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) +
        ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x)) -
        2 * soninPacketMean b c hbc κ *
          (∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x)) +
        soninPacketMean b c hbc κ ^ 2 * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 := by
  set μ := soninPacketMean b c hbc κ with hμ
  have hI1 : Integrable (fun x : ℝ =>
      soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2) :=
    integrable_soninAnnulusBump_sq_mul b c hb hbc
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2)
  have hI2 : Integrable (fun x : ℝ =>
      2 * μ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x))) :=
    ((integrable_soninAnnulusBump_sq_mul b c hb hbc
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).const_mul _)
  have hI4 : Integrable (fun x : ℝ => soninAnnulusBump b c hbc x ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      ((continuous_soninAnnulusBump b c hbc).pow 2)
      (hasCompactSupport_soninAnnulusBump_sq b c hb hbc)
  have hI3 : Integrable (fun x : ℝ => μ ^ 2 * soninAnnulusBump b c hbc x ^ 2) :=
    hI4.const_mul _
  have hI5 : Integrable (fun x : ℝ =>
      soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x)) :=
    integrable_soninAnnulusBump_sq_mul b c hb hbc
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsplit : ∀ x : ℝ, soninPacket b c hbc κ x ^ 2 =
      soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2 -
        2 * μ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x)) +
        μ ^ 2 * soninAnnulusBump b c hbc x ^ 2 := by
    intro x
    simp only [soninPacket, hμ]
    ring
  have hcos : ∀ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2 =
      (2 : ℝ)⁻¹ * soninAnnulusBump b c hbc x ^ 2 +
        (2 : ℝ)⁻¹ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x)) := by
    intro x
    rw [Real.cos_sq (κ * x)]
    rw [show 2 * (κ * x) = 2 * κ * x by ring]
    ring
  have hfirst : ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2 =
      ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) +
        ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x)) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hI4.const_mul _) (hI5.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall hcos)
  calc ∫ x : ℝ, soninPacket b c hbc κ x ^ 2
      = ∫ x : ℝ, (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2 -
            2 * μ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x)) +
            μ ^ 2 * soninAnnulusBump b c hbc x ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = (∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2) -
          (∫ x : ℝ, 2 * μ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x))) +
          ∫ x : ℝ, μ ^ 2 * soninAnnulusBump b c hbc x ^ 2 := by
        have hI12 : Integrable (fun x : ℝ =>
            soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x) ^ 2 -
              2 * μ * (soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x))) := hI1.sub hI2
        rw [integral_add hI12 hI3, integral_sub hI1 hI2]
    _ = _ := by
        rw [hfirst, integral_const_mul, integral_const_mul]

/-- **Normalisation `(6)`.**  The squared `L²` norm of the wavepacket tends to half the profile's
energy, which is positive. -/
theorem tendsto_integral_soninPacket_sq_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, soninPacket b c hbc κ x ^ 2) atTop
      (𝓝 ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)) := by
  have hmean := tendsto_soninPacketMean_atTop b c hb hbc
  have hosc := tendsto_integral_soninAnnulusBump_sq_mul_cos_atTop b c hb hbc
  have hosc2 := tendsto_integral_soninAnnulusBump_sq_mul_cos_two_atTop b c hb hbc
  have hlim :
      Tendsto (fun κ : ℝ =>
        ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) +
          ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x)) -
          2 * soninPacketMean b c hbc κ *
            (∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x)) +
          soninPacketMean b c hbc κ ^ 2 * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)
        atTop (𝓝 ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)) := by
    have h1 : Tendsto (fun κ : ℝ =>
        (2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (2 * κ * x))
        atTop (𝓝 0) := by
      simpa using hosc2.const_mul ((2 : ℝ)⁻¹)
    have h2 : Tendsto (fun κ : ℝ =>
        2 * soninPacketMean b c hbc κ *
          (∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 * Real.cos (κ * x))) atTop (𝓝 0) := by
      simpa using ((hmean.const_mul (2 : ℝ)).mul hosc)
    have h3 : Tendsto (fun κ : ℝ =>
        soninPacketMean b c hbc κ ^ 2 * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)
        atTop (𝓝 0) := by
      simpa using ((hmean.pow 2).mul_const
        (∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2))
    simpa using (((tendsto_const_nhds.add h1).sub h2).add h3)
  refine hlim.congr fun κ => ?_
  exact (integral_soninPacket_sq_eq b c hb hbc κ).symm

/-- The limiting energy is positive, so the wavepacket normalisation never degenerates. -/
theorem integral_soninAnnulusBump_sq_pos (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    0 < ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2 := by
  have hint : Integrable (fun x : ℝ => soninAnnulusBump b c hbc x ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      ((continuous_soninAnnulusBump b c hbc).pow 2)
      (hasCompactSupport_soninAnnulusBump_sq b c hb hbc)
  have hnonneg : 0 ≤ fun x : ℝ => soninAnnulusBump b c hbc x ^ 2 := fun x => sq_nonneg _
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen (Function.support (fun x : ℝ => soninAnnulusBump b c hbc x ^ 2)) :=
    isOpen_ne.preimage ((continuous_soninAnnulusBump b c hbc).pow 2)
  refine hopen.measure_pos volume ⟨(b + c) / 2, ?_⟩
  have := soninAnnulusBump_midpoint b c hb hbc
  simp only [Function.mem_support, this]
  norm_num

end RHTower
