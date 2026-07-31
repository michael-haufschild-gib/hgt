import GaloisForLFunctions.RHTower.SoninAnnulusPacketAsymptotics

/-!
# The annular wavepacket escapes weakly

Pairing the wavepacket against any fixed weight whose product with the profile is integrable gives
an oscillatory integral plus a vanishing multiple of a fixed constant, so the pairing tends to
zero.  This is the weak escape that makes every fixed compact correction disappear along the
family.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- Multiplying a complex integrable function by a cosine keeps it integrable. -/
theorem integrable_complex_mul_cos {h : ℝ → ℂ} (hh : Integrable h) (a : ℝ) :
    Integrable (fun x : ℝ => h x * (Real.cos (a * x) : ℂ)) := by
  refine Integrable.mono' hh.norm
    (hh.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖h x‖ * |Real.cos (a * x)| ≤ ‖h x‖ * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = ‖h x‖ := mul_one _

/-- Complex Riemann--Lebesgue with the frequency written directly. -/
theorem tendsto_integral_complex_mul_cos_freq_atTop {h : ℝ → ℂ} (hh : Integrable h) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, h x * (Real.cos (κ * x) : ℂ)) atTop (𝓝 0) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi) ≠ 0 := by positivity
  have hscale : Tendsto (fun κ : ℝ => κ / (2 * Real.pi)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun d => ⟨d * (2 * Real.pi), fun a ha => ?_⟩
    rw [le_div_iff₀ hpi]
    exact ha
  have hcomp := (tendsto_integral_complex_mul_cos_atTop hh).comp hscale
  refine hcomp.congr fun κ => ?_
  show (∫ x : ℝ, h x * (Real.cos (2 * Real.pi * x * (κ / (2 * Real.pi))) : ℂ)) =
    ∫ x : ℝ, h x * (Real.cos (κ * x) : ℂ)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show h x * (Real.cos (2 * Real.pi * x * (κ / (2 * Real.pi))) : ℂ) =
    h x * (Real.cos (κ * x) : ℂ)
  rw [show 2 * Real.pi * x * (κ / (2 * Real.pi)) = κ * x by field_simp]

/-- **Weak escape `(7)`.**  Every fixed weight integrable against the profile pairs to zero with
the wavepacket at high frequency. -/
theorem tendsto_integral_mul_soninPacket_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {g : ℝ → ℂ}
    (hg : Integrable (fun x : ℝ => g x * (soninAnnulusBump b c hbc x : ℂ))) :
    Tendsto (fun κ : ℝ => ∫ x : ℝ, g x * (soninPacket b c hbc κ x : ℂ)) atTop (𝓝 0) := by
  have hosc := tendsto_integral_complex_mul_cos_freq_atTop hg
  have hmean := tendsto_soninPacketMean_atTop b c hb hbc
  have hsplit : ∀ κ : ℝ, (∫ x : ℝ, g x * (soninPacket b c hbc κ x : ℂ)) =
      (∫ x : ℝ, (g x * (soninAnnulusBump b c hbc x : ℂ)) * (Real.cos (κ * x) : ℂ)) -
        ((soninPacketMean b c hbc κ : ℝ) : ℂ) *
          ∫ x : ℝ, g x * (soninAnnulusBump b c hbc x : ℂ) := by
    intro κ
    have hI1 := integrable_complex_mul_cos hg κ
    have hI2 : Integrable (fun x : ℝ =>
        ((soninPacketMean b c hbc κ : ℝ) : ℂ) *
          (g x * (soninAnnulusBump b c hbc x : ℂ))) := hg.const_mul _
    have hpt : ∀ x : ℝ, g x * (soninPacket b c hbc κ x : ℂ) =
        (g x * (soninAnnulusBump b c hbc x : ℂ)) * (Real.cos (κ * x) : ℂ) -
          ((soninPacketMean b c hbc κ : ℝ) : ℂ) *
            (g x * (soninAnnulusBump b c hbc x : ℂ)) := by
      intro x
      simp only [soninPacket]
      push_cast
      ring
    rw [show (∫ x : ℝ, g x * (soninPacket b c hbc κ x : ℂ)) =
        ∫ x : ℝ, ((g x * (soninAnnulusBump b c hbc x : ℂ)) * (Real.cos (κ * x) : ℂ) -
          ((soninPacketMean b c hbc κ : ℝ) : ℂ) *
            (g x * (soninAnnulusBump b c hbc x : ℂ))) from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hI1 hI2, integral_const_mul]
  have hmeanC : Tendsto (fun κ : ℝ => ((soninPacketMean b c hbc κ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hmean
  have hlim : Tendsto (fun κ : ℝ =>
      (∫ x : ℝ, (g x * (soninAnnulusBump b c hbc x : ℂ)) * (Real.cos (κ * x) : ℂ)) -
        ((soninPacketMean b c hbc κ : ℝ) : ℂ) *
          ∫ x : ℝ, g x * (soninAnnulusBump b c hbc x : ℂ)) atTop (𝓝 0) := by
    simpa using hosc.sub (hmeanC.mul_const
      (∫ x : ℝ, g x * (soninAnnulusBump b c hbc x : ℂ)))
  exact hlim.congr fun κ => (hsplit κ).symm

end RHTower
