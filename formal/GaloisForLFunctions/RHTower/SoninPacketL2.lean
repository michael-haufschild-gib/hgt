import GaloisForLFunctions.RHTower.SoninPacketWeakEscape
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# The annular wavepacket as a vector of the even Sonin space

The wavepacket is continuous with compact support, so it defines an element of `L²(ℝ)`, and it is
even, so that element lies in the even subspace.  Pairing it against a fixed `L²` weight is the
integral pairing of the previous module, so the packet family escapes weakly, and every fixed
compact operator therefore kills it in the limit.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- The complexified wavepacket is square integrable. -/
theorem memLp_soninPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    MemLp (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) 2 (volume : Measure ℝ) := by
  refine Continuous.memLp_of_hasCompactSupport
    (Complex.continuous_ofReal.comp (continuous_soninPacket b c hbc κ)) ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninPacket b c hb hbc κ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- The wavepacket as an element of `L²(ℝ)`. -/
def soninPacketL2 (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) : SoninL2 :=
  (memLp_soninPacket b c hb hbc κ).toLp _

theorem soninPacketL2_coeFn (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    (soninPacketL2 b c hb hbc κ : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (soninPacket b c hbc κ x : ℂ) :=
  MemLp.coeFn_toLp (memLp_soninPacket b c hb hbc κ)

/-- The wavepacket is even, so its `L²` class lies in the even subspace. -/
theorem soninPacketL2_mem_evenSubspace (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    soninPacketL2 b c hb hbc κ ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hrefl := l2Reflection_ae (soninPacketL2 b c hb hbc κ)
  have hcoe := soninPacketL2_coeFn b c hb hbc κ
  have hcoeNeg := hcoe.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hrefl, hcoe, hcoeNeg] with x hx hval hvalNeg
  rw [hx]
  have hvalNeg' : (soninPacketL2 b c hb hbc κ : ℝ → ℂ) (-x) =
      (soninPacket b c hbc κ (-x) : ℂ) := by
    simpa [Function.comp_apply] using hvalNeg
  rw [hvalNeg', hval, soninPacket_even b c hbc κ x]

/-- The wavepacket as a vector of the even Sonin carrier. -/
def soninPacketEven (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) : evenSubspace :=
  ⟨soninPacketL2 b c hb hbc κ, soninPacketL2_mem_evenSubspace b c hb hbc κ⟩

@[simp] theorem coe_soninPacketEven (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ((soninPacketEven b c hb hbc κ : evenSubspace) : SoninL2) =
      soninPacketL2 b c hb hbc κ := rfl

/-- The complexified profile is square integrable. -/
theorem memLp_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    MemLp (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) 2 (volume : Measure ℝ) := by
  refine Continuous.memLp_of_hasCompactSupport
    (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc)) ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- Conjugation preserves square integrability. -/
theorem memLp_conj {g : ℝ → ℂ} (h : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => (starRingEnd ℂ) (g x)) 2 (volume : Measure ℝ) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable h.1, ?_⟩
  have hn : ∀ x : ℝ, ‖(starRingEnd ℂ) (g x)‖ = ‖g x‖ := fun x => by simp
  calc eLpNorm (fun x : ℝ => (starRingEnd ℂ) (g x)) 2 volume
      = eLpNorm g 2 volume :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall hn)
    _ < ⊤ := h.2

/-- **Weak escape in `L²`.**  Every fixed `L²` weight pairs to zero with the wavepacket at high
frequency. -/
theorem tendsto_inner_soninPacketL2_atTop (b c : ℝ) (hb : 0 < b) (hbc : b < c) (g : SoninL2) :
    Tendsto (fun κ : ℝ => ⟪g, soninPacketL2 b c hb hbc κ⟫_ℂ) atTop (𝓝 0) := by
  have hgphi : Integrable (fun x : ℝ =>
      (starRingEnd ℂ) ((g : ℝ → ℂ) x) * (soninAnnulusBump b c hbc x : ℂ)) := by
    refine MemLp.integrable_mul (p := 2) (q := 2) ?_ (memLp_soninAnnulusBump b c hb hbc)
    exact memLp_conj (Lp.memLp g)
  have hpair := tendsto_integral_mul_soninPacket_atTop b c hb hbc hgphi
  refine hpair.congr fun κ => ?_
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [soninPacketL2_coeFn b c hb hbc κ] with x hx
  rw [hx, RCLike.inner_apply]
  ring

/-- The mean correction never exceeds one in absolute value. -/
theorem abs_soninPacketMean_le_one (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    |soninPacketMean b c hbc κ| ≤ 1 := by
  have hmass := integral_soninAnnulusBump_pos b c hb hbc
  have hI1 := integrable_soninAnnulusBump_mul_cos b c hb hbc κ
  have hI2 := integrable_soninAnnulusBump b c hb hbc
  have hnum : |∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (κ * x)| ≤
      ∫ x : ℝ, soninAnnulusBump b c hbc x := by
    calc |∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (κ * x)|
        ≤ ∫ x : ℝ, |soninAnnulusBump b c hbc x * Real.cos (κ * x)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x : ℝ, soninAnnulusBump b c hbc x := by
          refine integral_mono hI1.abs hI2 fun x => ?_
          rw [abs_mul, abs_of_nonneg (soninAnnulusBump_nonneg b c hbc x)]
          calc soninAnnulusBump b c hbc x * |Real.cos (κ * x)|
              ≤ soninAnnulusBump b c hbc x * 1 := by
                gcongr
                · exact soninAnnulusBump_nonneg b c hbc x
                · exact Real.abs_cos_le_one _
            _ = soninAnnulusBump b c hbc x := mul_one _
  rw [soninPacketMean, abs_div, abs_of_pos hmass, div_le_one hmass]
  exact hnum

/-- The wavepacket never exceeds twice the profile. -/
theorem abs_soninPacket_le (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ x : ℝ) :
    |soninPacket b c hbc κ x| ≤ 2 * soninAnnulusBump b c hbc x := by
  have hμ := abs_soninPacketMean_le_one b c hb hbc κ
  have hφ := soninAnnulusBump_nonneg b c hbc x
  rw [soninPacket, abs_mul, abs_of_nonneg hφ]
  have hfac : |Real.cos (κ * x) - soninPacketMean b c hbc κ| ≤ 2 := by
    calc |Real.cos (κ * x) - soninPacketMean b c hbc κ|
        ≤ |Real.cos (κ * x)| + |soninPacketMean b c hbc κ| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) hμ
      _ = 2 := by norm_num
  calc soninAnnulusBump b c hbc x * |Real.cos (κ * x) - soninPacketMean b c hbc κ|
      ≤ soninAnnulusBump b c hbc x * 2 := by gcongr
    _ = 2 * soninAnnulusBump b c hbc x := mul_comm _ _

/-- The profile as an element of `L²(ℝ)`. -/
def soninBumpL2 (b c : ℝ) (hb : 0 < b) (hbc : b < c) : SoninL2 :=
  (memLp_soninAnnulusBump b c hb hbc).toLp _

/-- **Uniform bound.**  The wavepacket family is bounded in `L²` independently of the frequency. -/
theorem norm_soninPacketL2_le (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ‖soninPacketL2 b c hb hbc κ‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ := by
  have hbound : ∀ᵐ x : ℝ, ‖(soninPacket b c hbc κ x : ℂ)‖ ≤
      ‖((2 : ℝ) • fun y : ℝ => (soninAnnulusBump b c hbc y : ℂ)) x‖ := by
    filter_upwards with x
    have h := abs_soninPacket_le b c hb hbc κ x
    have hφ := soninAnnulusBump_nonneg b c hbc x
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 2 * soninAnnulusBump b c hbc x)] using h
  have hmono := eLpNorm_mono_ae (p := 2) (μ := (volume : Measure ℝ)) hbound
  have hfin : eLpNorm (fun y : ℝ => (soninAnnulusBump b c hbc y : ℂ)) 2
      (volume : Measure ℝ) ≠ ⊤ := (memLp_soninAnnulusBump b c hb hbc).2.ne
  have hsmul : eLpNorm ((2 : ℝ) • fun y : ℝ => (soninAnnulusBump b c hbc y : ℂ)) 2
      (volume : Measure ℝ) =
      ‖(2 : ℝ)‖ₑ * eLpNorm (fun y : ℝ => (soninAnnulusBump b c hbc y : ℂ)) 2 volume :=
    eLpNorm_const_smul (2 : ℝ) _ 2 volume
  rw [hsmul] at hmono
  have hle := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hmono
  rw [ENNReal.toReal_mul] at hle
  rw [soninPacketL2, soninBumpL2, Lp.norm_toLp, Lp.norm_toLp]
  simpa using hle

end RHTower
