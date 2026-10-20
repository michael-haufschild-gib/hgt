import GaloisForLFunctions.BiScaleUncertainty.PacketOneSidedGrowthLaw
import GaloisForLFunctions.BiScaleUncertainty.AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis

/-!
# The Weil energy of a source is at most the energy of its packet

For a real compact `C²` source `f` the linear packet `P_f` and the quadratic Weil functional of its
autocorrelation `h_f` read the same zeros with different weights: the packet energy weighs a
critical zero by `m_ρ²|f̂(γ_ρ)|²`, the Weil functional by `m_ρ|f̂(γ_ρ)|²`.

**Packet–Weil law** (`packet_weil_law`). If `P_f` is eventually bounded above, then
unconditionally
* `(1/L)∫_w^L P_f² → E(f) = Σ_{Re ρ = 1/2} m_ρ²|f̂(γ_ρ)|²`;
* the Weil functional of `h_f` is `W(f) = Σ_{Re ρ = 1/2} m_ρ|f̂(γ_ρ)|²`, so `0 ≤ W(f) ≤ E(f)`;
* `W(f) = E(f)` iff every critical zero seen by `f` is simple.

In the field's coordinates (`levyWeilEnergy_le_packetEnergy`):
`0 ≤ Ω(0) h_f(0) + 𝒥(f) − 2⟨h_f, ν⟩ ≤ lim (1/L)∫_w^L P_f²` for every real Weil test whose packet is
bounded above. For a source with vanishing prime–polar pairing (a grid-blind polar source) this
is the bi-scale uncertainty inequality `|Ω(0)| h_f(0) ≤ 𝒥(f)`, obtained from a one-sided bound on
a single linear packet (`biScaleUncertainty_of_pairing_eq_zero`). Under RH every packet is bounded above, and the simple-zero conjecture becomes an
energy identity (`forall_mult_eq_one_iff_forall_packet_energy_eq_weil`): all zeros are simple iff
the asymptotic packet energy equals the Weil energy for every source.

**Mechanism.** By the one-sided growth law, a packet bounded above is blind to the zeros right of
the line. Its zero series splits into the critical almost periodic part and a part over zeros left
of the line, which decays (`tendsto_offCritical_zeroSeries`); Parseval on the critical part with
injective ordinates gives `E(f)`. On the Weil side `ĥ_f(γ) = f̂(γ) conj f̂(conj γ)`: right of the
line `f̂(γ_ρ) = 0`; left of it `conj γ_ρ = γ_{1 − ρ̄}` with `1 − ρ̄` right of the line; on the line
`ĥ_f(γ) = |f̂(γ)|²`. Multiplicities satisfy `m ≤ m²`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- The zeros on the critical line. -/
def criticalZeros : Set 𝒵 := {ρ | (ρ : ℂ).re = 1 / 2}

/-- The packet energy weights `m_ρ²|f̂(γ_ρ)|²` over the critical zeros. -/
def criticalPacketEnergy (f : ℝ → ℝ) : ℝ :=
  ∑' ρ : criticalZeros, (Zeta23.zetaZeroConfig.mult ρ : ℝ) ^ 2 *
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2

/-- The Weil weights `m_ρ|f̂(γ_ρ)|²` over the critical zeros. -/
def criticalWeilEnergy (f : ℝ → ℝ) : ℝ :=
  ∑' ρ : criticalZeros, (Zeta23.zetaZeroConfig.mult ρ : ℝ) *
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2

theorem zeroShift_of_mem_critical {ρ : 𝒵} (hρ : ρ ∈ criticalZeros) :
    zeroShift ρ = (((ρ : ℂ).im : ℝ) : ℂ) * I := by
  have h : (ρ : ℂ).re = 1 / 2 := hρ
  apply Complex.ext <;> simp [zeroShift, h]

theorem gammaOf_of_mem_critical {ρ : 𝒵} (hρ : ρ ∈ criticalZeros) :
    Zeta23.gammaOf ρ = (((ρ : ℂ).im : ℝ) : ℂ) := by
  have h := I_mul_gammaOf ρ
  rw [zeroShift_of_mem_critical hρ, mul_comm _ I] at h
  exact mul_left_cancel₀ I_ne_zero h

/-- Off the line the packet coefficient decays or vanishes: left of the line `|e^{λ_ρ τ}| → 0`,
right of it the source is blind. -/
theorem tendsto_offCritical_zeroSeries {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    Tendsto (fun τ : ℝ => ∑' ρ : ↥(criticalZerosᶜ : Set 𝒵),
      packetCoeff f ρ * cexp (zeroShift (ρ : 𝒵) * τ)) atTop (𝓝 0) := by
  have hc := summable_norm_packetCoeff hf hfc
  have hzero : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re → packetCoeff f ρ = 0 := fun ρ h =>
    (packetCoeff_eq_zero_iff f ρ).mpr (hblind ρ h)
  have hnorm : ∀ (ρ : 𝒵) (τ : ℝ), ‖packetCoeff f ρ * cexp (zeroShift ρ * τ)‖ =
      ‖packetCoeff f ρ‖ * Real.exp (((ρ : ℂ).re - 1 / 2) * τ) := fun ρ τ => by
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [zeroShift]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (τ : ℝ) (ρ : ↥(criticalZerosᶜ : Set 𝒵)) => packetCoeff f ρ * cexp (zeroShift (ρ : 𝒵) * τ))
    (g := fun _ => 0) (bound := fun ρ => ‖packetCoeff f ρ‖) (hc.subtype _) (fun ρ => ?_) ?_
  · simpa using h
  · have hρ : ((ρ : 𝒵) : ℂ).re ≠ 1 / 2 := ρ.2
    rcases lt_or_gt_of_ne hρ with hlt | hgt
    · refine squeeze_zero_norm (fun τ => le_of_eq (hnorm ρ τ)) ?_
      have h1 : Tendsto (fun τ : ℝ => Real.exp ((((ρ : 𝒵) : ℂ).re - 1 / 2) * τ)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      simpa using h1.const_mul ‖packetCoeff f ρ‖
    · simp [hzero ρ hgt]
  · filter_upwards [eventually_ge_atTop 0] with τ hτ ρ
    by_cases hgt : 1 / 2 < ((ρ : 𝒵) : ℂ).re
    · simp [hzero ρ hgt]
    · rw [hnorm]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ))

/-- The critical almost periodic series `Σ_{Re ρ = 1/2} m_ρ f̂(γ_ρ) e^{iγ_ρ τ}`. -/
def criticalSeries (f : ℝ → ℝ) (τ : ℝ) : ℂ :=
  ∑' ρ : criticalZeros, packetCoeff f ρ * cexp (((((ρ : 𝒵) : ℂ).im * τ : ℝ) : ℂ) * I)

theorem norm_criticalSeries_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (τ : ℝ) : ‖criticalSeries f τ‖ ≤ ∑' ρ : criticalZeros, ‖packetCoeff f ρ‖ := by
  have ha : Summable fun ρ : criticalZeros => ‖packetCoeff f ρ‖ :=
    (summable_norm_packetCoeff hf hfc).subtype _
  have hn : ∀ ρ : criticalZeros,
      ‖packetCoeff f ρ * cexp (((((ρ : 𝒵) : ℂ).im * τ : ℝ) : ℂ) * I)‖ = ‖packetCoeff f ρ‖ :=
    fun ρ => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact (norm_tsum_le_tsum_norm (ha.congr fun ρ => (hn ρ).symm)).trans
    (le_of_eq (tsum_congr hn))

theorem continuous_criticalSeries {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : Continuous (criticalSeries f) :=
  continuous_tsum (fun ρ => by fun_prop) ((summable_norm_packetCoeff hf hfc).subtype _)
    fun ρ τ => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; rfl

/-- **Critical decomposition of a blind packet.** Beyond the support, the packet of a source blind
to the zeros right of the line is a continuous term tending to `0` minus the critical series. -/
theorem exists_packet_eq_sub_criticalSeries {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    ∃ B : ℝ → ℂ, Continuous B ∧ Tendsto B atTop (𝓝 0) ∧
      ∀ τ, w < τ → (stationaryPacket f τ : ℂ) = B τ - criticalSeries f τ := by
  have hc := summable_norm_packetCoeff hf hfc
  -- the zero series is the critical part plus a decaying part
  have hsplit : ∀ τ : ℝ, zeroSeries (packetCoeff f) τ = criticalSeries f τ +
      ∑' ρ : ↥(criticalZerosᶜ : Set 𝒵), packetCoeff f ρ * cexp (zeroShift (ρ : 𝒵) * τ) :=
    fun τ => by
    have hS : Summable fun ρ : 𝒵 => packetCoeff f ρ * cexp (zeroShift ρ * τ) :=
      Summable.of_norm_bounded (hc.mul_right (Real.exp (|τ| / 2))) fun ρ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_exp_zeroShift_mul_le ρ τ) (norm_nonneg _)
    rw [zeroSeries, ← Summable.tsum_add_tsum_compl (s := criticalZeros) (hS.subtype _)
      (hS.subtype _)]
    congr 1
    refine tsum_congr fun ρ => ?_
    rw [zeroShift_of_mem_critical ρ.2]
    push_cast
    ring_nf
  refine ⟨fun τ => packetArchTail f τ - (zeroSeries (packetCoeff f) τ - criticalSeries f τ),
    (continuous_packetArchTail hf hfc hw).sub
      ((continuous_zeroSeries hc).sub (continuous_criticalSeries hf hfc)), ?_, fun τ hτ => ?_⟩
  · have h := (tendsto_packetArchTail f).sub (tendsto_offCritical_zeroSeries hf hfc hblind)
    rw [sub_zero] at h
    refine h.congr fun τ => ?_
    rw [hsplit τ]
    ring
  · rw [stationaryPacket_eq hf hfc hw0 hw hτ]
    ring

/-- **Unconditional packet Parseval law.** For a real compact `C²` source blind to the zeros right
of the line, `(1/L)∫_w^L P_f² → Σ_{Re ρ = 1/2} m_ρ²|f̂(γ_ρ)|²`. -/
theorem tendsto_mean_sq_stationaryPacket_of_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket f τ ^ 2) / L) atTop
      (𝓝 (criticalPacketEnergy f)) := by
  have hc := summable_norm_packetCoeff hf hfc
  haveI : Countable 𝒵 := (countable_carrier _).to_subtype
  set a : criticalZeros → ℂ := fun ρ => packetCoeff f ρ
  have ha : Summable fun ρ => ‖a ρ‖ := hc.subtype _
  set S₁ := ∑' ρ, ‖a ρ‖
  set Gc : ℝ → ℂ := criticalSeries f
  have hGcb : ∀ τ, ‖Gc τ‖ ≤ S₁ := norm_criticalSeries_le hf hfc
  have hGcc : Continuous Gc := continuous_criticalSeries hf hfc
  obtain ⟨B, hBc, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hf hfc hw0 hw hblind
  have hsq : ∀ τ, w < τ → stationaryPacket f τ ^ 2 = ‖B τ - Gc τ‖ ^ 2 := fun τ hτ => by
    rw [← hEF τ hτ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the decaying error
  set D : ℝ → ℝ := fun τ => ‖B τ - Gc τ‖ ^ 2 - ‖Gc τ‖ ^ 2
  have hDc : Continuous D := by simp only [D]; fun_prop
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have hb : ∀ τ, |D τ| ≤ ‖B τ‖ * (2 * S₁ + ‖B τ‖) := by
      intro τ
      have h3 := hGcb τ
      have h4 := abs_norm_sub_norm_le (B τ - Gc τ) (-(Gc τ))
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at h4
      have hnn := norm_nonneg (B τ)
      have hnA := norm_nonneg (Gc τ)
      rw [abs_le]
      constructor <;> nlinarith [abs_le.mp h4, norm_nonneg (B τ - Gc τ)]
    have hlim : Tendsto (fun τ => ‖B τ‖ * (2 * S₁ + ‖B τ‖)) atTop
        (𝓝 (‖(0 : ℂ)‖ * (2 * S₁ + ‖(0 : ℂ)‖))) :=
      hB0.norm.mul (tendsto_const_nhds.add hB0.norm)
    rw [norm_zero, zero_mul] at hlim
    exact squeeze_zero_norm (fun τ => by rw [Real.norm_eq_abs]; exact hb τ) hlim
  -- Parseval on the critical part
  have hinj : Function.Injective fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ).im := by
    intro ρ ρ' h
    have hr : ((ρ : 𝒵) : ℂ).re = ((ρ' : 𝒵) : ℂ).re := by
      rw [show ((ρ : 𝒵) : ℂ).re = 1 / 2 from ρ.2, show ((ρ' : 𝒵) : ℂ).re = 1 / 2 from ρ'.2]
    exact Subtype.ext (Subtype.ext (Complex.ext hr h))
  have hmain : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L, ‖Gc τ‖ ^ 2) / L) atTop
      (𝓝 (∑' ρ, ‖a ρ‖ ^ 2)) := tendsto_mean_normSq_tsum ha hinj
  have hcesaro := tendsto_mean_of_tendsto_zero hDc hD0 w
  have hconst : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..w, ‖Gc τ‖ ^ 2) / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := (hmain.sub hconst).add hcesaro
  rw [sub_zero, add_zero] at hsum
  have htarget : (∑' ρ, ‖a ρ‖ ^ 2) = criticalPacketEnergy f := by
    refine tsum_congr fun ρ => ?_
    simp only [a, packetCoeff, norm_mul, Complex.norm_natCast, mul_pow,
      gammaOf_of_mem_critical ρ.2]
  rw [htarget] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop w] with L hL
  have hAI : ∀ a b : ℝ, IntervalIntegrable (fun τ => ‖Gc τ‖ ^ 2) volume a b :=
    fun a b => (hGcc.norm.pow 2).intervalIntegrable a b
  have hcongr : (∫ τ in w..L, stationaryPacket f τ ^ 2) =
      ∫ τ in w..L, (‖Gc τ‖ ^ 2 + D τ) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
    rw [uIoc_of_le hL] at hτ
    rw [hsq τ hτ.1]; simp only [D]; ring
  rw [hcongr, intervalIntegral.integral_add (hAI w L) (hDc.intervalIntegrable w L),
    ← intervalIntegral.integral_interval_sub_left (hAI 0 L) (hAI 0 w)]
  field_simp

/-- Reflection across the line conjugates the ordinate: `conj γ_ρ = γ_{1 − ρ̄}`. -/
theorem conj_gammaOf (z : ℂ) : (starRingEnd ℂ) (Zeta23.gammaOf z) =
    Zeta23.gammaOf (Zeta23.reflect z) := by
  simp only [Zeta23.gammaOf, Zeta23.reflect, Complex.div_I, map_neg, map_mul, map_sub,
    Complex.conj_I, map_one, map_div₀, map_ofNat]
  ring

/-- **The Weil functional of a source blind right of the line** is its critical Weil energy:
`literatureRHS(h_f) = Σ_{Re ρ = 1/2} m_ρ|f̂(γ_ρ)|²`. -/
theorem literatureRHS_weilTest_of_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    Zeta23.EF.literatureRHS (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      (criticalWeilEnergy f : ℂ) := by
  set f₀ : ℝ → ℂ := fun u => (f u : ℂ)
  have hf₀ : ContDiff ℝ 2 f₀ := Complex.ofRealCLM.contDiff.comp hf
  have hf₀c : HasCompactSupport f₀ := hfc.comp_left Complex.ofReal_zero
  have hk := Zeta23.EF.weilTest_contDiff hf₀ hf₀.continuous hf₀c
  have hkc := Zeta23.EF.weilTest_hasCompactSupport hf₀c hf₀c
  have hFT : ∀ z : ℂ, Zeta23.paperFT (Zeta23.EF.weilTest f₀ f₀) z =
      Zeta23.paperFT f₀ z * (starRingEnd ℂ) (Zeta23.paperFT f₀ ((starRingEnd ℂ) z)) :=
    Zeta23.EF.paperFT_weilTest hf₀.continuous hf₀.continuous hf₀c hf₀c
  set F : 𝒵 → ℂ := fun ρ => (((Zeta23.zetaZeroConfig.mult ρ : ℝ) *
    ‖Zeta23.paperFT f₀ (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)
  rw [← (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hk hkc).2, criticalWeilEnergy, Complex.ofReal_tsum,
    show (∑' ρ : criticalZeros, F ρ) = ∑' ρ, criticalZeros.indicator F ρ from
      tsum_subtype criticalZeros F]
  refine tsum_congr fun ρ => ?_
  by_cases hρ : ρ ∈ criticalZeros
  · rw [indicator_of_mem hρ, hFT, gammaOf_of_mem_critical hρ, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [F]
    push_cast
    ring
  · rw [indicator_of_notMem hρ, hFT]
    have hne : (ρ : ℂ).re ≠ 1 / 2 := hρ
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : Zeta23.reflect ρ ∈ 𝒵 := Zeta23.zetaZeroConfig.reflect_mem ρ ρ.2
      have hre : 1 / 2 < (Zeta23.reflect ρ).re := by
        simp only [Zeta23.reflect, sub_re, one_re, conj_re]
        linarith
      rw [conj_gammaOf, hblind ⟨_, hmem⟩ hre, map_zero, mul_zero, mul_zero]
    · rw [hblind ρ hgt, zero_mul, mul_zero]

theorem summable_criticalPacketEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Summable fun ρ : criticalZeros => (Zeta23.zetaZeroConfig.mult ρ : ℝ) ^ 2 *
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 := by
  have hc : Summable fun ρ : criticalZeros => ‖packetCoeff f ρ‖ :=
    (summable_norm_packetCoeff hf hfc).subtype _
  set S₁ := ∑' ρ : criticalZeros, ‖packetCoeff f ρ‖
  refine (hc.mul_left S₁).of_nonneg_of_le (fun _ => by positivity) fun ρ => ?_
  have hle : ‖packetCoeff f ρ‖ ≤ S₁ :=
    hc.le_tsum ρ fun _ _ => norm_nonneg _
  have heq : (Zeta23.zetaZeroConfig.mult ρ : ℝ) ^ 2 *
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 =
        ‖packetCoeff f ρ‖ * ‖packetCoeff f ρ‖ := by
    simp only [packetCoeff, norm_mul, Complex.norm_natCast, gammaOf_of_mem_critical ρ.2]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- **Multiplicity comparison.** `W(f) ≤ E(f)`, with equality iff every critical zero seen by `f`
is simple. -/
theorem criticalWeilEnergy_le_criticalPacketEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    criticalWeilEnergy f ≤ criticalPacketEnergy f ∧
      (criticalWeilEnergy f = criticalPacketEnergy f ↔ ∀ ρ : criticalZeros,
        Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ) ≠ 0 →
          Zeta23.zetaZeroConfig.mult ρ = 1) := by
  set x : criticalZeros → ℝ := fun ρ =>
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2
  set m : criticalZeros → ℝ := fun ρ => (Zeta23.zetaZeroConfig.mult ρ : ℝ)
  have hm1 : ∀ ρ, 1 ≤ m ρ := fun ρ => by
    simp only [m]
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
  have hx0 : ∀ ρ, 0 ≤ x ρ := fun ρ => by positivity
  have hterm : ∀ ρ, m ρ * x ρ ≤ m ρ ^ 2 * x ρ := fun ρ =>
    mul_le_mul_of_nonneg_right (by nlinarith [hm1 ρ]) (hx0 ρ)
  have hE : Summable fun ρ => m ρ ^ 2 * x ρ := summable_criticalPacketEnergy hf hfc
  have hW : Summable fun ρ => m ρ * x ρ :=
    hE.of_nonneg_of_le (fun ρ => mul_nonneg (by linarith [hm1 ρ]) (hx0 ρ)) hterm
  refine ⟨hW.tsum_le_tsum hterm hE, ?_⟩
  have hdiff : criticalPacketEnergy f - criticalWeilEnergy f =
      ∑' ρ, (m ρ ^ 2 * x ρ - m ρ * x ρ) := (hE.tsum_sub hW).symm
  have hd0 : ∀ ρ, 0 ≤ m ρ ^ 2 * x ρ - m ρ * x ρ := fun ρ => by linarith [hterm ρ]
  rw [eq_comm, ← sub_eq_zero, hdiff, ← (hE.sub hW).hasSum_iff,
    hasSum_zero_iff_of_nonneg hd0]
  constructor
  · intro h ρ hne
    have h1 := congrFun h ρ
    have hx : 0 < x ρ := by positivity
    have hmm : m ρ * (m ρ - 1) * x ρ = 0 := by simp only [Pi.zero_apply] at h1; linarith
    rcases mul_eq_zero.mp hmm with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith [hm1 ρ]
      · have h4 : (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) = 1 := by
          simp only [m] at h3
          linarith
        exact_mod_cast h4
    · linarith
  · intro h
    funext ρ
    by_cases hne : Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ) = 0
    · simp [x, hne]
    · have h1 : m ρ = 1 := by simp only [m]; exact_mod_cast h ρ hne
      simp [h1]

/-- **Packet–Weil law.** For a real compact `C²` source whose packet is eventually bounded above,
unconditionally: `(1/L)∫_w^L P_f² → E(f)`, the Weil functional of `h_f` is `W(f)`, and
`0 ≤ W(f) ≤ E(f)` with equality iff every critical zero seen by `f` is simple. -/
theorem packet_weil_law {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket f τ ^ 2) / L) atTop
        (𝓝 (criticalPacketEnergy f)) ∧
      Zeta23.EF.literatureRHS (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
        (criticalWeilEnergy f : ℂ) ∧
      0 ≤ criticalWeilEnergy f ∧ criticalWeilEnergy f ≤ criticalPacketEnergy f := by
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
    have h := (packet_upper_iff hf hfc le_rfl).mp
      (by obtain ⟨T, K, hK⟩ := hup; exact ⟨T, K, fun τ hτ => by simpa using hK τ hτ⟩)
    exact fun ρ hρ => h ρ (by linarith)
  refine ⟨tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw0 hw hblind,
    literatureRHS_weilTest_of_blind hf hfc hblind,
    tsum_nonneg fun ρ => by positivity, (criticalWeilEnergy_le_criticalPacketEnergy hf hfc).1⟩

/-- **Field form of the Weil side.** For a real Weil test whose packet is eventually bounded above,
`Ω(0) h_f(0) + 𝒥(f) − 2⟨h_f, ν⟩` is the critical Weil energy `Σ_{Re ρ = 1/2} m_ρ|f̂(γ_ρ)|²`. -/
theorem levyWeilEnergy_eq_criticalWeilEnergy (g : RealWeilTestFn) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
        biScaleLevyEnergy g.source -
        2 * SignedPrimePolar.pairing g.supportScale (RHTower.ArchimedeanAnomaly.autocorr g.source) =
      criticalWeilEnergy g.source := by
  obtain ⟨-, hW, -, -⟩ :=
    packet_weil_law g.contDiff_source g.hasCompactSupport_source hw0 hw hup
  have hbridge :=
    RealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing g
  rw [_root_.RHTower.weilFullFunctional_vonMangoldt, ← g.source_eq, hW, ofReal_re] at hbridge
  rw [g.autocorr_eq 0, ← g.source_eq, ← hbridge]

/-- **Field form.** For a real Weil test whose packet is eventually bounded above,
`0 ≤ Ω(0) h_f(0) + 𝒥(f) − 2⟨h_f, ν⟩ ≤ lim (1/L)∫_w^L P_f²`. -/
theorem levyWeilEnergy_le_packetEnergy (g : RealWeilTestFn) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket g.source τ ^ 2) / L) atTop
        (𝓝 (criticalPacketEnergy g.source)) ∧
      0 ≤ Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source -
          2 * SignedPrimePolar.pairing g.supportScale (RHTower.ArchimedeanAnomaly.autocorr g.source) ∧
      Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source -
          2 * SignedPrimePolar.pairing g.supportScale (RHTower.ArchimedeanAnomaly.autocorr g.source) ≤
        criticalPacketEnergy g.source := by
  obtain ⟨hlim, -, h0, hle⟩ :=
    packet_weil_law g.contDiff_source g.hasCompactSupport_source hw0 hw hup
  rw [levyWeilEnergy_eq_criticalWeilEnergy g hw0 hw hup]
  exact ⟨hlim, h0, hle⟩

/-- **Bi-scale uncertainty from a one-sided packet bound.** If the signed prime–polar pairing of
`h_f` vanishes (a grid-blind source on the polar hyperplane, for instance) and the packet of `f` is
eventually bounded above, then `|Ω(0)| h_f(0) ≤ 𝒥(f)`, with surplus at most the asymptotic packet
energy. -/
theorem biScaleUncertainty_of_pairing_eq_zero (g : RealWeilTestFn) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hpair : SignedPrimePolar.pairing g.supportScale
      (RHTower.ArchimedeanAnomaly.autocorr g.source) = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    0 ≤ Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
        biScaleLevyEnergy g.source ∧
      Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source ≤ criticalPacketEnergy g.source := by
  obtain ⟨-, h0, hle⟩ := levyWeilEnergy_le_packetEnergy g hw0 hw hup
  rw [hpair, mul_zero, sub_zero] at h0 hle
  exact ⟨h0, hle⟩

/-- **Simple zeros as an energy identity.** Under RH, every zero of `ζ` is simple iff for every
real compact `C²` source the asymptotic packet energy equals the Weil energy of `h_f`. -/
theorem forall_mult_eq_one_iff_forall_packet_energy_eq_weil (hRH : RiemannHypothesis) :
    (∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult ρ = 1) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ w : ℝ, 0 ≤ w →
        (∀ v : ℝ, w < |v| → f v = 0) →
          Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket f τ ^ 2) / L) atTop
            (𝓝 (Zeta23.EF.literatureRHS
              (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) := by
  have hblind : ∀ f : ℝ → ℝ, ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun f ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  constructor
  · intro hsimple f hf hfc w hw0 hw
    rw [literatureRHS_weilTest_of_blind hf hfc (hblind f), ofReal_re,
      (criticalWeilEnergy_le_criticalPacketEnergy hf hfc).2.mpr fun ρ _ => hsimple ρ]
    exact tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw0 hw (hblind f)
  · intro h ρ
    obtain ⟨f, hf, hfc, hne⟩ := exists_bump_paperFT_ne_zero (Zeta23.gammaOf ρ)
    obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
    have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
      hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
    have hcrit : ρ ∈ criticalZeros := re_eq_half_of_mem hRH ρ
    have hlim := tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw.le hwz (hblind f)
    have heq := tendsto_nhds_unique hlim (h f hf hfc w hw.le hwz)
    rw [literatureRHS_weilTest_of_blind hf hfc (hblind f), ofReal_re] at heq
    exact (criticalWeilEnergy_le_criticalPacketEnergy hf hfc).2.mp heq.symm ⟨ρ, hcrit⟩
      (by rwa [← gammaOf_of_mem_critical hcrit])

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
