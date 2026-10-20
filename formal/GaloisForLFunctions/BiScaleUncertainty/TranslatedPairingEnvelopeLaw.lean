import GaloisForLFunctions.BiScaleUncertainty.PacketZeroAmplitudeLaw

/-!
# The envelope of the translated pairings of an autocorrelation

For a real compact `C²` source `f`, write `h_f` for its autocorrelation and

`W(h_f) = Re 𝒲(h_f) = Ω(0)h_f(0) + 𝒥(f) − 2⟨h_f, ν⟩`

for the Weil functional of `h_f`. Weil's criterion makes `W(h_f) ≥ 0` for all `f` equivalent to
RH. The packet of `h_f` at shift `τ` is the translated pairing `P_{h_f}(τ) = ⟨h_f(· − τ), ν⟩`.

**Weil bound by one packet** (`weil_le_translated_pairing_frequently`, unconditional).

`W(h_f) ≤ limsup_{τ→∞} −⟨h_f(· − τ), ν⟩`.

This answers the packet frontier question about bounding the Weil energy of `h_f` above by
prime-side data of a single linear packet without the one-sided hypothesis. The one-sided
hypothesis is needed only for equality.

**Envelope law** (`translated_pairing_envelope_law`). Suppose the translated pairings of `h_f`
are eventually bounded on one side, above or below. Then `W(h_f) ≥ 0`, eventually
`|⟨h_f(· − τ), ν⟩| ≤ W(h_f) + ε`, and `−⟨h_f(· − τ), ν⟩ ≥ W(h_f) − ε` at arbitrarily large shifts.
So `W(h_f)` is the exact asymptotic envelope of the translated pairings. A one-sided bound on the
single packet of `h_f` thus gives Weil positivity for `f`.

**Mechanism.** By the one-sided law, a one-sided bound makes `ĥ_f` vanish at the zeros right of
the line. Since `ĥ_f(γ_ρ) = conj ĥ_f(γ_{1−ρ̄})`, it also vanishes at the zeros left of it. So
`𝒲(h_f)` is the critical sum `Σ m_ρ|f̂(γ_ρ)|²` (`literatureRHS_weilTest_of_autocorr_blind`), and
beyond the support `−P_{h_f} = Γ − B`. Here `Γ` has nonnegative coefficients summing to `W(h_f)`,
so `|Γ| ≤ W(h_f)`, and `Γ` recurs to `Γ(0) = W(h_f)`. Without a one-sided bound the pairings are
unbounded in both directions.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

theorem reflect_reflect (z : ℂ) : Zeta23.reflect (Zeta23.reflect z) = z := by
  simp [Zeta23.reflect]

/-- **The Weil functional of an autocorrelation blind right of the line** is the critical Weil
energy: blindness of `ĥ_f` on the right transfers to the left through
`ĥ_f(γ_ρ) = f̂(γ_ρ) conj f̂(γ_{1−ρ̄})`. -/
theorem literatureRHS_weilTest_of_autocorr_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re → Zeta23.paperFT
      (fun u => ((RHTower.ArchimedeanAnomaly.autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0) :
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
  have hblind' : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (Zeta23.EF.weilTest f₀ f₀) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [← autocorr_ofReal_eq_weilTest]; exact hblind ρ hρ
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
  · rw [indicator_of_notMem hρ]
    have hne : (ρ : ℂ).re ≠ 1 / 2 := hρ
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- left of the line: pair with the reflected zero on the right
      have hmem : Zeta23.reflect ρ ∈ 𝒵 := Zeta23.zetaZeroConfig.reflect_mem ρ ρ.2
      have hre : 1 / 2 < (Zeta23.reflect ρ).re := by
        simp only [Zeta23.reflect, sub_re, one_re, conj_re]
        linarith
      have h0 := hblind' ⟨_, hmem⟩ hre
      rw [hFT, conj_gammaOf, reflect_reflect] at h0
      rw [hFT, conj_gammaOf]
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h, map_zero, mul_zero, mul_zero]
      · rw [map_eq_zero] at h
        rw [h, zero_mul, mul_zero]
    · rw [hblind' ρ hgt, mul_zero]

/-- **Envelope of a blind autocorrelation.** If `ĥ_f` vanishes right of the line, the translated
pairings of `h_f` are eventually within `W + ε` of `0` in absolute value, and `−P_{h_f}` returns
above `W − ε` at arbitrarily large shifts, with `W = W_crit(f)`. -/
theorem autocorr_packet_envelope {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re → Zeta23.paperFT
      (fun u => ((RHTower.ArchimedeanAnomaly.autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ →
      |stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ| ≤ criticalWeilEnergy f + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ τ : ℝ, T ≤ τ ∧
      criticalWeilEnergy f - ε ≤ -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ) := by
  set h := RHTower.ArchimedeanAnomaly.autocorr f
  have hh := contDiff_autocorr hf hfc
  have hhc := hasCompactSupport_autocorr hfc
  obtain ⟨w, hw, hwf⟩ := hhc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → h v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  obtain ⟨B, -, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hh hhc hw.le hwz hblind
  haveI : Countable 𝒵 := (countable_carrier _).to_subtype
  set a : criticalZeros → ℂ := fun ρ => packetCoeff h ρ
  set γ : criticalZeros → ℝ := fun ρ => ((ρ : 𝒵) : ℂ).im
  have ha : Summable fun ρ => ‖a ρ‖ := (summable_norm_packetCoeff hh hhc).subtype _
  have hcoeff : ∀ ρ : criticalZeros, a ρ =
      (((Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) *
        ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 : ℝ) : ℂ) := fun ρ => by
    simp only [a, packetCoeff, gammaOf_of_mem_critical ρ.2]
    rw [paperFT_autocorr hf.continuous hfc, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hnorm : ∀ ρ, ‖a ρ‖ = (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) *
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 := fun ρ => by
    rw [hcoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hW : ∑' ρ, ‖a ρ‖ = criticalWeilEnergy f := by
    simp only [hnorm]; rfl
  have hG0 : criticalSeries h 0 = (criticalWeilEnergy f : ℂ) := by
    show apSeries a γ 0 = _
    rw [apSeries, ← hW, Complex.ofReal_tsum]
    refine tsum_congr fun ρ => ?_
    simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [hnorm, hcoeff]
  have hGle : ∀ τ, ‖criticalSeries h τ‖ ≤ criticalWeilEnergy f := fun τ => by
    rw [← hW]
    exact norm_criticalSeries_le hh hhc τ
  have hP : ∀ τ, w < τ → stationaryPacket h τ = (B τ - criticalSeries h τ).re := fun τ hτ => by
    rw [← hEF τ hτ, ofReal_re]
  refine ⟨fun ε hε => ?_, fun ε hε T => ?_⟩
  · obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hB0.norm.eventually
      (ge_mem_nhds (show ‖(0 : ℂ)‖ < ε by simpa using hε)))
    refine ⟨max T₁ (w + 1), fun τ hτ => ?_⟩
    rw [hP τ (by linarith [le_max_right T₁ (w + 1)])]
    calc |(B τ - criticalSeries h τ).re| ≤ ‖B τ - criticalSeries h τ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖B τ‖ + ‖criticalSeries h τ‖ := norm_sub_le _ _
      _ ≤ ε + criticalWeilEnergy f := add_le_add (hT₁ τ (le_of_max_le_left hτ)) (hGle τ)
      _ = criticalWeilEnergy f + ε := add_comm _ _
  · obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hB0.norm.eventually
      (ge_mem_nhds (show ‖(0 : ℂ)‖ < ε / 2 by simpa using half_pos hε)))
    obtain ⟨ξ, hξ, hξG⟩ := exists_large_apSeries_near_zero ha γ (half_pos hε)
      (max (max T T₁) (w + 1))
    refine ⟨ξ, (le_max_left _ _).trans ((le_max_left _ _).trans hξ), ?_⟩
    rw [hP ξ (by linarith [le_max_right (max T T₁) (w + 1)])]
    have hB := hT₁ ξ ((le_max_right _ _).trans ((le_max_left _ _).trans hξ))
    have hG : ‖criticalSeries h ξ - criticalSeries h 0‖ ≤ ε / 2 := hξG
    rw [hG0] at hG
    have hre : criticalWeilEnergy f - ε / 2 ≤ (criticalSeries h ξ).re := by
      have := (Complex.abs_re_le_norm (criticalSeries h ξ - (criticalWeilEnergy f : ℂ))).trans hG
      simp only [sub_re, ofReal_re, abs_le] at this
      linarith [this.1]
    have hBre : (B ξ).re ≤ ε / 2 := (Complex.re_le_norm _).trans hB
    simp only [sub_re]
    linarith

/-- **Envelope law.** If the translated pairings of `h_f` are eventually bounded on one side, then
`W(h_f) ≥ 0`, `|⟨h_f(· − τ), ν⟩| ≤ W(h_f) + ε` eventually, and `−⟨h_f(· − τ), ν⟩ ≥ W(h_f) − ε` at
arbitrarily large shifts. -/
theorem translated_pairing_envelope_law {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hside : (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ ≤ K) ∨
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → -K ≤ stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ) :
    0 ≤ (Zeta23.EF.literatureRHS
        (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re ∧
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ →
      |stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ| ≤
        (Zeta23.EF.literatureRHS
          (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ τ : ℝ, T ≤ τ ∧
      (Zeta23.EF.literatureRHS
          (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re - ε ≤
        -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ) := by
  have hh := contDiff_autocorr hf hfc
  have hhc := hasCompactSupport_autocorr hfc
  have hup_iff := packet_upper_iff hh hhc le_rfl
  have hlow_iff := packet_lower_iff hh hhc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff hlow_iff
  have hblind0 := hside.elim hup_iff.mp hlow_iff.mp
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re → Zeta23.paperFT
      (fun u => ((RHTower.ArchimedeanAnomaly.autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => hblind0 ρ (by linarith)
  rw [literatureRHS_weilTest_of_autocorr_blind hf hfc hblind, ofReal_re]
  exact ⟨tsum_nonneg fun _ => by positivity, autocorr_packet_envelope hf hfc hblind⟩

/-- **Weil bound by one packet**, unconditional: `−⟨h_f(· − τ), ν⟩` exceeds `W(h_f) − ε` at
arbitrarily large shifts, so `W(h_f) ≤ limsup_{τ→∞} −⟨h_f(· − τ), ν⟩`. -/
theorem weil_le_translated_pairing_frequently {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      (Zeta23.EF.literatureRHS
          (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re - ε ≤
        -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ := by
  set W := (Zeta23.EF.literatureRHS
    (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re
  by_cases hlow : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
      -K ≤ stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ
  · exact (translated_pairing_envelope_law hf hfc (Or.inr hlow)).2.2 ε hε T
  · push Not at hlow
    obtain ⟨τ, hτ, hlt⟩ := hlow T (W - ε)
    exact ⟨τ, hτ, by linarith⟩

/-- In the field's coordinates: `Ω(0)h_g(0) + 𝒥(g) − 2⟨h_g, ν⟩ ≤ limsup −⟨h_g(· − τ), ν⟩` for every
real Weil test. -/
theorem weil_le_translated_pairing_frequently_levy (g : RealWeilTestFn) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source -
          2 * SignedPrimePolar.pairing g.supportScale
            (RHTower.ArchimedeanAnomaly.autocorr g.source) - ε ≤
        -SignedPrimePolar.fullPairing (fun x =>
          RHTower.ArchimedeanAnomaly.autocorr g.source (x - τ)) := by
  rw [← re_literatureRHS_weilTest_eq_levy g]
  simp only [← stationaryPacket_eq_fullPairing]
  exact weil_le_translated_pairing_frequently g.contDiff_source g.hasCompactSupport_source hε T

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
