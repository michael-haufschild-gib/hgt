import GaloisForLFunctions.BiScaleUncertainty.UniversalProbeLaw

/-!
# The simple zero conjecture as one packet identity

A packet weighs a critical zero by `m_ρ²|f̂(γ_ρ)|²`, the Weil functional of `h_f` by
`m_ρ|f̂(γ_ρ)|²` (`PacketWeilEnergyLaw`). A universal probe `U` sees every zero, so the two energies
agree exactly when every critical zero is simple (`criticalWeilEnergy_eq_iff_simple_of_universal`).

**Criterion** (`riemannHypothesis_and_simple_iff_of_universal`). For a universal probe `U`, RH holds
and every zero of `ζ` is simple iff

* the single packet `P_U` is eventually bounded above, and
* its asymptotic mean square `lim (1/L)∫_w^L P_U²` equals the Weil functional of `h_U`, i.e.
  `Ω(0) h_U(0) + 𝒥(U) − 2⟨h_U, ν⟩` (`riemannHypothesis_and_simple_iff_of_universal_levy`).

Both sides are prime–polar data of one compact source: a linear packet energy and a quadratic
bi-scale energy. Such sources exist as boosts of every nonzero source
(`exists_tilt_simple_zero_criterion`).
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- For a universal probe, packet energy and Weil energy agree iff every critical zero is simple. -/
theorem criticalWeilEnergy_eq_iff_simple_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    criticalWeilEnergy U = criticalPacketEnergy U ↔
      ∀ ρ : criticalZeros, Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) = 1 := by
  rw [(criticalWeilEnergy_le_criticalPacketEnergy hU hUc).2]
  refine ⟨fun h ρ => h ρ ?_, fun h ρ _ => h ρ⟩
  have := hsees ρ
  rwa [gammaOf_of_mem_critical ρ.2] at this

/-- **RH and simple zeros from one packet.** For a universal probe `U` vanishing outside
`[−w, w]`: RH holds and every zero is simple iff the packet of `U` is eventually bounded above and
its asymptotic mean square is the Weil functional of `h_U`. -/
theorem riemannHypothesis_and_simple_iff_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → U v = 0) :
    (RiemannHypothesis ∧ ∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult (ρ : ℂ) = 1) ↔
      (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket U τ ≤ K) ∧
        Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket U τ ^ 2) / L) atTop
          (𝓝 (Zeta23.EF.literatureRHS
            (Zeta23.EF.weilTest (fun u => (U u : ℂ)) (fun u => (U u : ℂ)))).re) := by
  constructor
  · rintro ⟨hRH, hsimple⟩
    have hup := (riemannHypothesis_iff_packet_bddAbove_of_universal hU hUc hsees).mp hRH
    obtain ⟨hlim, hW, -, -⟩ := packet_weil_law hU hUc hw0 hw hup
    refine ⟨hup, ?_⟩
    rw [hW, ofReal_re, (criticalWeilEnergy_eq_iff_simple_of_universal hU hUc hsees).mpr
      fun ρ => hsimple ρ]
    exact hlim
  · rintro ⟨hup, hlim'⟩
    have hRH := (riemannHypothesis_iff_packet_bddAbove_of_universal hU hUc hsees).mpr hup
    obtain ⟨hlim, hW, -, -⟩ := packet_weil_law hU hUc hw0 hw hup
    rw [hW, ofReal_re] at hlim'
    have heq := tendsto_nhds_unique hlim' hlim
    refine ⟨hRH, fun ρ => ?_⟩
    exact (criticalWeilEnergy_eq_iff_simple_of_universal hU hUc hsees).mp heq
      ⟨ρ, re_eq_half_of_mem hRH ρ⟩

/-- The Weil functional of `h_g` in the field's coordinates, unconditionally. -/
theorem re_literatureRHS_weilTest_eq_levy (g : RealWeilTestFn) :
    (Zeta23.EF.literatureRHS (Zeta23.EF.weilTest (fun u => (g.source u : ℂ))
      (fun u => (g.source u : ℂ)))).re =
        Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source -
          2 * SignedPrimePolar.pairing g.supportScale
            (RHTower.ArchimedeanAnomaly.autocorr g.source) := by
  have hbridge :=
    RealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing g
  rw [_root_.RHTower.weilFullFunctional_vonMangoldt, ← g.source_eq] at hbridge
  rw [hbridge, g.autocorr_eq 0, ← g.source_eq]

/-- **Field form.** For a real Weil test `g` whose source is a universal probe: RH holds and every
zero is simple iff the packet of `g` is eventually bounded above and its asymptotic mean square is
`Ω(0) h_g(0) + 𝒥(g) − 2⟨h_g, ν⟩`. -/
theorem riemannHypothesis_and_simple_iff_of_universal_levy (g : RealWeilTestFn)
    (hsees : SeesAllZeros g.source) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0) :
    (RiemannHypothesis ∧ ∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult (ρ : ℂ) = 1) ↔
      (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) ∧
        Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket g.source τ ^ 2) / L) atTop
          (𝓝 (Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
            biScaleLevyEnergy g.source -
            2 * SignedPrimePolar.pairing g.supportScale
              (RHTower.ArchimedeanAnomaly.autocorr g.source))) := by
  rw [← re_literatureRHS_weilTest_eq_levy g]
  exact riemannHypothesis_and_simple_iff_of_universal g.contDiff_source g.hasCompactSupport_source
    hsees hw0 hw

/-- **Existence.** Every nonzero real `φ ∈ C²_c` has a boost `U = e^{tu}φ` for which RH together
with simplicity of all zeros is the single packet criterion above. -/
theorem exists_tilt_simple_zero_criterion {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : φ ≠ 0) :
    ∃ t w : ℝ, 0 ≤ w ∧
      ((RiemannHypothesis ∧ ∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult (ρ : ℂ) = 1) ↔
        (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket (tiltedSource φ t) τ ≤ K) ∧
          Tendsto (fun L : ℝ => (∫ τ in w..L, stationaryPacket (tiltedSource φ t) τ ^ 2) / L)
            atTop (𝓝 (Zeta23.EF.literatureRHS
              (Zeta23.EF.weilTest (fun u => (tiltedSource φ t u : ℂ))
                (fun u => (tiltedSource φ t u : ℂ)))).re)) := by
  obtain ⟨t, ht⟩ := exists_universal_tilt hφ.continuous hφc hφ0
  have hUc := hasCompactSupport_tiltedSource hφc t
  obtain ⟨w, hw, hwf⟩ := hUc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → tiltedSource φ t v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  exact ⟨t, w, hw.le,
    riemannHypothesis_and_simple_iff_of_universal (contDiff_tiltedSource hφ t) hUc ht hw.le hwz⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
