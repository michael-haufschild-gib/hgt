import GaloisForLFunctions.BiScaleUncertainty.PacketBandLaw
import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain

/-!
# The Weil energy is the recurrent maximum of the translated pairings

The packet of the autocorrelation `h_f` at shift `τ` is the prime–polar pairing of the translated
correlation (`stationaryPacket_eq_fullPairing`):

`P_{h_f}(τ) = ⟨h_f(· − τ), ν⟩ = Σ_n Λ(n) n^{-1/2} h_f(log n − τ) − ∫_0^∞ 2cosh(x/2) h_f(x − τ) dx`.

At `τ = 0` this pairing enters the Weil functional; for large `τ` it is governed by the zeros.

**Pairing recurrence law** (`pairing_recurrence_law`). If the packet of `f` is eventually bounded
above (for every `f` under RH), then

`limsup_{τ→∞} −⟨h_f(· − τ), ν⟩ = W(f) = Ω(0) h_f(0) + 𝒥(f) − 2⟨h_f, ν⟩`:

the negated translated pairing is eventually at most `W(f) + ε` and returns above `W(f) − ε` at
arbitrarily large shifts (`pairing_recurrence_law_levy` in the field's coordinates). The Lévy energy
of a source is therefore fixed by prime–polar pairings alone: its pairing at the origin and the
recurrent maximum of its translated pairings.

**Mechanism.** Beyond the support `−P_{h_f} = Γ − B` with `B → 0` and
`Γ(τ) = Σ_{Re ρ = 1/2} m_ρ |f̂(γ_ρ)|² e^{iγ_ρ τ}`. All coefficients are nonnegative, so `|Γ(τ)| ≤ Γ(0) = W(f)`;
truncating to finitely many ordinates and using simultaneous recurrence of finitely many characters
(`GaloisForLFunctions.exists_large_simultaneous_almostPeriod`) makes `Γ` return to `Γ(0)` at
arbitrarily large shifts (`exists_large_apSeries_near_zero`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Packets are translated pairings -/

/-- The packet of a source at shift `τ` is the prime–polar pairing of the translated source. -/
theorem stationaryPacket_eq_fullPairing (H : ℝ → ℝ) (τ : ℝ) :
    stationaryPacket H τ = SignedPrimePolar.fullPairing fun x => H (x - τ) := by
  unfold stationaryPacket SignedPrimePolar.fullPairing
  congr 1
  · refine tsum_congr fun n => ?_
    unfold SignedPrimePolar.primeTerm SignedPrimePolar.primeWeight
    split_ifs with hn
    · rfl
    · interval_cases n <;> simp
  · rw [integral_Ici_eq_integral_Ioi]
    rfl

/-! ## Recurrence of absolutely convergent almost periodic series -/

/-- **Recurrence.** An absolutely convergent almost periodic series returns within `ε` of its value
at `0` at arbitrarily large times. -/
theorem exists_large_apSeries_near_zero {ι : Type*} [Countable ι] {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ ξ : ℝ, R ≤ ξ ∧ ‖apSeries a γ ξ - apSeries a γ 0‖ ≤ ε := by
  classical
  -- a finite set carrying all but `ε/3` of the mass
  obtain ⟨S, hS⟩ := (tendsto_tsum_compl_atTop_zero fun i => ‖a i‖).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity)) |>.exists
  set A := ∑' i, ‖a i‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  set δ := ε / (3 * (A + 1))
  have hδ : 0 < δ := by positivity
  -- simultaneous recurrence of the finitely many characters in `S`
  set u : Fin S.card → ℝ := fun j => γ (S.equivFin.symm j)
  obtain ⟨ξ, hξR, hξ⟩ := GaloisForLFunctions.exists_large_simultaneous_almostPeriod u hδ R
  refine ⟨ξ, hξR, ?_⟩
  have hchar : ∀ i ∈ S, ‖cexp (((γ i * ξ : ℝ) : ℂ) * I) - 1‖ ≤ δ := fun i hi => by
    have h := hξ (S.equivFin ⟨i, hi⟩)
    simp only [u, Equiv.symm_apply_apply] at h
    rw [show (((γ i * ξ : ℝ) : ℂ) * I) = I * ((ξ : ℂ) * ((γ i : ℝ) : ℂ)) by push_cast; ring]
    exact h
  -- split the difference into the finite part and the tail
  set F : ι → ℂ := fun i => a i * (cexp (((γ i * ξ : ℝ) : ℂ) * I) - 1)
  have hFn : ∀ i, ‖F i‖ ≤ 2 * ‖a i‖ := fun i => by
    simp only [F, norm_mul]
    have : ‖cexp (((γ i * ξ : ℝ) : ℂ) * I) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
    nlinarith [norm_nonneg (a i)]
  have hF : Summable fun i => ‖F i‖ :=
    (ha.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _) hFn
  have hdiff : apSeries a γ ξ - apSeries a γ 0 = ∑' i, F i := by
    have hs1 : Summable fun i => a i * cexp (((γ i * ξ : ℝ) : ℂ) * I) :=
      Summable.of_norm (ha.congr fun i => (norm_shift_coeff a γ ξ i).symm)
    have hs0 : Summable fun i => a i * cexp (((γ i * 0 : ℝ) : ℂ) * I) :=
      Summable.of_norm (ha.congr fun i => (norm_shift_coeff a γ 0 i).symm)
    rw [apSeries, apSeries, ← hs1.tsum_sub hs0]
    refine tsum_congr fun i => ?_
    simp only [F, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    ring
  rw [hdiff, ← (Summable.of_norm hF).sum_add_tsum_compl (s := S)]
  have h1 : ‖∑ i ∈ S, F i‖ ≤ ε / 3 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ S, ‖F i‖ ≤ ∑ i ∈ S, ‖a i‖ * δ := Finset.sum_le_sum fun i hi => by
          simp only [F, norm_mul]
          exact mul_le_mul_of_nonneg_left (hchar i hi) (norm_nonneg _)
      _ = (∑ i ∈ S, ‖a i‖) * δ := by rw [Finset.sum_mul]
      _ ≤ A * δ := mul_le_mul_of_nonneg_right
          (ha.sum_le_tsum S fun _ _ => norm_nonneg _) hδ.le
      _ ≤ ε / 3 := by
          simp only [δ]
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have h2 : ‖∑' i : ↥((S : Set ι)ᶜ), F i‖ ≤ 2 * (ε / 3) := by
    refine (norm_tsum_le_tsum_norm (hF.subtype _)).trans ?_
    calc ∑' i : ↥((S : Set ι)ᶜ), ‖F i‖ ≤ ∑' i : ↥((S : Set ι)ᶜ), 2 * ‖a i‖ :=
          (hF.subtype _).tsum_le_tsum (fun i => hFn i) ((ha.mul_left 2).subtype _)
      _ = 2 * ∑' i : ↥((S : Set ι)ᶜ), ‖a i‖ := tsum_mul_left
      _ ≤ 2 * (ε / 3) := by
          have h3 : ∑' i : ↥((S : Set ι)ᶜ), ‖a i‖ ≤ ε / 3 := hS.le
          linarith
  calc ‖∑ i ∈ S, F i + ∑' i : ↥((S : Set ι)ᶜ), F i‖
      ≤ ‖∑ i ∈ S, F i‖ + ‖∑' i : ↥((S : Set ι)ᶜ), F i‖ := norm_add_le _ _
    _ ≤ ε / 3 + 2 * (ε / 3) := add_le_add h1 h2
    _ = ε := by ring

/-! ## The autocorrelation as a source -/

/-- The complexified autocorrelation is the Weil test `f ⋆ f̃`. -/
theorem autocorr_ofReal_eq_weilTest (f : ℝ → ℝ) :
    (fun u => ((RHTower.ArchimedeanAnomaly.autocorr f u : ℝ) : ℂ)) =
      Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
  funext u
  rw [← RHTower.ArchimedeanExactForm.autocorr_neg f u,
    RHTower.ArchimedeanExactForm.autocorr_eq_weilTest, neg_neg]

theorem contDiff_autocorr {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 2 (RHTower.ArchimedeanAnomaly.autocorr f) := by
  have h : ContDiff ℝ 2 (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
    Zeta23.EF.weilTest_contDiff (Complex.ofRealCLM.contDiff.comp hf)
      (Complex.continuous_ofReal.comp hf.continuous) (hfc.comp_left Complex.ofReal_zero)
  rw [← autocorr_ofReal_eq_weilTest] at h
  have := Complex.reCLM.contDiff.comp h
  simpa [Function.comp_def] using this

theorem hasCompactSupport_autocorr {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (RHTower.ArchimedeanAnomaly.autocorr f) := by
  have h : HasCompactSupport (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
    Zeta23.EF.weilTest_hasCompactSupport (hfc.comp_left Complex.ofReal_zero)
      (hfc.comp_left Complex.ofReal_zero)
  rw [← autocorr_ofReal_eq_weilTest] at h
  have := h.comp_left Complex.zero_re
  simpa [Function.comp_def] using this

/-- The transform of the autocorrelation: `ĥ_f(z) = f̂(z) · conj f̂(conj z)`. -/
theorem paperFT_autocorr {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (z : ℂ) :
    Zeta23.paperFT (fun u => ((RHTower.ArchimedeanAnomaly.autocorr f u : ℝ) : ℂ)) z =
      Zeta23.paperFT (fun u => (f u : ℂ)) z *
        conj (Zeta23.paperFT (fun u => (f u : ℂ)) (conj z)) := by
  rw [autocorr_ofReal_eq_weilTest]
  exact Zeta23.EF.paperFT_weilTest (Complex.continuous_ofReal.comp hf)
    (Complex.continuous_ofReal.comp hf) (hfc.comp_left Complex.ofReal_zero)
    (hfc.comp_left Complex.ofReal_zero) z

/-! ## The recurrence law -/

/-- **Pairing recurrence law.** If the packet of a real compact `C²` source is eventually bounded
above, the negated packet of its autocorrelation — the negated translated pairing — is eventually
at most `W(f) + ε` and returns above `W(f) − ε` at arbitrarily large shifts. -/
theorem pairing_recurrence_law {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ →
      -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ ≤ criticalWeilEnergy f + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ τ : ℝ, T ≤ τ ∧
      criticalWeilEnergy f - ε ≤ -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ) := by
  set h := RHTower.ArchimedeanAnomaly.autocorr f
  have hh := contDiff_autocorr hf hfc
  have hhc := hasCompactSupport_autocorr hfc
  -- blindness of `f`, hence of `h_f`
  have hup_iff := packet_upper_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (h u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [paperFT_autocorr hf.continuous hfc, hup_iff.mp hup ρ (by linarith), zero_mul]
  obtain ⟨w, hw, hwf⟩ := hhc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → h v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  obtain ⟨B, -, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hh hhc hw.le hwz hblind
  -- the critical series of `h_f` has nonnegative coefficients summing to `W(f)`
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
  -- the packet is `B − Γ` beyond the support
  have hP : ∀ τ, w < τ → -stationaryPacket h τ = (criticalSeries h τ - B τ).re := fun τ hτ => by
    have := congrArg Complex.re (hEF τ hτ)
    simp only [ofReal_re, sub_re] at this
    simp only [sub_re]
    linarith
  refine ⟨fun ε hε => ?_, fun ε hε T => ?_⟩
  · obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hB0.norm.eventually
      (ge_mem_nhds (show ‖(0 : ℂ)‖ < ε by simpa using hε)))
    refine ⟨max T₁ (w + 1), fun τ hτ => ?_⟩
    rw [hP τ (by linarith [le_max_right T₁ (w + 1)])]
    have h1 := hT₁ τ (le_of_max_le_left hτ)
    calc (criticalSeries h τ - B τ).re ≤ ‖criticalSeries h τ - B τ‖ := Complex.re_le_norm _
      _ ≤ ‖criticalSeries h τ‖ + ‖B τ‖ := norm_sub_le _ _
      _ ≤ criticalWeilEnergy f + ε := add_le_add (hGle τ) h1
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

/-- **Field form.** For a real Weil test whose packet is eventually bounded above, the negated
translated pairings of `h_g` have recurrent maximum `Ω(0) h_g(0) + 𝒥(g) − 2⟨h_g, ν⟩`. -/
theorem pairing_recurrence_law_levy (g : RealWeilTestFn) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ →
      -SignedPrimePolar.fullPairing (fun x =>
        RHTower.ArchimedeanAnomaly.autocorr g.source (x - τ)) ≤
          Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
            biScaleLevyEnergy g.source -
            2 * SignedPrimePolar.pairing g.supportScale
              (RHTower.ArchimedeanAnomaly.autocorr g.source) + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ τ : ℝ, T ≤ τ ∧
      Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
          biScaleLevyEnergy g.source -
          2 * SignedPrimePolar.pairing g.supportScale
            (RHTower.ArchimedeanAnomaly.autocorr g.source) - ε ≤
        -SignedPrimePolar.fullPairing (fun x =>
          RHTower.ArchimedeanAnomaly.autocorr g.source (x - τ))) := by
  rw [levyWeilEnergy_eq_criticalWeilEnergy g hw0 hw hup]
  simp only [← stationaryPacket_eq_fullPairing]
  exact pairing_recurrence_law g.contDiff_source g.hasCompactSupport_source hup

/-- **Under RH** the recurrence law holds for every real compact `C²` source: the negated translated
pairings of `h_f` have recurrent maximum `W(f)`, the Weil energy of `h_f`. -/
theorem pairing_recurrence_law_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τ : ℝ, T ≤ τ →
      -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ ≤ criticalWeilEnergy f + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ T : ℝ, ∃ τ : ℝ, T ≤ τ ∧
      criticalWeilEnergy f - ε ≤ -stationaryPacket (RHTower.ArchimedeanAnomaly.autocorr f) τ) := by
  refine pairing_recurrence_law hf hfc ?_
  obtain ⟨T, K, hK⟩ := (packet_upper_iff hf hfc le_rfl).mpr fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    norm_num at hρ
  exact ⟨T, K, fun τ hτ => by simpa using hK τ hτ⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
