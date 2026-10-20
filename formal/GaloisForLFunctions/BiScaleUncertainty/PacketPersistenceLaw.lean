import GaloisForLFunctions.BiScaleUncertainty.PacketWeilEnergyLaw
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# Every nonzero compact packet oscillates

A nonzero compact source cannot be blind to all critical zeros: its transform is entire of
exponential type, while the simple critical ordinates have superlinear density
(`RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero`). For the packet
this gives, unconditionally:

* `exists_critical_paperFT_ne_zero`: every nonzero real compact source sees a critical zero;
* `criticalWeilEnergy_pos`, `criticalPacketEnergy_pos`: its critical Weil and packet energies are
  positive. A nonzero real Weil test with vanishing prime–polar pairing whose packet is bounded
  above satisfies the strict bi-scale uncertainty inequality `|Ω(0)| h_f(0) < 𝒥(f)`
  (`biScaleUncertainty_strict_of_pairing_eq_zero`);
* **packet persistence** (`packet_oscillates_of_ne_zero`): for every nonzero real compact `C²`
  source there is `c > 0` with `P_f(τ) > c` and `P_f(τ) < −c` at arbitrarily large `τ`; no such
  packet converges (`not_tendsto_stationaryPacket`).

**Mechanism.** If `P_f` is unbounded above it sees a zero right of the line and is unbounded on
both sides (one-sided growth law). Otherwise it is bounded and, beyond the support, `P_f = B − G`
with `B → 0` and `G` the critical almost periodic series. `G` has no zero frequency because
`ζ(1/2) ≠ 0`, so `P_f` has Cesàro mean `0` (`tendsto_mean_tsum_exp`) and mean square `E(f) > 0`. If
`−M ≤ P_f ≤ c` eventually, then `(P_f + M)(P_f − c) ≤ 0`, i.e. `P_f² ≤ (c − M)P_f + Mc`, and
averaging gives `E(f) ≤ Mc`, impossible for `c = E(f)/(2(M + 1))` (`frequently_gt_of_mean`).
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Means of almost periodic series and of signals -/

/-- **Bohr mean.** An absolutely convergent almost periodic series without zero frequency has
Cesàro mean `0`. -/
theorem tendsto_mean_tsum_exp {ι : Type*} [Countable ι] {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {γ : ι → ℝ} (hγ : ∀ i, γ i ≠ 0) :
    Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L, ∑' i, a i * cexp ((γ i * τ : ℝ) * I)) / L)
      atTop (𝓝 0) := by
  have hn : ∀ i (τ : ℝ), ‖a i * cexp ((γ i * τ : ℝ) * I)‖ = ‖a i‖ := fun i τ => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hmean : ∀ L : ℝ, (∫ τ in (0 : ℝ)..L, ∑' i, a i * cexp ((γ i * τ : ℝ) * I)) / L =
      ∑' i, a i * characterMean (γ i) L := by
    intro L
    have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := L) (F := fun i τ => a i * cexp ((γ i * τ : ℝ) * I))
      (f := fun τ => ∑' i, a i * cexp ((γ i * τ : ℝ) * I))
      (fun (i : ι) (_ : ℝ) => ‖a i‖)
      (fun i => (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun i => Eventually.of_forall fun τ _ => (hn i τ).le)
      (Eventually.of_forall fun τ _ => ha)
      intervalIntegrable_const
      (Eventually.of_forall fun τ _ =>
        (Summable.of_norm (ha.congr fun i => (hn i τ).symm)).hasSum)
    rw [← hsum.tsum_eq, ← tsum_div_const]
    exact tsum_congr fun i => by rw [intervalIntegral.integral_const_mul, characterMean, mul_div_assoc]
  simp_rw [hmean]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun i => ‖a i‖) ha
    (f := fun L i => a i * characterMean (γ i) L) (g := fun _ => 0)
    (fun i => by simpa using (tendsto_characterMean (hγ i)).const_mul (a i))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL i
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_characterMean_le _ hL))
  simpa using h

/-- **Sign from mean and energy.** A continuous real signal with Cesàro mean `0`, mean square
`E > 0` and eventual bound `|p| ≤ M` exceeds `E/(2(M+1))` at arbitrarily large times. -/
theorem frequently_gt_of_mean {p : ℝ → ℝ} (hp : Continuous p) {w E M T₀ : ℝ}
    (hmean : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ) / L) atTop (𝓝 0))
    (hsq : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ ^ 2) / L) atTop (𝓝 E)) (hE : 0 < E)
    (hM : ∀ τ, T₀ ≤ τ → |p τ| ≤ M) (T : ℝ) :
    ∃ τ, T ≤ τ ∧ E / (2 * (M + 1)) < p τ := by
  by_contra h
  push Not at h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM T₀ le_rfl)
  set c := E / (2 * (M + 1))
  set T₂ := max (max T T₀) w
  -- `q = (c − M)p + Mc − p² ≥ 0` beyond `T₂`
  set q : ℝ → ℝ := fun τ => (c - M) * p τ + M * c - p τ ^ 2
  have hqc : Continuous q := by fun_prop
  have hq0 : ∀ τ, T₂ ≤ τ → 0 ≤ q τ := fun τ hτ => by
    have h1 := h τ ((le_max_left _ _).trans ((le_max_left _ _).trans hτ))
    have h2 := (abs_le.mp (hM τ ((le_max_right _ _).trans ((le_max_left _ _).trans hτ)))).1
    simp only [q]
    nlinarith
  -- its mean tends to `Mc − E`
  have hII : ∀ L, IntervalIntegrable p volume w L := fun L => hp.intervalIntegrable _ _
  have hII2 : ∀ L, IntervalIntegrable (fun τ => p τ ^ 2) volume w L :=
    fun L => (hp.pow 2).intervalIntegrable _ _
  have hqint : ∀ L, ∫ τ in w..L, q τ =
      (c - M) * (∫ τ in w..L, p τ) + M * c * (L - w) - ∫ τ in w..L, p τ ^ 2 := fun L => by
    simp only [q]
    rw [intervalIntegral.integral_sub ((hII L).const_mul _ |>.add intervalIntegrable_const)
      (hII2 L), intervalIntegral.integral_add ((hII L).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlen : Tendsto (fun L : ℝ => (L - w) / L) atTop (𝓝 1) := by
    have h1 : Tendsto (fun L : ℝ => 1 - w / L) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    field_simp
  have hqmean : Tendsto (fun L : ℝ => (∫ τ in w..L, q τ) / L) atTop
      (𝓝 ((c - M) * 0 + M * c * 1 - E)) := by
    refine ((hmean.const_mul (c - M)).add (hlen.const_mul (M * c))).sub hsq |>.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [hqint]
    field_simp
  -- and it is eventually at least `C₀/L → 0`
  set C₀ := ∫ τ in w..T₂, q τ
  have hlow : Tendsto (fun L : ℝ => C₀ / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hle : ∀ᶠ L in atTop, C₀ / L ≤ (∫ τ in w..L, q τ) / L := by
    filter_upwards [eventually_ge_atTop T₂, eventually_gt_atTop (0 : ℝ)] with L hL hL0
    refine div_le_div_of_nonneg_right ?_ hL0.le
    rw [← intervalIntegral.integral_add_adjacent_intervals (hqc.intervalIntegrable w T₂)
      (hqc.intervalIntegrable T₂ L)]
    have : 0 ≤ ∫ τ in T₂..L, q τ :=
      intervalIntegral.integral_nonneg hL fun τ hτ => hq0 τ hτ.1
    linarith
  have hlim := le_of_tendsto_of_tendsto hlow hqmean hle
  have hMc : M * c < E := by
    have hpos : 0 < M + 1 := by linarith
    simp only [c]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ## Critical zeros seen by a compact source -/

/-- **No nonzero compact source is blind to the critical line.** -/
theorem exists_critical_paperFT_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hne : f ≠ 0) :
    ∃ ρ : criticalZeros, Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have h0 := RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero
    (f := fun u => (f u : ℂ)) (Complex.continuous_ofReal.comp hf)
    (hfc.comp_left Complex.ofReal_zero) fun t ht => by
      rw [RHTower.CompactTestXiDivisibility.XiC_ofReal_eq_xi_linePt] at ht
      have hz := (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp ht).1
      have hre : (_root_.RHTower.linePt t).re = 1 / 2 := by simp [_root_.RHTower.linePt]
      have him : (_root_.RHTower.linePt t).im = t := by simp [_root_.RHTower.linePt]
      have hmem : _root_.RHTower.linePt t ∈ 𝒵 := ⟨hz, by rw [hre]; norm_num, by rw [hre]; norm_num⟩
      have := h ⟨⟨_, hmem⟩, hre⟩
      simpa [him] using this
  funext u
  simpa using congrFun h0 u

theorem criticalPacketEnergy_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hne : f ≠ 0) : 0 < criticalPacketEnergy f := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_critical_paperFT_ne_zero hf.continuous hfc hne
  have hm : (1 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) := by
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ₀ : 𝒵).2
  refine lt_of_lt_of_le ?_ ((summable_criticalPacketEnergy hf hfc).le_tsum ρ₀
    fun _ _ => by positivity)
  have : 0 < ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ₀ : 𝒵) : ℂ).im : ℂ)‖ := norm_pos_iff.mpr hρ₀
  positivity

theorem criticalWeilEnergy_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hne : f ≠ 0) : 0 < criticalWeilEnergy f := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_critical_paperFT_ne_zero hf.continuous hfc hne
  have hm1 : ∀ ρ : criticalZeros, (1 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) := fun ρ => by
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
  have hW : Summable fun ρ : criticalZeros => (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) *
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 :=
    (summable_criticalPacketEnergy hf hfc).of_nonneg_of_le (fun ρ => by positivity) fun ρ =>
      mul_le_mul_of_nonneg_right (by nlinarith [hm1 ρ]) (by positivity)
  refine lt_of_lt_of_le ?_ (hW.le_tsum ρ₀ fun _ _ => by positivity)
  have : 0 < ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ₀ : 𝒵) : ℂ).im : ℂ)‖ := norm_pos_iff.mpr hρ₀
  have := hm1 ρ₀
  positivity

/-- **Strict bi-scale uncertainty from a one-sided packet bound.** A nonzero real Weil test with
vanishing prime–polar pairing whose packet is eventually bounded above has
`|Ω(0)| h_f(0) < 𝒥(f)`. -/
theorem biScaleUncertainty_strict_of_pairing_eq_zero (g : RealWeilTestFn) (hne : g.source ≠ 0)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hpair : SignedPrimePolar.pairing g.supportScale
      (RHTower.ArchimedeanAnomaly.autocorr g.source) = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    0 < Zeta23.EF.gammaBracket 0 * RHTower.ArchimedeanAnomaly.autocorr g.source 0 +
      biScaleLevyEnergy g.source := by
  have h := levyWeilEnergy_eq_criticalWeilEnergy g hw0 hw hup
  rw [hpair, mul_zero, sub_zero] at h
  rw [h]
  exact criticalWeilEnergy_pos g.contDiff_source g.hasCompactSupport_source hne

/-! ## Packet persistence -/

/-- The critical ordinates are nonzero: `ζ(1/2) ≠ 0`. -/
theorem im_ne_zero_of_mem_critical (ρ : criticalZeros) : ((ρ : 𝒵) : ℂ).im ≠ 0 := by
  intro h
  have hre : ((ρ : 𝒵) : ℂ).re = 1 / 2 := ρ.2
  have hρ : ((ρ : 𝒵) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hre, h]
  exact _root_.RHTower.riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
    (by rw [← hρ]; exact (ρ : 𝒵).2.1)

/-- **Packet persistence.** Every nonzero real compact `C²` source has a packet above `c` and below
`−c` at arbitrarily large shifts, for some `c > 0`. -/
theorem packet_oscillates_of_ne_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hne : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, (∃ τ, T ≤ τ ∧ c < stationaryPacket f τ) ∧
      ∃ τ, T ≤ τ ∧ stationaryPacket f τ < -c := by
  have hup_iff := packet_upper_iff hf hfc le_rfl
  have hlow_iff := packet_lower_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff hlow_iff
  by_cases hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K
  · -- bounded above: blind right of the line, bounded, critical almost periodic
    have hblind0 := hup_iff.mp hup
    have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
      fun ρ hρ => hblind0 ρ (by linarith)
    obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
    have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
      hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
    obtain ⟨T₀, M, hM⟩ := (packet_bounded_iff_blind hf hfc).mpr hblind
    obtain ⟨B, hBc, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hf hfc hw.le hwz hblind
    set p : ℝ → ℝ := fun τ => (B τ - criticalSeries f τ).re
    have hpc : Continuous p :=
      Complex.continuous_re.comp (hBc.sub (continuous_criticalSeries hf hfc))
    have hpP : ∀ τ, w < τ → p τ = stationaryPacket f τ := fun τ hτ => by
      simp only [p]
      rw [← hEF τ hτ, ofReal_re]
    -- mean square
    have hsq : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ ^ 2) / L) atTop
        (𝓝 (criticalPacketEnergy f)) := by
      refine (tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw.le hwz hblind).congr' ?_
      filter_upwards [eventually_ge_atTop w] with L hL
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
      rw [uIoc_of_le hL] at hτ
      rw [hpP τ hτ.1]
    -- mean
    have hmean : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ) / L) atTop (𝓝 0) := by
      haveI : Countable 𝒵 := (countable_carrier _).to_subtype
      have hG := tendsto_mean_tsum_exp ((summable_norm_packetCoeff hf hfc).subtype _)
        (γ := fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ).im) im_ne_zero_of_mem_critical
      have hGre : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L, (criticalSeries f τ).re) / L) atTop
          (𝓝 0) := by
        have h := (Complex.continuous_re.tendsto _).comp hG
        rw [zero_re] at h
        refine h.congr' (Eventually.of_forall fun L => ?_)
        have hcomm : ∫ τ in (0 : ℝ)..L, (criticalSeries f τ).re =
            (∫ τ in (0 : ℝ)..L, criticalSeries f τ).re := by
          have := Complex.reCLM.intervalIntegral_comp_comm
            ((continuous_criticalSeries hf hfc).intervalIntegrable (μ := volume) 0 L)
          simpa using this
        show ((∫ τ in (0 : ℝ)..L, criticalSeries f τ) / (L : ℂ)).re =
          (∫ τ in (0 : ℝ)..L, (criticalSeries f τ).re) / L
        rw [hcomm, Complex.div_ofReal_re]
      have hBre := tendsto_mean_of_tendsto_zero (Complex.continuous_re.comp hBc)
        (by simpa using (Complex.continuous_re.tendsto 0).comp hB0) w
      have hconst : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..w, (criticalSeries f τ).re) / L)
          atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have h := hBre.sub (hGre.sub hconst)
      rw [sub_zero, sub_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      have hGI : ∀ a b : ℝ, IntervalIntegrable (fun τ => (criticalSeries f τ).re) volume a b :=
        fun a b => (Complex.continuous_re.comp (continuous_criticalSeries hf hfc)).intervalIntegrable
          a b
      simp only [Function.comp_apply, p, sub_re]
      rw [intervalIntegral.integral_sub (f := fun τ => (B τ).re)
        (g := fun τ => (criticalSeries f τ).re)
        ((Complex.continuous_re.comp hBc).intervalIntegrable w L) (hGI w L),
        ← intervalIntegral.integral_interval_sub_left (hGI 0 L) (hGI 0 w)]
      ring
    have hM' : ∀ τ, max T₀ (w + 1) ≤ τ → |p τ| ≤ M := fun τ hτ => by
      rw [hpP τ (by linarith [le_max_right T₀ (w + 1)])]
      exact hM τ (le_of_max_le_left hτ)
    have hE := criticalPacketEnergy_pos hf hfc hne
    refine ⟨criticalPacketEnergy f / (2 * (M + 1)), ?_, fun T => ⟨?_, ?_⟩⟩
    · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM T₀ le_rfl)
      positivity
    · obtain ⟨τ, hτ, hgt⟩ := frequently_gt_of_mean hpc hmean hsq hE hM' (max T (w + 1))
      exact ⟨τ, le_of_max_le_left hτ,
        by rwa [← hpP τ (by linarith [le_max_right T (w + 1)])]⟩
    · obtain ⟨τ, hτ, hgt⟩ := frequently_gt_of_mean hpc.neg
        (by simpa [neg_div, intervalIntegral.integral_neg] using hmean.neg)
        (by simpa [neg_sq] using hsq) hE (fun τ hτ => by rw [Pi.neg_apply, abs_neg]; exact hM' τ hτ)
        (max T (w + 1))
      have hgt' : criticalPacketEnergy f / (2 * (M + 1)) < -p τ := hgt
      refine ⟨τ, le_of_max_le_left hτ, ?_⟩
      rw [← hpP τ (by linarith [le_max_right T (w + 1)])]
      linarith
  · -- unbounded above: then also unbounded below
    refine ⟨1, one_pos, fun T => ⟨?_, ?_⟩⟩
    · push Not at hup
      obtain ⟨τ, hτ, h⟩ := hup T 1
      exact ⟨τ, hτ, h⟩
    · by_contra h
      push Not at h
      exact hup (hup_iff.mpr (hlow_iff.mp ⟨T, 1, h⟩))

/-- **No nonzero compact packet converges.** -/
theorem not_tendsto_stationaryPacket {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hne : f ≠ 0) (l : ℝ) :
    ¬ Tendsto (stationaryPacket f) atTop (𝓝 l) := by
  intro hl
  obtain ⟨c, hc, hosc⟩ := packet_oscillates_of_ne_zero hf hfc hne
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hl.eventually (Metric.ball_mem_nhds l hc))
  obtain ⟨τ₁, hτ₁, h₁⟩ := (hosc T).1
  obtain ⟨τ₂, hτ₂, h₂⟩ := (hosc T).2
  have e₁ := hT τ₁ hτ₁
  have e₂ := hT τ₂ hτ₂
  rw [Real.dist_eq, abs_lt] at e₁ e₂
  rcases le_or_gt 0 l with hl0 | hl0 <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
