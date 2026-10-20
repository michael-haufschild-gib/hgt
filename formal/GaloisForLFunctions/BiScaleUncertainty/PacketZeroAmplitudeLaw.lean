import GaloisForLFunctions.BiScaleUncertainty.MultiplicityCeilingLaw

/-!
# Per-zero amplitude law: every zero a probe sees is felt in both directions

**Per-zero amplitude law** (`packet_zero_amplitude_law`, unconditional). For every real compact
`C²` source `f` and every critical zero `ρ`,

`limsup_{τ→∞} P_f(τ) ≥ m_ρ |f̂(γ_ρ)|`,  `liminf_{τ→∞} P_f(τ) ≤ −m_ρ |f̂(γ_ρ)|`.

This makes the oscillation of a packet quantitative for every probe, in terms of the zeros it
sees, with no dilation structure.

**Mechanism.** A packet that is not bounded above is unbounded in both directions (the one-sided
law). Otherwise `P_f = B − Γ` beyond the support, with `B → 0` and `Γ = Σ c_ρ e^{iγ_ρτ}`,
`c_ρ = m_ρ f̂(γ_ρ)`. The Bohr mean of an absolutely convergent almost periodic series picks the
coefficients at frequency `0` (`tendsto_mean_apSeries`). So `Γ` has mean `0`, since no critical
ordinate is `0`. And `Γ(τ)e^{−iγ₀τ}` has mean `c_{ρ₀}`, since critical ordinates are distinct.
Weight the packet by `1 + cos(γ₀τ + θ) ≥ 0`, of mean `1`. It then has weighted mean
`Re(e^{−iθ}(−c_{ρ₀}))`, which is `±|c_{ρ₀}|` for the two phases of `∓c_{ρ₀}`. An eventual bound
`P ≤ |c_{ρ₀}| − ε` or `P ≥ −|c_{ρ₀}| + ε` contradicts this (`le_mul_of_mean_weighted`).

**Tuned probes resonate** (`tunedSpline_amplitude`). The tuned cubic spline
`f_R(u) = B(u/R) cos(γ_ρu)` has `|f̂_R(γ_ρ)| ≥ 15R/32` once `R|γ_ρ| ≥ 1`. So its packet exceeds
`15 m_ρ R/32` and falls below `−15 m_ρ R/32` at arbitrarily large shifts. That is linear growth in
`R` against source energy `≍ R`, a resonance; dilates grow only like `√(t log(1/t))`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Bohr means -/

open Classical in
/-- **Bohr mean.** The Cesàro mean of an absolutely convergent almost periodic series is the sum
of its coefficients at frequency `0`. -/
theorem tendsto_mean_apSeries {ι : Type*} [Countable ι] {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (γ : ι → ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L, apSeries a γ τ) / L) atTop
      (𝓝 (∑' i, if γ i = 0 then a i else 0)) := by
  simp_rw [mean_apSeries_eq ha γ]
  refine tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖) ha (fun i => ?_) ?_
  · by_cases h : γ i = 0
    · rw [if_pos h]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [h, characterMean_zero hL, mul_one]
    · rw [if_neg h]
      simpa using (tendsto_characterMean h).const_mul (a i)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL i
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_characterMean_le _ hL)

/-- A character twist shifts the frequencies: `Γ(τ)e^{−iητ} = Σ a_i e^{i(γ_i − η)τ}`. -/
theorem apSeries_mul_cexp {ι : Type*} (a : ι → ℂ) (γ : ι → ℝ) (η τ : ℝ) :
    apSeries a γ τ * cexp ((-η * τ : ℝ) * I) = apSeries a (fun i => γ i - η) τ := by
  unfold apSeries
  rw [← tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Means over `[w, L]` and over `[0, L]` have the same limit. -/
theorem tendsto_mean_shift {g : ℝ → ℂ} (hg : Continuous g) {c : ℂ}
    (h : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..L, g τ) / L) atTop (𝓝 c)) (w : ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, g τ) / L) atTop (𝓝 c) := by
  have h0 : Tendsto (fun L : ℝ => (∫ τ in (0 : ℝ)..w, g τ) / (L : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := ‖∫ τ in (0 : ℝ)..w, g τ‖)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    exact le_rfl
  have := h.sub h0
  rw [sub_zero] at this
  refine this.congr' (Eventually.of_forall fun L => ?_)
  rw [← sub_div, intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable 0 L)
    (hg.intervalIntegrable 0 w)]

/-- A decaying signal has Cesàro mean `0`. -/
theorem tendsto_mean_of_tendsto_zero_complex {g : ℝ → ℂ} (hg : Continuous g)
    (h0 : Tendsto g atTop (𝓝 0)) (w : ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, g τ) / L) atTop (𝓝 0) := by
  have hn := tendsto_mean_of_tendsto_zero hg.norm (by simpa using h0.norm) w
  refine squeeze_zero_norm' ?_ hn
  filter_upwards [eventually_ge_atTop w, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  exact div_le_div_of_nonneg_right (intervalIntegral.norm_integral_le_integral_norm hL) hL0.le

/-- **Weighted mean bound.** If `p ≤ A` eventually, `v ≥ 0`, and the means of `p v` and `v` converge
to `a` and `b`, then `a ≤ A b`. -/
theorem le_mul_of_mean_weighted {p v : ℝ → ℝ} (hp : Continuous p) (hv : Continuous v)
    (hv0 : ∀ τ, 0 ≤ v τ) {w a b A T : ℝ}
    (hpv : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ * v τ) / L) atTop (𝓝 a))
    (hvm : Tendsto (fun L : ℝ => (∫ τ in w..L, v τ) / L) atTop (𝓝 b))
    (hA : ∀ τ, T ≤ τ → p τ ≤ A) : a ≤ A * b := by
  set T' := max T w
  set C₁ := ∫ τ in w..T', p τ * v τ
  set C₂ := ∫ τ in w..T', v τ
  have hR : Tendsto (fun L : ℝ => C₁ / L + A * ((∫ τ in w..L, v τ) / L) - A * C₂ / L) atTop
      (𝓝 (0 + A * b - 0)) :=
    ((tendsto_const_nhds.div_atTop tendsto_id).add (hvm.const_mul A)).sub
      (tendsto_const_nhds.div_atTop tendsto_id)
  rw [zero_add, sub_zero] at hR
  refine le_of_tendsto_of_tendsto hpv hR ?_
  filter_upwards [eventually_ge_atTop T', eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have hpvI : ∀ x y : ℝ, IntervalIntegrable (fun τ => p τ * v τ) volume x y := fun x y =>
    (hp.mul hv).intervalIntegrable x y
  have hvI : ∀ x y : ℝ, IntervalIntegrable v volume x y := fun x y => hv.intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hpvI w T') (hpvI T' L),
    ← intervalIntegral.integral_add_adjacent_intervals (hvI w T') (hvI T' L)]
  have hle : ∫ τ in T'..L, p τ * v τ ≤ A * ∫ τ in T'..L, v τ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hL (hpvI T' L) ((hvI T' L).const_mul A)
      fun τ hτ => mul_le_mul_of_nonneg_right (hA τ ((le_max_left _ _).trans hτ.1)) (hv0 τ)
  have e : C₁ / L + A * ((C₂ + ∫ τ in T'..L, v τ) / L) - A * C₂ / L =
      (C₁ + A * ∫ τ in T'..L, v τ) / L := by
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hL0.le

/-- `1 + cos(γ₀τ + θ)` has mean `1` for `γ₀ ≠ 0`. -/
theorem tendsto_mean_one_add_cos {γ₀ : ℝ} (hγ : γ₀ ≠ 0) (θ w : ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in w..L, (1 + Real.cos (γ₀ * τ + θ))) / L) atTop (𝓝 1) := by
  have hint : ∀ L : ℝ, ∫ τ in w..L, (1 + Real.cos (γ₀ * τ + θ)) =
      (L - w) + γ₀⁻¹ * (Real.sin (γ₀ * L + θ) - Real.sin (γ₀ * w + θ)) := fun L => by
    rw [intervalIntegral.integral_add (f := fun _ => (1 : ℝ))
      (g := fun τ => Real.cos (γ₀ * τ + θ)) intervalIntegrable_const
      ((by fun_prop : Continuous fun τ : ℝ => Real.cos (γ₀ * τ + θ)).intervalIntegrable _ _),
      intervalIntegral.integral_comp_mul_add Real.cos hγ θ, integral_cos]
    simp
  have hs : Tendsto (fun L : ℝ =>
      γ₀⁻¹ * (Real.sin (γ₀ * L + θ) - Real.sin (γ₀ * w + θ)) / L) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 2 * |γ₀⁻¹|)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hL, abs_mul]
    refine div_le_div_of_nonneg_right ?_ hL.le
    have h1 := Real.abs_sin_le_one (γ₀ * L + θ)
    have h2 := Real.abs_sin_le_one (γ₀ * w + θ)
    have := abs_sub (Real.sin (γ₀ * L + θ)) (Real.sin (γ₀ * w + θ))
    nlinarith [abs_nonneg γ₀⁻¹]
  have hl : Tendsto (fun L : ℝ => (L - w) / L) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := w)).div_atTop tendsto_id)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    simp only [id_eq]
    field_simp
  have := hl.add hs
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun L => ?_)
  beta_reduce
  rw [hint, add_div]

/-! ## The twisted packet means -/

open Classical in
/-- **Twisted packet mean.** For a source blind right of the line, the Cesàro mean of
`P_f(τ)e^{−iητ}` is minus the critical coefficient at ordinate `η`. -/
theorem tendsto_mean_packet_twist {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) (η : ℝ) :
    Tendsto (fun L : ℝ => (∫ τ in w..L,
        (stationaryPacket f τ : ℂ) * cexp ((-η * τ : ℝ) * I)) / L) atTop
      (𝓝 (-∑' ρ : criticalZeros,
        if ((ρ : 𝒵) : ℂ).im - η = 0 then packetCoeff f ρ else 0)) := by
  haveI : Countable 𝒵 := (countable_carrier _).to_subtype
  obtain ⟨B, hBc, hB0, hEF⟩ := exists_packet_eq_sub_criticalSeries hf hfc hw0 hw hblind
  set a : criticalZeros → ℂ := fun ρ => packetCoeff f ρ
  set γ : criticalZeros → ℝ := fun ρ => ((ρ : 𝒵) : ℂ).im
  have ha : Summable fun ρ => ‖a ρ‖ := (summable_norm_packetCoeff hf hfc).subtype _
  have hG : ∀ τ, criticalSeries f τ = apSeries a γ τ := fun _ => rfl
  have hχ : Continuous fun τ : ℝ => cexp ((-η * τ : ℝ) * I) := by fun_prop
  have hGc : Continuous fun τ => apSeries a (fun ρ => γ ρ - η) τ := by
    have e : (fun τ => apSeries a (fun ρ => γ ρ - η) τ) =
        fun τ => criticalSeries f τ * cexp ((-η * τ : ℝ) * I) :=
      funext fun τ => by rw [hG, apSeries_mul_cexp]
    rw [e]
    exact (continuous_criticalSeries hf hfc).mul hχ
  have hGm := tendsto_mean_shift hGc (tendsto_mean_apSeries ha fun ρ => γ ρ - η) w
  have hBχ : Tendsto (fun τ => B τ * cexp ((-η * τ : ℝ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun τ => ?_) (by simpa using hB0.norm)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hBm := tendsto_mean_of_tendsto_zero_complex
    (g := fun τ => B τ * cexp ((-η * τ : ℝ) * I)) (hBc.mul hχ) hBχ w
  have := hBm.sub hGm
  rw [zero_sub] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop w] with L hL
  rw [← sub_div, ← intervalIntegral.integral_sub (f := fun τ => B τ * cexp ((-η * τ : ℝ) * I))
    ((hBc.mul hχ).intervalIntegrable w L) (hGc.intervalIntegrable w L)]
  congr 1
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
  rw [uIoc_of_le hL] at hτ
  rw [hEF τ hτ.1, sub_mul, hG, apSeries_mul_cexp]

/-! ## The amplitude law -/

/-- **Per-zero amplitude law.** For every real compact `C²` source and every critical zero `ρ`, the
packet exceeds `m_ρ|f̂(γ_ρ)| − ε` and falls below `−m_ρ|f̂(γ_ρ)| + ε` at arbitrarily large shifts. -/
theorem packet_zero_amplitude_law {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ρ₀ : criticalZeros) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    (∃ τ, T ≤ τ ∧ (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
        ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ - ε <
          stationaryPacket f τ) ∧
      ∃ τ, T ≤ τ ∧ stationaryPacket f τ < -((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
        ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖) + ε := by
  classical
  set c := (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖
  have hup_iff := packet_upper_iff hf hfc le_rfl
  have hlow_iff := packet_lower_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff hlow_iff
  by_cases hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K
  swap
  · -- unbounded above, hence also unbounded below
    push Not at hup
    refine ⟨?_, ?_⟩
    · obtain ⟨τ, hτ, h⟩ := hup T (c - ε)
      exact ⟨τ, hτ, h⟩
    · by_contra h
      push Not at h
      obtain ⟨T', K', hK'⟩ := hup_iff.mpr (hlow_iff.mp ⟨T, c - ε, fun τ hτ => by
        linarith [h τ hτ]⟩)
      obtain ⟨τ, hτ, hlt⟩ := hup T' K'
      linarith [hK' τ hτ]
  -- bounded above: blind right of the line
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => hup_iff.mp hup ρ (by linarith)
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hP := continuous_stationaryPacket hf.continuous hfc
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  have hγ0 : γ₀ ≠ 0 := im_ne_zero_of_mem_critical ρ₀
  set c₀ := packetCoeff f ρ₀
  have hc₀ : ‖c₀‖ = c := by
    simp only [c₀, c, packetCoeff, norm_mul, Complex.norm_natCast, gammaOf_of_mem_critical ρ₀.2]
  -- the two twisted means
  have hS0 : (∑' ρ : criticalZeros, if ((ρ : 𝒵) : ℂ).im - 0 = 0 then packetCoeff f ρ else 0) =
      0 := (tsum_congr fun ρ => if_neg (by rw [sub_zero]; exact im_ne_zero_of_mem_critical ρ)).trans
        tsum_zero
  have hS1 : (∑' ρ : criticalZeros, if ((ρ : 𝒵) : ℂ).im - γ₀ = 0 then packetCoeff f ρ else 0) =
      c₀ := by
    rw [tsum_eq_single ρ₀ fun ρ hρ => if_neg fun h => hρ (eq_of_im_eq_critical (sub_eq_zero.mp h)),
      if_pos (sub_self _)]
  have hM0 : Tendsto (fun L : ℝ => (∫ τ in w..L, (stationaryPacket f τ : ℂ)) / L) atTop
      (𝓝 0) := by
    have h := tendsto_mean_packet_twist hf hfc hw.le hwz hblind 0
    rw [hS0] at h
    simpa using h
  have hM1 := tendsto_mean_packet_twist hf hfc hw.le hwz hblind γ₀
  rw [hS1] at hM1
  -- weighted real means against `1 + cos(γ₀τ + θ)`
  have hweighted : ∀ θ : ℝ, Tendsto (fun L : ℝ =>
      (∫ τ in w..L, stationaryPacket f τ * (1 + Real.cos (γ₀ * τ + θ))) / L) atTop
        (𝓝 (cexp (-(θ : ℂ) * I) * -c₀).re) := by
    intro θ
    set F : ℝ → ℂ := fun τ => (stationaryPacket f τ : ℂ) +
      cexp (-(θ : ℂ) * I) * ((stationaryPacket f τ : ℂ) * cexp ((-γ₀ * τ : ℝ) * I))
    have hFc : Continuous F := by fun_prop
    have hFre : ∀ τ, stationaryPacket f τ * (1 + Real.cos (γ₀ * τ + θ)) = (F τ).re := fun τ => by
      have e : cexp (-(θ : ℂ) * I) * ((stationaryPacket f τ : ℂ) * cexp ((-γ₀ * τ : ℝ) * I)) =
          (stationaryPacket f τ : ℂ) * cexp (((-(γ₀ * τ + θ)) : ℝ) * I) := by
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      simp only [F, e, add_re, re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_neg, ofReal_re]
      ring
    have hC := hM0.add (hM1.const_mul (cexp (-(θ : ℂ) * I)))
    rw [zero_add] at hC
    have hR := (Complex.continuous_re.tendsto _).comp hC
    refine hR.congr' ?_
    filter_upwards [eventually_ge_atTop w] with L hL
    have hI : ∀ g : ℝ → ℂ, Continuous g → IntervalIntegrable g volume w L := fun g hg =>
      hg.intervalIntegrable w L
    simp only [Function.comp_apply]
    rw [mul_div_assoc', ← add_div, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hI _ (by fun_prop)) (hI _ (by fun_prop)),
      Complex.div_ofReal_re]
    congr 1
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm (hI F hFc)
    simp only [Complex.reCLM_apply] at hcomm
    rw [← hcomm]
    exact intervalIntegral.integral_congr fun τ _ => (hFre τ).symm
  have hv : ∀ θ : ℝ, Continuous fun τ : ℝ => 1 + Real.cos (γ₀ * τ + θ) := fun θ => by fun_prop
  have hv0 : ∀ θ τ, 0 ≤ 1 + Real.cos (γ₀ * τ + θ) := fun θ τ => by
    linarith [Real.neg_one_le_cos (γ₀ * τ + θ)]
  have hrot : ∀ z : ℂ, (cexp (-((Complex.arg z : ℝ) : ℂ) * I) * z).re = ‖z‖ := fun z => by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_left_comm, ← Complex.exp_add]
    simp
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have hle := le_mul_of_mean_weighted hP (hv (Complex.arg (-c₀))) (hv0 _)
      (hweighted (Complex.arg (-c₀))) (tendsto_mean_one_add_cos hγ0 _ w) h
    rw [hrot, norm_neg, hc₀] at hle
    linarith
  · by_contra h
    push Not at h
    have hneg := (hweighted (Complex.arg c₀)).neg
    have hle := le_mul_of_mean_weighted hP.neg (hv (Complex.arg c₀)) (hv0 _)
      (p := fun τ => -stationaryPacket f τ) (A := c - ε) (T := T)
      (hneg.congr fun L => by
        simp only [neg_mul, intervalIntegral.integral_neg, neg_div])
      (tendsto_mean_one_add_cos hγ0 _ w) fun τ hτ => by linarith [h τ hτ]
    have e : (cexp (-((Complex.arg c₀ : ℝ) : ℂ) * I) * -c₀).re = -c := by
      rw [mul_neg, neg_re, hrot, hc₀]
    rw [e, neg_neg] at hle
    linarith

/-! ## Tuned probes resonate -/

theorem paperFT_cubicSpline_zero : Zeta23.paperFT (fun x => (cubicSpline x : ℂ)) 0 = 1 := by
  unfold Zeta23.paperFT
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, integral_cubicSpline, ofReal_one]

/-- `|B̂(x)| ≤ x⁻⁴` on the real axis. -/
theorem norm_paperFT_cubicSpline_le {x : ℝ} (hx : x ≠ 0) :
    ‖Zeta23.paperFT (fun u => (cubicSpline u : ℂ)) (x : ℂ)‖ ≤ (1 / |x|) ^ 4 := by
  have h := RHTower.WeilDeletion.norm_paperFT_upow_le one_pos 3 (z := (x : ℂ))
    (by exact_mod_cast hx)
  simpa [cubicSpline, Complex.norm_real] using h

/-- **Resonance of tuned probes.** For `R|γ_ρ| ≥ 1` the tuned cubic spline `B(u/R)cos(γ_ρu)` has a
packet above `15 m_ρ R/32 − ε` and below `−15 m_ρ R/32 + ε` at arbitrarily large shifts. -/
theorem tunedSpline_amplitude (ρ₀ : criticalZeros) {R : ℝ} (hR : 0 < R)
    (hRγ : 1 ≤ R * |((ρ₀ : 𝒵) : ℂ).im|) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    (∃ τ, T ≤ τ ∧ 15 / 32 * (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) * R - ε <
        stationaryPacket (tunedProbe cubicSpline ((ρ₀ : 𝒵) : ℂ).im R) τ) ∧
      ∃ τ, T ≤ τ ∧ stationaryPacket (tunedProbe cubicSpline ((ρ₀ : 𝒵) : ℂ).im R) τ <
        -(15 / 32 * (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) * R) + ε := by
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  set m := (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hγ0 : γ₀ ≠ 0 := im_ne_zero_of_mem_critical ρ₀
  -- `|f̂_R(γ₀)| ≥ 15R/32`
  have hFT : 15 / 32 * R ≤
      ‖Zeta23.paperFT (fun u => (tunedProbe cubicSpline γ₀ R u : ℂ)) ((γ₀ : ℝ) : ℂ)‖ := by
    rw [paperFT_tunedProbe contDiff_cubicSpline.continuous hasCompactSupport_cubicSpline γ₀ hR,
      sub_self, mul_zero, paperFT_cubicSpline_zero,
      show (R : ℂ) * ((γ₀ : ℂ) + γ₀) = ((2 * R * γ₀ : ℝ) : ℂ) by push_cast; ring, norm_mul,
      show (R / 2 : ℂ) = ((R / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hR)]
    have h2 : 2 ≤ |2 * R * γ₀| := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hR]; linarith
    have hy := norm_paperFT_cubicSpline_le (x := 2 * R * γ₀)
      (mul_ne_zero (mul_ne_zero two_ne_zero hR.ne') hγ0)
    have hy' : (1 / |2 * R * γ₀|) ^ 4 ≤ 1 / 16 := by
      have : 1 / |2 * R * γ₀| ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
      have h0 : 0 ≤ 1 / |2 * R * γ₀| := by positivity
      calc (1 / |2 * R * γ₀|) ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ h0 this 4
        _ ≤ 1 / 16 := by norm_num
    have hlow : 15 / 16 ≤ ‖1 + Zeta23.paperFT (fun u => (cubicSpline u : ℂ))
        ((2 * R * γ₀ : ℝ) : ℂ)‖ := by
      have := norm_sub_le (1 + Zeta23.paperFT (fun u => (cubicSpline u : ℂ))
        ((2 * R * γ₀ : ℝ) : ℂ)) (Zeta23.paperFT (fun u => (cubicSpline u : ℂ))
          ((2 * R * γ₀ : ℝ) : ℂ))
      rw [add_sub_cancel_right, norm_one] at this
      linarith
    nlinarith
  obtain ⟨⟨τ₁, hτ₁, h₁⟩, ⟨τ₂, hτ₂, h₂⟩⟩ := packet_zero_amplitude_law
    (contDiff_tunedProbe contDiff_cubicSpline γ₀ R)
    (hasCompactSupport_tunedProbe hasCompactSupport_cubicSpline γ₀ hR) ρ₀ hε T
  have hmF := mul_le_mul_of_nonneg_left hFT hm
  exact ⟨⟨τ₁, hτ₁, by linarith⟩, ⟨τ₂, hτ₂, by linarith⟩⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
