import GaloisForLFunctions.BiScaleUncertainty.TranslatedPairingEnvelopeLaw

/-!
# Cramér's lower bound in liminf form: the band is eventually above the zero energy

With `Ẽ(t) = e^{−t/2}(ψ(eᵗ) − eᵗ)`, the band `∫_0^M Ẽ² = ∫_1^{e^M} (ψ(x) − x)²/x² dx` is linear
under RH. The slope law shows that a valid band constant is at least the zero energy
`Σ_ρ m_ρ²/|ρ|²`, which is a statement about `limsup (1/M)∫_0^M Ẽ²`.

**Cramér liminf law** (`cramer_liminf_law`). Under RH, for every finite set `S` of zeros and every
`ε > 0`,

`(1/M) ∫_0^M Ẽ² ≥ Σ_{ρ∈S} m_ρ²/|ρ|² − ε` for all large `M`.

So the band is eventually above every finite part of the zero energy, not only infinitely often.
The mean square of `(ψ(x) − x)/x` in `log x` has `liminf ≥ Σ_ρ m_ρ²/|ρ|²`.

**Mechanism.**

* **Gauge bridge** (`stationaryPacket_eq_gauge`). Beyond its support and below the cutoff, the
  stationary packet of a compact source is the forward residual minus the Chebyshev gauge
  convolution, `P_f(τ) = R(−τ) − D_N(−τ)`.
* **Windowed energy.** Young's inequality for `D_N` and the residual energy bound give
  `∫_w^L P_f² ≤ (1+η) ‖f' − f/2‖₁² ∫_0^{L+w+3} Ẽ² + (1 + 1/η) · 10 h_f(0)`
  (`integral_sq_packet_le`).
* **Probe lower bound.** Under RH, `(1/L)∫_w^L P_f² → E(f)`. Hence `(1/M)∫_0^M Ẽ²` is eventually at
  least `E(f)/‖f' − f/2‖₁² − ε` for every probe (`eventually_mean_sq_normalizedLogError_ge`).
* **Gauge-delta probes.** `f = e^{u/2}(K(u) − K(u+T))`, with `K` the primitive of a normalized bump
  of radius `r`, has gauge derivative `e^{u/2}(k(u) − k(u+T))`. This has `L¹` norm at most
  `e^{r/2} + e^{(r−T)/2}` and transform within `e^{|ρ|r} − 1 + e^{(r−T)/2}` of `1` at `γ_ρ`.
  Since `|ĝ(γ)| = |ρ||f̂(γ)|`, the ratio `E(f)/‖g‖₁²` tends to the zero energy of `S`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## The gauge bridge -/

/-- Beyond the support and below the cutoff, the stationary packet is the finite signed packet. -/
theorem stationaryPacket_eq_signedSource (F : C_c(ℝ, ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0) {τ : ℝ} {N : ℕ} (hN : τ + w < cutoff N) :
    stationaryPacket F τ = signedSource F N (-τ) := by
  show _ = atomicSource F N (-τ) - polarSource F N (-τ)
  unfold stationaryPacket
  congr 1
  · show _ = ∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * F (-τ + Real.log n)
    rw [tsum_eq_sum (s := Finset.Icc 1 (N + 2)) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [primeWeight, neg_add_eq_sub]
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · have hn' : N + 2 < n := by
          by_contra h
          exact hn (Finset.mem_Icc.mpr ⟨hn0, not_lt.mp h⟩)
        have hlog : cutoff N < Real.log n := by
          unfold cutoff
          exact Real.log_lt_log (by positivity) (by exact_mod_cast hn')
        rw [hw _ (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  · show _ = ∫ t in Icc 0 (cutoff N), polarDensity t * F (-τ + t)
    have hL : 0 ≤ cutoff N := cutoff_nonneg N
    rw [integral_Icc_eq_integral_Ioc,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        fun x hx => ?_]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      rw [polarDensity, neg_add_eq_sub]
    · have hxL : cutoff N < x := by
        by_contra h
        exact hx.2 ⟨hx.1, not_lt.mp h⟩
      rw [hw _ (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]

/-- **Gauge bridge.** For `w < τ` and `τ + w < cutoff N`,
`P_f(τ) = R_N(−τ) − D_N(−τ)`: forward residual minus Chebyshev gauge convolution. -/
theorem stationaryPacket_eq_gauge (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → F v = 0) {τ : ℝ} {N : ℕ} (hN : τ + w < cutoff N) :
    stationaryPacket F τ = forwardResidual F N (-τ) - chebyshevGaugeConvolution F N (-τ) := by
  rw [stationaryPacket_eq_signedSource F hw0 hw hN, signedSource_eq_gauge F hF N,
    hw _ (by rw [abs_of_pos (by linarith)]; linarith), mul_zero, add_zero]

/-! ## The windowed packet energy -/

theorem continuous_forwardResidual (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) (N : ℕ) :
    Continuous (forwardResidual F N) := by
  have e : forwardResidual F N = fun u => signedSource F N u -
      normalizedLogError (cutoff N) * F (u + cutoff N) + chebyshevGaugeConvolution F N u :=
    funext fun u => by rw [signedSource_eq_gauge F hF N]; ring
  rw [e]
  exact ((signedSource F N).continuous.sub (continuous_const.mul
    (F.continuous.comp (continuous_add_const _)))).add (continuous_chebyshevGaugeConvolution F hF N)

theorem hasCompactSupport_forwardResidual (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 1 (F : ℝ → ℝ))
    (N : ℕ) : HasCompactSupport (forwardResidual F N) := by
  have e : forwardResidual F N = fun u => signedSource F N u -
      normalizedLogError (cutoff N) * F (u + cutoff N) + chebyshevGaugeConvolution F N u :=
    funext fun u => by rw [signedSource_eq_gauge F hF N]; ring
  rw [e]
  exact ((signedSource F N).hasCompactSupport.sub
    (hasCompactSupport_comp_add F.hasCompactSupport (cutoff N)).mul_left).add
      (hasCompactSupport_chebyshevGaugeConvolution F N)

/-- A cutoff between `L + w` and `L + w + 3`. -/
theorem exists_cutoff_between {a : ℝ} (ha : 0 ≤ a) :
    ∃ N : ℕ, a < cutoff N ∧ cutoff N ≤ a + 3 := by
  refine ⟨⌈Real.exp (a + 1)⌉₊, ?_, ?_⟩
  · unfold cutoff
    have h1 : Real.exp (a + 1) ≤ (⌈Real.exp (a + 1)⌉₊ : ℝ) := Nat.le_ceil _
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
    push_cast
    linarith [Real.exp_lt_exp.mpr (show a < a + 1 by linarith)]
  · unfold cutoff
    have h1 : (⌈Real.exp (a + 1)⌉₊ : ℝ) < Real.exp (a + 1) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    rw [Real.log_le_iff_le_exp (by positivity)]
    push_cast
    have h3 : Real.exp (a + 3) = Real.exp (a + 1) * Real.exp 2 := by
      rw [← Real.exp_add]; ring_nf
    have h4 : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have h6 : 2 ≤ Real.exp (a + 1) := by linarith [Real.add_one_le_exp (a + 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) (sub_nonneg.mpr h4)]

/-- `(a − b)² ≤ (1+η)b² + (1+1/η)a²`. -/
theorem sub_sq_le_weighted {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a - b) ^ 2 ≤ (1 + η) * b ^ 2 + (1 + 1 / η) * a ^ 2 := by
  have h : 0 ≤ (η * b + a) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
  have e : (a - b) ^ 2 = (1 + η) * b ^ 2 + (1 + 1 / η) * a ^ 2 - (η * b + a) ^ 2 / η := by
    field_simp
    ring
  linarith

theorem integral_Ioo_le_integral_of_nonneg {g : ℝ → ℝ} (hg : Integrable g) (hg0 : ∀ u, 0 ≤ g u)
    {a b : ℝ} (hab : a ≤ b) : ∫ u in a..b, g u ≤ ∫ u, g u := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_le_integral hg (Eventually.of_forall hg0)

/-- **Windowed packet energy** for a compactly supported `C²` source. -/
theorem integral_sq_packet_le_of_compact (F : C_c(ℝ, ℝ)) (hF : ContDiff ℝ 2 (F : ℝ → ℝ))
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → F v = 0) {η : ℝ} (hη : 0 < η) {L : ℝ}
    (hL : w ≤ L) :
    ∫ τ in w..L, stationaryPacket F τ ^ 2 ≤
      (1 + η) * ((∫ u, |gaugeDerivative F u|) ^ 2 *
          ∫ t in Icc 0 (L + w + 3), normalizedLogError t ^ 2) +
        (1 + 1 / η) * (10 * autocorr F 0) := by
  have hF1 : ContDiff ℝ 1 (F : ℝ → ℝ) := hF.of_le (by norm_num)
  obtain ⟨N, hN1, hN2⟩ := exists_cutoff_between (a := L + w) (by linarith)
  have hRc := continuous_forwardResidual F hF1 N
  have hDc := continuous_chebyshevGaugeConvolution F hF1 N
  have hRs : HasCompactSupport fun u => forwardResidual F N u ^ 2 :=
    (hasCompactSupport_forwardResidual F hF1 N).mono fun x hx h => hx (by
      simp only at h ⊢; rw [h]; norm_num)
  have hDs : HasCompactSupport fun u => chebyshevGaugeConvolution F N u ^ 2 :=
    (hasCompactSupport_chebyshevGaugeConvolution F N).mono fun x hx h => hx (by
      simp only at h ⊢; rw [h]; norm_num)
  have hR2 : Integrable fun u => forwardResidual F N u ^ 2 :=
    (hRc.pow 2).integrable_of_hasCompactSupport hRs
  have hD2 : Integrable fun u => chebyshevGaugeConvolution F N u ^ 2 :=
    (hDc.pow 2).integrable_of_hasCompactSupport hDs
  have hPI : IntervalIntegrable (fun τ => stationaryPacket F τ ^ 2) volume w L :=
    ((continuous_stationaryPacket F.continuous F.hasCompactSupport).pow 2).intervalIntegrable w L
  have hDn : Continuous fun τ : ℝ => (1 + η) * chebyshevGaugeConvolution F N (-τ) ^ 2 :=
    continuous_const.mul ((hDc.comp continuous_neg).pow 2)
  have hRn : Continuous fun τ : ℝ => (1 + 1 / η) * forwardResidual F N (-τ) ^ 2 :=
    continuous_const.mul ((hRc.comp continuous_neg).pow 2)
  -- pointwise comparison on `(w, L]`
  have h1 : ∫ τ in w..L, stationaryPacket F τ ^ 2 ≤
      ∫ τ in w..L, ((1 + η) * chebyshevGaugeConvolution F N (-τ) ^ 2 +
        (1 + 1 / η) * forwardResidual F N (-τ) ^ 2) := by
    refine intervalIntegral.integral_mono_ae_restrict hL hPI
      ((hDn.add hRn).intervalIntegrable w L) ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (Measure.ae_ne volume w).mono fun τ hτw hτ => ?_
    have hτ' : w < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτw)
    rw [stationaryPacket_eq_gauge F hF1 hw0 hw (by linarith [hτ.2])]
    exact sub_sq_le_weighted hη _ _
  -- split and reflect
  have h2 : ∫ τ in w..L, ((1 + η) * chebyshevGaugeConvolution F N (-τ) ^ 2 +
        (1 + 1 / η) * forwardResidual F N (-τ) ^ 2) =
      (1 + η) * (∫ u in -L..-w, chebyshevGaugeConvolution F N u ^ 2) +
        (1 + 1 / η) * ∫ u in -L..-w, forwardResidual F N u ^ 2 := by
    rw [intervalIntegral.integral_add (hDn.intervalIntegrable w L) (hRn.intervalIntegrable w L),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_neg (fun u => chebyshevGaugeConvolution F N u ^ 2),
      intervalIntegral.integral_comp_neg (fun u => forwardResidual F N u ^ 2)]
  have hDle : ∫ u in -L..-w, chebyshevGaugeConvolution F N u ^ 2 ≤
      (∫ u, |gaugeDerivative F u|) ^ 2 * ∫ t in Icc 0 (L + w + 3), normalizedLogError t ^ 2 := by
    refine (integral_Ioo_le_integral_of_nonneg hD2 (fun _ => sq_nonneg _) (by linarith)).trans
      ((integral_sq_chebyshevGaugeConvolution_le F hF1 N).trans ?_)
    exact mul_le_mul_of_nonneg_left (setIntegral_mono_set (integrableOn_normalizedLogError_sq _)
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall (Icc_subset_Icc_right hN2))) (sq_nonneg _)
  have hRle : ∫ u in -L..-w, forwardResidual F N u ^ 2 ≤ 10 * autocorr F 0 :=
    (integral_Ioo_le_integral_of_nonneg hR2 (fun _ => sq_nonneg _) (by linarith)).trans
      (integral_sq_forwardResidual_le F N)
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left hDle (by linarith : (0 : ℝ) ≤ 1 + η),
    mul_le_mul_of_nonneg_left hRle hη1]

/-! ## The probe lower bound for the band -/

/-- `L/(L + c) → 1`. -/
theorem tendsto_div_add_const (c : ℝ) : Tendsto (fun L : ℝ => L / (L + c)) atTop (𝓝 1) := by
  have h : Tendsto (fun L : ℝ => 1 - c / (L + c)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ c
      tendsto_id))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (-c)] with L hL
  have : L + c ≠ 0 := by linarith
  field_simp
  ring

/-- **Probe lower bound for the band.** Under RH, for every real compact `C²` source `f` and every
`ε > 0`, eventually `(1/M) ∫_0^M Ẽ² ≥ E(f)/‖f' − f/2‖₁² − ε`. -/
theorem eventually_mean_sq_normalizedLogError_ge (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℝ in atTop, criticalPacketEnergy f / (∫ u, |gaugeDerivative f u|) ^ 2 - ε ≤
      (∫ t in Icc 0 M, normalizedLogError t ^ 2) / M := by
  obtain ⟨F, rfl⟩ : ∃ F : C_c(ℝ, ℝ), (F : ℝ → ℝ) = f := ⟨⟨⟨f, hf.continuous⟩, hfc⟩, rfl⟩
  set E := criticalPacketEnergy F
  set G := ∫ u, |gaugeDerivative F u|
  set I : ℝ → ℝ := fun M => ∫ t in Icc 0 M, normalizedLogError t ^ 2
  have hI0 : ∀ M, 0 ≤ I M := fun M => setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => by positivity
  by_cases hG : G = 0
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    rw [hG, sq, mul_zero, div_zero, zero_sub]
    exact (neg_nonpos.mpr hε.le).trans (div_nonneg (hI0 M) hM.le)
  have hG2 : 0 < G ^ 2 := by positivity
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → F v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (F u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  have hP := tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw.le hwz hblind
  set a := E / G ^ 2
  have ha0 : 0 ≤ a := div_nonneg hE0 hG2.le
  set η := ε / (2 * (a + 1))
  have hη : 0 < η := by positivity
  set C := (1 + 1 / η) * (10 * autocorr F 0)
  set c := w + 3
  -- the lower envelope `((∫_w^L P²) − C)/((1+η) G² (L + c))`
  have hT : Tendsto (fun L : ℝ => ((∫ τ in w..L, stationaryPacket F τ ^ 2) - C) /
      ((1 + η) * G ^ 2 * (L + c))) atTop (𝓝 (E * 1 / ((1 + η) * G ^ 2))) := by
    have h1 := ((hP.sub (tendsto_const_nhds (x := C) |>.div_atTop tendsto_id)).mul
      (tendsto_div_add_const c)).div_const ((1 + η) * G ^ 2)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hLc : L + c ≠ 0 := by simp only [c]; linarith
    simp only [id]
    field_simp
  have hlim : a - ε < E * 1 / ((1 + η) * G ^ 2) := by
    have e : E * 1 / ((1 + η) * G ^ 2) = a / (1 + η) := by
      simp only [a]; field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    have : a * η ≤ ε / 2 := by
      simp only [η]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hev : ∀ᶠ L : ℝ in atTop, a - ε ≤ I (L + c) / (L + c) := by
    filter_upwards [hT.eventually (lt_mem_nhds hlim), eventually_ge_atTop w] with L hL hLw
    refine hL.le.trans ?_
    have hbound : (∫ τ in w..L, stationaryPacket F τ ^ 2) ≤ (1 + η) * (G ^ 2 * I (L + c)) + C := by
      have h := integral_sq_packet_le_of_compact F hf hw.le hwz hη hLw
      rw [show L + w + 3 = L + c by simp only [c]; ring] at h
      exact h
    have hLc : 0 < L + c := by simp only [c]; linarith
    rw [div_le_div_iff₀ (by positivity) hLc]
    have : (∫ τ in w..L, stationaryPacket F τ ^ 2) - C ≤ (1 + η) * G ^ 2 * I (L + c) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right this hLc.le]
  have hshift := (tendsto_atTop_add_const_right atTop (-c) tendsto_id).eventually hev
  filter_upwards [hshift] with M hM
  simpa only [id, neg_add_cancel_right] using hM

/-! ## Gauge-delta probes -/

section GaugeDelta

variable {r : ℝ} (hr : 0 < r) (T : ℝ)

local notation "k" => RHTower.WeilDeletion.smoothBump r hr

theorem smoothBump_eq_zero {s : ℝ} (hs : r < |s|) : k s = 0 := by
  by_contra h
  have hm := RHTower.WeilDeletion.support_smoothBump_subset hr h
  have := abs_le.mpr ⟨hm.1, hm.2⟩
  linarith

/-- The gauge-delta probe `f(u) = e^{u/2} ∫_u^{u+T} k_r`; its gauge derivative is
`e^{u/2}(k_r(u+T) − k_r(u))`. -/
def gaugeDeltaProbe (u : ℝ) : ℝ := Real.exp (u / 2) * ∫ s in u..u + T, k s

theorem gaugeDeltaProbe_eq (u : ℝ) : gaugeDeltaProbe hr T u = Real.exp (u / 2) *
    ((∫ s in (0 : ℝ)..u + T, k s) - ∫ s in (0 : ℝ)..u, k s) := by
  have hI : ∀ a b : ℝ, IntervalIntegrable k volume a b := fun a b =>
    (RHTower.WeilDeletion.smoothBump_contDiff hr).continuous.intervalIntegrable a b
  rw [gaugeDeltaProbe, intervalIntegral.integral_interval_sub_left (hI 0 (u + T)) (hI 0 u)]

theorem contDiff_gaugeDeltaProbe : ContDiff ℝ 2 (gaugeDeltaProbe hr T) := by
  have hP := (contDiff_primitive (RHTower.WeilDeletion.smoothBump_contDiff hr)).of_le
    (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((2 + 1 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by norm_num))
  rw [funext (gaugeDeltaProbe_eq hr T)]
  exact (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul
    ((hP.comp (contDiff_id.add contDiff_const)).sub hP)

theorem gaugeDeltaProbe_eq_zero (hT : 0 ≤ T) {u : ℝ} (hu : u ∉ Icc (-r - T) r) :
    gaugeDeltaProbe hr T u = 0 := by
  rw [gaugeDeltaProbe, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_,
    intervalIntegral.integral_zero, mul_zero]
  rw [uIcc_of_le (by linarith)] at hs
  rcases not_and_or.mp hu with h | h
  · exact smoothBump_eq_zero hr (by rw [abs_of_neg (by linarith [hs.2])]; push Not at h; linarith [hs.2])
  · exact smoothBump_eq_zero hr (by push Not at h; rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.1])

theorem hasCompactSupport_gaugeDeltaProbe (hT : 0 ≤ T) : HasCompactSupport (gaugeDeltaProbe hr T) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => gaugeDeltaProbe_eq_zero hr T hT hu

theorem gaugeDerivative_gaugeDeltaProbe (u : ℝ) :
    gaugeDerivative (gaugeDeltaProbe hr T) u = Real.exp (u / 2) * (k (u + T) - k u) := by
  have hkc := (RHTower.WeilDeletion.smoothBump_contDiff hr).continuous
  have hd : ∀ x, HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, k s) (k x) x := fun x =>
    (hkc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hE : HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
    simpa using ((hasDerivAt_id u).div_const 2).exp
  have hF : HasDerivAt (fun u => (∫ s in (0 : ℝ)..u + T, k s) - ∫ s in (0 : ℝ)..u, k s)
      (k (u + T) - k u) u := by
    have h1 := (hd (u + T)).comp u ((hasDerivAt_id u).add_const T)
    exact h1.sub (hd u)
  have hfd : HasDerivAt (fun x => Real.exp (x / 2) *
      ((∫ s in (0 : ℝ)..x + T, k s) - ∫ s in (0 : ℝ)..x, k s))
      (Real.exp (u / 2) * (1 / 2) * ((∫ s in (0 : ℝ)..u + T, k s) - ∫ s in (0 : ℝ)..u, k s) +
        Real.exp (u / 2) * (k (u + T) - k u)) u := hE.mul hF
  rw [gaugeDerivative, show gaugeDeltaProbe hr T = _ from funext (gaugeDeltaProbe_eq hr T),
    hfd.deriv]
  ring

end GaugeDelta

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
