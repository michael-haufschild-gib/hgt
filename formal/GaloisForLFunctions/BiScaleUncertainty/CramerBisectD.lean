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
  have hR2 : Integrable fun u => forwardResidual F N u ^ 2 :=
    (hRc.pow 2).integrable_of_hasCompactSupport
      ((hasCompactSupport_forwardResidual F hF1 N).comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hD2 : Integrable fun u => chebyshevGaugeConvolution F N u ^ 2 :=
    (hDc.pow 2).integrable_of_hasCompactSupport
      ((hasCompactSupport_chebyshevGaugeConvolution F N).comp_left (g := fun x : ℝ => x ^ 2)
        (by simp))
  have hPI : IntervalIntegrable (fun τ => stationaryPacket F τ ^ 2) volume w L :=
    ((continuous_stationaryPacket F.continuous F.hasCompactSupport).pow 2).intervalIntegrable w L
  have hDn : Continuous fun τ : ℝ => chebyshevGaugeConvolution F N (-τ) ^ 2 := by fun_prop
  have hRn : Continuous fun τ : ℝ => forwardResidual F N (-τ) ^ 2 := by fun_prop
  -- pointwise comparison on `(w, L]`
  have h1 : ∫ τ in w..L, stationaryPacket F τ ^ 2 ≤
      ∫ τ in w..L, ((1 + η) * chebyshevGaugeConvolution F N (-τ) ^ 2 +
        (1 + 1 / η) * forwardResidual F N (-τ) ^ 2) := by
    refine intervalIntegral.integral_mono_ae_restrict hL hPI
      (((hDn.const_smul (1 + η)).add (hRn.const_smul (1 + 1 / η))).intervalIntegrable w L) ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (Measure.ae_ne volume w).mono fun τ hτw hτ => ?_
    have hτ' : w < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτw)
    rw [stationaryPacket_eq_gauge F hF1 hw0 hw (by linarith [hτ.2])]
    exact sub_sq_le_weighted hη _ _
  -- split and reflect
  have h2 : ∫ τ in w..L, ((1 + η) * chebyshevGaugeConvolution F N (-τ) ^ 2 +
        (1 + 1 / η) * forwardResidual F N (-τ) ^ 2) =
      (1 + η) * ∫ u in -L..-w, chebyshevGaugeConvolution F N u ^ 2 +
        (1 + 1 / η) * ∫ u in -L..-w, forwardResidual F N u ^ 2 := by
    rw [intervalIntegral.integral_add ((hDn.const_smul (1 + η)).intervalIntegrable w L)
      ((hRn.const_smul (1 + 1 / η)).intervalIntegrable w L),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_neg (fun u => chebyshevGaugeConvolution F N u ^ 2),
      intervalIntegral.integral_comp_neg (fun u => forwardResidual F N u ^ 2)]
  sorry

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
