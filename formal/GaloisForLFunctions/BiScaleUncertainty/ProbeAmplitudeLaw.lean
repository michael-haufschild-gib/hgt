import GaloisForLFunctions.BiScaleUncertainty.PacketPersistenceLaw
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction

/-!
# A probe of width `t` has packet amplitude at least `√(t log(1/t))`

The bi-scale uncertainty of probes, quantitatively and unconditionally. Narrowing a source to
width `t` (`f_t(u) = f(u/t)`) widens its spectral window to `|ξ| ≲ 1/t`, which contains `≍ t⁻¹ log(1/t)`
critical zeros. Each of them costs packet energy.

* `packetEnergy_le_sq_of_abs_le`: if `|P_f| ≤ A` eventually then the packet energy `E(f)` is at
  most `A²`; so `limsup |P_f| ≥ √E(f)`, unconditionally (`exists_abs_packet_gt_of_sq_lt`).
* `criticalPacketEnergy_dilate_ge`: if `∫ f ≠ 0` then `E(f_t) ≥ c t log(1/t)` for all small `t`.
* **Probe amplitude law** (`probe_amplitude_law`): for all small `t`, `|P_{f_t}(τ)|` exceeds
  `√(c t log(1/t))` at arbitrarily large `τ`. Since `‖f_t‖₂² = t‖f‖₂²`, the packet energy per unit
  source energy grows like `log(1/t)`: the logarithm is the zero density, the signature of the
  square-root barrier.

**Mechanism.** `f̂_t(ξ) = t f̂(tξ)` and `|f̂| ≥ |∫ f|/2` on `|ξ| ≤ ξ₀`, so every critical zero of
height at most `ξ₀/t` contributes `t²|∫ f|²/4` to `E(f_t)`. There are at least
`(72π)⁻¹ (ξ₀/t) log(ξ₀/t)` of them (`RHTower.eventually_superlinear_xiSimpleCriticalZeroCount`,
from the simple critical density in `Zeta23`). For the amplitude: a packet bounded by `A` is
bounded above, hence blind right of the line, and its mean square `E(f)` is at most `A²`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- A continuous signal whose mean square tends to `E` and which is eventually bounded by `A`
has `E ≤ A²`. -/
theorem le_sq_of_tendsto_mean_sq {p : ℝ → ℝ} (hp : Continuous p) {w E A T : ℝ}
    (hsq : Tendsto (fun L : ℝ => (∫ τ in w..L, p τ ^ 2) / L) atTop (𝓝 E))
    (hA : ∀ τ, T ≤ τ → |p τ| ≤ A) : E ≤ A ^ 2 := by
  set T' := max T w
  set C := ∫ τ in w..T', p τ ^ 2
  have hp2 : Continuous fun τ => p τ ^ 2 := by fun_prop
  have hup : Tendsto (fun L : ℝ => C / L + A ^ 2 * ((L - T') / L)) atTop (𝓝 (0 + A ^ 2 * 1)) := by
    refine (tendsto_const_nhds.div_atTop tendsto_id).add (Tendsto.const_mul _ ?_)
    have h1 : Tendsto (fun L : ℝ => 1 - T' / L) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    field_simp
  have hle : ∀ᶠ L in atTop, (∫ τ in w..L, p τ ^ 2) / L ≤ C / L + A ^ 2 * ((L - T') / L) := by
    filter_upwards [eventually_ge_atTop T', eventually_gt_atTop (0 : ℝ)] with L hL hL0
    rw [← intervalIntegral.integral_add_adjacent_intervals (hp2.intervalIntegrable w T')
      (hp2.intervalIntegrable T' L)]
    have htail : ∫ τ in T'..L, p τ ^ 2 ≤ A ^ 2 * (L - T') := by
      have := intervalIntegral.integral_mono_on hL (hp2.intervalIntegrable (μ := volume) T' L)
        (intervalIntegrable_const (μ := volume) (c := A ^ 2)) fun τ hτ => by
          have h := hA τ ((le_max_left T w).trans hτ.1)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
    rw [mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hL0.le
  have := le_of_tendsto_of_tendsto hsq hup hle
  linarith

/-- A packet blind right of the line agrees beyond its support with a continuous signal of mean
square `E(f)`. -/
theorem exists_continuous_packet_meanSq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0) :
    ∃ p : ℝ → ℝ, Continuous p ∧ (∀ τ, w < τ → p τ = stationaryPacket f τ) ∧
      Tendsto (fun L : ℝ => (∫ τ in w..L, p τ ^ 2) / L) atTop (𝓝 (criticalPacketEnergy f)) := by
  obtain ⟨B, hBc, -, hEF⟩ := exists_packet_eq_sub_criticalSeries hf hfc hw0 hw hblind
  set p : ℝ → ℝ := fun τ => (B τ - criticalSeries f τ).re
  have hpP : ∀ τ, w < τ → p τ = stationaryPacket f τ := fun τ hτ => by
    simp only [p]
    rw [← hEF τ hτ, ofReal_re]
  refine ⟨p, Complex.continuous_re.comp (hBc.sub (continuous_criticalSeries hf hfc)), hpP, ?_⟩
  refine (tendsto_mean_sq_stationaryPacket_of_blind hf hfc hw0 hw hblind).congr' ?_
  filter_upwards [eventually_ge_atTop w] with L hL
  congr 1
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun τ hτ => ?_)
  rw [uIoc_of_le hL] at hτ
  rw [hpP τ hτ.1]

/-- **Amplitude dominates energy.** If `|P_f| ≤ A` eventually, then `E(f) ≤ A²`. -/
theorem packetEnergy_le_sq_of_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A T : ℝ} (hA : ∀ τ, T ≤ τ → |stationaryPacket f τ| ≤ A) :
    criticalPacketEnergy f ≤ A ^ 2 := by
  have hup := packet_upper_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup
  have hblind0 := hup.mp ⟨T, A, fun τ hτ => (le_abs_self _).trans (hA τ hτ)⟩
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  obtain ⟨p, hpc, hpP, hsq⟩ := exists_continuous_packet_meanSq hf hfc hw.le hwz
    fun ρ hρ => hblind0 ρ (by linarith)
  refine le_sq_of_tendsto_mean_sq hpc hsq (T := max T (w + 1)) fun τ hτ => ?_
  rw [hpP τ (by linarith [le_max_right T (w + 1)])]
  exact hA τ (le_of_max_le_left hτ)

/-- **`limsup |P_f| ≥ √E(f)`**, unconditionally: below the square root of the packet energy the
packet cannot settle. -/
theorem exists_abs_packet_gt_of_sq_lt {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A : ℝ} (hA : A ^ 2 < criticalPacketEnergy f) (T : ℝ) :
    ∃ τ, T ≤ τ ∧ A < |stationaryPacket f τ| := by
  by_contra h
  push Not at h
  exact absurd (packetEnergy_le_sq_of_abs_le hf hfc h) (not_le.mpr hA)

/-- **Energy of narrow probes.** If `∫ f ≠ 0`, then `E(f_t) ≥ c t log(1/t)` for all small `t > 0`,
with `f_t(u) = f(u/t)`. -/
theorem criticalPacketEnergy_dilate_ge {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hint : ∫ u, f u ≠ 0) :
    ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ t₀ < 1 ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      c * t * Real.log (1 / t) ≤ criticalPacketEnergy fun u => f (u / t) := by
  set f₀ : ℝ → ℂ := fun u => (f u : ℂ)
  set a := |∫ u, f u|
  have ha : 0 < a := abs_pos.mpr hint
  -- the transform stays away from zero near the origin
  have hcont : Continuous fun r : ℝ => Zeta23.paperFT f₀ r :=
    Zeta23.Taper.continuous_paperFT_ofReal
      (hf.continuous.integrable_of_hasCompactSupport hfc |>.ofReal)
  have h0 : ‖Zeta23.paperFT f₀ ((0 : ℝ) : ℂ)‖ = a := by
    simp only [Zeta23.paperFT, ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, f₀]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (a / 2) (half_pos ha)
  set ξ₀ := min (δ / 2) (1 / 2)
  have hξ₀ : 0 < ξ₀ := lt_min (half_pos hδ) (by norm_num)
  have hξ₀1 : ξ₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hlow : ∀ ξ : ℝ, |ξ| ≤ ξ₀ → a / 2 ≤ ‖Zeta23.paperFT f₀ ξ‖ := fun ξ hξ => by
    have hd : dist ξ 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      exact hξ.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
    have h := hδc hd
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (Zeta23.paperFT f₀ ((0 : ℝ) : ℂ)) (Zeta23.paperFT f₀ ξ)
    rw [norm_sub_rev] at h
    linarith
  -- the superlinear count of simple critical zeros
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp _root_.RHTower.eventually_superlinear_xiSimpleCriticalZeroCount
  set T₂ := max T₁ 1
  set t₀ := min (ξ₀ / T₂) (ξ₀ ^ 2)
  have ht₀ : 0 < t₀ := lt_min (div_pos hξ₀ (by positivity)) (by positivity)
  have ht₀1 : t₀ < 1 := (min_le_right _ _).trans_lt (by nlinarith)
  refine ⟨a ^ 2 * ξ₀ / (576 * Real.pi), t₀, by positivity, ht₀, ht₀1, fun t ht htt₀ => ?_⟩
  set T := ξ₀ / t
  have hT : T₁ ≤ T := by
    have h1 : t < ξ₀ / T₂ := htt₀.trans_le (min_le_left _ _)
    have hT₂ : 0 < T₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [lt_div_iff₀ hT₂] at h1
    rw [le_div_iff₀ ht]
    nlinarith [le_max_left T₁ 1]
  have hcount := hT₁ T hT
  -- the critical zeros of height at most `T`, as a finite set of `criticalZeros`
  set F := (_root_.RHTower.stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ (analyticOrderAt _root_.RHTower.xi z).toNat = 1)
  have hinj : Set.InjOn (fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ))
      ((fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ)) ⁻¹' (F : Set ℂ)) :=
    (Subtype.val_injective.comp Subtype.val_injective).injOn
  set s := F.preimage (fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ)) hinj
  have hcard : (F.card : ℝ) ≤ s.card := by
    have hsub : F ⊆ s.image fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ) := by
      intro z hz
      obtain ⟨⟨hre0, hre1, him0, -, hxi⟩, hcrit, -⟩ :=
        (Finset.mem_filter.mp hz).imp_left _root_.RHTower.mem_stripFinsetPos.mp
      have hζ := (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
      exact Finset.mem_image.mpr ⟨⟨⟨z, hζ, hre0, hre1⟩, hcrit⟩,
        Finset.mem_preimage.mpr hz, rfl⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  -- each of them contributes `t² a²/4`
  have hdil : ∀ ξ : ℝ, Zeta23.paperFT (fun u => ((f (u / t) : ℝ) : ℂ)) (ξ : ℂ) =
      (t : ℂ) * Zeta23.paperFT f₀ ((t * ξ : ℝ) : ℂ) := fun ξ => by
    rw [_root_.RHTower.paperFT_comp_div (f := f₀) ht]
    push_cast
    rfl
  have hterm : ∀ ρ ∈ s, t ^ 2 * (a / 2) ^ 2 ≤
      (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ^ 2 *
        ‖Zeta23.paperFT (fun u => ((f (u / t) : ℝ) : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2 := by
    intro ρ hρ
    have hρF := Finset.mem_preimage.mp hρ
    obtain ⟨⟨-, -, him0, himT, -⟩, -⟩ :=
      (Finset.mem_filter.mp hρF).imp_left _root_.RHTower.mem_stripFinsetPos.mp
    have hm : (1 : ℝ) ≤ Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) := by
      exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
    have hξ : |t * ((ρ : 𝒵) : ℂ).im| ≤ ξ₀ := by
      rw [abs_of_pos (mul_pos ht him0)]
      have := mul_le_mul_of_nonneg_left himT ht.le
      rwa [show t * T = ξ₀ by simp only [T]; field_simp] at this
    have hF := hlow _ hξ
    rw [hdil, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have h1 : t * (a / 2) ≤ t * ‖Zeta23.paperFT f₀ ((t * ((ρ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hF ht.le
    have h2 : (t * (a / 2)) ^ 2 ≤
        (t * ‖Zeta23.paperFT f₀ ((t * ((ρ : 𝒵) : ℂ).im : ℝ) : ℂ)‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 1 ≤ (Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) : ℝ) ^ 2 := by nlinarith
    calc t ^ 2 * (a / 2) ^ 2 = (t * (a / 2)) ^ 2 := by ring
      _ ≤ (t * ‖Zeta23.paperFT f₀ ((t * ((ρ : 𝒵) : ℂ).im : ℝ) : ℂ)‖) ^ 2 := h2
      _ ≤ _ := le_mul_of_one_le_left (by positivity) h3
  have hft : ContDiff ℝ 2 fun u => f (u / t) := hf.comp (contDiff_id.div_const t)
  have hftc : HasCompactSupport fun u => f (u / t) := by
    have e : (fun u => f (u / t)) = fun u => f (t⁻¹ • u) := by
      funext u; rw [smul_eq_mul, div_eq_inv_mul]
    rw [e]
    exact hfc.comp_smul (inv_ne_zero ht.ne')
  have hsum := (summable_criticalPacketEnergy hft hftc).sum_le_tsum s
    (fun _ _ => by positivity)
  have hsum' : (s.card : ℝ) * (t ^ 2 * (a / 2) ^ 2) ≤ criticalPacketEnergy fun u => f (u / t) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact (Finset.sum_le_sum hterm).trans hsum
  -- assemble
  have hlogT : (1 / 2) * Real.log (1 / t) ≤ Real.log T := by
    have htξ : t ≤ ξ₀ ^ 2 := htt₀.le.trans (min_le_right _ _)
    have h1 : Real.log T = Real.log ξ₀ + Real.log (1 / t) := by
      rw [show T = ξ₀ * (1 / t) by simp only [T]; ring, Real.log_mul hξ₀.ne' (by positivity)]
    have h2 : Real.log t ≤ 2 * Real.log ξ₀ := by
      rw [← Real.log_rpow hξ₀, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact Real.log_le_log ht htξ
    have h3 : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
    rw [h1]
    linarith
  have hT0 : 0 < T := div_pos hξ₀ ht
  have hlog0 : 0 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]; exact neg_nonneg.mpr (Real.log_nonpos ht.le (htt₀.trans ht₀1).le)
  calc a ^ 2 * ξ₀ / (576 * Real.pi) * t * Real.log (1 / t)
      = (1 / (72 * Real.pi) * T * ((1 / 2) * Real.log (1 / t))) * (t ^ 2 * (a / 2) ^ 2) := by
        simp only [T]
        field_simp
        ring
    _ ≤ (1 / (72 * Real.pi) * T * Real.log T) * (t ^ 2 * (a / 2) ^ 2) := by
        gcongr
    _ ≤ (F.card : ℝ) * (t ^ 2 * (a / 2) ^ 2) := by
        gcongr
        exact hcount
    _ ≤ (s.card : ℝ) * (t ^ 2 * (a / 2) ^ 2) := by gcongr
    _ ≤ _ := hsum'

/-- **Probe amplitude law.** For a real compact `C²` source with `∫ f ≠ 0` there are `c, t₀ > 0`
such that for every width `t < t₀` the packet of `f_t(u) = f(u/t)` exceeds `√(c t log(1/t))` in
absolute value at arbitrarily large shifts. Unconditional. -/
theorem probe_amplitude_law {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hint : ∫ u, f u ≠ 0) :
    ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ∀ T : ℝ, ∃ τ, T ≤ τ ∧
      Real.sqrt (c * t * Real.log (1 / t)) < |stationaryPacket (fun u => f (u / t)) τ| := by
  obtain ⟨c, t₀, hc, ht₀, ht₀1, hE⟩ := criticalPacketEnergy_dilate_ge hf hfc hint
  refine ⟨c / 2, t₀, half_pos hc, ht₀, fun t ht htt₀ T => ?_⟩
  have hft : ContDiff ℝ 2 fun u => f (u / t) := hf.comp (contDiff_id.div_const t)
  have hftc : HasCompactSupport fun u => f (u / t) := by
    have e : (fun u => f (u / t)) = fun u => f (t⁻¹ • u) := by
      funext u; rw [smul_eq_mul, div_eq_inv_mul]
    rw [e]
    exact hfc.comp_smul (inv_ne_zero ht.ne')
  have hlog : 0 < Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    exact neg_pos.mpr (Real.log_neg ht (htt₀.trans ht₀1))
  have hpos : 0 ≤ c / 2 * t * Real.log (1 / t) := by positivity
  refine exists_abs_packet_gt_of_sq_lt hft hftc ?_ T
  rw [Real.sq_sqrt hpos]
  have := hE t ht htt₀
  nlinarith [mul_pos (mul_pos hc ht) hlog]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
