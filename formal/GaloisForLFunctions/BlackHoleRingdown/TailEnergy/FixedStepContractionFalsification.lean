import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence
import GaloisForLFunctions.BlackHoleRingdown.PassiveTwinEchoAndFiniteTimeDistinction
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Arithmetic Path Returns, Logarithmic Cusp Trapping, and Falsification of Fixed-Step Contraction

This module settles the physical path-dephasing question on the actual modular surface `PSL₂(ℤ)\ℍ`:
do repeated arithmetic traversals with travel times `2 log c` and Euler-totient amplitudes `φ(c)/c`
produce a fixed-step tail-energy contraction `E_h(T + L) / E_h(T) ≤ θ < 1`?

1. **Exact Repeated-Prime Invariance and Finite Path-Return Decomposition**:
   - Every prime-power traversal `c = p ^ k` (`k ≥ 1`) has travel time `2 k log p` and constant
     non-decaying amplitude `φ(p ^ k) / p ^ k = 1 - 1 / p` (`echoDelay_and_weight_prime_pow`).
   - For any mean-zero pulse `h` supported in `[-S₀, S₀]`, both `pulseReflected h u` (`u ≤ B`) and
     `stepDecrement h T L` equal finite sums over arithmetic returns `1 ≤ c ≤ ⌈e^{(B + S₀) / 2}⌉₊`
     against `(1 - e^{-v})^{-1/2}` (`pulseReflected_eq_finite_path_returns`,
     `stepDecrement_eq_finite_path_returns`).
2. **Quantitative `O(|y|^{-1/2})` Stationary-Phase Decay and Logarithmic Cusp Trapping**:
   - Each individual bounce kernel satisfies
     `‖∫_0^∞ e^{-(1 + i y) v} (1 - e^{-v})^{-1/2} dv‖ ≤ √(2π / (1 - e^{-2})) / √|y|` (`|y| ≥ 1`),
     giving `‖scatteringPhase (1 + i y)‖ ≤ C_sc / √(1 + |y|)` for all `y ∈ ℝ`.
   - The carrier-modulated mean-zero family `cuspTrappingPulse S₀ hS₀ Ω` (`supp ⊆ [-S₀, S₀]`)
     radiates at most `K_trap * e^{2T} / Ω` energy up to any time `T ∈ ℝ`, while its `L²` norm
     converges to `∫ ‖scaledBumpPulse S₀ hS₀‖² > 0`.
3. **Unconditional Falsification of Fixed-Step Contraction on `PSL₂(ℤ)\ℍ`**:
   - **Sub-logarithmic & fixed horizon stall (`tendsto_tailEnergy_ratio_sublogarithmic`)**: Along
     every horizon `T(Ω) = T₀ + α log Ω` (`0 ≤ α < 1 / 2`, `L ≥ 0`),
     `lim_{Ω → ∞} E_{p_Ω}(T(Ω) + L) / E_{p_Ω}(T(Ω)) = 1`.
   - **Deep-tail phase-uniform two-pulse falsification
     (`exists_two_pulse_deep_tail_contraction_falsifier`)**: For all `S₀ > 0, L > 0, T₀ ∈ ℝ`,
     `η ∈ (0, 1)`, and `θ < 1`, explicit mean-zero pulses `g, w` supported in `[-S₀, S₀]` and
     `T ≥ T₀` satisfy simultaneously **for every relative phase `φ ∈ ℝ`**:
     `0 < E_{g + e^{iφ} w}(T) ≤ η * ∫ ‖g + e^{iφ} w‖²` and
     `θ < E_{g + e^{iφ} w}(T + L) / E_{g + e^{iφ} w}(T)`.
   - **Multi-epoch staircase stall (`exists_multi_epoch_staircase_falsifier`)**: For any number of
     epochs `K + 1`, `L > 0`, `η ∈ (0, 1)`, and `θ < 1`, a single mean-zero pulse `h` supported in
     `[-S₀, S₀]` sheds more than `1 - η` of its remaining energy between consecutive late windows
     yet violates `E_h(T_i + L) / E_h(T_i) ≤ θ` on every window `i`, while obeying unconditional
     exponential tail decay `O_h(e^{-2σ T})` (`0 < σ < 3001 / 48000`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## 1. Repeated-Prime Amplitude Invariance and Finite Path-Return Formula -/

/-- Finite denominator cutoff `⌈e^{X / 2}⌉₊` for arithmetic cusp path returns up to `X`. -/
def pathReturnCutoff (X : ℝ) : ℕ := ⌈Real.exp (X / 2)⌉₊

/-- **Repeated-Prime Traversal Law.** Every `k`-fold traversal `c = p ^ k` (`k ≥ 1`) of a prime
path has travel time `2 k log p` and constant weight `φ(p ^ k) / p ^ k = 1 - 1 / p` independent of
multiplicity `k`. -/
theorem echoDelay_and_weight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    echoDelay (p ^ k) = 2 * (k : ℝ) * Real.log p ∧
      echoWeight (p ^ k) = 1 - 1 / (p : ℝ) := by
  constructor
  · rw [echoDelay, Nat.cast_pow, Real.log_pow]
    ring
  · have htot : Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
      Nat.totient_prime_pow hp (by omega)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hpk : p ^ k = p ^ (k - 1) * p := by
      cases k with
      | zero => omega
      | succ m => simp [pow_succ]
    have hpow_ne : (p : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ hp_pos.ne'
    rw [echoWeight, htot, hpk, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp1,
      Nat.cast_one]
    field_simp [hp_pos.ne', hpow_ne]

/-- Up to delay `X`, `echoKernel τ` is the exact finite sum over `1 ≤ c ≤ pathReturnCutoff X`. -/
theorem echoKernel_eq_finset_sum_of_le {X τ : ℝ} (hτ : τ ≤ X) :
    echoKernel τ = ∑ c ∈ Finset.Icc 1 (pathReturnCutoff X), echoTerm c τ := by
  rw [echoKernel, tsum_eq_sum]
  intro c hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact echoTerm_zero τ
  · have hc_gt : pathReturnCutoff X < c := by
      simp only [Finset.mem_Icc, not_and, not_le] at hc
      exact hc (Nat.one_le_iff_ne_zero.mpr hc0)
    have hexp : Real.exp (τ / 2) ≤ (c : ℝ) := by
      calc Real.exp (τ / 2) ≤ Real.exp (X / 2) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ (pathReturnCutoff X : ℝ) := Nat.le_ceil _
        _ ≤ (c : ℝ) := by exact_mod_cast hc_gt.le
    exact echoTerm_eq_zero_of_exp_le (Nat.pos_of_ne_zero hc0) hexp

theorem integrable_pulse_mul_echoTerm (h : CompactPulse) (c : ℕ) (u : ℝ) :
    Integrable fun τ : ℝ => h (u - τ) * ((echoTerm c τ : ℝ) : ℂ) := by
  have hdom := (h.integrable_pulse_mul_echoKernel u).norm
  have hmeas : Measurable fun τ : ℝ => h (u - τ) * ((echoTerm c τ : ℝ) : ℂ) :=
    (h.continuous_toFun.comp (continuous_const.sub continuous_id)).measurable.mul
      (Complex.measurable_ofReal.comp (measurable_echoTerm c))
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (echoTerm_nonneg c τ), Real.norm_of_nonneg (echoKernel_nonneg τ)]
  exact mul_le_mul_of_nonneg_left (echoTerm_le_echoKernel c τ) (norm_nonneg _)

theorem integral_pulse_mul_echoTerm_eq_bounce (h : CompactPulse) (c : ℕ) (u : ℝ) :
    (∫ τ : ℝ, h (u - τ) * ((echoTerm c τ : ℝ) : ℂ)) =
      ((echoWeight c : ℝ) : ℂ) *
        ∫ v in Ioi (0 : ℝ), h (u - echoDelay c - v) * ((bounceKernel v : ℝ) : ℂ) := by
  rw [← integral_add_right_eq_self (fun τ : ℝ => h (u - τ) * ((echoTerm c τ : ℝ) : ℂ))
    (echoDelay c)]
  have hpt : (fun v : ℝ => h (u - (v + echoDelay c)) * ((echoTerm c (v + echoDelay c) : ℝ) : ℂ)) =
      (Ioi (0 : ℝ)).indicator (fun v : ℝ =>
        ((echoWeight c : ℝ) : ℂ) * (h (u - echoDelay c - v) * ((bounceKernel v : ℝ) : ℂ))) := by
    funext v
    by_cases hv : 0 < v
    · have hd : echoDelay c < v + echoDelay c := by linarith
      have hv_mem : v ∈ Ioi (0 : ℝ) := hv
      rw [indicator_of_mem hv_mem, echoTerm, if_pos hd, add_sub_cancel_right,
        show u - (v + echoDelay c) = u - echoDelay c - v by ring]
      push_cast; ring
    · have hd : ¬echoDelay c < v + echoDelay c := by linarith
      have hnot : v ∉ Ioi (0 : ℝ) := hv
      rw [indicator_of_notMem hnot, echoTerm, if_neg hd, Complex.ofReal_zero, mul_zero]
  rw [hpt, integral_indicator measurableSet_Ioi, integral_const_mul]

/-- **Exact Finite Arithmetic Path-Return Decomposition of `pulseReflected`.** For any mean-zero
compact pulse `h` supported in `[-S₀, S₀]` and any `u ≤ B`, `pulseReflected h u` is the exact finite
sum over denominators `1 ≤ c ≤ pathReturnCutoff (B + S₀)` with delays `2 log c` and weights
`φ(c)/c`. -/
theorem pulseReflected_eq_finite_path_returns (h : CompactPulse) (hm : meanCoefficient h = 0)
    {S₀ B : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {u : ℝ} (hu : u ≤ B) :
    pulseReflected h u =
      ∑ c ∈ Finset.Icc 1 (pathReturnCutoff (B + S₀)),
        ((echoWeight c : ℝ) : ℂ) *
          ∫ v in Ioi (0 : ℝ), h (u - echoDelay c - v) * ((bounceKernel v : ℝ) : ℂ) := by
  have heq_echo : pulseReflected h u = pulseEcho h u := by
    have he := h.pulseEcho_eq u
    rw [hm, zero_mul, add_zero] at he
    exact he.symm
  rw [heq_echo, pulseEcho]
  set S := Finset.Icc 1 (pathReturnCutoff (B + S₀))
  have hpt : ∀ τ : ℝ, h (u - τ) * ((echoKernel τ : ℝ) : ℂ) =
      ∑ c ∈ S, h (u - τ) * ((echoTerm c τ : ℝ) : ℂ) := by
    intro τ
    rcases le_or_gt τ (B + S₀) with hτ | hτ
    · rw [echoKernel_eq_finset_sum_of_le hτ, Complex.ofReal_sum, Finset.mul_sum]
    · have hgt : S₀ < |u - τ| := by
        have : S₀ < τ - u := by linarith
        exact this.trans_le (by rw [abs_sub_comm]; exact le_abs_self _)
      rw [hS₀ (u - τ) hgt, zero_mul]
      simp
  simp_rw [hpt]
  rw [integral_finsetSum S fun c _ => integrable_pulse_mul_echoTerm h c u]
  exact Finset.sum_congr rfl fun c _ => integral_pulse_mul_echoTerm_eq_bounce h c u

/-- **Exact Finite Path-Return Formula for the Step Decrement `E_h(T) - E_h(T + L)`.** -/
theorem stepDecrement_eq_finite_path_returns (h : CompactPulse) (hm : meanCoefficient h = 0)
    {S₀ T L : ℝ} (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) :
    stepDecrement h T L =
      ∫ u in Ioc T (T + L),
        ‖∑ c ∈ Finset.Icc 1 (pathReturnCutoff (T + L + S₀)),
          ((echoWeight c : ℝ) : ℂ) *
            ∫ v in Ioi (0 : ℝ), h (u - echoDelay c - v) * ((bounceKernel v : ℝ) : ℂ)‖ ^ 2 := by
  unfold stepDecrement
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [pulseReflected_eq_finite_path_returns h hm hS₀ hu.2]

/-! ## 2. Quantitative `O(|y|^{-1/2})` Bounce Stationary-Phase and Scattering Decay -/

/-- **Path-Return Bounce Oscillatory Decay.** On the Laplace line `1 + i y` (`|y| ≥ 1`), the
transform of `(1 - e^{-v})^{-1/2}` decays quantitatively as `O(|y|^{-1/2})`. -/
theorem norm_bounce_laplace_lineOne_le {y : ℝ} (hy : 1 ≤ |y|) :
    ‖∫ v in Ioi (0 : ℝ), Complex.exp (-linePoint 1 y * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ)‖ ≤
      Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) / Real.sqrt |y| ∧
    ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ ≤
      Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) / Real.sqrt |y| := by
  have hre : 0 < (linePoint 1 y).re := by simp [linePoint]
  have hint := (integrableOn_and_integral_bounce hre).2
  suffices hβ : ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ ≤
      Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) / Real.sqrt |y| by
    exact ⟨hint.symm ▸ hβ, hβ⟩
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hre (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)
  have hnorm_eq : ‖Complex.Gamma (linePoint 1 y + 1 / 2)‖ *
      ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ =
      ‖Complex.Gamma (linePoint 1 y)‖ * ‖Complex.Gamma (1 / 2)‖ := by
    rw [← norm_mul, ← norm_mul, hbeta]
  have hl1 : linePoint 1 y = 1 + (y : ℂ) * I := by simp [linePoint]
  have hl2 : linePoint 1 y + 1 / 2 = 1 / 2 + (y : ℂ) * I + ((1 : ℕ) : ℂ) := by
    simp [linePoint]; ring
  have hnum := (norm_Gamma_one_add_I_bounds hy).2
  have hden := (norm_Gamma_half_add_nat_bounds 1 hy).1
  rw [pow_one] at hden
  have hGhalf : ‖Complex.Gamma (1 / 2)‖ = Real.sqrt Real.pi := by
    rw [Complex.Gamma_one_half_eq, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      show (1 / 2 : ℂ).re = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  rw [hl2, hl1, hGhalf] at hnorm_eq
  have hy_pos : 0 < |y| := by linarith
  have he2 : 0 < 1 - Real.exp (-2 : ℝ) := by
    have : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  set E : ℝ := Real.sqrt Real.pi * Real.exp (-(Real.pi * |y| / 2))
  have hE_pos : 0 < E := by dsimp only [E]; positivity
  have hmul1 : (|y| * E) * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ ≤
      (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y|) * E := by
    have hlow' : |y| * E ≤ ‖Complex.Gamma (1 / 2 + (y : ℂ) * I + ((1 : ℕ) : ℂ))‖ := by
      dsimp only [E]; linarith
    have hsplit_sqrt : Real.sqrt (2 * Real.pi * |y| / (1 - Real.exp (-2))) =
        Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y| := by
      rw [show 2 * Real.pi * |y| / (1 - Real.exp (-2)) =
        (2 * Real.pi / (1 - Real.exp (-2))) * |y| by ring, Real.sqrt_mul (by positivity)]
    calc (|y| * E) * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖
        ≤ ‖Complex.Gamma (1 / 2 + (y : ℂ) * I + ((1 : ℕ) : ℂ))‖ *
            ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ :=
          mul_le_mul_of_nonneg_right hlow' (norm_nonneg _)
      _ = ‖Complex.Gamma (1 + (y : ℂ) * I)‖ * Real.sqrt Real.pi := hnorm_eq
      _ ≤ (Real.sqrt (2 * Real.pi * |y| / (1 - Real.exp (-2))) *
            Real.exp (-(Real.pi * |y| / 2))) * Real.sqrt Real.pi :=
          mul_le_mul_of_nonneg_right hnum (Real.sqrt_nonneg _)
      _ = (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y|) * E := by
          rw [hsplit_sqrt]; dsimp only [E]; ring
  have hmul2 : |y| * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ ≤
      Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y| := by
    refine le_of_mul_le_mul_right ?_ hE_pos
    calc |y| * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ * E
        = (|y| * E) * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ := by ring
      _ ≤ (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y|) * E := hmul1
  have hsy_pos : 0 < Real.sqrt |y| := Real.sqrt_pos.mpr hy_pos
  rw [le_div_iff₀ hsy_pos]
  refine le_of_mul_le_mul_left ?_ hsy_pos
  calc Real.sqrt |y| * (‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ * Real.sqrt |y|)
      = (Real.sqrt |y| * Real.sqrt |y|) * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ := by ring
    _ = |y| * ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ := by rw [Real.mul_self_sqrt hy_pos.le]
    _ ≤ Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |y| := hmul2
    _ = Real.sqrt |y| * Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) := mul_comm _ _

/-- Global `O((1 + |y|)^{-1/2})` decay of `scatteringPhase` along `linePoint 1 y = 1 + i y`. -/
theorem exists_norm_scatteringPhase_lineOne_le :
    ∃ C_sc : ℝ, 0 < C_sc ∧ ∀ y : ℝ,
      ‖scatteringPhase (linePoint 1 y)‖ ≤ C_sc / Real.sqrt (1 + |y|) := by
  set S₂ : ℝ := ∑' c : ℕ, (1 / (c : ℝ) ^ (2 : ℕ))
  have hsum2 : Summable fun c : ℕ => 1 / (c : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hS₂_nn : 0 ≤ S₂ := tsum_nonneg fun c => by positivity
  set C₁ : ℝ := Real.sqrt 2 * Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * S₂
  set C_sc : ℝ := max (5 * Real.sqrt 2) (C₁ + 1)
  have hC_pos : 0 < C_sc := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C_sc, hC_pos, fun y => ?_⟩
  have hsy_pos : 0 < Real.sqrt (1 + |y|) := Real.sqrt_pos.mpr (by linarith [abs_nonneg y])
  by_cases hy : 1 ≤ |y|
  · have hw_half : 1 / 2 < (linePoint 1 y).re := by simp [linePoint]
    have hre3 : 2 < (2 * linePoint 1 y + 1).re := by simp [linePoint]
    have hsc_eq : scatteringPhase (linePoint 1 y) =
        Complex.betaIntegral (linePoint 1 y) (1 / 2) *
          LSeries (fun n : ℕ => (Nat.totient n : ℂ)) (2 * linePoint 1 y + 1) := by
      rw [← completed_div_eq_scatteringPhase hw_half,
        ← integral_cexp_mul_echoKernel_eq_completed hw_half,
        integral_cexp_mul_echoKernel hw_half,
        show riemannZeta (2 * linePoint 1 y) =
          riemannZeta (2 * linePoint 1 y + 1 - 1) by congr 1; ring,
        ← lseries_totient hre3]
    have hL_bd : ‖LSeries (fun n : ℕ => (Nat.totient n : ℂ)) (2 * linePoint 1 y + 1)‖ ≤ S₂ := by
      have hterm_eq : ∀ c : ℕ, LSeries.term (fun n : ℕ => (Nat.totient n : ℂ))
          (2 * linePoint 1 y + 1) c = echoCoefficient (linePoint 1 y) c :=
        fun c => (echoCoefficient_eq_term (linePoint 1 y) c).symm
      have hdom : ∀ c : ℕ, ‖echoCoefficient (linePoint 1 y) c‖ ≤ 1 / (c : ℝ) ^ (2 : ℕ) := by
        intro c
        have hb := norm_echoCoefficient_le (w := linePoint 1 y) c
        have hre1 : 2 * (linePoint 1 y).re = (2 : ℝ) := by simp [linePoint]
        rw [hre1] at hb
        exact hb.trans (le_of_eq (by norm_cast))
      have hsum_norm : Summable fun c : ℕ => ‖echoCoefficient (linePoint 1 y) c‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hsum2
      rw [LSeries, show (fun c : ℕ => LSeries.term (fun n : ℕ => (Nat.totient n : ℂ))
          (2 * linePoint 1 y + 1) c) = echoCoefficient (linePoint 1 y) from funext hterm_eq]
      exact (norm_tsum_le_tsum_norm hsum_norm).trans (hsum_norm.tsum_le_tsum hdom hsum2)
    have hβ_bd := (norm_bounce_laplace_lineOne_le hy).2
    have hsqrt_rel : Real.sqrt (1 + |y|) ≤ Real.sqrt 2 * Real.sqrt |y| := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hinv_sqrt : 1 / Real.sqrt |y| ≤ Real.sqrt 2 / Real.sqrt (1 + |y|) := by
      have hy0 : 0 < Real.sqrt |y| := Real.sqrt_pos.mpr (by linarith)
      rw [div_le_div_iff₀ hy0 hsy_pos, one_mul]
      exact hsqrt_rel
    rw [hsc_eq, norm_mul]
    calc ‖Complex.betaIntegral (linePoint 1 y) (1 / 2)‖ *
          ‖LSeries (fun n : ℕ => (Nat.totient n : ℂ)) (2 * linePoint 1 y + 1)‖
        ≤ (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) / Real.sqrt |y|) * S₂ :=
          mul_le_mul hβ_bd hL_bd (norm_nonneg _) (by
            have : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
            positivity)
      _ = (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * S₂) * (1 / Real.sqrt |y|) := by ring
      _ ≤ (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * S₂) *
            (Real.sqrt 2 / Real.sqrt (1 + |y|)) :=
          mul_le_mul_of_nonneg_left hinv_sqrt (by
            have : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
            positivity)
      _ = C₁ / Real.sqrt (1 + |y|) := by dsimp only [C₁]; ring
      _ ≤ C_sc / Real.sqrt (1 + |y|) :=
          div_le_div_of_nonneg_right ((by linarith : C₁ ≤ C₁ + 1).trans (le_max_right _ _))
            hsy_pos.le
  · have hy_lt : |y| ≤ 1 := (not_le.mp hy).le
    have hw_nn : 0 ≤ (linePoint 1 y).re := by simp [linePoint]
    have hrat := norm_scatteringPhase_le hw_nn
    have hden1 : (1 : ℝ) ≤ ‖2 * linePoint 1 y - 1‖ := by
      have hre1 : (2 * linePoint 1 y - 1).re = 1 := by simp [linePoint]; norm_num
      calc (1 : ℝ) = |(2 * linePoint 1 y - 1).re| := by rw [hre1]; norm_num
        _ ≤ ‖2 * linePoint 1 y - 1‖ := Complex.abs_re_le_norm _
    have hnum5 : ‖1 + 2 * linePoint 1 y‖ ≤ 5 := by
      have hre3 : (1 + 2 * linePoint 1 y).re = 3 := by simp [linePoint]; norm_num
      have him2 : (1 + 2 * linePoint 1 y).im = 2 * y := by simp [linePoint]
      calc ‖1 + 2 * linePoint 1 y‖
          ≤ |(1 + 2 * linePoint 1 y).re| + |(1 + 2 * linePoint 1 y).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = 3 + 2 * |y| := by
            rw [hre3, him2, abs_of_pos (by norm_num), abs_mul, abs_of_pos (by norm_num)]
        _ ≤ 5 := by linarith
    have hle5 : ‖scatteringPhase (linePoint 1 y)‖ ≤ 5 := by
      refine hrat.trans ?_
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hsy_le : Real.sqrt (1 + |y|) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
    calc ‖scatteringPhase (linePoint 1 y)‖ ≤ 5 := hle5
      _ ≤ (5 * Real.sqrt 2) / Real.sqrt (1 + |y|) := by
          rw [le_div_iff₀ hsy_pos]
          exact mul_le_mul_of_nonneg_left hsy_le (by norm_num)
      _ ≤ C_sc / Real.sqrt (1 + |y|) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hsy_pos.le

/-! ## 3. Carrier-Modulated Cusp-Trapping Pulse Family -/

/-- Frequency-modulated compact pulse `S ↦ e^{i Ω S} b(S)`. -/
def CompactPulse.modulate (Ω : ℝ) (b : CompactPulse) : CompactPulse where
  toFun S := Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b S
  smooth := ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).mul b.smooth
  compact := b.compact.mul_left

@[simp] theorem CompactPulse.modulate_apply (Ω : ℝ) (b : CompactPulse) (S : ℝ) :
    (b.modulate Ω) S = Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b S := rfl

theorem pulseAmplitude_modulate (Ω : ℝ) (b : CompactPulse) (w : ℂ) :
    pulseAmplitude (b.modulate Ω) w = pulseAmplitude b (w - (Ω : ℂ)) := by
  rw [pulseAmplitude, pulseAmplitude]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun S => ?_)
  dsimp only [CompactPulse.modulate_apply]
  have hexp : Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * Complex.exp (-(I * w * (S : ℂ))) =
      Complex.exp (-(I * (w - (Ω : ℂ)) * (S : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination b S * hexp

theorem CompactPulse.modulate_D_apply (Ω : ℝ) (b : CompactPulse) (S : ℝ) :
    (b.modulate Ω).D S =
      I * (Ω : ℂ) * Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b S +
        Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b.D S := by
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (I * (Ω : ℂ) * (t : ℂ)))
      (Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * (I * (Ω : ℂ))) S := by
    have hlin : HasDerivAt (fun t : ℝ => I * (Ω : ℂ) * (t : ℂ)) (I * (Ω : ℂ)) S := by
      simpa [mul_assoc] using (Complex.ofRealCLM.hasDerivAt (x := S)).const_mul (I * (Ω : ℂ))
    exact hlin.cexp
  have hprod : HasDerivAt (b.modulate Ω)
      (I * (Ω : ℂ) * Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b S +
        Complex.exp (I * (Ω : ℂ) * (S : ℂ)) * b.D S) S :=
    (hexp.mul (b.hasDerivAt S)).congr_deriv (by ring)
  exact ((b.modulate Ω).hasDerivAt S).unique hprod

/-- **Cusp-Trapping Carrier-Modulated Mean-Zero Pulse Family.** Supported in `[-S₀, S₀]`, with
exact `meanCoefficient = 0` for every `Ω ∈ ℝ` and asymptotic `L²` profile `scaledBumpPulse S₀ hS₀`. -/
def cuspTrappingPulse (S₀ : ℝ) (hS₀ : 0 < S₀) (Ω : ℝ) : CompactPulse :=
  CompactPulse.smul (1 / (1 + I * (Ω : ℂ)))
    (meanZeroPulse ((scaledBumpPulse S₀ hS₀).modulate Ω))

theorem one_add_I_mul_ofReal_ne_zero (Ω : ℝ) : (1 : ℂ) + I * (Ω : ℂ) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this

theorem meanCoefficient_cuspTrappingPulse {S₀ : ℝ} (hS₀ : 0 < S₀) (Ω : ℝ) :
    meanCoefficient (cuspTrappingPulse S₀ hS₀ Ω) = 0 := by
  rw [cuspTrappingPulse, meanCoefficient, pulseAmplitude_smul,
    show 6 * (1 / (1 + I * (Ω : ℂ)) * pulseAmplitude
      (meanZeroPulse ((scaledBumpPulse S₀ hS₀).modulate Ω)) (-I * (1 / 2))) =
      (1 / (1 + I * (Ω : ℂ))) * meanCoefficient
        (meanZeroPulse ((scaledBumpPulse S₀ hS₀).modulate Ω)) by
      rw [meanCoefficient]; ring,
    meanCoefficient_meanZeroPulse, mul_zero]

theorem cuspTrappingPulse_apply_decomp {S₀ : ℝ} (hS₀ : 0 < S₀) (Ω S : ℝ) :
    cuspTrappingPulse S₀ hS₀ Ω S =
      Complex.exp (I * (Ω : ℂ) * (S : ℂ)) *
        (scaledBumpPulse S₀ hS₀ S +
          (1 / (1 + I * (Ω : ℂ))) *
            ((scaledBumpPulse S₀ hS₀).D S - (3 / 2 : ℂ) * scaledBumpPulse S₀ hS₀ S)) := by
  set b₀ := scaledBumpPulse S₀ hS₀
  have hne := one_add_I_mul_ofReal_ne_zero Ω
  change (1 / (1 + I * (Ω : ℂ))) *
      ((-1 / 2 : ℂ) * (b₀.modulate Ω S) + (b₀.modulate Ω).D S) = _
  rw [CompactPulse.modulate_D_apply, CompactPulse.modulate_apply]
  field_simp [hne]
  ring

theorem cuspTrappingPulse_eq_zero_of_le {S₀ : ℝ} (hS₀ : 0 < S₀) (Ω : ℝ)
    {s : ℝ} (hs : S₀ ≤ |s|) :
    cuspTrappingPulse S₀ hS₀ Ω s = 0 := by
  rw [cuspTrappingPulse_apply_decomp, scaledBumpPulse_eq_zero_of_le hS₀ hs]
  have hD0 : (scaledBumpPulse S₀ hS₀).D s = 0 := by
    by_cases hgt : S₀ < |s|
    · exact CompactPulse.D_eq_zero_of_support_bound (scaledBumpPulse S₀ hS₀)
        (fun x hx => scaledBumpPulse_eq_zero_of_le hS₀ hx.le) hgt
    · have hcont := (scaledBumpPulse S₀ hS₀).D.continuous_toFun
      set ε_sign : ℝ := if 0 ≤ s then 1 else -1
      have hseq : Tendsto (fun n : ℕ => s + ε_sign / ((n : ℝ) + 1)) atTop (𝓝 s) := by
        have hdiv : Tendsto (fun n : ℕ => ε_sign / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
          (tendsto_const_nhds (x := ε_sign)).div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
        simpa using (tendsto_const_nhds (x := s)).add hdiv
      have hev : ∀ n : ℕ, (scaledBumpPulse S₀ hS₀).D
          (s + ε_sign / ((n : ℝ) + 1)) = 0 := by
        intro n
        have hpos_d : 0 < 1 / ((n : ℝ) + 1) := by positivity
        refine CompactPulse.D_eq_zero_of_support_bound (scaledBumpPulse S₀ hS₀)
          (fun x hx => scaledBumpPulse_eq_zero_of_le hS₀ hx.le) ?_
        have heq_abs : |s| = S₀ := le_antisymm (not_lt.mp hgt) hs
        dsimp only [ε_sign]
        by_cases hs0 : 0 ≤ s
        · rw [if_pos hs0]
          have hs_val : s = S₀ := by rwa [abs_of_nonneg hs0] at heq_abs
          rw [hs_val, abs_of_pos (by linarith [hpos_d])]
          linarith
        · rw [if_neg hs0]
          have hs_neg : s < 0 := not_le.mp hs0
          have hs_val : s = -S₀ := by rw [abs_of_neg hs_neg] at heq_abs; linarith
          have hneg_sum : -S₀ + -1 / ((n : ℝ) + 1) < 0 := by
            have : -1 / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := neg_div _ _
            linarith
          rw [hs_val, abs_of_neg hneg_sum]
          have : -1 / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := neg_div _ _
          linarith
      have hlim := (hcont.tendsto s).comp hseq
      simp only [Function.comp_def, hev] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  rw [hD0]
  simp

/-- Quantitative `O(1 / Ω)` convergence of `∫ ‖cuspTrappingPulse S₀ hS₀ Ω S‖² dS` to
`∫ ‖scaledBumpPulse S₀ hS₀ S‖² dS > 0`. -/
theorem tendsto_integral_norm_sq_cuspTrappingPulse {S₀ : ℝ} (hS₀ : 0 < S₀) :
    Tendsto (fun Ω : ℝ => ∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2)
      atTop (𝓝 (∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) := by
  set b₀ := scaledBumpPulse S₀ hS₀
  set q₀ := b₀.D.add (CompactPulse.smul (-3 / 2) b₀)
  have hb_int : Integrable fun S : ℝ => ‖b₀ S‖ ^ 2 :=
    (memLp_two_pulse b₀).integrable_norm_pow (by norm_num)
  have hq_int : Integrable fun S : ℝ => ‖q₀ S‖ ^ 2 :=
    (memLp_two_pulse q₀).integrable_norm_pow (by norm_num)
  set C_err : ℝ := (∫ S : ℝ, ‖b₀ S‖ ^ 2) + 2 * ∫ S : ℝ, ‖q₀ S‖ ^ 2
  have hbd : ∀ Ω : ℝ, 1 ≤ Ω →
      |(∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) - ∫ S : ℝ, ‖b₀ S‖ ^ 2| ≤ C_err / Ω := by
    intro Ω hΩ
    set c : ℂ := 1 / (1 + I * (Ω : ℂ))
    have hc_le : ‖c‖ ≤ 1 / Ω := by
      dsimp only [c]
      rw [norm_div, norm_one]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have him : (1 + I * (Ω : ℂ)).im = Ω := by simp
      calc Ω = |(1 + I * (Ω : ℂ)).im| := by rw [him, abs_of_pos (by linarith)]
        _ ≤ ‖1 + I * (Ω : ℂ)‖ := Complex.abs_im_le_norm _
    have hc1 : ‖c‖ ≤ 1 := hc_le.trans (div_le_one_of_le₀ hΩ (by positivity))
    have hc_sq : ‖c‖ ^ 2 ≤ ‖c‖ := by nlinarith [norm_nonneg c, hc1]
    have hp_int : Integrable fun S : ℝ => ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2 :=
      (memLp_two_pulse (cuspTrappingPulse S₀ hS₀ Ω)).integrable_norm_pow (by norm_num)
    have hpt : ∀ S : ℝ,
        |‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2 - ‖b₀ S‖ ^ 2| ≤
          ‖c‖ * (‖b₀ S‖ ^ 2 + 2 * ‖q₀ S‖ ^ 2) := by
      intro S
      have hn : ‖cuspTrappingPulse S₀ hS₀ Ω S‖ = ‖b₀ S + c * q₀ S‖ := by
        rw [cuspTrappingPulse_apply_decomp, norm_mul, norm_exp_I_mul, one_mul]
        congr 2
        dsimp only [q₀, b₀]
        simp only [CompactPulse.add_apply, CompactPulse.smul_apply]
        ring
      rw [hn]
      have htri1 : ‖b₀ S + c * q₀ S‖ ≤ ‖b₀ S‖ + ‖c‖ * ‖q₀ S‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
      have htri2 : ‖b₀ S‖ - ‖c‖ * ‖q₀ S‖ ≤ ‖b₀ S + c * q₀ S‖ := by
        have := norm_sub_norm_le (b₀ S) (-(c * q₀ S))
        rw [sub_neg_eq_add, norm_neg, norm_mul] at this
        exact this
      have hup : ‖b₀ S + c * q₀ S‖ ^ 2 - ‖b₀ S‖ ^ 2 ≤
          ‖c‖ * (‖b₀ S‖ ^ 2 + 2 * ‖q₀ S‖ ^ 2) := by
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri1 2
        nlinarith [sq_nonneg (‖b₀ S‖ - ‖q₀ S‖), norm_nonneg c, hc_sq]
      have hlo : -(‖c‖ * (‖b₀ S‖ ^ 2 + 2 * ‖q₀ S‖ ^ 2)) ≤
          ‖b₀ S + c * q₀ S‖ ^ 2 - ‖b₀ S‖ ^ 2 := by
        rcases le_or_gt 0 (‖b₀ S‖ - ‖c‖ * ‖q₀ S‖) with hnn | hneg
        · have hsq := pow_le_pow_left₀ hnn htri2 2
          nlinarith [sq_nonneg (‖b₀ S‖ - ‖q₀ S‖), sq_nonneg ‖q₀ S‖, norm_nonneg c]
        · have hb_le : ‖b₀ S‖ ≤ ‖c‖ * ‖q₀ S‖ := by linarith
          have hbsq : ‖b₀ S‖ ^ 2 ≤ ‖c‖ ^ 2 * ‖q₀ S‖ ^ 2 := by
            have := pow_le_pow_left₀ (norm_nonneg _) hb_le 2
            rwa [mul_pow] at this
          nlinarith [sq_nonneg ‖b₀ S + c * q₀ S‖, sq_nonneg ‖b₀ S‖, hc_sq]
      exact abs_le.mpr ⟨hlo, hup⟩
    have hdom_int : Integrable fun S : ℝ => ‖c‖ * (‖b₀ S‖ ^ 2 + 2 * ‖q₀ S‖ ^ 2) :=
      (hb_int.add (hq_int.const_mul 2)).const_mul ‖c‖
    rw [← integral_sub hp_int hb_int, ← Real.norm_eq_abs]
    calc ‖∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2 - ‖b₀ S‖ ^ 2‖
        ≤ ∫ S : ℝ, ‖c‖ * (‖b₀ S‖ ^ 2 + 2 * ‖q₀ S‖ ^ 2) :=
          norm_integral_le_of_norm_le hdom_int
            (Eventually.of_forall fun S => by rw [Real.norm_eq_abs]; exact hpt S)
      _ = ‖c‖ * C_err := by
          rw [integral_const_mul, integral_add hb_int (hq_int.const_mul 2), integral_const_mul]
      _ ≤ (1 / Ω) * C_err := mul_le_mul_of_nonneg_right hc_le
          (add_nonneg (integral_nonneg fun _ => sq_nonneg _)
            (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)))
      _ = C_err / Ω := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_ge_atTop 1).mono fun Ω hΩ => by rw [Real.norm_eq_abs]; exact hbd Ω hΩ)
    ((tendsto_const_nhds (x := C_err)).div_atTop tendsto_id)

/-! ## 4. Quantitative Cusp Trapping and Unconditional Falsification of Fixed-Step Contraction -/

private theorem sqrt_le_sqrt_mul_one_add {Ω : ℝ} (hΩ : 0 ≤ Ω) (y : ℝ) :
    Real.sqrt Ω ≤ Real.sqrt (1 + |y|) * (1 + |y - Ω|) := by
  have htri : Ω ≤ |y| + |y - Ω| := by
    calc Ω = |Ω| := (abs_of_nonneg hΩ).symm
      _ = |y + (Ω - y)| := by ring_nf
      _ ≤ |y| + |Ω - y| := abs_add_le _ _
      _ = |y| + |y - Ω| := by rw [abs_sub_comm]
  have hsq : Ω ≤ (Real.sqrt (1 + |y|) * (1 + |y - Ω|)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h1 : 0 ≤ |y| * |y - Ω| := by positivity
    have h2 : 1 + |y - Ω| ≤ (1 + |y - Ω|) ^ 2 := by
      nlinarith [abs_nonneg (y - Ω), sq_nonneg |y - Ω|]
    nlinarith [abs_nonneg y, abs_nonneg (y - Ω)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at h

private theorem norm_prefactor_cuspTrappingPulse_le {Ω : ℝ} (hΩ : 1 ≤ Ω) (y : ℝ) :
    ‖((1 / 2 : ℂ) + I * (y : ℂ)) / (1 + I * (Ω : ℂ))‖ ≤ 2 * (1 + |y - Ω|) := by
  have hden_pos : 0 < ‖1 + I * (Ω : ℂ)‖ :=
    norm_pos_iff.mpr (one_add_I_mul_ofReal_ne_zero Ω)
  rw [norm_div, div_le_iff₀ hden_pos]
  have hnum : ‖(1 / 2 : ℂ) + I * (y : ℂ)‖ ≤ (1 + Ω) * (1 + |y - Ω|) := by
    have htri : |y| ≤ Ω + |y - Ω| := by
      calc |y| = |Ω + (y - Ω)| := by ring_nf
        _ ≤ |Ω| + |y - Ω| := abs_add_le _ _
        _ = Ω + |y - Ω| := by rw [abs_of_pos (by linarith)]
    calc ‖(1 / 2 : ℂ) + I * (y : ℂ)‖
        ≤ ‖(1 / 2 : ℂ)‖ + ‖I * (y : ℂ)‖ := norm_add_le _ _
      _ = 1 / 2 + |y| := by
          rw [norm_div, norm_one, Complex.norm_ofNat, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + Ω + |y - Ω| := by linarith
      _ ≤ (1 + Ω) * (1 + |y - Ω|) := by nlinarith [abs_nonneg (y - Ω)]
  have hden : 1 + Ω ≤ 2 * ‖1 + I * (Ω : ℂ)‖ := by
    have hsq : (1 + Ω) ^ 2 ≤ (2 * ‖1 + I * (Ω : ℂ)‖) ^ 2 := by
      rw [mul_pow, ← Complex.normSq_eq_norm_sq]
      have hre : (1 + I * (Ω : ℂ)).re = 1 := by simp
      have him : (1 + I * (Ω : ℂ)).im = Ω := by simp
      rw [Complex.normSq_apply, hre, him]
      nlinarith [sq_nonneg (Ω - 1)]
    have habs := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)] at habs
  exact hnum.trans ((mul_le_mul_of_nonneg_right hden
    (by positivity : 0 ≤ 1 + |y - Ω|)).trans (le_of_eq (by ring)))

/-- **Quantitative Cusp-Trapping Radiated Energy Bound.** For every `S₀ > 0`, there exists
`K_trap > 0` such that for all `Ω ≥ 1` and all `T ∈ ℝ`, the energy radiated by
`cuspTrappingPulse S₀ hS₀ Ω` up to time `T` is at most `K_trap * e^{2T} / Ω`. -/
theorem exists_radiated_energy_cuspTrappingPulse_le {S₀ : ℝ} (hS₀ : 0 < S₀) :
    ∃ K_trap : ℝ, 0 < K_trap ∧ ∀ (Ω : ℝ), 1 ≤ Ω → ∀ T : ℝ,
      0 ≤ (∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) -
          tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) T ∧
        (∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) -
          tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) T ≤ K_trap * Real.exp (2 * T) / Ω := by
  set b₀ := scaledBumpPulse S₀ hS₀
  obtain ⟨C_sc, hC_sc, hsc⟩ := exists_norm_scatteringPhase_lineOne_le
  obtain ⟨C_b, hC_b, hrap⟩ := b₀.rapidAmplitude.decay 1 4
  set I₂ : ℝ := ∫ ξ : ℝ, ((1 + |ξ|) ^ 2)⁻¹
  have hI₂_nn : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
  set M₀ : ℝ := 2 * C_b * C_sc * I₂ + 1
  have hM₀_pos : 0 < M₀ := by positivity
  set K_trap : ℝ := M₀ ^ 2 / 2
  refine ⟨K_trap, by positivity, fun Ω hΩ T => ?_⟩
  set p := cuspTrappingPulse S₀ hS₀ Ω
  refine ⟨sub_nonneg.mpr (tailEnergy_le_initial p T), ?_⟩
  -- Pointwise reflected bound `‖pulseReflected p u‖ ≤ M₀ * e^u / √Ω` via `pulseEcho_eq_line`
  have hpt_ref : ∀ u : ℝ, ‖pulseReflected p u‖ ≤ M₀ * Real.exp u / Real.sqrt Ω := by
    intro u
    have heq_echo : pulseReflected p u = pulseEcho p u := by
      have he := p.pulseEcho_eq u
      rw [meanCoefficient_cuspTrappingPulse hS₀ Ω, zero_mul, add_zero] at he
      exact he.symm
    rw [heq_echo, p.pulseEcho_eq_line u]
    have hΩ0 : 0 < Ω := by linarith
    have hsΩ_pos : 0 < Real.sqrt Ω := Real.sqrt_pos.mpr hΩ0
    have hdom_int : Integrable fun y : ℝ =>
        (2 * C_b * C_sc * Real.exp u / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹ :=
      ((integrable_inv_one_add_abs_sq.comp_sub_right Ω).const_mul _)
    have hpt_y : ∀ y : ℝ,
        ‖pulseAmplitude p (-I * linePoint 1 y) *
            Complex.exp (linePoint 1 y * (u : ℂ)) * scatteringPhase (linePoint 1 y)‖ ≤
          (2 * C_b * C_sc * Real.exp u / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹ := by
      intro y
      have hw : -I * linePoint 1 y = (y : ℂ) - I := by
        simp only [linePoint, Complex.ofReal_one]
        linear_combination (-(y : ℂ)) * I_sq
      have hamp_eq : pulseAmplitude p ((y : ℂ) - I) =
          (((1 / 2 : ℂ) + I * (y : ℂ)) / (1 + I * (Ω : ℂ))) *
            pulseAmplitude b₀ (((y - Ω : ℝ) : ℂ) - I) := by
        dsimp only [p]
        rw [cuspTrappingPulse, pulseAmplitude_smul, meanZeroPulse, pulseAmplitude_pulseLin,
          pulseAmplitude_modulate]
        have h1 : (-1 / 2 : ℂ) + I * ((y : ℂ) - I) = (1 / 2 : ℂ) + I * (y : ℂ) := by
          linear_combination -I_sq
        have h2 : (y : ℂ) - I - (Ω : ℂ) = ((y - Ω : ℝ) : ℂ) - I := by push_cast; ring
        rw [h1, h2]
        ring
      have hpre := norm_prefactor_cuspTrappingPulse_le hΩ y
      set z : ℂ := ((y - Ω : ℝ) : ℂ) - I
      have hz_re : z.re = y - Ω := by simp [z]
      have hz_im : |z.im| ≤ 1 := by simp [z]
      have hb_rap := hrap z hz_im
      rw [hz_re] at hb_rap
      have hamp_bd : ‖pulseAmplitude p ((y : ℂ) - I)‖ ≤
          2 * C_b / (1 + |y - Ω|) ^ 3 := by
        rw [hamp_eq, norm_mul, le_div_iff₀ (by positivity)]
        calc ‖((1 / 2 : ℂ) + I * (y : ℂ)) / (1 + I * (Ω : ℂ))‖ * ‖pulseAmplitude b₀ z‖ *
              (1 + |y - Ω|) ^ 3
            ≤ (2 * (1 + |y - Ω|)) * ‖pulseAmplitude b₀ z‖ * (1 + |y - Ω|) ^ 3 := by gcongr
          _ = 2 * (‖pulseAmplitude b₀ z‖ * (1 + |y - Ω|) ^ 4) := by ring
          _ ≤ 2 * C_b := mul_le_mul_of_nonneg_left hb_rap (by norm_num)
      have hexp_n : ‖Complex.exp (linePoint 1 y * (u : ℂ))‖ = Real.exp u := by
        rw [Complex.norm_exp]
        have : (linePoint 1 y * (u : ℂ)).re = u := by simp [linePoint]
        rw [this]
      have hsc_y := hsc y
      have htri_sq := sqrt_le_sqrt_mul_one_add hΩ0.le y
      have hkey : (1 / Real.sqrt (1 + |y|)) * (1 / (1 + |y - Ω|) ^ 3) ≤
          (1 / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹ := by
        have hsy_pos : 0 < Real.sqrt (1 + |y|) := Real.sqrt_pos.mpr (by positivity)
        have hd1 : 0 < 1 + |y - Ω| := by positivity
        rw [one_div_mul_one_div, one_div_mul_eq_div, inv_eq_one_div,
          div_le_div_iff₀ (by positivity) hsΩ_pos]
        calc 1 * Real.sqrt Ω = Real.sqrt Ω := one_mul _
          _ ≤ Real.sqrt (1 + |y|) * (1 + |y - Ω|) := htri_sq
          _ = 1 / (1 + |y - Ω|) ^ 2 * (Real.sqrt (1 + |y|) * (1 + |y - Ω|) ^ 3) := by
              field_simp [hd1.ne']
      rw [hw, norm_mul, norm_mul, hexp_n]
      calc ‖pulseAmplitude p ((y : ℂ) - I)‖ * Real.exp u * ‖scatteringPhase (linePoint 1 y)‖
          ≤ (2 * C_b / (1 + |y - Ω|) ^ 3) * Real.exp u * (C_sc / Real.sqrt (1 + |y|)) := by
            gcongr
        _ = (2 * C_b * C_sc * Real.exp u) *
              ((1 / Real.sqrt (1 + |y|)) * (1 / (1 + |y - Ω|) ^ 3)) := by ring
        _ ≤ (2 * C_b * C_sc * Real.exp u) * ((1 / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (2 * C_b * C_sc * Real.exp u / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹ := by ring
    have hint_val : (∫ y : ℝ,
        (2 * C_b * C_sc * Real.exp u / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹) =
        (2 * C_b * C_sc * I₂) * Real.exp u / Real.sqrt Ω := by
      rw [integral_const_mul, integral_sub_right_eq_self (fun ξ : ℝ => ((1 + |ξ|) ^ 2)⁻¹) Ω]
      dsimp only [I₂]
      ring
    calc ‖∫ y : ℝ, pulseAmplitude p (-I * linePoint 1 y) *
            Complex.exp (linePoint 1 y * (u : ℂ)) * scatteringPhase (linePoint 1 y)‖
        ≤ ∫ y : ℝ, (2 * C_b * C_sc * Real.exp u / Real.sqrt Ω) * ((1 + |y - Ω|) ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le hdom_int (Eventually.of_forall hpt_y)
      _ = (2 * C_b * C_sc * I₂) * Real.exp u / Real.sqrt Ω := hint_val
      _ ≤ M₀ * Real.exp u / Real.sqrt Ω := by
          dsimp only [M₀]
          gcongr
          linarith
  -- Decompose `(∫ ‖p‖²) - tailEnergy p T = ∫ u in Iic T, ‖pulseReflected p u‖²`
  have hint_sq := integrable_norm_sq_pulseReflected p
  have hall := integral_add_compl (s := Ioi T) measurableSet_Ioi hint_sq
  rw [integral_norm_sq_pulseReflected p, compl_Ioi] at hall
  have hrad_eq : (∫ S : ℝ, ‖p S‖ ^ 2) - tailEnergy p T =
      ∫ u in Iic T, ‖pulseReflected p u‖ ^ 2 := by
    unfold tailEnergy; linarith
  rw [hrad_eq]
  -- Vanishing of `pulseReflected p` on `(-∞, -S₀)`
  have hvanish : ∀ u : ℝ, u < -S₀ → pulseReflected p u = 0 := by
    intro u hu
    have he := p.pulseEcho_eq u
    rw [meanCoefficient_cuspTrappingPulse hS₀ Ω, zero_mul, add_zero] at he
    rw [← he]
    exact p.pulseEcho_eq_zero (fun s hs => cuspTrappingPulse_eq_zero_of_le hS₀ Ω hs.le) hu
  have hIic_neg : (∫ u in Iic (-S₀), ‖pulseReflected p u‖ ^ 2) = 0 := by
    rw [← setIntegral_congr_set Iio_ae_eq_Iic]
    exact setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
      rw [hvanish u hu, norm_zero, sq, mul_zero]
  rcases le_or_gt T (-S₀) with hTS | hTS
  · have hle0 : (∫ u in Iic T, ‖pulseReflected p u‖ ^ 2) ≤
        ∫ u in Iic (-S₀), ‖pulseReflected p u‖ ^ 2 :=
      setIntegral_mono_set hint_sq.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun u hu => hu.trans hTS)
    rw [hIic_neg] at hle0
    exact hle0.trans (by positivity)
  · have hdisj : Disjoint (Iic (-S₀)) (Ioc (-S₀) T) :=
      Set.disjoint_left.mpr fun _ h1 h2 => h1.not_gt h2.1
    have hunion : Iic (-S₀) ∪ Ioc (-S₀) T = Iic T := Iic_union_Ioc_eq_Iic hTS.le
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc hint_sq.integrableOn
      hint_sq.integrableOn, hIic_neg, zero_add]
    have hΩ0 : 0 < Ω := by linarith
    have hcont_maj : Continuous fun u : ℝ => (M₀ ^ 2 / Ω) * Real.exp (2 * u) := by fun_prop
    have hpt_sq : ∀ u : ℝ, ‖pulseReflected p u‖ ^ 2 ≤ (M₀ ^ 2 / Ω) * Real.exp (2 * u) := by
      intro u
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (hpt_ref u) 2
      rw [div_pow, mul_pow, Real.sq_sqrt hΩ0.le, sq (Real.exp u), ← Real.exp_add] at hsq
      refine hsq.trans (le_of_eq ?_)
      rw [show u + u = 2 * u by ring]
      ring
    have hmono := setIntegral_mono hint_sq.integrableOn hcont_maj.integrableOn_Ioc hpt_sq
    have hftc : (∫ u in (-S₀)..T, Real.exp (2 * u)) =
        (1 / 2) * Real.exp (2 * T) - (1 / 2) * Real.exp (2 * (-S₀)) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => (1 / 2) * Real.exp (2 * u))
        (fun u _ => ?_) ((by fun_prop : Continuous fun u : ℝ => Real.exp (2 * u)).intervalIntegrable _ _)
      have hd : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
        simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
      exact (hd.exp.const_mul (1 / 2 : ℝ)).congr_deriv (by ring)
    have hmaj_eq : (∫ u in Ioc (-S₀) T, (M₀ ^ 2 / Ω) * Real.exp (2 * u)) =
        (M₀ ^ 2 / Ω) * ((1 / 2) * Real.exp (2 * T) - (1 / 2) * Real.exp (2 * (-S₀))) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hTS.le, hftc]
    refine hmono.trans (hmaj_eq.le.trans ?_)
    have hexp_nn : 0 ≤ (1 / 2) * Real.exp (2 * (-S₀)) := by positivity
    have h1 : (M₀ ^ 2 / Ω) * ((1 / 2) * Real.exp (2 * T) - (1 / 2) * Real.exp (2 * (-S₀))) ≤
        (M₀ ^ 2 / Ω) * ((1 / 2) * Real.exp (2 * T)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact h1.trans (le_of_eq (by dsimp only [K_trap]; ring))

/-- Along every horizon `T(Ω) = T₀ + α log Ω` (`0 ≤ α < 1 / 2`), the tail energy of
`cuspTrappingPulse S₀ hS₀ Ω` converges to `∫ ‖scaledBumpPulse S₀ hS₀‖² > 0`. -/
theorem tendsto_tailEnergy_cuspTrappingPulse_sublogarithmic {S₀ : ℝ} (hS₀ : 0 < S₀)
    (T₀ : ℝ) {α : ℝ} (hα : α < 1 / 2) :
    Tendsto (fun Ω : ℝ => tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T₀ + α * Real.log Ω))
      atTop (𝓝 (∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) := by
  obtain ⟨K_trap, hK_pos, htrap⟩ := exists_radiated_energy_cuspTrappingPulse_le hS₀
  have hnorm_lim := tendsto_integral_norm_sq_cuspTrappingPulse hS₀
  have hdiff_lim : Tendsto (fun Ω : ℝ =>
      (∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) -
        tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T₀ + α * Real.log Ω)) atTop (𝓝 0) := by
    have hrpow_zero : Tendsto (fun Ω : ℝ => K_trap * Real.exp (2 * T₀) * Ω ^ (-(1 - 2 * α)))
        atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * α)).const_mul
        (K_trap * Real.exp (2 * T₀))
    refine squeeze_zero' ((eventually_ge_atTop 1).mono fun Ω hΩ => (htrap Ω hΩ _).1)
      ((eventually_ge_atTop 1).mono fun Ω hΩ => ?_) hrpow_zero
    have hΩ0 : 0 < Ω := by linarith
    refine (htrap Ω hΩ _).2.trans (le_of_eq ?_)
    have hexp_eq : Real.exp (2 * (T₀ + α * Real.log Ω)) / Ω =
        (K_trap * Real.exp (2 * T₀)) / K_trap * Ω ^ (-(1 - 2 * α)) := by
      rw [mul_add, Real.exp_add, show 2 * (α * Real.log Ω) = Real.log Ω * (2 * α) by ring,
        ← Real.rpow_def_of_pos hΩ0, div_eq_mul_inv,
        show Ω⁻¹ = Ω ^ (-1 : ℝ) by rw [Real.rpow_neg_one], mul_assoc,
        ← Real.rpow_add hΩ0]
      field_simp [hK_pos.ne']
      congr 2; ring
    calc K_trap * Real.exp (2 * (T₀ + α * Real.log Ω)) / Ω
        = K_trap * (Real.exp (2 * (T₀ + α * Real.log Ω)) / Ω) := by ring
      _ = K_trap * ((K_trap * Real.exp (2 * T₀)) / K_trap * Ω ^ (-(1 - 2 * α))) := by
          rw [hexp_eq]
      _ = K_trap * Real.exp (2 * T₀) * Ω ^ (-(1 - 2 * α)) := by field_simp [hK_pos.ne']
  have hsub := hnorm_lim.sub hdiff_lim
  rw [sub_zero] at hsub
  exact hsub.congr fun Ω => by ring

/-- **Falsification 1 (Sub-Logarithmic & Fixed-Horizon Contraction Stall).** Along every horizon
`T(Ω) = T₀ + α log Ω` (`0 ≤ α < 1 / 2`, including fixed `T = T₀` at `α = 0`) and every step `L`,
`lim_{Ω → +∞} E_{p_Ω}(T(Ω) + L) / E_{p_Ω}(T(Ω)) = 1`. -/
theorem tendsto_tailEnergy_ratio_sublogarithmic {S₀ : ℝ} (hS₀ : 0 < S₀)
    (T₀ L : ℝ) {α : ℝ} (hα : α < 1 / 2) :
    Tendsto (fun Ω : ℝ =>
        tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T₀ + α * Real.log Ω + L) /
          tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T₀ + α * Real.log Ω))
      atTop (𝓝 1) := by
  have hE₀_pos := integral_norm_sq_scaledBumpPulse_pos hS₀
  have hnum : Tendsto (fun Ω : ℝ =>
      tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T₀ + α * Real.log Ω + L))
      atTop (𝓝 (∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) :=
    (tendsto_tailEnergy_cuspTrappingPulse_sublogarithmic hS₀ (T₀ + L) hα).congr
      fun Ω => by congr 1; ring
  have hden := tendsto_tailEnergy_cuspTrappingPulse_sublogarithmic hS₀ T₀ hα
  have hdiv := hnum.div hden hE₀_pos.ne'
  rw [div_self hE₀_pos.ne'] at hdiv
  exact hdiv

private theorem tailEnergy_add_bounds (g w : CompactPulse) (u : ℝ) :
    (Real.sqrt (tailEnergy w u) - Real.sqrt (tailEnergy g u)) ^ 2 ≤
        tailEnergy (g.add w) u ∧
      tailEnergy (g.add w) u ≤
        (Real.sqrt (tailEnergy w u) + Real.sqrt (tailEnergy g u)) ^ 2 := by
  have hlin := tailEnergy_phaseMix 0 g w u
  have hp0 : pulseReflected (g.phaseMix 0 w) = pulseReflected (g.add w) := by
    funext x
    rw [pulseReflected_phaseMix, pulseReflected_add]
    simp
  have hte : tailEnergy (g.phaseMix 0 w) u = tailEnergy (g.add w) u := by
    unfold tailEnergy; rw [hp0]
  rw [hte, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hlin
  have hcs := Real.sqrt_le_sqrt (norm_tailCrossEnergy_sq_le_mul g w u)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (tailEnergy_nonneg g u)] at hcs
  have hre_le : |(tailCrossEnergy g w u).re| ≤ ‖tailCrossEnergy g w u‖ :=
    Complex.abs_re_le_norm _
  have hsq_g := Real.sq_sqrt (tailEnergy_nonneg g u)
  have hsq_w := Real.sq_sqrt (tailEnergy_nonneg w u)
  constructor
  · have : -(‖tailCrossEnergy g w u‖) ≤ (tailCrossEnergy g w u).re :=
      (neg_le_neg hre_le).trans (neg_abs_le _)
    nlinarith
  · have : (tailCrossEnergy g w u).re ≤ ‖tailCrossEnergy g w u‖ :=
      (le_abs_self _).trans hre_le
    nlinarith

private theorem tailEnergy_phaseMix_bounds (φ : ℝ) (g w : CompactPulse) (u : ℝ) :
    (Real.sqrt (tailEnergy w u) - Real.sqrt (tailEnergy g u)) ^ 2 ≤
        tailEnergy (g.phaseMix φ w) u ∧
      tailEnergy (g.phaseMix φ w) u ≤
        (Real.sqrt (tailEnergy w u) + Real.sqrt (tailEnergy g u)) ^ 2 := by
  have hb := tailEnergy_add_bounds g (CompactPulse.smul (Complex.exp (I * (φ : ℂ))) w) u
  have hnorm : ‖Complex.exp (I * (φ : ℂ))‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  have hew : tailEnergy (CompactPulse.smul (Complex.exp (I * (φ : ℂ))) w) u = tailEnergy w u := by
    unfold tailEnergy
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [pulseReflected_smul, norm_mul, hnorm, one_mul]
  rw [hew] at hb
  exact hb

/-- **Falsification 2 (Deep-Tail Phase-Uniform Two-Pulse Superposition Falsifier).**
For every support half-width `S₀ > 0`, step `L > 0`, onset `T₀ ∈ ℝ`, deep-tail escape fraction
`η ∈ (0, 1)` (arbitrarily small), and contraction factor `θ < 1`, there exist mean-zero compact
pulses `g, w` supported in `[-S₀, S₀]` and a cutoff `T ≥ max T₀ 0` such that **simultaneously for
every relative phase `φ ∈ ℝ`**:
1. `0 < tailEnergy (g.phaseMix φ w) T ≤ η * ∫ S, ‖(g.phaseMix φ w) S‖ ^ 2` (at least `1 - η` of the
   total wavepacket energy has already escaped the cusp before time `T`);
2. `θ < tailEnergy (g.phaseMix φ w) (T + L) / tailEnergy (g.phaseMix φ w) T` (fixed-step contraction
   fails across `(T, T + L]` uniformly in `φ`). -/
theorem exists_two_pulse_deep_tail_contraction_falsifier {S₀ L η : ℝ}
    (hS₀ : 0 < S₀) (hL : 0 < L) (T₀ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) {θ : ℝ} (hθ : θ < 1) :
    ∃ (g w : CompactPulse) (T : ℝ),
      meanCoefficient g = 0 ∧ meanCoefficient w = 0 ∧
      (∀ s : ℝ, S₀ < |s| → g s = 0) ∧ (∀ s : ℝ, S₀ < |s| → w s = 0) ∧
      max T₀ 0 ≤ T ∧
      ∀ φ : ℝ,
        0 < tailEnergy (g.phaseMix φ w) T ∧
        tailEnergy (g.phaseMix φ w) T ≤ η * (∫ S : ℝ, ‖(g.phaseMix φ w) S‖ ^ 2) ∧
        θ < tailEnergy (g.phaseMix φ w) (T + L) / tailEnergy (g.phaseMix φ w) T := by
  have hE₀_pos := integral_norm_sq_scaledBumpPulse_pos hS₀
  -- Step 1: Pick nonzero mean-zero anchor pulse `g` supported in `[-S₀, S₀]`
  obtain ⟨Ω₁, _, hg_pos⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      ((tendsto_integral_norm_sq_cuspTrappingPulse hS₀).eventually
        (eventually_gt_nhds (half_lt_self hE₀_pos)))).exists
  set g := cuspTrappingPulse S₀ hS₀ Ω₁
  set Eg₀ : ℝ := ∫ S : ℝ, ‖g S‖ ^ 2
  have hEg₀_pos : 0 < Eg₀ := lt_trans (by positivity) hg_pos
  -- Step 2: Set target `w` energy `μ = (η / 16) * Eg₀` and tolerance `δ ∈ (0, 1/16]`
  set μ : ℝ := (η / 16) * Eg₀
  have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
  set δ : ℝ := (1 - max θ 0) / 16
  have hδ_pos : 0 < δ := by
    have : max θ 0 < 1 := max_lt hθ zero_lt_one
    dsimp only [δ]; linarith
  have hδ_le : δ ≤ 1 / 16 := by
    have : 0 ≤ max θ 0 := le_max_right _ _
    dsimp only [δ]; linarith
  have hθ_ratio : θ * (1 + δ) ^ 2 < (1 - δ) ^ 2 := by
    have hθm : θ ≤ 1 - 16 * δ := by
      have : θ ≤ max θ 0 := le_max_left _ _
      dsimp only [δ]; linarith
    have h1 : θ * (1 + δ) ^ 2 ≤ (1 - 16 * δ) * (1 + δ) ^ 2 :=
      mul_le_mul_of_nonneg_right hθm (sq_nonneg _)
    nlinarith [sq_nonneg δ, mul_pos hδ_pos (sq_pos_of_pos hδ_pos)]
  -- Step 3: Choose `T ≥ max T₀ 0` so `tailEnergy g T < (δ / 2)^2 * μ`
  obtain ⟨T, hT_ge, hEgT⟩ :=
    ((eventually_ge_atTop (max T₀ 0)).and
      ((tendsto_tailEnergy_atTop g).eventually
        (eventually_lt_nhds (by positivity : 0 < (δ / 2) ^ 2 * μ)))).exists
  -- Step 4: Choose `Ω₂` so `p = cuspTrappingPulse S₀ hS₀ Ω₂` traps `(1 - δ / 2)^2` past `T + L`
  have htrap_lim : Tendsto (fun Ω : ℝ =>
      tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T + L) -
        (1 - δ / 2) ^ 2 * ∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) atTop
      (𝓝 ((1 - (1 - δ / 2) ^ 2) * ∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) := by
    have ht1 : Tendsto (fun Ω : ℝ => tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T + L))
        atTop (𝓝 (∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) :=
      (tendsto_tailEnergy_cuspTrappingPulse_sublogarithmic hS₀ (T + L)
        (α := 0) (by norm_num)).congr fun Ω => by simp
    have ht2 := (tendsto_integral_norm_sq_cuspTrappingPulse hS₀).const_mul ((1 - δ / 2) ^ 2)
    convert ht1.sub ht2 using 2; ring
  have hlim_pos : 0 < (1 - (1 - δ / 2) ^ 2) * ∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2 :=
    mul_pos (by nlinarith) hE₀_pos
  obtain ⟨Ω₂, _, hp_pos, hp_trap⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      (((tendsto_integral_norm_sq_cuspTrappingPulse hS₀).eventually
          (eventually_gt_nhds (half_lt_self hE₀_pos))).and
        (htrap_lim.eventually (eventually_gt_nhds hlim_pos)))).exists
  set p := cuspTrappingPulse S₀ hS₀ Ω₂
  set Ep₀ : ℝ := ∫ S : ℝ, ‖p S‖ ^ 2
  have hEp₀_pos : 0 < Ep₀ := lt_trans (by positivity) hp_pos
  set cw : ℝ := Real.sqrt (μ / Ep₀)
  have hcw_pos : 0 < cw := Real.sqrt_pos.mpr (div_pos hμ_pos hEp₀_pos)
  set w := CompactPulse.smul (cw : ℂ) p
  have hcw_sq : cw ^ 2 * Ep₀ = μ := by
    dsimp only [cw]
    rw [Real.sq_sqrt (div_nonneg hμ_pos.le hEp₀_pos.le), div_mul_cancel₀ _ hEp₀_pos.ne']
  have hw_mean : meanCoefficient w = 0 := by
    rw [meanCoefficient, pulseAmplitude_smul,
      show 6 * ((cw : ℂ) * pulseAmplitude p (-I * (1 / 2))) = (cw : ℂ) * meanCoefficient p by
        rw [meanCoefficient]; ring,
      meanCoefficient_cuspTrappingPulse hS₀ Ω₂, mul_zero]
  have hw_supp : ∀ s : ℝ, S₀ < |s| → w s = 0 := fun s hs => by
    simp [w, p, cuspTrappingPulse_eq_zero_of_le hS₀ Ω₂ hs.le]
  have hw_energy : ∀ u : ℝ, tailEnergy w u = cw ^ 2 * tailEnergy p u := by
    intro u
    unfold tailEnergy
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [pulseReflected_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcw_pos.le, mul_pow]
  have hEw_hi : tailEnergy w T ≤ μ := by
    rw [hw_energy T, ← hcw_sq]
    exact mul_le_mul_of_nonneg_left (tailEnergy_le_initial p T) (sq_nonneg cw)
  have hEw_lo : (1 - δ / 2) ^ 2 * μ ≤ tailEnergy w (T + L) := by
    rw [hw_energy (T + L), ← hcw_sq]
    have hp_ineq : (1 - δ / 2) ^ 2 * Ep₀ ≤ tailEnergy p (T + L) := by linarith
    have := mul_le_mul_of_nonneg_left hp_ineq (sq_nonneg cw)
    linarith
  refine ⟨g, w, T, meanCoefficient_cuspTrappingPulse hS₀ Ω₁, hw_mean,
    fun s hs => cuspTrappingPulse_eq_zero_of_le hS₀ Ω₁ hs.le, hw_supp, hT_ge, fun φ => ?_⟩
  -- Bounds on `E_{g + e^{iφ} w}(T)` and `E_{g + e^{iφ} w}(T + L)`
  have hbT := tailEnergy_phaseMix_bounds φ g w T
  have hbTL := tailEnergy_phaseMix_bounds φ g w (T + L)
  have hsqrt_gT : Real.sqrt (tailEnergy g T) ≤ (δ / 2) * Real.sqrt μ := by
    have := Real.sqrt_le_sqrt hEgT.le
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at this
  have hsqrt_gTL : Real.sqrt (tailEnergy g (T + L)) ≤ (δ / 2) * Real.sqrt μ :=
    (Real.sqrt_le_sqrt (tailEnergy_anti g (by linarith))).trans hsqrt_gT
  have hsqrt_wT : Real.sqrt (tailEnergy w T) ≤ Real.sqrt μ := Real.sqrt_le_sqrt hEw_hi
  have hsqrt_wTL : (1 - δ / 2) * Real.sqrt μ ≤ Real.sqrt (tailEnergy w (T + L)) := by
    have := Real.sqrt_le_sqrt hEw_lo
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)] at this
  have hETL_lo : ((1 - δ) * Real.sqrt μ) ^ 2 ≤ tailEnergy (g.phaseMix φ w) (T + L) := by
    refine (pow_le_pow_left₀ (by positivity) ?_ 2).trans hbTL.1
    linarith
  have hET_hi : tailEnergy (g.phaseMix φ w) T ≤ ((1 + δ) * Real.sqrt μ) ^ 2 := by
    refine hbT.2.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    linarith [Real.sqrt_nonneg μ]
  have hETL_pos : 0 < tailEnergy (g.phaseMix φ w) (T + L) := by
    have : 0 < ((1 - δ) * Real.sqrt μ) ^ 2 := sq_pos_of_pos (mul_pos (by linarith)
      (Real.sqrt_pos.mpr hμ_pos))
    linarith
  have hET_pos : 0 < tailEnergy (g.phaseMix φ w) T :=
    lt_of_lt_of_le hETL_pos (tailEnergy_anti _ (by linarith))
  -- Lower bound on total initial `L²` norm of `g.phaseMix φ w`
  have hinit_lo : (1 / 2) * Eg₀ - μ ≤ ∫ S : ℝ, ‖(g.phaseMix φ w) S‖ ^ 2 := by
    have hg_i : Integrable fun S : ℝ => ‖g S‖ ^ 2 :=
      (memLp_two_pulse g).integrable_norm_pow (by norm_num)
    have hp_i : Integrable fun S : ℝ => ‖p S‖ ^ 2 :=
      (memLp_two_pulse p).integrable_norm_pow (by norm_num)
    have hmix_i : Integrable fun S : ℝ => ‖(g.phaseMix φ w) S‖ ^ 2 :=
      (memLp_two_pulse (g.phaseMix φ w)).integrable_norm_pow (by norm_num)
    have hpt : ∀ S : ℝ, (1 / 2) * ‖g S‖ ^ 2 - cw ^ 2 * ‖p S‖ ^ 2 ≤
        ‖(g.phaseMix φ w) S‖ ^ 2 := by
      intro S
      rw [CompactPulse.phaseMix_apply]
      set z₁ : ℂ := g S
      set z₂ : ℂ := Complex.exp (I * (φ : ℂ)) * w S
      have hz₂_sq : ‖z₂‖ ^ 2 = cw ^ 2 * ‖p S‖ ^ 2 := by
        dsimp only [z₂, w]
        rw [norm_mul, CompactPulse.smul_apply, norm_mul, mul_comm I,
          Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hcw_pos.le, mul_pow]
      rw [← hz₂_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
        Complex.normSq_apply, Complex.add_re, Complex.add_im]
      nlinarith [sq_nonneg (z₁.re + 2 * z₂.re), sq_nonneg (z₁.im + 2 * z₂.im)]
    have hint_le := integral_mono ((hg_i.const_mul (1 / 2)).sub (hp_i.const_mul (cw ^ 2)))
      hmix_i hpt
    rw [integral_sub (hg_i.const_mul (1 / 2)) (hp_i.const_mul (cw ^ 2)),
      integral_const_mul, integral_const_mul] at hint_le
    dsimp only [Eg₀, Ep₀] at *
    linarith
  have hdeep : tailEnergy (g.phaseMix φ w) T ≤ η * ∫ S : ℝ, ‖(g.phaseMix φ w) S‖ ^ 2 := by
    have h1 : ((1 + δ) * Real.sqrt μ) ^ 2 ≤ 2 * μ := by
      rw [mul_pow, Real.sq_sqrt hμ_pos.le]
      nlinarith
    have h2 : 2 * μ ≤ η * ((1 / 2) * Eg₀ - μ) := by
      dsimp only [μ]
      nlinarith
    exact hET_hi.trans (h1.trans (h2.trans (mul_le_mul_of_nonneg_left hinit_lo hη0.le)))
  have hstall : θ < tailEnergy (g.phaseMix φ w) (T + L) / tailEnergy (g.phaseMix φ w) T := by
    rw [lt_div_iff₀ hET_pos]
    have h1 : ((1 - δ) * Real.sqrt μ) ^ 2 = (1 - δ) ^ 2 * μ := by
      rw [mul_pow, Real.sq_sqrt hμ_pos.le]
    have h2 : ((1 + δ) * Real.sqrt μ) ^ 2 = (1 + δ) ^ 2 * μ := by
      rw [mul_pow, Real.sq_sqrt hμ_pos.le]
    rw [h1] at hETL_lo
    rw [h2] at hET_hi
    by_cases hθ0 : θ ≤ 0
    · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hθ0 hET_pos.le) hETL_pos
    · push Not at hθ0
      calc θ * tailEnergy (g.phaseMix φ w) T
          ≤ θ * ((1 + δ) ^ 2 * μ) := mul_le_mul_of_nonneg_left hET_hi hθ0.le
        _ = (θ * (1 + δ) ^ 2) * μ := by ring
        _ < (1 - δ) ^ 2 * μ := mul_lt_mul_of_pos_right hθ_ratio hμ_pos
        _ ≤ tailEnergy (g.phaseMix φ w) (T + L) := hETL_lo
  exact ⟨hET_pos, hdeep, hstall⟩

/-- **Falsification 3 (Multi-Epoch Staircase Stall Theorem).**
For any number of epochs `K + 1` (`K : ℕ`), support half-width `S₀ > 0`, step `L > 0`, inter-epoch
escape fraction `η ∈ (0, 1)`, and contraction factor `θ < 1`, there exist a single mean-zero compact
pulse `h` supported in `[-S₀, S₀]` and separated epochs
`0 ≤ T 0 < T 0 + L < T 1 < T 1 + L < ... < T K < T K + L` such that:
1. `tailEnergy h (T 0) < η * ∫ S, ‖h S‖ ^ 2` and
   `∀ j : Fin K, tailEnergy h (T j.succ) < η * tailEnergy h (T j.castSucc + L)` (arbitrarily steep
   inter-epoch energy radiation);
2. `∀ i : Fin (K + 1), θ < tailEnergy h (T i + L) / tailEnergy h (T i)` (simultaneous fixed-step
   contraction failure on every epoch);
3. For every `0 < σ < 3001 / 48000`, `tailEnergy h u = O_h(e^{-2σ u})` unconditionally as
   `u → +∞`. -/
theorem exists_multi_epoch_staircase_falsifier (K : ℕ) {S₀ L η : ℝ}
    (hS₀ : 0 < S₀) (hL : 0 < L) (hη0 : 0 < η) (hη1 : η < 1) {θ : ℝ} (hθ : θ < 1) :
    ∃ (h : CompactPulse) (T : Fin (K + 1) → ℝ),
      meanCoefficient h = 0 ∧
      (∀ s : ℝ, S₀ < |s| → h s = 0) ∧
      0 ≤ T 0 ∧
      (∀ j : Fin K, T j.castSucc + L < T j.succ) ∧
      tailEnergy h (T 0) < η * (∫ S : ℝ, ‖h S‖ ^ 2) ∧
      (∀ j : Fin K, tailEnergy h (T j.succ) < η * tailEnergy h (T j.castSucc + L)) ∧
      (∀ i : Fin (K + 1), θ < tailEnergy h (T i + L) / tailEnergy h (T i)) ∧
      (∀ σ : ℝ, 0 < σ → σ < 3001 / 48000 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → tailEnergy h u ≤ C * Real.exp (-2 * σ * u)) := by
  suffices hcore : ∃ (h : CompactPulse) (T : Fin (K + 1) → ℝ),
      meanCoefficient h = 0 ∧
      (∀ s : ℝ, S₀ < |s| → h s = 0) ∧
      0 ≤ T 0 ∧
      (∀ j : Fin K, T j.castSucc + L < T j.succ) ∧
      tailEnergy h (T 0) < η * (∫ S : ℝ, ‖h S‖ ^ 2) ∧
      (∀ j : Fin K, tailEnergy h (T j.succ) < η * tailEnergy h (T j.castSucc + L)) ∧
      (∀ i : Fin (K + 1), θ < tailEnergy h (T i + L) / tailEnergy h (T i)) by
    obtain ⟨h, T, hm, hs, hT0, hsep, hinit, hinter, hstall⟩ := hcore
    refine ⟨h, T, hm, hs, hT0, hsep, hinit, hinter, hstall, fun σ hσ0 hσ => ?_⟩
    obtain ⟨C, hC0, _, htail⟩ := (unconditional_cusp_escape_sub_seven_eighths hσ0 hσ h).2
    exact ⟨C ^ 2 / (2 * σ), by positivity, htail⟩
  induction K with
  | zero =>
    obtain ⟨g, w, T₀, hg_m, hw_m, hg_s, hw_s, hT₀_ge, hφ⟩ :=
      exists_two_pulse_deep_tail_contraction_falsifier hS₀ hL 0 (by positivity : 0 < η / 2)
        (by linarith) hθ
    obtain ⟨hET_pos, hdeep, hstall⟩ := hφ 0
    set h := g.phaseMix 0 w
    have hh_m : meanCoefficient h = 0 := by
      dsimp only [h]
      rw [CompactPulse.phaseMix, meanCoefficient, pulseAmplitude_add, pulseAmplitude_smul]
      have hg0 : pulseAmplitude g (-I * (1 / 2)) = 0 := by
        have := hg_m; rw [meanCoefficient] at this
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      have hw0 : pulseAmplitude w (-I * (1 / 2)) = 0 := by
        have := hw_m; rw [meanCoefficient] at this
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      rw [hg0, hw0]; simp
    have hh_s : ∀ s : ℝ, S₀ < |s| → h s = 0 := fun s hs => by
      simp [h, hg_s s hs, hw_s s hs]
    have hinit_pos : 0 < ∫ S : ℝ, ‖h S‖ ^ 2 := by
      have := tailEnergy_le_initial h T₀
      linarith
    refine ⟨h, fun _ => T₀, hh_m, hh_s, le_trans (le_max_right 0 0) hT₀_ge,
      fun j => Fin.elim0 j, by linarith, fun j => Fin.elim0 j, fun i => ?_⟩
    fin_cases i
    exact hstall
  | succ K ih =>
    obtain ⟨h, T, hh_m, hh_s, hT0, hsep, hinit, hinter, hstall⟩ := ih
    have hh_ne : ∃ S : ℝ, h S ≠ 0 := by
      by_contra hall; push Not at hall
      have hp0 : pulseReflected h = 0 := by
        funext u
        have heq : h = CompactPulse.zero := by cases h; congr; funext S; exact hall S
        rw [heq, pulseReflected_zero]; rfl
      have hE0 : tailEnergy h (T 0) = 0 := by unfold tailEnergy; simp [hp0]
      have hI0 : (∫ S : ℝ, ‖h S‖ ^ 2) = 0 := by simp [hall]
      rw [hE0, hI0, mul_zero] at hinit
      exact lt_irrefl 0 hinit
    -- Continuous perturbation stability on the existing finite set of strict inequalities
    have hcont_pert : Continuous fun r : ℝ =>
        let Eh0_up := (Real.sqrt (tailEnergy h (T 0)) + |r|) ^ 2
        let Ih_lo := (max (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) - |r|) 0) ^ 2
        Eh0_up - η * Ih_lo := by fun_prop
    have h0_val : ((Real.sqrt (tailEnergy h (T 0)) + |(0 : ℝ)|) ^ 2 -
        η * (max (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) - |(0 : ℝ)|) 0) ^ 2) < 0 := by
      have hI_nn : 0 ≤ ∫ S : ℝ, ‖h S‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
      simp only [abs_zero, add_zero, sub_zero, max_eq_left (Real.sqrt_nonneg _),
        Real.sq_sqrt (tailEnergy_nonneg h (T 0)), Real.sq_sqrt hI_nn]
      linarith
    have hev_init := hcont_pert.tendsto 0 |>.eventually (eventually_lt_nhds h0_val)
    have hev_inter : ∀ j : Fin K, ∀ᶠ r : ℝ in 𝓝 0,
        (Real.sqrt (tailEnergy h (T j.succ)) + |r|) ^ 2 <
          η * (max (Real.sqrt (tailEnergy h (T j.castSucc + L)) - |r|) 0) ^ 2 := by
      intro j
      have hc : Continuous fun r : ℝ =>
          (Real.sqrt (tailEnergy h (T j.succ)) + |r|) ^ 2 -
            η * (max (Real.sqrt (tailEnergy h (T j.castSucc + L)) - |r|) 0) ^ 2 := by fun_prop
      have hv : (Real.sqrt (tailEnergy h (T j.succ)) + |(0 : ℝ)|) ^ 2 -
          η * (max (Real.sqrt (tailEnergy h (T j.castSucc + L)) - |(0 : ℝ)|) 0) ^ 2 < 0 := by
        simp only [abs_zero, add_zero, sub_zero, max_eq_left (Real.sqrt_nonneg _),
          Real.sq_sqrt (tailEnergy_nonneg h _)]
        linarith [hinter j]
      exact ((hc.tendsto 0).eventually (eventually_lt_nhds hv)).mono fun _ hr => sub_neg.mp hr
    have hev_stall : ∀ i : Fin (K + 1), ∀ᶠ r : ℝ in 𝓝 0,
        max θ 0 * (Real.sqrt (tailEnergy h (T i)) + |r|) ^ 2 <
          (max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0) ^ 2 ∧
          0 < max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0 := by
      intro i
      have hET_pos := tailEnergy_pos h hh_ne (T i)
      have hETL_pos := tailEnergy_pos h hh_ne (T i + L)
      have hst_i := hstall i
      rw [lt_div_iff₀ hET_pos] at hst_i
      have hst_max : max θ 0 * tailEnergy h (T i) < tailEnergy h (T i + L) := by
        rcases le_or_gt θ 0 with hθ0 | hθ0
        · rw [max_eq_right hθ0, zero_mul]; exact hETL_pos
        · rw [max_eq_left hθ0.le]; exact hst_i
      have hc1 : Continuous fun r : ℝ =>
          max θ 0 * (Real.sqrt (tailEnergy h (T i)) + |r|) ^ 2 -
            (max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0) ^ 2 := by fun_prop
      have hv1 : max θ 0 * (Real.sqrt (tailEnergy h (T i)) + |(0 : ℝ)|) ^ 2 -
          (max (Real.sqrt (tailEnergy h (T i + L)) - |(0 : ℝ)|) 0) ^ 2 < 0 := by
        simp only [abs_zero, add_zero, sub_zero, max_eq_left (Real.sqrt_nonneg _),
          Real.sq_sqrt hET_pos.le, Real.sq_sqrt hETL_pos.le]
        linarith
      have hc2 : Continuous fun r : ℝ => max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0 := by
        fun_prop
      have hv2 : 0 < max (Real.sqrt (tailEnergy h (T i + L)) - |(0 : ℝ)|) 0 := by
        simp only [abs_zero, sub_zero, max_eq_left (Real.sqrt_nonneg _)]
        exact Real.sqrt_pos.mpr hETL_pos
      exact ((hc1.tendsto 0).eventually (eventually_lt_nhds hv1)).mp
        (((hc2.tendsto 0).eventually (eventually_gt_nhds hv2)).mono fun r h2 h1 =>
          ⟨by linarith, h2⟩)
    set E_last : ℝ := tailEnergy h (T (Fin.last K) + L)
    have hE_last_pos : 0 < E_last := tailEnergy_pos h hh_ne _
    have hev_last : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
        4 * r ^ 2 < η * (max (Real.sqrt E_last - |r|) 0) ^ 2 := by
      have hc : Continuous fun r : ℝ =>
          4 * r ^ 2 - η * (max (Real.sqrt E_last - |r|) 0) ^ 2 := by fun_prop
      have hv : 4 * (0 : ℝ) ^ 2 - η * (max (Real.sqrt E_last - |(0 : ℝ)|) 0) ^ 2 < 0 := by
        simp only [abs_zero, sub_zero, max_eq_left (Real.sqrt_nonneg _),
          Real.sq_sqrt hE_last_pos.le]
        have : 0 < η * E_last := mul_pos hη0 hE_last_pos
        linarith
      exact ((hc.tendsto 0).eventually (eventually_lt_nhds hv)).mono fun _ hr => sub_neg.mp hr
    have hev_all : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
        ((Real.sqrt (tailEnergy h (T 0)) + |r|) ^ 2 <
          η * (max (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) - |r|) 0) ^ 2) ∧
        (∀ j : Fin K, (Real.sqrt (tailEnergy h (T j.succ)) + |r|) ^ 2 <
          η * (max (Real.sqrt (tailEnergy h (T j.castSucc + L)) - |r|) 0) ^ 2) ∧
        (∀ i : Fin (K + 1),
          max θ 0 * (Real.sqrt (tailEnergy h (T i)) + |r|) ^ 2 <
            (max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0) ^ 2 ∧
            0 < max (Real.sqrt (tailEnergy h (T i + L)) - |r|) 0) ∧
        (4 * r ^ 2 < η * (max (Real.sqrt E_last - |r|) 0) ^ 2) := by
      refine (hev_init.and ((Filter.eventually_all.mpr hev_inter).and
        ((Filter.eventually_all.mpr hev_stall).and hev_last))).mono ?_
      rintro r ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, h2, h3, h4⟩
    obtain ⟨ρ_rad, hρ_pos, hball⟩ := Metric.eventually_nhds_iff.mp hev_all
    set r₀ : ℝ := ρ_rad / 2
    have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; positivity
    obtain ⟨hr_init, hr_inter, hr_stall, hr_last⟩ :=
      hball (y := r₀) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr₀_pos]; dsimp only [r₀]; linarith)
    set μ : ℝ := r₀ ^ 2
    have hμ_pos : 0 < μ := sq_pos_of_pos hr₀_pos
    have hsqrt_μ : Real.sqrt μ = r₀ := Real.sqrt_sq hr₀_pos.le
    have habs_r₀ : |r₀| = r₀ := abs_of_pos hr₀_pos
    -- Choose tolerance `δ` and next epoch `T_next > T (Fin.last K) + L`
    set δ : ℝ := (1 - max θ 0) / 16
    have hδ_pos : 0 < δ := by
      have : max θ 0 < 1 := max_lt hθ zero_lt_one
      dsimp only [δ]; linarith
    have hδ_le : δ ≤ 1 / 16 := by
      have : 0 ≤ max θ 0 := le_max_right _ _
      dsimp only [δ]; linarith
    have hθ_ratio : θ * (1 + δ) ^ 2 < (1 - δ) ^ 2 := by
      have hθm : θ ≤ 1 - 16 * δ := by
        have : θ ≤ max θ 0 := le_max_left _ _
        dsimp only [δ]; linarith
      have h1 : θ * (1 + δ) ^ 2 ≤ (1 - 16 * δ) * (1 + δ) ^ 2 :=
        mul_le_mul_of_nonneg_right hθm (sq_nonneg _)
      nlinarith [sq_nonneg δ, mul_pos hδ_pos (sq_pos_of_pos hδ_pos)]
    obtain ⟨T_next, hT_next_gt, hEh_next⟩ :=
      ((eventually_gt_atTop (T (Fin.last K) + L)).and
        ((tendsto_tailEnergy_atTop h).eventually
          (eventually_lt_nhds (by positivity : 0 < (δ / 2) ^ 2 * μ)))).exists
    -- Construct `w` of total energy `μ` trapped past `T_next + L`
    have hE₀_pos := integral_norm_sq_scaledBumpPulse_pos hS₀
    have htrap_lim : Tendsto (fun Ω : ℝ =>
        tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T_next + L) -
          (1 - δ / 2) ^ 2 * ∫ S : ℝ, ‖cuspTrappingPulse S₀ hS₀ Ω S‖ ^ 2) atTop
        (𝓝 ((1 - (1 - δ / 2) ^ 2) * ∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) := by
      have ht1 : Tendsto (fun Ω : ℝ => tailEnergy (cuspTrappingPulse S₀ hS₀ Ω) (T_next + L))
          atTop (𝓝 (∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2)) :=
        (tendsto_tailEnergy_cuspTrappingPulse_sublogarithmic hS₀ (T_next + L)
          (α := 0) (by norm_num)).congr fun Ω => by simp
      have ht2 := (tendsto_integral_norm_sq_cuspTrappingPulse hS₀).const_mul ((1 - δ / 2) ^ 2)
      convert ht1.sub ht2 using 2; ring
    have hlim_pos : 0 < (1 - (1 - δ / 2) ^ 2) * ∫ S : ℝ, ‖scaledBumpPulse S₀ hS₀ S‖ ^ 2 :=
      mul_pos (by nlinarith) hE₀_pos
    obtain ⟨Ω, _, hp_pos, hp_trap⟩ :=
      ((eventually_ge_atTop (1 : ℝ)).and
        (((tendsto_integral_norm_sq_cuspTrappingPulse hS₀).eventually
            (eventually_gt_nhds (half_lt_self hE₀_pos))).and
          (htrap_lim.eventually (eventually_gt_nhds hlim_pos)))).exists
    set p := cuspTrappingPulse S₀ hS₀ Ω
    set Ep₀ : ℝ := ∫ S : ℝ, ‖p S‖ ^ 2
    have hEp₀_pos : 0 < Ep₀ := lt_trans (by positivity) hp_pos
    set cw : ℝ := Real.sqrt (μ / Ep₀)
    have hcw_pos : 0 < cw := Real.sqrt_pos.mpr (div_pos hμ_pos hEp₀_pos)
    set w := CompactPulse.smul (cw : ℂ) p
    have hcw_sq : cw ^ 2 * Ep₀ = μ := by
      dsimp only [cw]
      rw [Real.sq_sqrt (div_nonneg hμ_pos.le hEp₀_pos.le), div_mul_cancel₀ _ hEp₀_pos.ne']
    have hw_energy : ∀ u : ℝ, tailEnergy w u = cw ^ 2 * tailEnergy p u := by
      intro u
      unfold tailEnergy
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      rw [pulseReflected_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hcw_pos.le, mul_pow]
    have hEw_le : ∀ u : ℝ, tailEnergy w u ≤ μ := fun u => by
      rw [hw_energy u, ← hcw_sq]
      exact mul_le_mul_of_nonneg_left (tailEnergy_le_initial p u) (sq_nonneg cw)
    have hsqrt_w_le : ∀ u : ℝ, Real.sqrt (tailEnergy w u) ≤ r₀ := fun u => by
      rw [← hsqrt_μ]
      exact Real.sqrt_le_sqrt (hEw_le u)
    have hEw_trap : (1 - δ / 2) ^ 2 * μ ≤ tailEnergy w (T_next + L) := by
      rw [hw_energy (T_next + L), ← hcw_sq]
      have hp_ineq : (1 - δ / 2) ^ 2 * Ep₀ ≤ tailEnergy p (T_next + L) := by linarith
      have := mul_le_mul_of_nonneg_left hp_ineq (sq_nonneg cw)
      linarith
    set h' := h.add w
    set T' : Fin (K + 2) → ℝ := Fin.snoc T T_next
    have hT'0 : T' 0 = T 0 := by
      dsimp only [T']
      exact Fin.snoc_castSucc (α := fun _ => ℝ) T T_next 0
    -- Helper bounds on `tailEnergy h' u` and `∫ ‖h'‖²`
    have hE_up : ∀ u : ℝ, tailEnergy h' u ≤ (Real.sqrt (tailEnergy h u) + r₀) ^ 2 := by
      intro u
      have hb := (tailEnergy_add_bounds h w u).2
      refine hb.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
      linarith [hsqrt_w_le u]
    have hE_lo : ∀ u : ℝ, (max (Real.sqrt (tailEnergy h u) - r₀) 0) ^ 2 ≤ tailEnergy h' u := by
      intro u
      rcases le_or_gt (Real.sqrt (tailEnergy h u) - r₀) 0 with hle | hgt
      · rw [max_eq_right hle, sq, zero_mul]
        exact tailEnergy_nonneg h' u
      · rw [max_eq_left hgt.le]
        have hb := (tailEnergy_add_bounds h w u).1
        have hsub : Real.sqrt (tailEnergy h u) - r₀ ≤
            Real.sqrt (tailEnergy h u) - Real.sqrt (tailEnergy w u) := by
          linarith [hsqrt_w_le u]
        have hsq : (Real.sqrt (tailEnergy h u) - r₀) ^ 2 ≤
            (Real.sqrt (tailEnergy w u) - Real.sqrt (tailEnergy h u)) ^ 2 := by
          rw [show (Real.sqrt (tailEnergy w u) - Real.sqrt (tailEnergy h u)) ^ 2 =
            (Real.sqrt (tailEnergy h u) - Real.sqrt (tailEnergy w u)) ^ 2 by ring]
          exact pow_le_pow_left₀ hgt.le hsub 2
        exact hsq.trans hb
    have hI_lo : (max (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) - r₀) 0) ^ 2 ≤ ∫ S : ℝ, ‖h' S‖ ^ 2 := by
      rcases le_or_gt (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) - r₀) 0 with hle | hgt
      · rw [max_eq_right hle, sq, zero_mul]
        exact integral_nonneg fun _ => sq_nonneg _
      · rw [max_eq_left hgt.le]
        -- Use Plancherel `∫ ‖h'‖² = lim_{B → -∞} tailEnergy h' B ≥ tailEnergy h' (-S₀ - 1)`!
        have hp_zero : ∀ u : ℝ, u < -(S₀ + 1) → pulseReflected h' u = 0 := by
          intro u hu
          have hh'_m : meanCoefficient h' = 0 := by
            dsimp only [h']
            rw [meanCoefficient, pulseAmplitude_add]
            have h1 : pulseAmplitude h (-I * (1 / 2)) = 0 := by
              have := hh_m; rw [meanCoefficient] at this
              exact (mul_eq_zero.mp this).resolve_left (by norm_num)
            have h2 : pulseAmplitude w (-I * (1 / 2)) = 0 := by
              dsimp only [w]
              rw [pulseAmplitude_smul]
              have := meanCoefficient_cuspTrappingPulse hS₀ Ω
              rw [meanCoefficient] at this
              rw [(mul_eq_zero.mp this).resolve_left (by norm_num), mul_zero]
            rw [h1, h2]; simp
          have he := h'.pulseEcho_eq u
          rw [hh'_m, zero_mul, add_zero] at he
          rw [← he]
          exact h'.pulseEcho_eq_zero (fun s hs => by
            have hs' : S₀ < |s| := by linarith
            dsimp only [h', w, p]
            simp [hh_s s hs', cuspTrappingPulse_eq_zero_of_le hS₀ Ω hs'.le]) hu
        have hI_eq_tail : (∫ S : ℝ, ‖h' S‖ ^ 2) = tailEnergy h' (-(S₀ + 1)) := by
          have hint := integrable_norm_sq_pulseReflected h'
          have hall := integral_add_compl (s := Ioi (-(S₀ + 1))) measurableSet_Ioi hint
          rw [integral_norm_sq_pulseReflected h', compl_Ioi] at hall
          have h0 : (∫ u in Iic (-(S₀ + 1)), ‖pulseReflected h' u‖ ^ 2) = 0 := by
            rw [← setIntegral_congr_set Iio_ae_eq_Iic]
            exact setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
              rw [hp_zero u hu, norm_zero, sq, mul_zero]
          unfold tailEnergy; linarith
        have hIh_eq_tail : (∫ S : ℝ, ‖h S‖ ^ 2) = tailEnergy h (-(S₀ + 1)) := by
          have hint := integrable_norm_sq_pulseReflected h
          have hall := integral_add_compl (s := Ioi (-(S₀ + 1))) measurableSet_Ioi hint
          rw [integral_norm_sq_pulseReflected h, compl_Ioi] at hall
          have h0 : (∫ u in Iic (-(S₀ + 1)), ‖pulseReflected h u‖ ^ 2) = 0 := by
            rw [← setIntegral_congr_set Iio_ae_eq_Iic]
            refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
            have he := h.pulseEcho_eq u
            rw [hh_m, zero_mul, add_zero] at he
            rw [← he, h.pulseEcho_eq_zero (fun s hs => hh_s s (by linarith)) hu,
              norm_zero, sq, mul_zero]
          unfold tailEnergy; linarith
        rw [hI_eq_tail, hIh_eq_tail]
        have hb := hE_lo (-(S₀ + 1))
        rwa [← hIh_eq_tail, max_eq_left hgt.le] at hb
    -- Assemble all claims for `(h', T')`
    have hh'_m : meanCoefficient h' = 0 := by
      dsimp only [h']
      rw [meanCoefficient, pulseAmplitude_add]
      have h1 : pulseAmplitude h (-I * (1 / 2)) = 0 := by
        have := hh_m; rw [meanCoefficient] at this
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      have h2 : pulseAmplitude w (-I * (1 / 2)) = 0 := by
        dsimp only [w]; rw [pulseAmplitude_smul]
        have := meanCoefficient_cuspTrappingPulse hS₀ Ω
        rw [meanCoefficient] at this
        rw [(mul_eq_zero.mp this).resolve_left (by norm_num), mul_zero]
      rw [h1, h2]; simp
    have hh'_s : ∀ s : ℝ, S₀ < |s| → h' s = 0 := fun s hs => by
      dsimp only [h', w, p]
      simp [hh_s s hs, cuspTrappingPulse_eq_zero_of_le hS₀ Ω hs.le]
    refine ⟨h', T', hh'_m, hh'_s, by rw [hT'0]; exact hT0, ?_, ?_, ?_, ?_⟩
    · -- Epoch separation `T' j.castSucc + L < T' j.succ`
      intro j
      refine Fin.lastCases ?_ (fun j₀ => ?_) j
      · dsimp only [T']
        rw [Fin.succ_last, Fin.snoc_last,
          show (Fin.last K).castSucc = (Fin.last K).castSucc from rfl,
          Fin.snoc_castSucc]
        exact hT_next_gt
      · dsimp only [T']
        rw [Fin.castSucc_castSucc, Fin.snoc_castSucc,
          show j₀.castSucc.succ = j₀.succ.castSucc from (Fin.succ_castSucc j₀).symm,
          Fin.snoc_castSucc]
        exact hsep j₀
    · -- Initial drop `tailEnergy h' (T' 0) < η * ∫ ‖h'‖²`
      rw [hT'0]
      rw [habs_r₀] at hr_init
      exact (hE_up (T 0)).trans (lt_of_lt_of_le hr_init
        (mul_le_mul_of_nonneg_left hI_lo hη0.le))
    · -- Inter-epoch drops `tailEnergy h' (T' j.succ) < η * tailEnergy h' (T' j.castSucc + L)`
      intro j
      refine Fin.lastCases ?_ (fun j₀ => ?_) j
      · dsimp only [T']
        rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
        -- At `T_next`: `tailEnergy h' T_next ≤ (√(tailEnergy h T_next) + r₀)² ≤ 4 r₀²`
        have hsqrt_next : Real.sqrt (tailEnergy h T_next) ≤ r₀ := by
          have h1 := Real.sqrt_le_sqrt hEh_next.le
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hsqrt_μ] at h1
          nlinarith
        have hup_next : tailEnergy h' T_next ≤ 4 * r₀ ^ 2 :=
          (hE_up T_next).trans (by
            have := pow_le_pow_left₀ (by positivity) (by linarith : Real.sqrt (tailEnergy h T_next) + r₀ ≤ 2 * r₀) 2
            linarith)
        rw [habs_r₀] at hr_last
        exact hup_next.trans (lt_of_lt_of_le hr_last
          (mul_le_mul_of_nonneg_left (hE_lo (T (Fin.last K) + L)) hη0.le))
      · dsimp only [T']
        rw [show j₀.castSucc.succ = j₀.succ.castSucc from (Fin.succ_castSucc j₀).symm,
          Fin.snoc_castSucc, Fin.castSucc_castSucc, Fin.snoc_castSucc]
        have hj := hr_inter j₀
        rw [habs_r₀] at hj
        exact (hE_up (T j₀.succ)).trans (lt_of_lt_of_le hj
          (mul_le_mul_of_nonneg_left (hE_lo (T j₀.castSucc + L)) hη0.le))
    · -- Contraction stall on every epoch `i : Fin (K + 2)`
      intro i
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · dsimp only [T']
        rw [Fin.snoc_last]
        -- At `T_next`: `w` dominates `h`
        have hb1 := tailEnergy_add_bounds h w T_next
        have hb2 := tailEnergy_add_bounds h w (T_next + L)
        have hsqrt_h1 : Real.sqrt (tailEnergy h T_next) ≤ (δ / 2) * r₀ := by
          have := Real.sqrt_le_sqrt hEh_next.le
          rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hsqrt_μ] at this
        have hsqrt_h2 : Real.sqrt (tailEnergy h (T_next + L)) ≤ (δ / 2) * r₀ :=
          (Real.sqrt_le_sqrt (tailEnergy_anti h (by linarith))).trans hsqrt_h1
        have hsqrt_w2 : (1 - δ / 2) * r₀ ≤ Real.sqrt (tailEnergy w (T_next + L)) := by
          have := Real.sqrt_le_sqrt hEw_trap
          rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), hsqrt_μ] at this
        have hETL_lo : (1 - δ) ^ 2 * r₀ ^ 2 ≤ tailEnergy h' (T_next + L) := by
          have h1 : ((1 - δ) * r₀) ^ 2 ≤
              (Real.sqrt (tailEnergy w (T_next + L)) - Real.sqrt (tailEnergy h (T_next + L))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
          calc (1 - δ) ^ 2 * r₀ ^ 2 = ((1 - δ) * r₀) ^ 2 := by ring
            _ ≤ tailEnergy h' (T_next + L) := h1.trans hb2.1
        have hET_hi : tailEnergy h' T_next ≤ (1 + δ) ^ 2 * r₀ ^ 2 := by
          have h1 : (Real.sqrt (tailEnergy w T_next) + Real.sqrt (tailEnergy h T_next)) ^ 2 ≤
              ((1 + δ) * r₀) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith [hsqrt_w_le T_next]) 2
          calc tailEnergy h' T_next ≤ ((1 + δ) * r₀) ^ 2 := hb1.2.trans h1
            _ = (1 + δ) ^ 2 * r₀ ^ 2 := by ring
        have hETL_pos : 0 < tailEnergy h' (T_next + L) :=
          lt_of_lt_of_le (mul_pos (sq_pos_of_pos (by linarith)) hμ_pos) hETL_lo
        have hET_pos : 0 < tailEnergy h' T_next :=
          lt_of_lt_of_le hETL_pos (tailEnergy_anti h' (by linarith))
        rw [lt_div_iff₀ hET_pos]
        by_cases hθ0 : θ ≤ 0
        · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hθ0 hET_pos.le) hETL_pos
        · push Not at hθ0
          calc θ * tailEnergy h' T_next
              ≤ θ * ((1 + δ) ^ 2 * r₀ ^ 2) := mul_le_mul_of_nonneg_left hET_hi hθ0.le
            _ = (θ * (1 + δ) ^ 2) * r₀ ^ 2 := by ring
            _ < (1 - δ) ^ 2 * r₀ ^ 2 := mul_lt_mul_of_pos_right hθ_ratio hμ_pos
            _ ≤ tailEnergy h' (T_next + L) := hETL_lo
      · dsimp only [T']
        rw [Fin.snoc_castSucc]
        obtain ⟨hst_i, hpos_lo⟩ := hr_stall i₀
        rw [habs_r₀] at hst_i hpos_lo
        have hETL_pos : 0 < tailEnergy h' (T i₀ + L) :=
          lt_of_lt_of_le (sq_pos_of_pos hpos_lo) (hE_lo (T i₀ + L))
        have hET_pos : 0 < tailEnergy h' (T i₀) :=
          lt_of_lt_of_le hETL_pos (tailEnergy_anti h' (by linarith))
        rw [lt_div_iff₀ hET_pos]
        by_cases hθ0 : θ ≤ 0
        · exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hθ0 hET_pos.le) hETL_pos
        · push Not at hθ0
          rw [max_eq_left hθ0.le] at hst_i
          exact (mul_le_mul_of_nonneg_left (hE_up (T i₀)) hθ0.le).trans_lt
            (lt_of_lt_of_le hst_i (hE_lo (T i₀ + L)))

/-! ## 5. Complete Resolution of the Physical Path-Dephasing Test on `PSL₂(ℤ)\ℍ` -/

/-- **Complete Unconditional Resolution of the Modular Cusp Path-Dephasing and Tail-Energy Question.**
Packages in a single theorem:
1. Strict eternal tail positivity (`0 < tailEnergy h T`) and four-phase polarization of `E_{g,h}(T)`;
2. Agmon–Sobolev local regularity (`‖r_h(T)‖^4 ≤ 4 E_h(T) E_{h'}(T)`) and causal horocycle zero-mode
   receiver readout;
3. Repeated-prime amplitude invariance (`φ(p^k)/p^k = 1 - 1/p`) and exact finite path-return step
   formula;
4. Unconditional falsification of every fixed-step contraction `E_h(T + L) / E_h(T) ≤ θ < 1` on the
   actual modular surface (both along logarithmic horizons and deep in the escaped tail across all
   relative phases `φ ∈ ℝ`), together with the surviving pulse-uniform Sobolev-cone escape law and
   its equivalence to the Riemann Hypothesis at `δ = 1/4`. -/
theorem complete_resolution_of_physical_dephasing_test :
    -- (1) Strict eternal tail positivity for every nonzero compact pulse
    (∀ (h : CompactPulse), (∃ S : ℝ, h S ≠ 0) → ∀ T : ℝ, 0 < tailEnergy h T) ∧
    -- (2) Four-phase polarization of the two-pulse cross-energy
    (∀ (g h : CompactPulse) (T : ℝ),
      tailCrossEnergy g h T =
        ((1 / 4 : ℝ) : ℂ) *
          (((tailEnergy (g.add h) T - tailEnergy (g.add (CompactPulse.smul (-1) h)) T : ℝ) : ℂ) +
            I * ((tailEnergy (g.add (CompactPulse.smul I h)) T -
              tailEnergy (g.add (CompactPulse.smul (-I) h)) T : ℝ) : ℂ))) ∧
    -- (3) Agmon–Sobolev local regularity & causal horocycle receiver readout
    (∀ (h : CompactPulse) (T : ℝ),
      ‖pulseReflected h T‖ ^ 4 ≤ 4 * tailEnergy h T * tailEnergy h.D T) ∧
    (∀ (h : CompactPulse) {S₀ : ℝ}, (∀ s : ℝ, S₀ < |s| → h s = 0) →
      ∀ (T : ℝ) {Y : ℝ}, 0 < Y → S₀ < T + 2 * Real.log Y →
        pulseReflected h T =
          ((Real.sqrt Y : ℝ) : ℂ)⁻¹ * ∫ x in Ioc (0 : ℝ) 1, pulseField h (T + Real.log Y) x Y) ∧
    -- (4) Repeated-prime path weight invariance
    (∀ {p k : ℕ}, p.Prime → 1 ≤ k →
      echoDelay (p ^ k) = 2 * (k : ℝ) * Real.log p ∧ echoWeight (p ^ k) = 1 - 1 / (p : ℝ)) ∧
    -- (5) Phase-uniform deep-tail falsification of every fixed-step contraction `θ < 1`
    (∀ {S₀ L η θ : ℝ}, 0 < S₀ → 0 < L → ∀ T₀ : ℝ, 0 < η → η < 1 → θ < 1 →
      ∃ (g w : CompactPulse) (T : ℝ),
        meanCoefficient g = 0 ∧ meanCoefficient w = 0 ∧
        (∀ s : ℝ, S₀ < |s| → g s = 0) ∧ (∀ s : ℝ, S₀ < |s| → w s = 0) ∧
        max T₀ 0 ≤ T ∧
        ∀ φ : ℝ,
          0 < tailEnergy (g.phaseMix φ w) T ∧
          tailEnergy (g.phaseMix φ w) T ≤ η * (∫ S : ℝ, ‖(g.phaseMix φ w) S‖ ^ 2) ∧
          θ < tailEnergy (g.phaseMix φ w) (T + L) / tailEnergy (g.phaseMix φ w) T) ∧
    -- (6) Unconditional sub-`3001/48000` Sobolev-cone escape & RH equivalence at `δ = 1/4`
    (∀ {σ S₀ : ℝ}, 0 < σ → σ < 3001 / 48000 → 0 < S₀ →
      ∃ (N : ℕ) (K : ℝ), 0 < K ∧ ∀ h : CompactPulse,
        (∀ s : ℝ, S₀ < |s| → h s = 0) → ∀ T : ℝ, 0 ≤ T →
          tailEnergy h T ≤
            K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) *
              Real.exp (-2 * σ * T)) ∧
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse,
        ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → tailEnergy h T ≤ C * Real.exp (-(1 / 2 - 2 * ε) * T)) :=
  ⟨tailEnergy_pos,
   tailCrossEnergy_eq_polarization,
   norm_pulseReflected_pow_four_le,
   fun h {_} hS₀ T {_} hY hclear => pulseReflected_eq_horocycle_receiver h hS₀ T hY hclear,
   fun {_ _} hp hk => echoDelay_and_weight_prime_pow hp hk,
   fun {_ _ _ _} hS₀ hL T₀ hη0 hη1 hθ =>
     exists_two_pulse_deep_tail_contraction_falsifier hS₀ hL T₀ hη0 hη1 hθ,
   fun {_ _} hσ0 hσ hS₀ => unconditional_sobolev_cone_tailEnergy_escape hσ0 hσ hS₀,
   riemannHypothesis_iff_tailEnergy_decay.1⟩

end GaloisForLFunctions.BlackHoleRingdown

end
