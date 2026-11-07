import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheBracketOfTheBestRate
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheSmoothMeanValueOfTheMultiplicity

/-!
# The half scale of the rate

The peak law `w ≤ 100 (1 + log K)² (K T + m)` replaces the sharp mean value in the two laws at a zero.

* **The floor.** One zero gives `ε x ≥ c₀`, and the peak law gives `x ≲ (1 + log K)² (K ε + 1)`. So every producer on
  an alphabet in `[1, K]` has `ε ≥ c₁ / (√K (1 + log K))`.
* **The reading.** With `ε ≤ K^{-a}` the law at a zero has exponent `(1 − a)(1 − β) − a β = 1 − β − a` in `K`. So a
  rate `K^{-a}` forces `Re ρ ≤ 1 − a`.
* **The end of the scale.** Rates `K^{-a}` for all `a < 1/2` give the Riemann hypothesis, and no rate with `a > 1/2`
  exists. The end of the scale and the bound `Θ ≥ ½` are the same statement.
* **Certificates.** A producer certifying `ζ(s) ≠ 0` at `s` has `‖s‖ ≲ √K (1 + log K)`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- **The peak ratio at alphabet size `K`.** -/
theorem IsProducer.peakRatio_le {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K)
    (hK1 : 1 ≤ K) :
    IsProducer.peakRatio c m ≤ 100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * rate c m B + 1) := by
  have hm := hP.m_pos
  have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 := hP.peak_le hK hK1
  have h2 := hP.excess_le
  rw [IsProducer.peakRatio, div_le_iff₀ hm]
  refine h1.trans ?_
  have h3 : (K : ℝ) * excess c m B ≤ (K : ℝ) * ((m : ℝ) * rate c m B) :=
    mul_le_mul_of_nonneg_left h2 hKR
  have hexp : 100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * rate c m B + 1) * (m : ℝ) =
      100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * ((m : ℝ) * rate c m B) + m) := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `1 + log K ≤ 2 √K`. -/
private lemma one_add_log_le_two_sqrt {K : ℝ} (hK : 1 ≤ K) : 1 + Real.log K ≤ 2 * √K := by
  have hK0 : 0 < K := by linarith
  have hs : 0 < √K := Real.sqrt_pos.mpr hK0
  have h1 : Real.log K = 2 * Real.log √K := by
    rw [Real.log_sqrt hK0.le]
    ring
  have h2 : Real.log √K ≤ √K - 1 := Real.log_le_sub_one_of_pos hs
  linarith

/-- The real core of the floor. -/
private lemma floor_core {ε x c₀ l K : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hK : 1 ≤ K) (hl0 : 0 ≤ l)
    (hl : 1 + l ≤ 2 * √K) (hε : 0 < ε) (h1 : c₀ ≤ ε * x)
    (h2 : x ≤ 100 * (1 + l) ^ 2 * (K * ε + 1)) :
    c₀ / 300 / (√K * (1 + l)) ≤ ε := by
  have hK0 : 0 < K := by linarith
  have hs : 0 < √K := Real.sqrt_pos.mpr hK0
  have hsq : √K * √K = K := Real.mul_self_sqrt hK0.le
  have hl1 : 0 < 1 + l := by linarith
  have hD : 0 < √K * (1 + l) := by positivity
  rw [div_le_iff₀ hD]
  by_contra hlt
  push Not at hlt
  set y := ε * (√K * (1 + l)) with hy
  have hy0 : 0 < y := by positivity
  have hc1 : c₀ / 300 ≤ 1 := by linarith
  have hy2 : y ^ 2 < c₀ / 300 := by nlinarith
  have hexp : ε * (100 * (1 + l) ^ 2 * (K * ε + 1)) = 100 * (y ^ 2 + y * ((1 + l) / √K)) := by
    have h3 : y ^ 2 = ε ^ 2 * K * (1 + l) ^ 2 := by
      have hsq2 : √K ^ 2 = K := Real.sq_sqrt hK0.le
      calc y ^ 2 = ε ^ 2 * √K ^ 2 * (1 + l) ^ 2 := by
            rw [hy]
            ring
        _ = _ := by rw [hsq2]
    have h4 : y * ((1 + l) / √K) = ε * (1 + l) ^ 2 := by
      rw [hy]
      field_simp
    rw [h3, h4]
    ring
  have hratio : (1 + l) / √K ≤ 2 := by
    rw [div_le_iff₀ hs]
    exact hl
  have hprod : y * ((1 + l) / √K) ≤ y * 2 := mul_le_mul_of_nonneg_left hratio hy0.le
  have h3 : c₀ ≤ ε * (100 * (1 + l) ^ 2 * (K * ε + 1)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hε.le)
  rw [hexp] at h3
  linarith

/-- **The half floor.** There is an absolute `c₁ > 0` such that every producer on an alphabet in `[1, K]` has rate at
least `c₁ / (√K (1 + log K))`. -/
theorem exists_half_floor :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B → AlphabetLE c K →
      c₁ / (√(K : ℝ) * (1 + Real.log K)) ≤ rate c m B := by
  obtain ⟨c₀, hc₀, hc₀1, hlaw⟩ := exists_uncertainty_constant
  refine ⟨c₀ / 300, by positivity, fun K c m B hK hP hal => ?_⟩
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hε := hP.rate_pos
  by_cases hr : rate c m B ≤ 1
  · exact floor_core hc₀ hc₀1 hKR hl0 (one_add_log_le_two_sqrt hKR) hε (hlaw c m B hP hr)
      (hP.peakRatio_le hal hK)
  · push Not at hr
    have hs : 1 ≤ √(K : ℝ) := Real.one_le_sqrt.mpr hKR
    have hD : 1 ≤ √(K : ℝ) * (1 + Real.log K) := by nlinarith
    have h1 : c₀ / 300 / (√(K : ℝ) * (1 + Real.log K)) ≤ c₀ / 300 :=
      div_le_self (by positivity) hD
    linarith

/-- `(1 + log x) x^{-δ} → 0`. -/
private lemma tendsto_one_add_log_mul_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (1 + Real.log x) * x ^ (-δ)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hδ
  have h2 := (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp

/-- **The end of the scale.** No rate `K^{-a}` with `a > 1/2` exists. -/
theorem not_hasRate_rpow_of_half_lt {a : ℝ} (ha : 1 / 2 < a) :
    ¬ HasRate fun K => (K : ℝ) ^ (-a) := by
  intro h
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
  have hδ : 0 < a - 1 / 2 := by linarith
  have hlim := (tendsto_one_add_log_mul_rpow hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK1, hKlt, c, m, B, hP, hal, hr⟩ :=
    ((eventually_ge_atTop 1).and ((hlim.eventually (gt_mem_nhds hc₁)).and h)).exists
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hf := (hfloor K c m B hK1 hP hal).trans hr
  have hl1 : 0 < 1 + Real.log (K : ℝ) := by
    have := Real.log_nonneg hKR
    linarith
  rw [div_le_iff₀ (by positivity)] at hf
  have hsplit : (K : ℝ) ^ (-a) * (√(K : ℝ) * (1 + Real.log K)) =
      (1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(a - 1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hK0]
    have : -a + 1 / 2 = -(a - 1 / 2) := by ring
    rw [this]
    ring
  rw [hsplit] at hf
  simp only [Function.comp] at hKlt
  linarith

/-- **The sharp reading.** A rate `K^{-a}` forces `Re ρ ≤ 1 − a` for every zero. -/
theorem re_le_of_hasRate_rpow_half {a : ℝ} (ha0 : 0 < a) (h : HasRate fun K => (K : ℝ) ^ (-a)) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) : ρ.re ≤ 1 - a := by
  by_cases ha : 1 / 2 < a
  · exact absurd h (not_hasRate_rpow_of_half_lt ha)
  push Not at ha
  by_contra hlt
  push Not at hlt
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re hgt.le hρ
  have hβ : 1 / 2 ≤ ρ.re := by linarith
  have hδ0 : 0 < ρ.re + a - 1 := by linarith
  obtain ⟨β, hβdef⟩ : ∃ β, β = ρ.re := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = β + a - 1 := ⟨_, rfl⟩
  rw [← hβdef] at hβ hβ1 hδ0
  have hδpos : 0 < δ := by rw [hδ]; exact hδ0
  have hlim := (((tendsto_one_add_log_mul_rpow (half_pos hδpos)).pow 2).const_mul
    (4800 * ‖ρ‖)).comp tendsto_natCast_atTop_atTop
  have hzero : (4800 * ‖ρ‖) * (0 : ℝ) ^ 2 = 0 := by simp
  rw [hzero] at hlim
  obtain ⟨K, hK1, hKlt, c, m, B, hP, hal, hr⟩ :=
    ((eventually_ge_atTop 1).and ((hlim.eventually (gt_mem_nhds zero_lt_one)).and h)).exists
  simp only [Function.comp] at hKlt
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hl0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hpow1 : (K : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hKR (by linarith)
  have hr1 : rate c m B ≤ 1 := hr.trans hpow1
  have hε := hP.rate_pos
  have hlaw := hP.zero_law hr1 hρ (by rw [← hβdef]; exact hβ) (by rw [← hβdef]; exact hβ1)
  rw [← hβdef] at hlaw
  -- The peak ratio at the rate `K^{-a}`.
  have hKa : (K : ℝ) * rate c m B ≤ (K : ℝ) ^ (1 - a) := by
    have hsplit : (K : ℝ) ^ (1 - a) = (K : ℝ) * (K : ℝ) ^ (-a) := by
      rw [sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hr hK0.le
  have hK1a : 1 ≤ (K : ℝ) ^ (1 - a) := Real.one_le_rpow hKR (by linarith)
  have hx : IsProducer.peakRatio c m ≤ 200 * (1 + Real.log K) ^ 2 * (K : ℝ) ^ (1 - a) := by
    refine (hP.peakRatio_le hal hK1).trans ?_
    have hsum : (K : ℝ) * rate c m B + 1 ≤ 2 * (K : ℝ) ^ (1 - a) := by linarith
    calc 100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * rate c m B + 1)
        ≤ 100 * (1 + Real.log K) ^ 2 * (2 * (K : ℝ) ^ (1 - a)) := by gcongr
      _ = _ := by ring
  have hx1 := hP.one_le_peakRatio
  have hexp : 0 ≤ 1 - β := by linarith
  have hL : 1 ≤ 200 * (1 + Real.log (K : ℝ)) ^ 2 := by nlinarith
  have hp1 : IsProducer.peakRatio c m ^ (1 - β) ≤
      200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ ((1 - a) * (1 - β)) := by
    calc IsProducer.peakRatio c m ^ (1 - β)
        ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (1 - a)) ^ (1 - β) :=
          Real.rpow_le_rpow (by linarith) hx hexp
      _ = (200 * (1 + Real.log (K : ℝ)) ^ 2) ^ (1 - β) * (K : ℝ) ^ ((1 - a) * (1 - β)) := by
          rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hK0.le]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc _ ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hL (by linarith)
            _ = _ := Real.rpow_one _
  have hβ0 : 0 ≤ β := by linarith
  have hp2 : rate c m B ^ β ≤ (K : ℝ) ^ (-(a * β)) := by
    calc rate c m B ^ β ≤ ((K : ℝ) ^ (-a)) ^ β := Real.rpow_le_rpow hε.le hr hβ0
      _ = _ := by
          rw [← Real.rpow_mul hK0.le]
          congr 1
          ring
  have hprod : IsProducer.peakRatio c m ^ (1 - β) * rate c m B ^ β ≤
      200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ) := by
    have hcomb : (K : ℝ) ^ ((1 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β)) = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hK0, hδ]
      congr 1
      ring
    calc _ ≤ (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ ((1 - a) * (1 - β))) * (K : ℝ) ^ (-(a * β)) :=
          mul_le_mul hp1 hp2 (by positivity) (by positivity)
      _ = 200 * (1 + Real.log (K : ℝ)) ^ 2 *
          ((K : ℝ) ^ ((1 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β))) := by ring
      _ = _ := by rw [hcomb]
  have hρ0 := norm_nonneg ρ
  have hfinal : 1 ≤ 24 * ‖ρ‖ * (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ)) :=
    hlaw.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hsq : ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(δ / 2))) ^ 2 =
      (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ) := by
    have h3 : ((K : ℝ) ^ (-(δ / 2))) ^ 2 = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, h3]
  have hid : 24 * ‖ρ‖ * (200 * (1 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (-δ)) =
      4800 * ‖ρ‖ * ((1 + Real.log (K : ℝ)) * (K : ℝ) ^ (-(δ / 2))) ^ 2 := by
    rw [hsq]
    ring
  rw [hid] at hfinal
  linarith

/-- **Rates up to the end of the scale give the Riemann hypothesis.** If rates `K^{-a}` exist for all `a < 1/2`, the
Riemann hypothesis holds. -/
theorem riemannHypothesis_of_hasRate_half
    (h : ∀ a : ℝ, 0 < a → a < 1 / 2 → HasRate fun K => (K : ℝ) ^ (-a)) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs hs1 hzero
  have hb := re_le_of_hasRate_rpow_half (a := ((1 - s.re) + 1 / 2) / 2) (by linarith)
    (h _ (by linarith) (by linarith)) hzero
  linarith

/-- **The necessary alphabet of a certificate.** A producer on an alphabet in `[1, K]` with `ε x < 1` has
`c x < √K (1 + log K)`. So certifying `ζ(1 + iτ) ≠ 0` needs an alphabet of size about `τ²`, up to logarithms. -/
theorem exists_necessary_alphabet_half :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (c' : ℕ →₀ ℤ) (m B : ℕ) (x : ℝ), 1 ≤ K → IsProducer c' m B →
      AlphabetLE c' K → 0 < x → rate c' m B * x < 1 → c * x < √(K : ℝ) * (1 + Real.log K) := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
  refine ⟨c₁, hc₁, fun K c' m B x hK hP hal hx hr => ?_⟩
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : 1 ≤ √(K : ℝ) := Real.one_le_sqrt.mpr hKR
  have hl0 := Real.log_nonneg hKR
  have hD : 0 < √(K : ℝ) * (1 + Real.log K) := by positivity
  have hf := hfloor K c' m B hK hP hal
  have h1 : c₁ / (√(K : ℝ) * (1 + Real.log K)) * x < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hf hx.le) hr
  rw [div_mul_eq_mul_div, div_lt_one hD] at h1
  exact h1

/-- **The bracket of the best rate.** For `0 < α < 3/5` and all large `K`,
`c₁ / (√K (1 + log K)) ≤ bestRate K ≤ exp(−(log K)^α)`. -/
theorem exists_half_bracket_bestRate {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ K : ℕ in atTop,
      c₁ / (√(K : ℝ) * (1 + Real.log K)) ≤ bestRate K ∧
        bestRate K ≤ Real.exp (-(Real.log (K : ℝ) ^ α)) := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [hasRate_vk hα0 hα, eventually_ge_atTop 1] with K hK hK1
  obtain ⟨c, m, B, hP, hKa, hr⟩ := hK
  have hmem : rate c m B ∈ rateSet K := ⟨c, m, B, hP, hKa, rfl⟩
  have hbdd : BddBelow (rateSet K) := by
    refine ⟨0, ?_⟩
    rintro ε ⟨c', m', B', hP', _, rfl⟩
    exact hP'.rate_pos.le
  refine ⟨le_csInf ⟨_, hmem⟩ ?_, (csInf_le hbdd hmem).trans hr⟩
  rintro ε ⟨c', m', B', hP', hKa', rfl⟩
  exact hfloor K c' m' B' hK1 hP' hKa'

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
