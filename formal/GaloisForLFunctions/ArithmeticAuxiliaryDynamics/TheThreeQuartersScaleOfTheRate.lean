import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMeanValueOfTheMultiplicity
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheRateReadsTheZeroWidth
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The three-quarters scale of the rate

Three laws bound a producer with rate `ε`, peak ratio `x = w/m`, on an alphabet in `[1, K]`:

* **uncertainty** (one zero of `ζ`): `ε x ≥ c₀`;
* **mean value:** `x² ≤ 144 ε E/m` when `x ≥ 4`;
* **coefficient mass:** `E/m ≤ 2K² (1 + log K + (K + 1) ε)`.

Together they give the floor `ε ≥ c₁ K^{-3/4}`. The law at a zero and the uncertainty constant proved here are the
inputs of every floor. The loss to `3/4` is in the sharp mean value, whose error is the first moment `E`: smoothing removes
it, and the true end of the scale is `1/2`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- The peak ratio `x = w/m`. -/
def peakRatio (c : ℕ →₀ ℤ) (m : ℕ) : ℝ := (peak c : ℝ) / m

theorem one_le_peakRatio (hP : IsProducer c m B) : 1 ≤ peakRatio c m := by
  have h : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
  rw [peakRatio, one_le_div hP.m_pos]
  exact h

/-- **The law at a zero, in the peak ratio.** For `½ ≤ β ≤ 1` and `ε ≤ 1`,
`1 ≤ 24 ‖ρ‖ x^{1−β} ε^β`. -/
theorem zero_law (hP : IsProducer c m B) (hr : rate c m B ≤ 1) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hβ : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) :
    1 ≤ 24 * ‖ρ‖ * (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re) := by
  have hβ0 : 0 < ρ.re := by linarith
  have hε := hP.rate_pos
  have hm := hP.m_pos
  have hT0 := hP.excess_pos
  have hTle := hP.excess_le
  have hw0 := hP.peak_pos
  have hwm : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
  have hTw : excess c m B ≤ peak c := by nlinarith
  have hlaw := hP.uncertainty_law hρ hβ0 hβ1 hTw
  have hwin := hP.quarter_le_norm_window (ρ := ρ) hβ
  have hx := hP.one_le_peakRatio
  have hwx : (peak c : ℝ) = (m : ℝ) * peakRatio c m := by
    rw [peakRatio]; field_simp
  have hexp : 0 ≤ 1 - ρ.re := by linarith
  have hpow2 : excess c m B ^ ρ.re ≤ ((m : ℝ) * rate c m B) ^ ρ.re :=
    Real.rpow_le_rpow hT0.le hTle hβ0.le
  have hsplit : (peak c : ℝ) ^ (1 - ρ.re) * ((m : ℝ) * rate c m B) ^ ρ.re =
      (m : ℝ) * (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re) := by
    rw [hwx, Real.mul_rpow hm.le (by linarith), Real.mul_rpow hm.le hε.le]
    have hmm : (m : ℝ) ^ (1 - ρ.re) * (m : ℝ) ^ ρ.re = m := by
      rw [← Real.rpow_add hm, show 1 - ρ.re + ρ.re = 1 by ring, Real.rpow_one]
    calc _ = ((m : ℝ) ^ (1 - ρ.re) * (m : ℝ) ^ ρ.re) *
          (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re) := by ring
      _ = _ := by rw [hmm]
  have hmass : (peak c : ℝ) ^ (1 - ρ.re) * excess c m B ^ ρ.re ≤
      (m : ℝ) * (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
  have hconst : 4 + 1 / ρ.re ≤ 6 := by
    have : 1 / ρ.re ≤ 2 := by
      rw [div_le_iff₀ hβ0]; linarith
    linarith
  have hprod : 0 ≤ peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re := by positivity
  have hρ0 := norm_nonneg ρ
  have hupper : (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ ≤
      ‖ρ‖ * (6 * ((m : ℝ) * (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re))) := by
    refine hlaw.trans (mul_le_mul_of_nonneg_left ?_ hρ0)
    exact mul_le_mul hconst hmass (by positivity) (by norm_num)
  have hlower : (m : ℝ) * (1 / 4) ≤ (m : ℝ) * ‖1 - ((B : ℝ) : ℂ) ^ (-ρ)‖ :=
    mul_le_mul_of_nonneg_left hwin hm.le
  have hcancel : (m : ℝ) * 1 ≤ (m : ℝ) * (24 * ‖ρ‖ * (peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re)) := by
    nlinarith
  exact le_of_mul_le_mul_left hcancel hm

/-- From the law to the product: `x^{1−β} ε^β ≤ √(x ε)` for `x ≥ 1`, `ε ≤ 1`, `β ≥ ½`. So one zero of
modulus `‖ρ‖` gives `x ε ≥ (24 ‖ρ‖)^{-2}`. -/
theorem le_rate_mul_peakRatio (hP : IsProducer c m B) (hr : rate c m B ≤ 1) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hβ : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) :
    1 / (24 * ‖ρ‖) ^ 2 ≤ rate c m B * peakRatio c m := by
  have hlaw := hP.zero_law hr hρ hβ hβ1
  have hε := hP.rate_pos
  have hx := hP.one_le_peakRatio
  have hρpos : 0 < ‖ρ‖ := by
    by_contra hneg
    have : ‖ρ‖ = 0 := le_antisymm (not_lt.mp hneg) (norm_nonneg _)
    rw [this] at hlaw
    norm_num at hlaw
  have h1 : peakRatio c m ^ (1 - ρ.re) ≤ peakRatio c m ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h2 : rate c m B ^ ρ.re ≤ rate c m B ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hr hβ
  have hprod : peakRatio c m ^ (1 - ρ.re) * rate c m B ^ ρ.re ≤
      (peakRatio c m * rate c m B) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by linarith) hε.le]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hC : 0 < 24 * ‖ρ‖ := by positivity
  have hle : 1 ≤ 24 * ‖ρ‖ * (peakRatio c m * rate c m B) ^ (1 / 2 : ℝ) :=
    hlaw.trans (mul_le_mul_of_nonneg_left hprod hC.le)
  have hsq : (peakRatio c m * rate c m B) ^ (1 / 2 : ℝ) = √(peakRatio c m * rate c m B) :=
    (Real.sqrt_eq_rpow _).symm
  rw [hsq] at hle
  have hprodpos : 0 ≤ peakRatio c m * rate c m B := by positivity
  have hsquared : 1 ≤ (24 * ‖ρ‖) ^ 2 * (peakRatio c m * rate c m B) := by
    have h3 := Real.sq_sqrt hprodpos
    have h4 : (1 : ℝ) ^ 2 ≤ (24 * ‖ρ‖ * √(peakRatio c m * rate c m B)) ^ 2 :=
      pow_le_pow_left₀ zero_le_one hle 2
    rw [mul_pow, h3] at h4
    linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The peak ratio is bounded by the mean-value law.** If `x ≥ 4`, then
`x² ≤ 288 ε K² (1 + log K + (K + 1) ε)`. -/
theorem peakRatio_sq_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K)
    (hx : 4 ≤ peakRatio c m) :
    peakRatio c m ^ 2 ≤
      288 * rate c m B * (K : ℝ) ^ 2 * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B) := by
  have hm := hP.m_pos
  have hε := hP.rate_pos
  have hw4 : 4 * (m : ℝ) ≤ peak c := by
    rw [peakRatio, le_div_iff₀ hm] at hx
    linarith
  have h1 := hP.peak_sq_le hw4
  have h2 := hP.firstMoment_le_mul hK
  have h3 := hP.coeffMass_div_le hK
  rw [div_le_iff₀ hm] at h3
  have hT := hP.excess_le
  have hT0 := hP.excess_pos
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hE0 : 0 ≤ firstMoment c := by
    have := peak_le_coeffMass c
    have := hP.coeffMass_le_firstMoment
    have := hP.peak_pos
    linarith
  set Q : ℝ := 1 + Real.log K + ((K : ℝ) + 1) * rate c m B with hQ
  have hE : firstMoment c ≤ (K : ℝ) * (2 * (K : ℝ) * Q * m) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 hK0)
  have hprod : excess c m B * firstMoment c ≤
      ((m : ℝ) * rate c m B) * ((K : ℝ) * (2 * (K : ℝ) * Q * m)) :=
    mul_le_mul hT hE hE0 (by positivity)
  have hmain : (peak c : ℝ) ^ 2 ≤ 288 * rate c m B * (K : ℝ) ^ 2 * Q * (m : ℝ) ^ 2 := by
    calc (peak c : ℝ) ^ 2 ≤ 144 * (excess c m B * firstMoment c) := by linarith
      _ ≤ 144 * (((m : ℝ) * rate c m B) * ((K : ℝ) * (2 * (K : ℝ) * Q * m))) := by gcongr
      _ = _ := by ring
  rw [peakRatio, div_pow, div_le_iff₀ (by positivity)]
  exact hmain

end IsProducer

/-- The first zero: a zero of `ζ` in `[½, 1)`. -/
private lemma exists_zero_re_ge_half :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  obtain ⟨ρ, h0, h1, hz⟩ := RHTower.exists_riemannZeta_zero_mem_openStrip
  by_cases h : 1 / 2 ≤ ρ.re
  · exact ⟨ρ, hz, h, h1.le⟩
  · refine ⟨1 - ρ, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hz h0 h1, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith

/-- **The uncertainty principle of producers.** There is an absolute `c₀ ∈ (0, 1]` with
`c₀ ≤ ε · (w/m)` for every producer of rate at most `1`. -/
theorem exists_uncertainty_constant :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∀ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B → rate c m B ≤ 1 →
      c₀ ≤ rate c m B * IsProducer.peakRatio c m := by
  obtain ⟨ρ, hρ, hβ, hβ1⟩ := exists_zero_re_ge_half
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp at hβ
    linarith
  have hnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  refine ⟨min 1 (1 / (24 * ‖ρ‖) ^ 2), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro c m B hP hr
  exact (min_le_right _ _).trans (hP.le_rate_mul_peakRatio hr hρ hβ hβ1)

/-- The real core of the floor: with `K = R⁴`, the laws force `c₀² ≤ 2016 c₁` once `ε R³ ≤ c₁ ≤ 1`. -/
private lemma floor_core {R ε x L c₀ c₁ : ℝ} (hR : 1 ≤ R) (hL : 1 + L ≤ 5 * R) (hL0 : 0 ≤ L)
    (hε : 0 < ε) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hεR : ε * R ^ 3 ≤ c₁) (hc₀ : 0 ≤ c₀)
    (hU : c₀ ≤ ε * x) (hmv : x ^ 2 ≤ 288 * ε * R ^ 8 * (1 + L + (R ^ 4 + 1) * ε)) :
    c₀ ^ 2 ≤ 2016 * c₁ := by
  have hR0 : 0 < R := by linarith
  have hεR0 : 0 ≤ ε * R ^ 3 := by positivity
  have hc₀sq : c₀ ^ 2 ≤ ε ^ 2 * x ^ 2 := by
    have := pow_le_pow_left₀ hc₀ hU 2
    rwa [mul_pow] at this
  have hR4 : R ^ 4 + 1 ≤ 2 * R ^ 4 := by
    have : 1 ≤ R ^ 4 := one_le_pow₀ hR
    linarith
  have h3 : (ε * R ^ 3) ^ 3 ≤ c₁ ^ 3 := pow_le_pow_left₀ hεR0 hεR 3
  have h4 : (ε * R ^ 3) ^ 4 ≤ c₁ ^ 4 := pow_le_pow_left₀ hεR0 hεR 4
  have hterm1 : ε ^ 3 * R ^ 8 * (1 + L) ≤ 5 * c₁ ^ 3 := by
    calc ε ^ 3 * R ^ 8 * (1 + L) ≤ ε ^ 3 * R ^ 8 * (5 * R) := by gcongr
      _ = 5 * (ε * R ^ 3) ^ 3 := by ring
      _ ≤ 5 * c₁ ^ 3 := by gcongr
  have hterm2 : ε ^ 4 * R ^ 8 * (R ^ 4 + 1) ≤ 2 * c₁ ^ 4 := by
    calc ε ^ 4 * R ^ 8 * (R ^ 4 + 1) ≤ ε ^ 4 * R ^ 8 * (2 * R ^ 4) := by gcongr
      _ = 2 * (ε * R ^ 3) ^ 4 := by ring
      _ ≤ 2 * c₁ ^ 4 := by gcongr
  have hexp : ε ^ 2 * x ^ 2 ≤ 288 * (ε ^ 3 * R ^ 8 * (1 + L)) + 288 * (ε ^ 4 * R ^ 8 * (R ^ 4 + 1)) := by
    calc ε ^ 2 * x ^ 2 ≤ ε ^ 2 * (288 * ε * R ^ 8 * (1 + L + (R ^ 4 + 1) * ε)) := by gcongr
      _ = _ := by ring
  have hc3 : c₁ ^ 3 ≤ c₁ := by
    calc c₁ ^ 3 ≤ c₁ ^ 1 := pow_le_pow_of_le_one hc₁0.le hc₁1 (by norm_num)
      _ = c₁ := pow_one c₁
  have hc4 : c₁ ^ 4 ≤ c₁ := by
    calc c₁ ^ 4 ≤ c₁ ^ 1 := pow_le_pow_of_le_one hc₁0.le hc₁1 (by norm_num)
      _ = c₁ := pow_one c₁
  linarith

/-- **The three-quarters floor.** There is an absolute `c₁ > 0` such that every producer on an
alphabet in `[1, K]` has rate at least `c₁ K^{-3/4}`. -/
theorem exists_three_quarters_floor :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B →
      AlphabetLE c K → c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ rate c m B := by
  obtain ⟨c₀, hc₀, hc₀1, hU⟩ := exists_uncertainty_constant
  have hc₁0 : 0 < c₀ ^ 2 / 4032 := by positivity
  have hc₁1 : c₀ ^ 2 / 4032 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    nlinarith
  refine ⟨c₀ ^ 2 / 4032, hc₁0, fun K c m B hK1 hP hK => ?_⟩
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hP0 : 0 < (K : ℝ) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hK0 _
  have hP1 : (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hKR (by norm_num)
  by_contra hlt
  push Not at hlt
  have hε := hP.rate_pos
  have hprod1 : c₀ ^ 2 / 4032 * (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ 1 := by nlinarith
  have hε1 : rate c m B ≤ 1 := by linarith
  have hUc := hU c m B hP hε1
  by_cases hx4 : IsProducer.peakRatio c m < 4
  · -- A small peak: the uncertainty principle alone gives a constant floor.
    have h1 : c₀ ≤ 4 * rate c m B := by nlinarith
    have h2 : c₀ ^ 2 / 4032 ≤ c₀ / 4 := by nlinarith
    nlinarith
  push Not at hx4
  have hmv := hP.peakRatio_sq_le hK hx4
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  obtain ⟨R, hRdef⟩ : ∃ R, R = (K : ℝ) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := hRdef ▸ Real.one_le_rpow hKR (by norm_num)
  have hR4 : R ^ 4 = K := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    norm_num
  have hPR : (K : ℝ) ^ (-(3 / 4) : ℝ) * R ^ 3 = 1 := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
    norm_num
  have hlogR : 1 + Real.log (K : ℝ) ≤ 5 * R := by
    have h := Real.log_le_rpow_div hK0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    have h' : Real.log (K : ℝ) ≤ 4 * R := by
      rw [hRdef]
      calc Real.log (K : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) := h
        _ = 4 * (K : ℝ) ^ (1 / 4 : ℝ) := by ring
    linarith
  have hεR : rate c m B * R ^ 3 ≤ c₀ ^ 2 / 4032 := by
    have h := mul_le_mul_of_nonneg_right hlt.le (by positivity : 0 ≤ R ^ 3)
    calc rate c m B * R ^ 3 ≤ c₀ ^ 2 / 4032 * (K : ℝ) ^ (-(3 / 4) : ℝ) * R ^ 3 := h
      _ = c₀ ^ 2 / 4032 * ((K : ℝ) ^ (-(3 / 4) : ℝ) * R ^ 3) := by ring
      _ = c₀ ^ 2 / 4032 := by rw [hPR, mul_one]
  have hmv' : IsProducer.peakRatio c m ^ 2 ≤ 288 * rate c m B * R ^ 8 *
      (1 + Real.log (K : ℝ) + (R ^ 4 + 1) * rate c m B) := by
    have hK2 : (K : ℝ) ^ 2 = R ^ 8 := by rw [← hR4]; ring
    rw [← hK2, hR4]
    exact hmv
  have hfinal := floor_core hR1 hlogR hlogK hε hc₁0 hc₁1 hεR hc₀.le hUc hmv'
  have hlin : c₀ ^ 2 ≤ c₀ ^ 2 / 2 := by linarith
  nlinarith [pow_pos hc₀ 2]

/-- A rate faster than `K^{-3/4}` does not exist. -/
theorem not_hasRate_rpow_of_three_quarters_lt {a : ℝ} (ha : 3 / 4 < a) :
    ¬ HasRate fun K => (K : ℝ) ^ (-a) := by
  intro h
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_three_quarters_floor
  have hδ : 0 < a - 3 / 4 := by linarith
  have hlim : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(a - 3 / 4))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hev := hlim.eventually (gt_mem_nhds hc₁)
  obtain ⟨K, hK1, hKlt, c, m, B, hP, hKa, hr⟩ := ((eventually_ge_atTop 1).and (hev.and h)).exists
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hfl := hfloor K c m B hK1 hP hKa
  have hsplit : (K : ℝ) ^ (-a) = (K : ℝ) ^ (-(a - 3 / 4)) * (K : ℝ) ^ (-(3 / 4) : ℝ) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  have hP0 : 0 < (K : ℝ) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hK0 _
  have : c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ (K : ℝ) ^ (-(a - 3 / 4)) * (K : ℝ) ^ (-(3 / 4) : ℝ) := by
    rw [← hsplit]
    exact hfl.trans hr
  have := le_of_mul_le_mul_right this hP0
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
