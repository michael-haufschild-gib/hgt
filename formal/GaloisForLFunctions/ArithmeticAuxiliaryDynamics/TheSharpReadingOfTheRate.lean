import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheThreeQuartersScaleOfTheRate

/-!
# The sharp reading of the rate

Insert the mean-value law into the law at a zero. A rate `ε ≤ K^{-a}` has peak ratio
`x ≲ (log K)^{1/2} K^{3/2 − a}`, so at a zero the exponent of `K` is
`(3/2 − a)(1 − β) − aβ = 3/2 − a − (3/2)β`, and therefore

`Re ρ ≤ 1 − 2a/3`.

This is the reading available from the sharp mean value. Any `a > 0` gives a zero-free strip, which is all that the
equivalence with zero-free strips uses. The smooth mean value improves the reading to `Re ρ ≤ 1 − a`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- `(3 + log x) x^{-δ} → 0`. -/
private lemma tendsto_three_add_log_mul_rpow {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => (3 + Real.log x) * x ^ (-δ)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_neg_atTop hδ
  have h2 := (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h3 := (h1.const_mul 3).add h2
  rw [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp

/-- **The peak ratio at a polynomial rate.** With `ε ≤ K^{-a}`, `0 < a ≤ 1`, we have
`x ≤ 17 (3 + log K) K^{3/2 − a}`. -/
private lemma peakRatio_le_of_rate {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B)
    (hK : AlphabetLE c K) (hK1 : 1 ≤ K) {a : ℝ} (ha1 : a ≤ 1)
    (hr : rate c m B ≤ (K : ℝ) ^ (-a)) :
    IsProducer.peakRatio c m ≤ 17 * (3 + Real.log K) * (K : ℝ) ^ ((3 : ℝ) / 2 - a) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hP32 : 1 ≤ (K : ℝ) ^ ((3 : ℝ) / 2 - a) := Real.one_le_rpow hKR (by linarith)
  have hL : 1 ≤ 3 + Real.log (K : ℝ) := by linarith
  by_cases hx4 : IsProducer.peakRatio c m < 4
  · have : 17 * 1 * 1 ≤ 17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ ((3 : ℝ) / 2 - a) := by
      gcongr
    linarith
  push Not at hx4
  have hmv := hP.peakRatio_sq_le hK hx4
  have hε := hP.rate_pos
  set ε := rate c m B with hεdef
  set f : ℝ := (K : ℝ) ^ (-a) with hf
  have hf0 : 0 < f := Real.rpow_pos_of_pos hK0 _
  -- Replace `ε` by `f`.
  have hQ : 1 + Real.log (K : ℝ) + ((K : ℝ) + 1) * ε ≤ (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (1 - a) := by
    have hsplit : (K : ℝ) ^ (1 - a) = (K : ℝ) * f := by
      rw [hf, sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_one]
    have hK1a : 1 ≤ (K : ℝ) ^ (1 - a) := Real.one_le_rpow hKR (by linarith)
    have h1 : ((K : ℝ) + 1) * ε ≤ ((K : ℝ) + 1) * f := by gcongr
    have h2 : ((K : ℝ) + 1) * f ≤ 2 * (K : ℝ) ^ (1 - a) := by
      rw [hsplit]; nlinarith
    nlinarith
  have hsq : IsProducer.peakRatio c m ^ 2 ≤
      (17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ ((3 : ℝ) / 2 - a)) ^ 2 := by
    have hpow : ((K : ℝ) ^ ((3 : ℝ) / 2 - a)) ^ 2 = (K : ℝ) ^ (3 - 2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    have hcomb : (K : ℝ) ^ (3 - 2 * a) = f * (K : ℝ) ^ (2 : ℝ) * (K : ℝ) ^ (1 - a) := by
      rw [hf, ← Real.rpow_add hK0, ← Real.rpow_add hK0]
      congr 1
      ring
    have hK2 : (K : ℝ) ^ (2 : ℝ) = (K : ℝ) ^ 2 := by
      rw [← Real.rpow_natCast]
      norm_num
    have hstep : 288 * ε * (K : ℝ) ^ 2 * (1 + Real.log K + ((K : ℝ) + 1) * ε) ≤
        288 * f * (K : ℝ) ^ 2 * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (1 - a)) := by
      have hQ0 : 0 ≤ 1 + Real.log (K : ℝ) + ((K : ℝ) + 1) * ε := by positivity
      gcongr
    calc IsProducer.peakRatio c m ^ 2 ≤ _ := hmv
      _ ≤ 288 * f * (K : ℝ) ^ 2 * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (1 - a)) := hstep
      _ = 288 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (3 - 2 * a) := by
          rw [hcomb, hK2]; ring
      _ ≤ 289 * (3 + Real.log (K : ℝ)) ^ 2 * (K : ℝ) ^ (3 - 2 * a) := by
          have hK3 : 0 ≤ (K : ℝ) ^ (3 - 2 * a) := by positivity
          have : 288 * (3 + Real.log (K : ℝ)) ≤ 289 * (3 + Real.log (K : ℝ)) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this hK3
      _ = _ := by
          rw [mul_pow, mul_pow, hpow]; ring
  have hbase : 0 ≤ 17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ ((3 : ℝ) / 2 - a) := by positivity
  exact (pow_le_pow_iff_left₀ (by linarith) hbase (by norm_num)).mp hsq

/-- **The sharp reading.** A rate `K^{-a}`, `0 < a ≤ 1`, forces `Re ρ ≤ 1 − 2a/3` for every zero. -/
theorem re_le_of_hasRate_rpow_sharp {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (h : HasRate fun K => (K : ℝ) ^ (-a)) {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - 2 * a / 3 := by
  by_cases ha34 : 3 / 4 < a
  · exact absurd h (not_hasRate_rpow_of_three_quarters_lt ha34)
  push Not at ha34
  by_contra hlt
  push Not at hlt
  have hβ1 : ρ.re ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact riemannZeta_ne_zero_of_one_le_re hgt.le hρ
  have hβ : 1 / 2 ≤ ρ.re := by linarith
  have hδ0 : 0 < (3 / 2) * ρ.re + a - 3 / 2 := by linarith
  set β := ρ.re with hβdef
  set δ : ℝ := (3 / 2) * β + a - 3 / 2 with hδ
  have hlimK : Tendsto (fun K : ℕ => 408 * ‖ρ‖ * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)))
      atTop (𝓝 0) := by
    have := ((tendsto_three_add_log_mul_rpow hδ0).comp tendsto_natCast_atTop_atTop).const_mul
      (408 * ‖ρ‖)
    simpa using this
  have hev := hlimK.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨K, hK1, hKlt, c, m, B, hP, hKa, hr⟩ := ((eventually_ge_atTop 1).and (hev.and h)).exists
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
  have hpow1 : (K : ℝ) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hKR (by linarith)
  have hr1 : rate c m B ≤ 1 := hr.trans hpow1
  have hε := hP.rate_pos
  have hlaw := hP.zero_law hr1 hρ hβ hβ1
  rw [← hβdef] at hlaw
  have hx := peakRatio_le_of_rate hP hKa hK1 ha1 hr
  have hx1 := hP.one_le_peakRatio
  have hexp : 0 ≤ 1 - β := by linarith
  have hL : 1 ≤ 17 * (3 + Real.log (K : ℝ)) := by linarith
  have hp1 : IsProducer.peakRatio c m ^ (1 - β) ≤
      17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (((3 : ℝ) / 2 - a) * (1 - β)) := by
    calc IsProducer.peakRatio c m ^ (1 - β)
        ≤ (17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ ((3 : ℝ) / 2 - a)) ^ (1 - β) :=
          Real.rpow_le_rpow (by linarith) hx hexp
      _ = (17 * (3 + Real.log (K : ℝ))) ^ (1 - β) * (K : ℝ) ^ (((3 : ℝ) / 2 - a) * (1 - β)) := by
          rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hK0.le]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc _ ≤ (17 * (3 + Real.log (K : ℝ))) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hL (by linarith)
            _ = _ := Real.rpow_one _
  have hp2 : rate c m B ^ β ≤ (K : ℝ) ^ (-(a * β)) := by
    calc rate c m B ^ β ≤ ((K : ℝ) ^ (-a)) ^ β := Real.rpow_le_rpow hε.le hr (by linarith)
      _ = _ := by
          rw [← Real.rpow_mul hK0.le]
          congr 1
          ring
  have hprod : IsProducer.peakRatio c m ^ (1 - β) * rate c m B ^ β ≤
      17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ) := by
    have hcomb : (K : ℝ) ^ (((3 : ℝ) / 2 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β)) = (K : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hK0, hδ]
      congr 1
      ring
    calc _ ≤ (17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (((3 : ℝ) / 2 - a) * (1 - β))) *
          (K : ℝ) ^ (-(a * β)) := mul_le_mul hp1 hp2 (by positivity) (by positivity)
      _ = 17 * (3 + Real.log (K : ℝ)) *
          ((K : ℝ) ^ (((3 : ℝ) / 2 - a) * (1 - β)) * (K : ℝ) ^ (-(a * β))) := by ring
      _ = _ := by rw [hcomb]
  have hρ0 := norm_nonneg ρ
  have hfinal : 1 ≤ 24 * ‖ρ‖ * (17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)) :=
    hlaw.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hid : 24 * ‖ρ‖ * (17 * (3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)) =
      408 * ‖ρ‖ * ((3 + Real.log (K : ℝ)) * (K : ℝ) ^ (-δ)) := by ring
  rw [hid] at hfinal
  linarith

/-- **Rates up to the floor give the Riemann hypothesis.** If rates `K^{-a}` exist for all
`a < 3/4`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_hasRate_sharp
    (h : ∀ a : ℝ, 0 < a → a < 3 / 4 → HasRate fun K => (K : ℝ) ^ (-a)) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs hs1 hzero
  have hb := re_le_of_hasRate_rpow_sharp (a := (3 / 2 * (1 - s.re) + 3 / 4) / 2) (by linarith)
    (by linarith) (h _ (by linarith) (by linarith)) hzero
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
