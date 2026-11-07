import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheVinogradovKorobovBoundOnTheOneLine
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturnIsAnExtremeValue

/-!
# The first return past the Vinogradov scale

A weak return of the primes up to `N` at height `t` is a spike `|ζ(1 + 1/log N + it)| ≍ log N`
(`log_norm_zeta_ge_of_isWeakReturn`). The Vinogradov–Korobov bound
`|ζ(σ + it)| ≪ (log t · log log t)^{2/3}` on `1 ≤ σ ≤ 2` (`exists_norm_riemannZeta_le_two_thirds`)
caps the spike, so

`log t ≥ c (log N)^{3/2} / log log N`

at every weak return (`eventually_log_ge_of_isWeakReturn`), and the first return at bounded
harmonic defect, `η log log N ≤ D`, satisfies `R(N, η) ≥ exp(c (log N)^{3/2}/log log N)`
(`eventually_exp_le_firstReturn`). This raises the lower bracket `exp(c(log N)^{1−η})` of
`firstReturn_lower`, which used only `|ζ(1 + it)| ≪ log t`, to the exponent `3/2 − o(1)`.
-/

open Filter Topology

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- From `aX ≤ L log L` with `log X ≤ (3/2)λ`: `L ≥ min(1, 2a/3) X/λ`. -/
private theorem le_of_le_mul_log {a X lam L : ℝ} (ha : 0 < a) (hX : 0 < X) (hlam : 1 ≤ lam)
    (hXlam : Real.log X ≤ 3 / 2 * lam) (hL : 1 ≤ L) (h : a * X ≤ L * Real.log L) :
    min 1 (2 / 3 * a) * X / lam ≤ L := by
  have hlam0 : 0 < lam := by linarith
  have hm0 : 0 ≤ min 1 (2 / 3 * a) := le_min zero_le_one (by positivity)
  rw [div_le_iff₀ hlam0]
  by_cases hXL : X ≤ L
  · have h1 : min 1 (2 / 3 * a) * X ≤ 1 * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX.le
    have h2 : L ≤ L * lam := le_mul_of_one_le_right (by linarith) hlam
    linarith
  · push Not at hXL
    have hlogL : Real.log L ≤ 3 / 2 * lam :=
      (Real.log_le_log (by linarith) hXL.le).trans hXlam
    have h1 : L * Real.log L ≤ L * (3 / 2 * lam) := mul_le_mul_of_nonneg_left hlogL (by linarith)
    have h2 : min 1 (2 / 3 * a) * X ≤ 2 / 3 * a * X :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hX.le
    nlinarith only [h, h1, h2]

/-- **A spike caps the height from below.** If `log |ζ(1 + 1/log N + it)| ≥ log log N − B`, then
`log t ≥ c (log N)^{3/2}/log log N`, for all large `N`. -/
theorem eventually_log_ge_of_spike (B : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      RHTower.Sieve.logLog N - B ≤ Real.log ‖riemannZeta (spikePoint N t)‖ →
        c * Real.log N ^ ((3 : ℝ) / 2) / RHTower.Sieve.logLog N ≤ Real.log t := by
  obtain ⟨M, -, hM⟩ := exists_norm_zeta_le_log
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_le_two_thirds
  set τ₁ := Real.exp (Real.exp 30) with hτ₁
  set M₁ := M + Real.log (τ₁ + 1) with hM₁
  set a := (Real.exp (-B) / C) ^ ((3 : ℝ) / 2) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos (div_pos (Real.exp_pos _) hC0) _
  refine ⟨min 1 (2 / 3 * a), lt_min one_pos (by positivity), ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3, hlog.eventually_ge_atTop 1,
    tendsto_logLog.eventually_ge_atTop 1, tendsto_logLog.eventually_gt_atTop B,
    hlog.eventually_gt_atTop (M₁ * Real.exp B)] with N hN3 hlogN hll hllB hbig t ht h
  have hlogN0 : 0 < Real.log N := by linarith
  have hz0 : 0 < ‖riemannZeta (spikePoint N t)‖ := by
    rcases (norm_nonneg (riemannZeta (spikePoint N t))).lt_or_eq with hz | hz
    · exact hz
    · rw [← hz, Real.log_zero] at h
      linarith
  have hlow : Real.exp (-B) * Real.log N ≤ ‖riemannZeta (spikePoint N t)‖ := by
    have h1 := Real.exp_le_exp.mpr h
    rw [Real.exp_log hz0, Real.exp_sub, RHTower.Sieve.logLog, Real.exp_log hlogN0] at h1
    rw [Real.exp_neg, ← div_eq_inv_mul]
    exact h1
  have hinv0 : 0 < 1 / Real.log N := by positivity
  have hinv1 : 1 / Real.log N ≤ 1 := by rw [div_le_one hlogN0]; exact hlogN
  rcases lt_or_ge t τ₁ with htτ | htτ
  · exfalso
    have hb := norm_zeta_spikePoint_le hM hN3 (t := t) (by rw [abs_of_nonneg (by linarith)]; exact ht)
    rw [abs_of_nonneg (by linarith)] at hb
    have hmono : Real.log (t + 1) ≤ Real.log (τ₁ + 1) := Real.log_le_log (by linarith) (by linarith)
    have hbig' : M₁ < Real.exp (-B) * Real.log N := by
      rw [Real.exp_neg, ← div_eq_inv_mul, lt_div_iff₀ (Real.exp_pos _)]
      exact hbig
    linarith
  · have hτ : Real.exp (Real.exp 30) ≤ |t| := by rw [abs_of_nonneg (by linarith)]; exact htτ
    have hb := hC t (1 + 1 / Real.log N) hτ (by linarith) (by linarith)
    rw [abs_of_nonneg (by linarith)] at hb
    have hspike : spikePoint N t = (((1 + 1 / Real.log (N : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      rfl
    rw [hspike] at hlow
    have hL : Real.exp 30 ≤ Real.log t := by
      rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) htτ
    have hL1 : 1 ≤ Real.log t := le_trans (Real.one_le_exp (by norm_num)) hL
    have hl := RHTower.Sieve.one_le_log_of_exp_thirty_le hL
    set u := Real.log t * Real.log (Real.log t) with hu
    have hu0 : 0 ≤ u := by positivity
    have h2 : Real.exp (-B) / C * Real.log N ≤ u ^ ((2 : ℝ) / 3) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hC0]
      linarith [hlow.trans hb]
    have h3 : a * Real.log N ^ ((3 : ℝ) / 2) ≤ u := by
      have hc0 : 0 ≤ Real.exp (-B) / C * Real.log N := by positivity
      have := Real.rpow_le_rpow hc0 h2 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      rwa [Real.mul_rpow (by positivity) hlogN0.le, ← Real.rpow_mul hu0,
        show (2 : ℝ) / 3 * (3 / 2) = 1 by norm_num, Real.rpow_one] at this
    refine le_of_le_mul_log ha0 (by positivity) hll ?_ hL1 h3
    rw [Real.log_rpow hlogN0, RHTower.Sieve.logLog]

/-- **Weak returns past the Vinogradov scale.** For every bound `C` on the harmonic defect, a weak
return of the primes up to `N` at height `t` has `log t ≥ c (log N)^{3/2}/log log N`. -/
theorem eventually_log_ge_of_isWeakReturn (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 1 ≤ t → IsWeakReturn N C t →
      c * Real.log N ^ ((3 : ℝ) / 2) / RHTower.Sieve.logLog N ≤ Real.log t := by
  obtain ⟨c, hc, h⟩ := eventually_log_ge_of_spike (C + harmonicConst)
  refine ⟨c, hc, ?_⟩
  filter_upwards [h, eventually_ge_atTop 3] with N hN hN3 t ht hw
  have := log_norm_zeta_ge_of_isWeakReturn hN3 hw
  exact hN t ht (by linarith)

/-- **The first return at bounded harmonic defect.** For every `D` there is `c > 0` with
`R(N, η) ≥ exp(c (log N)^{3/2}/log log N)` whenever `η log log N ≤ D`, for all large `N`. -/
theorem eventually_exp_le_firstReturn (D : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η * RHTower.Sieve.logLog N ≤ D →
      Real.exp (c * Real.log N ^ ((3 : ℝ) / 2) / RHTower.Sieve.logLog N) ≤
        firstReturn (Nat.primesLE N) logStep η := by
  set B := D + D * |RHTower.Sieve.mertensSecondUpperConst| + harmonicConst with hB
  obtain ⟨c, hc, h⟩ := eventually_log_ge_of_spike B
  refine ⟨c, hc, ?_⟩
  filter_upwards [h, eventually_ge_atTop 3, tendsto_logLog.eventually_ge_atTop 1] with
    N hN hN3 hll η hη hηD
  have hR := firstReturn_mem (Nat.primesLE N) logStep hη
  have hdict := log_norm_zeta_ge_of_isReturn hN3 hη.le hR.2
  have hηle : η ≤ D := by nlinarith only [hll, hηD, hη]
  have hc' : η * |RHTower.Sieve.mertensSecondUpperConst| ≤
      D * |RHTower.Sieve.mertensSecondUpperConst| :=
    mul_le_mul_of_nonneg_right hηle (abs_nonneg _)
  have hlogR := hN _ hR.1 (by nlinarith only [hdict, hηD, hc'])
  calc Real.exp (c * Real.log N ^ ((3 : ℝ) / 2) / RHTower.Sieve.logLog N)
      ≤ Real.exp (Real.log (firstReturn (Nat.primesLE N) logStep η)) := Real.exp_le_exp.mpr hlogR
    _ = firstReturn (Nat.primesLE N) logStep η := Real.exp_log (by linarith [hR.1])

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
