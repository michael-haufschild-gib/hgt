import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCondensedCentralLimit
import GaloisForLFunctions.HTGeometry.PrimeLogSquareRpowSum

/-!
# The variance asymptotic in the condensed chamber

For `1/2 < σ < 1` the variance of `S_P = ∑_{p ≤ P} ξ_p` satisfies

`s_P² = (1 + o(1)) σ² ∑_{p ≤ P} p^{-σ} log² p = (1 + o(1)) σ²/(1-σ) · P^{1-σ} log P`.

Per prime, `Var ξ_p = σ² log² p · ∑ (r+1) q_p^{(j+1)(r+1)}` differs from `σ² log² p · q_p` by at
most
`192 σ² log² p · p^{-2σ}`, which is summable over all primes because `2σ > 1`; the prime sum
`∑_{p ≤ P} p^{-σ} log² p` itself grows like `P^{1-σ} log P/(1-σ)` by Abel summation against
Chebyshev's `θ`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `A(P) = ∑_{p ≤ P} p^{-σ} log² p`. -/
def primeCutoffLogSqSum (σ : ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff P, ((p : ℕ) : ℝ) ^ (-σ) * Real.log ((p : ℕ) : ℝ) ^ 2

theorem primeCutoffLogSqSum_eq (σ : ℝ) (P : ℕ) :
    primeCutoffLogSqSum σ P = primeLogSqRpowSum (1 - σ) (P : ℝ) := by
  rw [primeCutoffLogSqSum, primeLogSqRpowSum, Nat.floor_natCast,
    sum_primeCutoff P (fun n => (n : ℝ) ^ (-σ) * Real.log (n : ℝ) ^ 2)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show 1 - σ - 1 = -σ by ring]

/-- **`A(P) ~ P^{1-σ} log P/(1-σ)`** for `0 < σ < 1`. -/
theorem tendsto_primeCutoffLogSqSum {σ : ℝ} (hσ1 : σ < 1) :
    Tendsto (fun P : ℕ => primeCutoffLogSqSum σ P * (1 - σ)
      / ((P : ℝ) ^ (1 - σ) * Real.log (P : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_primeLogSqRpowSum (a := 1 - σ) (by linarith)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun P => ?_
  simp only [Function.comp_apply, primeCutoffLogSqSum_eq]

theorem summable_log_sq_mul_rpow_primes {σ : ℝ} (hhalf : 1 / 2 < σ) :
    Summable fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
  set ε : ℝ := (2 * σ - 1) / 4 with hε
  have hε0 : 0 < ε := by linarith
  have hnat : Summable fun n : ℕ => (1 / ε ^ 2) * ((n : ℝ) ^ (σ + 1 / 2))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  have hprime := hnat.comp_injective Nat.Primes.coe_nat_injective
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hprime
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hlog0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have hlog := Real.log_le_rpow_div hp.le hε0
  have hsq : Real.log ((p : ℕ) : ℝ) ^ 2 ≤ (((p : ℕ) : ℝ) ^ ε / ε) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hpow : (((p : ℕ) : ℝ) ^ ε / ε) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ))
      = (1 / ε ^ 2) * ((((p : ℕ) : ℝ) ^ (σ + 1 / 2))⁻¹) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_neg hp.le]
    field_simp
    rw [← Real.rpow_add hp]
    congr 1
    rw [hε]
    push_cast
    ring
  simp only [Function.comp_apply]
  rw [← hpow]
  exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hp.le _)

/-- The per-prime excess `Var ξ_p - σ² log² p · p^{-σ}`, bounded by `192 σ² log² p · p^{-2σ}`. -/
theorem lawVariance_sub_le {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (p : Nat.Primes) :
    0 ≤ (primeNome hσ p).lawVariance
        - σ ^ 2 * (((p : ℕ) : ℝ) ^ (-σ) * Real.log ((p : ℕ) : ℝ) ^ 2) ∧
      (primeNome hσ p).lawVariance
        - σ ^ 2 * (((p : ℕ) : ℝ) ^ (-σ) * Real.log ((p : ℕ) : ℝ) ^ 2)
        ≤ 192 * σ ^ 2 * (Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ))) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  set q := primeNome hσ p
  have hq := primeNome_lt_three_quarters hσ hhalf p
  have hlq : Real.log q.val ^ 2 = σ ^ 2 * Real.log ((p : ℕ) : ℝ) ^ 2 := by
    rw [← sq_abs, abs_log_primeNome]
    ring
  have hqv : q.val = ((p : ℕ) : ℝ) ^ (-σ) := primeNome_val hσ p
  have hlow := q.le_varSeries
  have hup := q.varSeries_sub_le
  have hq0 := q.pos
  have hq1 : 1 / 4 < 1 - q.val := by linarith
  have h3 : (1 / 4 : ℝ) ^ 3 ≤ (1 - q.val) ^ 3 := pow_le_pow_left₀ (by norm_num) hq1.le 3
  have hfrac : 3 * q.val ^ 2 / (1 - q.val) ^ 3 ≤ 192 * q.val ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg q.val]
  have hsq : q.val ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    rw [hqv, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    push_cast
    ring
  have hL : 0 ≤ Real.log ((p : ℕ) : ℝ) ^ 2 := sq_nonneg _
  rw [RealEulerNome.lawVariance, hlq, ← hqv]
  constructor
  · have : 0 ≤ q.varSeries - q.val := by linarith
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg σ) hL) this]
  · have hdiff : q.varSeries - q.val ≤ 192 * q.val ^ 2 := le_trans hup hfrac
    have := mul_le_mul_of_nonneg_left hdiff (mul_nonneg (sq_nonneg σ) hL)
    rw [← hsq]
    nlinarith [this]

/-- **(GAS3.4), first form.**  `s_P² / (σ² ∑_{p ≤ P} p^{-σ} log² p) → 1`. -/
theorem tendsto_condensedSocleVariance_div_logSqSum {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ)
    (hσ1 : σ < 1) :
    Tendsto (fun P : ℕ => condensedSocleVariance hσ P / (σ ^ 2 * primeCutoffLogSqSum σ P))
      atTop (𝓝 1) := by
  set B : ℝ := 192 * σ ^ 2 * ∑' p : Nat.Primes,
    Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ)) with hBdef
  have hsum := summable_log_sq_mul_rpow_primes hhalf
  have hdiff : ∀ P : ℕ, 0 ≤ condensedSocleVariance hσ P - σ ^ 2 * primeCutoffLogSqSum σ P ∧
      condensedSocleVariance hσ P - σ ^ 2 * primeCutoffLogSqSum σ P ≤ B := by
    intro P
    have heq : condensedSocleVariance hσ P - σ ^ 2 * primeCutoffLogSqSum σ P
        = ∑ p ∈ primeCutoff P, ((primeNome hσ p).lawVariance
          - σ ^ 2 * (((p : ℕ) : ℝ) ^ (-σ) * Real.log ((p : ℕ) : ℝ) ^ 2)) := by
      rw [condensedSocleVariance, primeCutoffLogSqSum, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [heq]
    refine ⟨Finset.sum_nonneg fun p _ => (lawVariance_sub_le hσ hhalf p).1, ?_⟩
    calc _ ≤ ∑ p ∈ primeCutoff P,
          192 * σ ^ 2 * (Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ))) :=
          Finset.sum_le_sum fun p _ => (lawVariance_sub_le hσ hhalf p).2
      _ = 192 * σ ^ 2 * ∑ p ∈ primeCutoff P,
          Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by rw [Finset.mul_sum]
      _ ≤ B := by
          rw [hBdef]
          gcongr
          exact hsum.sum_le_tsum _ fun p _ => by positivity
  have hA : Tendsto (fun P : ℕ => σ ^ 2 * primeCutoffLogSqSum σ P) atTop atTop := by
    refine tendsto_atTop_mono (fun P => ?_)
      (tendsto_atTop_add_const_right _ (-B) (tendsto_condensedSocleVariance_atTop hσ hσ1))
    linarith [(hdiff P).2]
  have hB : Tendsto (fun P : ℕ => (condensedSocleVariance hσ P
      - σ ^ 2 * primeCutoffLogSqSum σ P) / (σ ^ 2 * primeCutoffLogSqSum σ P)) atTop (𝓝 0) := by
    have hinv := hA.inv_tendsto_atTop
    have hmaj : Tendsto (fun P : ℕ => B * (σ ^ 2 * primeCutoffLogSqSum σ P)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul B
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [hA.eventually_gt_atTop 0] with P hP
      exact div_nonneg (hdiff P).1 hP.le
    · filter_upwards [hA.eventually_gt_atTop 0] with P hP
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hdiff P).2 (inv_nonneg.mpr hP.le)
  have h := hB.const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hA.eventually_gt_atTop 0] with P hP
  rw [one_add_div hP.ne']
  ring

/-- **(GAS3.4).**  `s_P² = (1 + o(1)) σ²/(1-σ) · P^{1-σ} log P` for `1/2 < σ < 1`. -/
theorem tendsto_condensedSocleVariance_asymptotic {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ)
    (hσ1 : σ < 1) :
    Tendsto (fun P : ℕ => condensedSocleVariance hσ P
      / (σ ^ 2 / (1 - σ) * ((P : ℝ) ^ (1 - σ) * Real.log (P : ℝ)))) atTop (𝓝 1) := by
  have h := (tendsto_condensedSocleVariance_div_logSqSum hσ hhalf hσ1).mul
    (tendsto_primeCutoffLogSqSum hσ1)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1,
    ((tendsto_condensedSocleVariance_div_logSqSum hσ hhalf hσ1).eventually
      (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))] with P hP1 hpos
  have hP1' : (1 : ℝ) < P := by exact_mod_cast hP1
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos hP1'
  have hpow : 0 < (P : ℝ) ^ (1 - σ) := Real.rpow_pos_of_pos (by linarith) _
  have hσ1' : 0 < 1 - σ := by linarith
  have hA : primeCutoffLogSqSum σ P ≠ 0 := by
    intro h0
    rw [h0, mul_zero, div_zero] at hpos
    exact lt_irrefl _ hpos
  field_simp

end GaloisForLFunctions.HTGeometry
