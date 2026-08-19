import GaloisForLFunctions.RHTower.PrimeSquareDeformedReflectionType
import GaloisForLFunctions.RHTower.MertensSecondPrimeRecipSum
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The superessential scale separation of the prime-square line comparison

The ordinary-prime Wold boundary coordinate `a_N = ∏_{p<N}(1-1/p)` has reciprocal at most
polylogarithmic in the cutoff: Mertens' second theorem bounds `∑_{p<N} 1/p` by `log log N + O(1)`
and `-log(1-1/p) ≤ 2/p`.  The critically normalized prime-square line comparison, by contrast, has
logarithm asymptotic to `|c| N`.  Hence the first-trace anomaly scale is negligible against the
prime-square scale: the two levels are separated.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The ordinary-prime Wold boundary volume `a_N = ∏_{p < N} (1 - 1/p)`. -/
def primeEulerVolume (N : ℕ) : ℝ := ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℕ) : ℝ)⁻¹)

theorem primeEulerVolume_pos (N : ℕ) : 0 < primeEulerVolume N := by
  refine Finset.prod_pos fun p hp => ?_
  rw [Nat.mem_primesBelow] at hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
  have hpinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem neg_log_one_sub_inv_le {p : ℕ} (hp : Nat.Prime p) :
    -Real.log (1 - ((p : ℕ) : ℝ)⁻¹) ≤ 2 * ((p : ℕ) : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hppos (by norm_num)]
    linarith
  have hbase : (0 : ℝ) < 1 - ((p : ℝ))⁻¹ := by linarith
  have hp1ne : ((p : ℝ)) - 1 ≠ 0 := by
    intro hcon
    have : (p : ℝ) = 1 := by linarith
    linarith
  have hlog : Real.log (1 - ((p : ℝ))⁻¹) = -Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) := by
    rw [Real.log_inv]
    ring
  have hle : Real.log ((1 - ((p : ℝ))⁻¹)⁻¹) ≤ (1 - ((p : ℝ))⁻¹)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hval : (1 - ((p : ℝ))⁻¹)⁻¹ - 1 = ((p : ℝ))⁻¹ / (1 - ((p : ℝ))⁻¹) := by
    rw [eq_div_iff (ne_of_gt hbase)]
    field_simp
    ring
  have hdiv : ((p : ℝ))⁻¹ / (1 - ((p : ℝ))⁻¹) ≤ 2 * ((p : ℝ))⁻¹ := by
    rw [div_le_iff₀ hbase]
    have hinvnn : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
    nlinarith
  rw [hlog]
  simp only [neg_neg]
  linarith [hle, hval, hdiv]

theorem neg_log_primeEulerVolume_le (N : ℕ) :
    -Real.log (primeEulerVolume N) ≤ 2 * primeRecipSum N := by
  classical
  have hlogprod : Real.log (primeEulerVolume N)
      = ∑ p ∈ Nat.primesBelow N, Real.log (1 - ((p : ℕ) : ℝ)⁻¹) := by
    rw [primeEulerVolume, Real.log_prod]
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    intro hcon
    have : (1 : ℝ) - ((p : ℝ))⁻¹ > 0 := by linarith
    linarith [hcon ▸ this]
  have hneg : -(∑ p ∈ Nat.primesBelow N, Real.log (1 - ((p : ℕ) : ℝ)⁻¹))
      = ∑ p ∈ Nat.primesBelow N, -Real.log (1 - ((p : ℕ) : ℝ)⁻¹) :=
    (Finset.sum_neg_distrib _).symm
  rw [hlogprod, hneg]
  have hterm : ∀ p ∈ Nat.primesBelow N,
      -Real.log (1 - ((p : ℕ) : ℝ)⁻¹) ≤ 2 * ((p : ℕ) : ℝ)⁻¹ := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    exact neg_log_one_sub_inv_le hp.2
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hleft : ∑ p ∈ Nat.primesBelow N, ((p : ℕ) : ℝ)⁻¹
      = ∑ p ∈ Nat.primesBelow N, primeRecipWeight p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.mem_primesBelow] at hp
    rw [primeRecipWeight, if_pos hp.2]
  rw [hleft, primeRecipSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Nat.mem_primesBelow] at hp
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, by omega⟩
  · intro p _ _
    rw [primeRecipWeight]
    split <;> positivity

/-- **The Wold boundary volume is at most polylogarithmically small.**  Mertens' second theorem
bounds its reciprocal by a constant times `(log N)²`. -/
theorem exists_inv_primeEulerVolume_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (primeEulerVolume N)⁻¹ ≤ C * (Real.log N) ^ 2 := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp tendsto_primeRecipSum_sub_logLog 1 (by norm_num)
  refine ⟨Real.exp (2 * (mertensSecondConstant + 1)), Real.exp_pos _, ?_⟩
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop 3] with N hN hN3
  have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (1 : ℝ) < Real.log N := by
    have h3 : Real.log 3 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hNr
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) this
    linarith
  have hbound : primeRecipSum N ≤ Real.log (Real.log N) + (mertensSecondConstant + 1) := by
    have hd := hM N hN
    rw [Real.dist_eq, abs_lt] at hd
    linarith [hd.2]
  have hneg := neg_log_primeEulerVolume_le N
  have hvolpos := primeEulerVolume_pos N
  have hlog : Real.log ((primeEulerVolume N)⁻¹) ≤ 2 * Real.log (Real.log N)
      + 2 * (mertensSecondConstant + 1) := by
    rw [Real.log_inv]
    linarith
  have hexp : (primeEulerVolume N)⁻¹
      ≤ Real.exp (2 * Real.log (Real.log N) + 2 * (mertensSecondConstant + 1)) := by
    have hpos : (0 : ℝ) < (primeEulerVolume N)⁻¹ := by positivity
    calc (primeEulerVolume N)⁻¹ = Real.exp (Real.log ((primeEulerVolume N)⁻¹)) :=
          (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  refine hexp.trans (le_of_eq ?_)
  rw [Real.exp_add, mul_comm]
  congr 1
  rw [show (2 : ℝ) * Real.log (Real.log N) = Real.log ((Real.log N) ^ 2) by
    rw [Real.log_pow]
    push_cast
    ring]
  exact Real.exp_log (by positivity)

theorem tendsto_log_sq_div_natCast :
    Tendsto (fun N : ℕ => (Real.log N) ^ 2 / (N : ℝ)) atTop (nhds 0) := by
  have hmaj : ∀ᶠ N : ℕ in atTop,
      |(Real.log N) ^ 2 / (N : ℝ)| ≤ 16 * ((N : ℝ) ^ (-(1/2) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog : Real.log (N : ℝ) ≤ 4 * ((N : ℝ) ^ ((1:ℝ)/4)) := by
      have := Mertens.log_le_rpow (x := (N : ℝ)) (α := (1:ℝ)/4) hNpos (by norm_num)
      calc Real.log (N : ℝ) ≤ (1 / ((1:ℝ)/4)) * ((N : ℝ) ^ ((1:ℝ)/4)) := this
        _ = 4 * ((N : ℝ) ^ ((1:ℝ)/4)) := by norm_num
    have hlognn : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 16 * ((N : ℝ) ^ ((1:ℝ)/2)) := by
      have hpow : ((N : ℝ) ^ ((1:ℝ)/4)) ^ 2 = (N : ℝ) ^ ((1:ℝ)/2) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hNpos.le]
        norm_num
      nlinarith [hlog, hlognn, Real.rpow_nonneg hNpos.le ((1:ℝ)/4)]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hNpos]
    have hrw : 16 * ((N : ℝ) ^ (-(1/2) : ℝ)) * (N : ℝ) = 16 * ((N : ℝ) ^ ((1:ℝ)/2)) := by
      have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      calc 16 * ((N : ℝ) ^ (-(1/2) : ℝ)) * (N : ℝ)
          = 16 * ((N : ℝ) ^ (-(1/2) : ℝ) * (N : ℝ) ^ (1 : ℝ)) := by
            rw [← hN1]
            ring
        _ = 16 * ((N : ℝ) ^ ((-(1/2) : ℝ) + 1)) := by rw [← Real.rpow_add hNpos]
        _ = 16 * ((N : ℝ) ^ ((1:ℝ)/2)) := by norm_num
    rw [hrw]
    exact hsq
  have hzero : Tendsto (fun N : ℕ => 16 * ((N : ℝ) ^ (-(1/2) : ℝ))) atTop (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ (-(1/2) : ℝ)) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have := (hbase.comp tendsto_natCast_atTop_atTop).const_mul (16 : ℝ)
    simpa using this
  exact squeeze_zero_norm' (by
    filter_upwards [hmaj] with N hN using hN) hzero

/-- **The superessential scale separation.**  The reciprocal Wold boundary volume — the exponent
scale of the first-trace anomaly — is negligible against the exponent of the critically normalized
prime-square line comparison. -/
theorem tendsto_inv_primeEulerVolume_div_logProd {c : ℝ} (hc : 0 < c) (hc2 : 2 * c ≤ 1) :
    Tendsto (fun N : ℕ => (primeEulerVolume N)⁻¹
        / (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hCbound⟩ := exists_inv_primeEulerVolume_le
  have hrate := tendsto_log_prod_criticalNormalizedReflection_div_natCast hc.le hc2
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hrate (c / 2) (by linarith)
  have hmaj : ∀ᶠ N : ℕ in atTop,
      ‖(primeEulerVolume N)⁻¹
        / (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))‖
        ≤ (2 * C / c) * ((Real.log N) ^ 2 / (N : ℝ)) := by
    filter_upwards [hCbound, eventually_ge_atTop M, eventually_ge_atTop 3] with N hN hNM hN3
    have hNr : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hd := hM N hNM
    rw [Real.dist_eq, abs_lt] at hd
    have hden : (c / 2) * (N : ℝ)
        ≤ ∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c) := by
      have h1 : c - c / 2
          < (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) / (N : ℝ) := by
        linarith [hd.1]
      have h2 : c - c / 2 = c / 2 := by ring
      rw [h2] at h1
      rw [← le_div_iff₀ hNpos] at *
      linarith [h1]
    have hdenpos : (0 : ℝ)
        < ∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c) := by
      have : (0 : ℝ) < (c / 2) * (N : ℝ) := by positivity
      linarith
    have hnumpos : (0 : ℝ) < (primeEulerVolume N)⁻¹ := by
      have := primeEulerVolume_pos N
      positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ hdenpos]
    calc (primeEulerVolume N)⁻¹ ≤ C * (Real.log N) ^ 2 := hN
      _ = (2 * C / c) * ((Real.log N) ^ 2 / (N : ℝ)) * ((c / 2) * (N : ℝ)) := by
          field_simp
      _ ≤ (2 * C / c) * ((Real.log N) ^ 2 / (N : ℝ))
          * (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) := by
          refine mul_le_mul_of_nonneg_left hden ?_
          have hlognn : (0 : ℝ) ≤ (Real.log N) ^ 2 := sq_nonneg _
          positivity
  have hzero : Tendsto (fun N : ℕ => (2 * C / c) * ((Real.log N) ^ 2 / (N : ℝ))) atTop (nhds 0) := by
    have := tendsto_log_sq_div_natCast.const_mul (2 * C / c)
    simpa using this
  exact squeeze_zero_norm' hmaj hzero

end

end RHTower
