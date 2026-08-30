import GaloisForLFunctions.RHTower.RandomEulerSecondMoment
import GaloisForLFunctions.RHTower.PrimeZetaAbelRepresentation
import GaloisForLFunctions.RHTower.MertensSecondRealVariable

/-!
# The blow-up rate of the total second moment

The local second moment of one Euler factor is its leading Dirichlet term `p^(-2σ)` plus a
higher-power tail that is uniformly `O(p^(-4σ))`, hence summable over the primes at and above the
half line.  Therefore the total second moment `V(σ)` differs from the prime zeta value `P(2σ)` by a
bounded amount, and the prime zeta asymptotic `P(s) + log(s-1) → -D(1)` turns that into the
blow-up rate

```text
V(σ) = log (1 / (2σ - 1)) + O(1)      (σ → ½⁺).
```

At `σ = ½` the same splitting turns Mertens' second theorem into the truncated growth
`∑_{p ≤ X} V_p(½) = log log X + O(1)`.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

noncomputable section

/-! ## The higher-power tail of one local second moment -/

/-- The part of one local second moment coming from the powers `k ≥ 2`. -/
def eulerLocalTail (σ : ℝ) (p : ℕ) : ℝ :=
  ∑' k : ℕ, ((p : ℝ) ^ (-σ)) ^ (2 * (k + 2)) * (1 / ((k + 2 : ℕ) : ℝ)) ^ 2

section Local

variable {σ : ℝ} {p : ℕ}

private theorem rpow_prime_pos (hp : p.Prime) : (0 : ℝ) < (p : ℝ) ^ (-σ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

private theorem rpow_prime_sq_le_half (hp : p.Prime) (hσ : 1 / 2 ≤ σ) :
    ((p : ℝ) ^ (-σ)) ^ 2 ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have h1 : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-σ * 2) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hp0]
    norm_num
  have h2 : (p : ℝ) ^ (-σ * 2) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3 : (p : ℝ) ^ (-(1 : ℝ)) = ((p : ℝ))⁻¹ := by
    rw [Real.rpow_neg hp0, Real.rpow_one]
  have h4 : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith [h1 ▸ h2.trans_eq h3]

private theorem summable_localTerm (hp : p.Prime) (hσ : 0 < σ) :
    Summable (fun k : ℕ => ((p : ℝ) ^ (-σ)) ^ (2 * k) * (1 / (k : ℝ)) ^ 2) := by
  set r : ℝ := (p : ℝ) ^ (-σ) with hrdef
  have hr0 : (0 : ℝ) < r := rpow_prime_pos hp
  have hr1 : r < 1 := lt_of_le_of_lt (prime_rpow_neg_le_rho hσ hp) (randomEulerRho_lt_one hσ)
  have hgeom : HasSum (fun k : ℕ => (r ^ 2) ^ k) (1 - r ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) (by nlinarith)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hgeom.summable
  rw [pow_mul]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hle : (1 / (k : ℝ)) ^ 2 ≤ 1 := by
      rw [div_pow, one_pow, div_le_one (by positivity)]
      nlinarith
    exact mul_le_of_le_one_right (by positivity) hle

/-- **The leading term splits off.**  The local second moment is `p^(-2σ)` plus the tail. -/
theorem eulerLocalSecondMoment_eq_add_tail (hp : p.Prime) (hσ : 0 < σ) :
    eulerLocalSecondMoment σ p = ((p : ℝ) ^ (-σ)) ^ 2 + eulerLocalTail σ p := by
  have h := (summable_localTerm hp hσ).sum_add_tsum_nat_add 2
  rw [eulerLocalSecondMoment, ← h, eulerLocalTail]
  norm_num [Finset.sum_range_succ]

/-- **The tail is `O(p^(-4σ))`, uniformly at and above the half line.** -/
theorem eulerLocalTail_le (hp : p.Prime) (hσ : 1 / 2 ≤ σ) :
    eulerLocalTail σ p ≤ ((p : ℝ) ^ (-σ)) ^ 4 := by
  have hσ0 : 0 < σ := by linarith
  set r : ℝ := (p : ℝ) ^ (-σ) with hrdef
  have hr0 : (0 : ℝ) < r := rpow_prime_pos hp
  have hrsq : r ^ 2 ≤ 1 / 2 := rpow_prime_sq_le_half hp hσ
  have hr1 : r ^ 2 < 1 := by linarith
  have hgeom : HasSum (fun k : ℕ => (r ^ 2) ^ k) (1 - r ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) hr1
  have hmaj : HasSum (fun k : ℕ => r ^ 4 * (1 / 4 : ℝ) * (r ^ 2) ^ k)
      (r ^ 4 * (1 / 4 : ℝ) * (1 - r ^ 2)⁻¹) := hgeom.mul_left _
  have hterm : ∀ k : ℕ, r ^ (2 * (k + 2)) * (1 / ((k + 2 : ℕ) : ℝ)) ^ 2
      ≤ r ^ 4 * (1 / 4 : ℝ) * (r ^ 2) ^ k := by
    intro k
    have hpow : r ^ (2 * (k + 2)) = r ^ 4 * (r ^ 2) ^ k := by
      rw [← pow_mul]
      ring_nf
    have hk2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hle : (1 / ((k + 2 : ℕ) : ℝ)) ^ 2 ≤ (1 / 4 : ℝ) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [hpow]
    have hnn : (0 : ℝ) ≤ r ^ 4 * (r ^ 2) ^ k := by positivity
    calc r ^ 4 * (r ^ 2) ^ k * (1 / ((k + 2 : ℕ) : ℝ)) ^ 2
        ≤ r ^ 4 * (r ^ 2) ^ k * (1 / 4 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hle hnn
      _ = r ^ 4 * (1 / 4 : ℝ) * (r ^ 2) ^ k := by ring
  have hsum : Summable (fun k : ℕ => r ^ (2 * (k + 2)) * (1 / ((k + 2 : ℕ) : ℝ)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hterm hmaj.summable
  have hle := Summable.tsum_le_tsum hterm hsum hmaj.summable
  rw [hmaj.tsum_eq] at hle
  refine le_trans hle ?_
  have hden : (1 : ℝ) / 2 ≤ 1 - r ^ 2 := by linarith
  have hinv : (1 - r ^ 2)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h4 : (0 : ℝ) ≤ r ^ 4 := by positivity
  nlinarith

theorem eulerLocalTail_nonneg (σ : ℝ) (p : ℕ) : 0 ≤ eulerLocalTail σ p := by
  rw [eulerLocalTail]
  exact tsum_nonneg fun k => by positivity

end Local

/-! ## The total tail over the primes -/

section Total

variable {σ : ℝ} {p : ℕ}

private theorem rpow_prime_pow_two (_hp : p.Prime) :
    ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hp0]
  congr 1
  push_cast
  ring

private theorem rpow_prime_pow_four (_hp : p.Prime) :
    ((p : ℝ) ^ (-σ)) ^ 4 = (p : ℝ) ^ (-(4 * σ)) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) 4, ← Real.rpow_mul hp0]
  congr 1
  push_cast
  ring

/-- The total higher-power tail `∑_p ∑_{k ≥ 2} p^(-2kσ)/k²`. -/
def randomEulerTailSum (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then eulerLocalTail σ n else 0

theorem summable_ite_prime_eulerLocalTail (hσ : 1 / 2 ≤ σ) :
    Summable (fun n : ℕ => if n.Prime then eulerLocalTail σ n else 0) := by
  have h4 : (1 : ℝ) < 4 * σ := by linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_ite_prime_rpow h4)
  · split_ifs with h
    · exact eulerLocalTail_nonneg σ n
    · exact le_rfl
  · split_ifs with h
    · exact (eulerLocalTail_le h hσ).trans_eq (rpow_prime_pow_four h)
    · exact le_rfl

theorem randomEulerTailSum_nonneg (σ : ℝ) : 0 ≤ randomEulerTailSum σ := by
  rw [randomEulerTailSum]
  refine tsum_nonneg fun n => ?_
  split_ifs with h
  · exact eulerLocalTail_nonneg σ n
  · exact le_rfl

/-- **The total tail is bounded uniformly at and above the half line** by the prime zeta value
`P(2)`. -/
theorem randomEulerTailSum_le (hσ : 1 / 2 ≤ σ) :
    randomEulerTailSum σ ≤ _root_.RHTower.primeZeta 2 := by
  have hcomp : Summable (fun n : ℕ => if n.Prime then ((n : ℝ)) ^ (-(2 : ℝ)) else 0) :=
    summable_ite_prime_rpow (by norm_num)
  have hterm : ∀ n : ℕ, (if n.Prime then eulerLocalTail σ n else 0)
      ≤ (if n.Prime then ((n : ℝ)) ^ (-(2 : ℝ)) else 0) := by
    intro n
    split_ifs with h
    · refine (eulerLocalTail_le h hσ).trans ?_
      rw [rpow_prime_pow_four h]
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      exact_mod_cast h.one_lt.le
    · exact le_rfl
  have := Summable.tsum_le_tsum hterm (summable_ite_prime_eulerLocalTail hσ) hcomp
  rw [randomEulerTailSum]
  refine this.trans_eq ?_
  exact _root_.RHTower.tsum_primeIndicatorRpow

/-- **The total second moment is the prime zeta value plus a bounded tail.** -/
theorem randomEulerV_eq_primeZeta_add_tail (hσ : 1 / 2 < σ) :
    randomEulerV σ = _root_.RHTower.primeZeta (2 * σ) + randomEulerTailSum σ := by
  have hσ0 : 0 < σ := by linarith
  have h2 : (1 : ℝ) < 2 * σ := by linarith
  have hs1 : Summable (fun n : ℕ => if n.Prime then ((n : ℝ)) ^ (-(2 * σ)) else 0) :=
    summable_ite_prime_rpow h2
  have hs2 := summable_ite_prime_eulerLocalTail (le_of_lt hσ)
  rw [randomEulerV, randomEulerTailSum,
    ← _root_.RHTower.tsum_primeIndicatorRpow (s := 2 * σ), ← hs1.tsum_add hs2]
  refine tsum_congr fun n => ?_
  split_ifs with h
  · rw [eulerLocalSecondMoment_eq_add_tail h hσ0, rpow_prime_pow_two h]
  · norm_num

end Total

/-! ## The blow-up rate at the half line -/

/-- **The exact blow-up law.**  Up to the bounded tail, the total second moment is
`log (1/(2σ-1))` plus the negative of the higher-prime-power defect. -/
theorem tendsto_randomEulerV_add_log_sub_tail :
    Tendsto (fun σ : ℝ => randomEulerV σ + Real.log (2 * σ - 1) - randomEulerTailSum σ)
      (𝓝[>] (1 / 2 : ℝ)) (nhds (-_root_.RHTower.primeLogDefect 1)) := by
  have hmap : Tendsto (fun σ : ℝ => 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun σ : ℝ => 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (nhds (2 * (1 / 2 : ℝ))) :=
        ((continuous_const.mul continuous_id).tendsto _).mono_left nhdsWithin_le_nhds
      simpa using hc
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_Ioi] at hσ ⊢
      linarith
  have h := _root_.RHTower.tendsto_primeZeta_add_log_sub.comp hmap
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [Set.mem_Ioi] at hσ
  rw [Function.comp_apply, randomEulerV_eq_primeZeta_add_tail hσ]
  ring

/-- **`V(σ) = log(1/(2σ-1)) + O(1)` as `σ → ½⁺`.** -/
theorem exists_bound_randomEulerV_sub_logInv :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
      |randomEulerV σ - Real.log (1 / (2 * σ - 1))| ≤ C := by
  set L : ℝ := -_root_.RHTower.primeLogDefect 1 with hL
  refine ⟨|L| + 1 + _root_.RHTower.primeZeta 2, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ _root_.RHTower.primeZeta 2 :=
      (randomEulerTailSum_nonneg (1 / 2)).trans (randomEulerTailSum_le le_rfl)
    positivity
  · have hball := tendsto_randomEulerV_add_log_sub_tail (Metric.ball_mem_nhds L one_pos)
    filter_upwards [hball, self_mem_nhdsWithin] with σ hσball hσ
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hσball
    simp only [Set.mem_Ioi] at hσ
    have hσ' : (1 : ℝ) / 2 ≤ σ := le_of_lt hσ
    have hpos : (0 : ℝ) < 2 * σ - 1 := by linarith
    have hlog : Real.log (1 / (2 * σ - 1)) = -Real.log (2 * σ - 1) := by
      rw [one_div, Real.log_inv]
    have htail0 := randomEulerTailSum_nonneg σ
    have htail1 := randomEulerTailSum_le hσ'
    have habs : |randomEulerV σ + Real.log (2 * σ - 1) - randomEulerTailSum σ - L| < 1 := hσball
    rw [hlog, sub_neg_eq_add]
    have := abs_lt.mp habs
    have hle : |randomEulerV σ + Real.log (2 * σ - 1)| ≤ |L| + 1 + randomEulerTailSum σ := by
      rw [abs_le]
      constructor
      · have := neg_abs_le L
        linarith [this, (abs_lt.mp habs).1]
      · have := le_abs_self L
        linarith [this, (abs_lt.mp habs).2]
    linarith

/-- The scale `log(1/(2σ-1))` diverges at the half line. -/
theorem tendsto_logInv_atTop :
    Tendsto (fun σ : ℝ => Real.log (1 / (2 * σ - 1))) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  have hsub : Tendsto (fun σ : ℝ => 2 * σ - 1) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun σ : ℝ => 2 * σ - 1) (𝓝[>] (1 / 2 : ℝ))
          (nhds (2 * (1 / 2 : ℝ) - 1)) :=
        (((continuous_const.mul continuous_id).sub continuous_const).tendsto _).mono_left
          nhdsWithin_le_nhds
      simpa using hc
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_Ioi] at hσ ⊢
      linarith
  have hinv : Tendsto (fun σ : ℝ => (2 * σ - 1)⁻¹) (𝓝[>] (1 / 2 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have := Real.tendsto_log_atTop.comp hinv
  refine this.congr fun σ => ?_
  simp [Function.comp_apply, one_div]

/-- **The blow-up rate.**  `V(σ) / log(1/(2σ-1)) → 1` as `σ → ½⁺`. -/
theorem tendsto_randomEulerV_div_logInv :
    Tendsto (fun σ : ℝ => randomEulerV σ / Real.log (1 / (2 * σ - 1)))
      (𝓝[>] (1 / 2 : ℝ)) (nhds 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_randomEulerV_sub_logInv
  have hL := tendsto_logInv_atTop
  have hL1 : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), (1 : ℝ) ≤ Real.log (1 / (2 * σ - 1)) :=
    hL.eventually_ge_atTop 1
  have hzero : Tendsto (fun σ : ℝ => randomEulerV σ / Real.log (1 / (2 * σ - 1)) - 1)
      (𝓝[>] (1 / 2 : ℝ)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ (Tendsto.div_atTop (f := fun _ : ℝ => C) tendsto_const_nhds hL)
    filter_upwards [hC, hL1] with σ hσC hσL
    have hLpos : (0 : ℝ) < Real.log (1 / (2 * σ - 1)) := by linarith
    have hEq : randomEulerV σ / Real.log (1 / (2 * σ - 1)) - 1
        = (randomEulerV σ - Real.log (1 / (2 * σ - 1))) / Real.log (1 / (2 * σ - 1)) := by
      field_simp
    rw [Real.norm_eq_abs, hEq, abs_div, abs_of_pos hLpos]
    exact div_le_div_of_nonneg_right hσC hLpos.le
  have := hzero.add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at this
  refine this.congr fun σ => ?_
  ring

/-! ## Truncated growth at the half line -/

/-- The truncated total second moment `∑_{p ≤ N} V_p(σ)`. -/
def randomEulerVTrunc (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, if n.Prime then eulerLocalSecondMoment σ n else 0

private theorem icc_zero_eq_range (N : ℕ) : Finset.Icc 0 N = Finset.range (N + 1) := by
  ext n
  simp

private theorem rpow_prime_half_sq {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = ((p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [rpow_prime_pow_two hp, show -(2 * (1 / 2 : ℝ)) = -(1 : ℝ) by norm_num,
    Real.rpow_neg hp0, Real.rpow_one]

theorem randomEulerVTrunc_half_eq (N : ℕ) :
    randomEulerVTrunc (1 / 2) N
      = _root_.RHTower.primeRecipSum N
        + ∑ n ∈ Finset.Icc 0 N, (if n.Prime then eulerLocalTail (1 / 2) n else 0) := by
  rw [randomEulerVTrunc, _root_.RHTower.primeRecipSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, _root_.RHTower.primeRecipWeight, if_pos h,
      eulerLocalSecondMoment_eq_add_tail h (by norm_num), rpow_prime_half_sq h]
  · rw [if_neg h, if_neg h, _root_.RHTower.primeRecipWeight, if_neg h]
    ring

theorem tendsto_tailPartialSum :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, (if n.Prime then eulerLocalTail (1 / 2) n else 0))
      atTop (nhds (randomEulerTailSum (1 / 2))) := by
  have hs := summable_ite_prime_eulerLocalTail (σ := 1 / 2) le_rfl
  have h := hs.hasSum.tendsto_sum_nat
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun N => ?_
  rw [icc_zero_eq_range]
  rfl

/-- **Truncated growth on the critical line.**  `∑_{p ≤ X} V_p(½) - log log X` converges, so the
truncated second moment at `σ = ½` grows like `log log X`. -/
theorem tendsto_randomEulerVTrunc_half_sub_logLog :
    Tendsto (fun t : ℝ => randomEulerVTrunc (1 / 2) ⌊t⌋₊ - Real.log (Real.log t)) atTop
      (nhds (_root_.RHTower.mertensSecondConstant + randomEulerTailSum (1 / 2))) := by
  have h1 := _root_.RHTower.tendsto_primeRecipSum_floor_sub_logLog
  have h2 := tendsto_tailPartialSum.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h3 := h1.add h2
  refine h3.congr fun t => ?_
  rw [randomEulerVTrunc_half_eq]
  simp only [Function.comp_apply]
  ring

end

end GaloisForLFunctions.RHTower
