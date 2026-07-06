/-
# The near-pole steepness limit: the local factor `κ` from the field

The edge law's local factor `κ = 2/π²` is the continuum value of `2/(|F'(m)|·δ/i)`, where
`|F'(m)| = 2W(m)`, `W = ¼Σ csch²`. This file proves the underlying limit rigorously: on the harmonic
carrier the rescaled reduced energy at the gap midpoint converges,

> `W(m_i)/n² → π²/c²`  (`n = i+1`),   equivalently  `2W(m_i)·δ_i/i → 2π²/c` and `κ(c) = c/π²`.

The mechanism is a **Tannery limit** (dominated convergence for series): each pole contributes a
rescaled `csch²((dist)/2)/n²` term whose `n → ∞` limit is `(2/(c(k+½)))²` (near-pole `csch²(z) → 1/z²`
with `n·dist → c(k+½)`), dominated uniformly by the summable `(2/(c(k+½)))²`; the sum converges to
`Σ_k (2/(c(k+½)))² = 2π²/c²` per side (odd Basel).

Analytic core here: `self_lt_sinh`, `rcsch_sq_lt_inv_sq` (`csch²(z) < 1/z²`), `tendsto_self_div_sinh`
(`w/sinh w → 1`), and `tendsto_rescaled_csch_sq_term` (the single-pole rescaled limit).
-/
import GaloisForLFunctions.RHTower.LegStripEdge
open Real Set Filter Topology
noncomputable section
namespace RHTower

/-- `x < sinh x` for `x > 0`: the derivative `cosh x − 1` is positive, so `sinh x − x` strictly
increases from `0`. -/
theorem self_lt_sinh {x : ℝ} (hx : 0 < x) : x < Real.sinh x := by
  have hmono : StrictMonoOn (fun t => Real.sinh t - t) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (Real.continuous_sinh.sub continuous_id).continuousOn
    · intro y hy
      rw [interior_Ici] at hy
      have hd : HasDerivAt (fun t => Real.sinh t - t) (Real.cosh y - 1) y :=
        (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
      rw [hd.deriv]
      have : 1 < Real.cosh y := Real.one_lt_cosh.mpr (by simp only [mem_Ioi] at hy; linarith)
      linarith
  have := hmono self_mem_Ici (le_of_lt hx) hx
  simpa using this

/-- **`csch²(z) < 1/z²` for `z > 0`** — the near-pole envelope: `csch(z) = 1/sinh z < 1/z`. -/
theorem rcsch_sq_lt_inv_sq {z : ℝ} (hz : 0 < z) : (rcsch z)^2 < (1/z)^2 := by
  have h1 : rcsch z < 1/z := by
    rw [rcsch]; exact one_div_lt_one_div_of_lt hz (self_lt_sinh hz)
  have h0 : 0 < rcsch z := by rw [rcsch]; exact one_div_pos.mpr (sinh_pos_of_pos hz)
  nlinarith [h1, h0]

/-- `sinh w / w → 1` as `w → 0` (`≠ 0`): the derivative of `sinh` at `0` is `cosh 0 = 1`. -/
theorem tendsto_sinh_div : Tendsto (fun w : ℝ => Real.sinh w / w) (𝓝[≠] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cosh_zero] at h
  refine h.congr (fun w => ?_)
  rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]

/-- `w / sinh w → 1` as `w → 0` (`≠ 0`) — reciprocal of `tendsto_sinh_div`. -/
theorem tendsto_self_div_sinh : Tendsto (fun w : ℝ => w / Real.sinh w) (𝓝[≠] 0) (𝓝 1) := by
  have h := tendsto_sinh_div.inv₀ (by norm_num)
  rw [inv_one] at h
  exact h.congr (fun w => inv_div (Real.sinh w) w)

/-- **The single-pole rescaled `csch²` limit.** If the `k`-th pole distance `dist n` satisfies
`n·dist n → L > 0` (and `dist n > 0`), the rescaled contribution `csch²(dist n /2)/n²` converges to the
near-pole value `(2/L)²`: writing it as `(rcsch(dist/2)·(dist/2))² · (4/(n·dist)²)`, the first factor
`→ 1` (`w/sinh w → 1`) and the second `→ 4/L²`. -/
theorem tendsto_rescaled_csch_sq_term {dist : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hpos : ∀ᶠ n in atTop, 0 < dist n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * dist n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (1/(n : ℝ)^2) * (rcsch (dist n / 2))^2) atTop (𝓝 ((2/L)^2)) := by
  -- dist n → 0
  have hdist0 : Tendsto (fun n => dist n) atTop (𝓝 0) := by
    have hm := hlim.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [mul_zero] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  -- (dist n /2)/sinh(dist n/2) → 1
  have hhalf : Tendsto (fun n => dist n / 2) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using hdist0.div_const 2
    · filter_upwards [hpos] with n hn
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (half_pos hn).ne'
  have hfac1 : Tendsto (fun n => (dist n / 2) / Real.sinh (dist n / 2)) atTop (𝓝 1) :=
    tendsto_self_div_sinh.comp hhalf
  -- 4/(n·dist n)² → 4/L²
  have hpow := hlim.pow 2
  have hfac2 := (tendsto_const_nhds (x := (4:ℝ))).div hpow (show L^2 ≠ 0 by positivity)
  -- product → 1 · 4/L² = (2/L)²
  have hprod := (hfac1.pow 2).mul hfac2
  simp only [one_pow, one_mul] at hprod
  rw [show ((2:ℝ)/L)^2 = 4/L^2 by rw [div_pow]; norm_num]
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hpos] with n hn hdn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0 : dist n ≠ 0 := ne_of_gt hdn
  have hs0 : Real.sinh (dist n / 2) ≠ 0 := ne_of_gt (sinh_pos_of_pos (half_pos hdn))
  simp only [Pi.div_apply, rcsch]
  field_simp
  ring

/-- **The Tannery dominating bound.** If the pole distance `d ≥ (c/n)(k+½)`, its rescaled `csch²`
contribution is bounded by the summable near-pole value `(2/(c(k+½)))²` uniformly in `n`. -/
theorem rescaled_csch_sq_le {c : ℝ} (hc : 0 < c) (k : ℕ) {n : ℕ} (hn : 0 < n) {d : ℝ}
    (hdpos : 0 < d) (hlb : (c/(n:ℝ))*((k:ℝ)+1/2) ≤ d) :
    (1/(n:ℝ)^2)*(rcsch (d/2))^2 ≤ (2/(c*((k:ℝ)+1/2)))^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hcsch : (rcsch (d/2))^2 < (1/(d/2))^2 := rcsch_sq_lt_inv_sq (by positivity)
  have hk : (0:ℝ) < c*((k:ℝ)+1/2) := by positivity
  have hcancel : (n:ℝ) * ((c/(n:ℝ))*((k:ℝ)+1/2)) = c*((k:ℝ)+1/2) := by field_simp
  have hnd : c*((k:ℝ)+1/2) ≤ (n:ℝ)*d := by
    have h := mul_le_mul_of_nonneg_left hlb hn0.le
    rwa [hcancel] at h
  have step1 : (1/(n:ℝ)^2)*(rcsch (d/2))^2 ≤ (1/(n:ℝ)^2)*(1/(d/2))^2 :=
    mul_le_mul_of_nonneg_left hcsch.le (by positivity)
  have eq1 : (1/(n:ℝ)^2)*(1/(d/2))^2 = (2/((n:ℝ)*d))^2 := by field_simp
  have step2 : (2/((n:ℝ)*d))^2 ≤ (2/(c*((k:ℝ)+1/2)))^2 := by gcongr
  rw [eq1] at step1
  linarith [step1, step2]

/-- The near-pole bound `(2/(c(k+½)))²` is summable, with sum `2π²/c²` (odd Basel): it equals
`(16/c²)·Σ 1/(2k+1)² = (16/c²)(π²/8)`. -/
theorem summable_near_pole_bound {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => (2/(c*((k:ℝ)+1/2)))^2) := by
  have hrw : (fun k : ℕ => (2/(c*((k:ℝ)+1/2)))^2)
      = fun k : ℕ => (16/c^2) * (1/(2*(k:ℝ)+1)^2) := by
    funext k
    have h1 : c ≠ 0 := ne_of_gt hc
    have h2 : ((k:ℝ)+1/2) ≠ 0 := by positivity
    have h3 : (2*(k:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrw]
  exact (hasSum_odd_basel.summable.mul_left (16/c^2))

/-- The near-pole bound sums to `2π²/c²`. -/
theorem tsum_near_pole_bound {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, (2/(c*((k:ℝ)+1/2)))^2 = 2*π^2/c^2 := by
  have hrw : (fun k : ℕ => (2/(c*((k:ℝ)+1/2)))^2)
      = fun k : ℕ => (16/c^2) * (1/(2*(k:ℝ)+1)^2) := by
    funext k
    have h1 : c ≠ 0 := ne_of_gt hc
    have h2 : ((k:ℝ)+1/2) ≠ 0 := by positivity
    have h3 : (2*(k:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrw, tsum_mul_left, hasSum_odd_basel.tsum_eq]
  field_simp
  ring

/-- **The rescaled `csch²` sum limit (Tannery).** For a family of pole distances `dist n k` with
`n·dist n k → c(k+½)` (pointwise) and lower bound `dist n k ≥ (c/n)(k+½)`, the rescaled `csch²` sum
converges to `Σ_k (2/(c(k+½)))² = 2π²/c²` — the near-pole steepness of one side of the field. -/
theorem tendsto_rescaled_csch_sq_sum {c : ℝ} (hc : 0 < c) {dist : ℕ → ℕ → ℝ}
    (hpos : ∀ n k : ℕ, 0 < dist n k)
    (hlb : ∀ n k : ℕ, 0 < n → (c/(n:ℝ))*((k:ℝ)+1/2) ≤ dist n k)
    (hlim : ∀ k : ℕ, Tendsto (fun n : ℕ => (n:ℝ)*dist n k) atTop (𝓝 (c*((k:ℝ)+1/2)))) :
    Tendsto (fun n : ℕ => ∑' k : ℕ, (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2) atTop
      (𝓝 (2*π^2/c^2)) := by
  rw [← tsum_near_pole_bound hc]
  apply tendsto_tsum_of_dominated_convergence (summable_near_pole_bound hc)
  · intro k
    exact tendsto_rescaled_csch_sq_term (show (0:ℝ) < c*((k:ℝ)+1/2) by positivity)
      (Filter.Eventually.of_forall (fun n => hpos n k)) (hlim k)
  · filter_upwards [eventually_gt_atTop 0] with n hn k
    rw [Real.norm_of_nonneg (by positivity)]
    exact rescaled_csch_sq_le hc k hn (hpos n k) (hlb n k hn)

/-- Auxiliary: `i·k/(i − r) → k` for a fixed real shift `r` — the two squeeze bounds of the backward
harmonic sum. -/
theorem tendsto_mul_div_sub (k : ℕ) (r : ℝ) :
    Tendsto (fun i : ℕ => (i:ℝ)*(k:ℝ)/((i:ℝ)-r)) atTop (𝓝 (k:ℝ)) := by
  have h1 : Tendsto (fun i : ℕ => ((i:ℝ)-r)/(i:ℝ)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun i : ℕ => 1 - r*(1/(i:ℝ))) atTop (𝓝 (1 - r*0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
    simp only [mul_zero, sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with i hi
    have : (i:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h3 := (tendsto_const_nhds (x := (k:ℝ))).div h1 one_ne_zero
  simp only [div_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (⌈r⌉₊ + 1)] with i hi
  have hir : r < (i:ℝ) := lt_of_le_of_lt (Nat.le_ceil r) (by exact_mod_cast (by omega : ⌈r⌉₊ < i))
  have hik : (i:ℝ) - r ≠ 0 := by linarith
  have hi0 : (i:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Pi.div_apply]
  field_simp

/-- **The backward harmonic sum limit** `i·Σ_{j<k} 1/(i−1−j) → k`: each of the `k` terms is `≈ 1/i`.
Proved by squeezing between `i·k/(i−1)` and `i·k/(i−k)`, both `→ k`. This is the harmonic asymptotic
behind the near-pole distance limit `i·behind_k → c(k+½)`. -/
theorem tendsto_backward_harmonic_sum (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ))) atTop (𝓝 (k:ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_mul_div_sub k 1) (tendsto_mul_div_sub k (k:ℝ))
  · filter_upwards [eventually_gt_atTop (k+1)] with i hi
    have hik : (k:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : k < i)
    have h2i : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast (by omega : 2 ≤ i)
    have hi1 : (0:ℝ) < (i:ℝ) - 1 := by linarith
    have hlb : (k:ℝ) * (1/((i:ℝ)-1)) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ)) := by
      have := Finset.card_nsmul_le_sum (Finset.range k) (fun j => 1/((i:ℝ)-1-(j:ℝ)))
        (1/((i:ℝ)-1)) (fun j hj => by
          rw [Finset.mem_range] at hj
          have hj2 : (j:ℝ) + 2 ≤ (i:ℝ) := by exact_mod_cast (by omega : j+2 ≤ i)
          have hjnn : (0:ℝ) ≤ (j:ℝ) := by positivity
          exact one_div_le_one_div_of_le (by linarith) (by linarith))
      rwa [Finset.card_range, nsmul_eq_mul] at this
    have hipos : (0:ℝ) < (i:ℝ) := by linarith
    calc (i:ℝ)*(k:ℝ)/((i:ℝ)-1) = (i:ℝ) * ((k:ℝ) * (1/((i:ℝ)-1))) := by field_simp
      _ ≤ (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ)) :=
          mul_le_mul_of_nonneg_left hlb hipos.le
  · filter_upwards [eventually_gt_atTop (k+1)] with i hi
    have hik : (k:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : k < i)
    have hik0 : (0:ℝ) < (i:ℝ) - (k:ℝ) := by linarith
    have hub : ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ)) ≤ (k:ℝ) * (1/((i:ℝ)-(k:ℝ))) := by
      have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => 1/((i:ℝ)-1-(j:ℝ)))
        (1/((i:ℝ)-(k:ℝ))) (fun j hj => by
          rw [Finset.mem_range] at hj
          have hj1 : (j:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast (by omega : j+1 ≤ k)
          exact one_div_le_one_div_of_le hik0 (by linarith))
      rwa [Finset.card_range, nsmul_eq_mul] at this
    have hipos : (0:ℝ) < (i:ℝ) := by linarith
    calc (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ))
        ≤ (i:ℝ) * ((k:ℝ) * (1/((i:ℝ)-(k:ℝ)))) := mul_le_mul_of_nonneg_left hub hipos.le
      _ = (i:ℝ)*(k:ℝ)/((i:ℝ)-(k:ℝ)) := by field_simp

/-- **The near-pole distance limit.** The `k`-th behind pole distance from the gap midpoint,
`bdist_i(k) = c/(2i) + c·Σ_{j<k} 1/(i−1−j)`, satisfies `i·bdist_i(k) → c(k+½)`: the shift `c/(2i)`
contributes `c/2` and the harmonic sum `c/k` (backward harmonic limit). This is the `hlim` hypothesis
of `tendsto_rescaled_csch_sq_sum`. -/
theorem tendsto_behind_dist (c : ℝ) (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * (c/(2*(i:ℝ)) + c*∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ))))
      atTop (𝓝 (c*((k:ℝ)+1/2))) := by
  have hbase := (tendsto_backward_harmonic_sum k).const_mul c
  have hsum : Tendsto (fun i : ℕ => c/2 + c*((i:ℝ)*∑ j ∈ Finset.range k, 1/((i:ℝ)-1-(j:ℝ))))
      atTop (𝓝 (c/2 + c*(k:ℝ))) := tendsto_const_nhds.add hbase
  rw [show c*((k:ℝ)+1/2) = c/2 + c*(k:ℝ) by ring]
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (i:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **The near-pole distance lower bound** `bdist_i(k) ≥ (c/i)(k+½)` (`k < i`): each harmonic term
`1/(i−1−j) ≥ 1/i` (denominator `≤ i`), so the sum is `≥ k/i` and `bdist = c/(2i) + c·sum ≥
c/(2i) + ck/i = (c/i)(k+½)`. This is the `hlb` hypothesis of `tendsto_rescaled_csch_sq_sum`. -/
theorem behind_dist_lb {c : ℝ} (hc : 0 < c) {i k : ℕ} (hik : k < i) :
    (c/(i:ℝ)) * ((k:ℝ) + 1/2)
      ≤ c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ) - 1 - (j:ℝ)) := by
  have hi0 : (0:ℝ) < (i:ℝ) := Nat.cast_pos.mpr (by omega)
  have hsum : (∑ j ∈ Finset.range k, (1:ℝ)/(i:ℝ))
      ≤ (∑ j ∈ Finset.range k, 1/((i:ℝ) - 1 - (j:ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hj2 : (j:ℝ) + 2 ≤ (i:ℝ) := by exact_mod_cast (show j + 2 ≤ i by omega)
    have hpos : (0:ℝ) < (i:ℝ) - 1 - (j:ℝ) := by linarith
    exact one_div_le_one_div_of_le hpos (by linarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] at hsum
  have hstep : c * ((k:ℝ)/(i:ℝ)) ≤ c * ∑ j ∈ Finset.range k, 1/((i:ℝ) - 1 - (j:ℝ)) :=
    mul_le_mul_of_nonneg_left hsum hc.le
  have heq : (c/(i:ℝ)) * ((k:ℝ) + 1/2) = c/(2*(i:ℝ)) + c * ((k:ℝ)/(i:ℝ)) := by
    field_simp; ring
  rw [heq]; linarith

/-- **The rescaled `csch²` sum limit for growing finite sums.** When the sum ranges over the actual
pole count `count n → ∞` (not all of `ℕ`), the rescaled `csch²` sum still converges to `2π²/c²`: the
finite sum is the `tsum` of the indicator-truncated terms, which converge pointwise and are dominated by
the same summable near-pole bound. This is the form needed for the literal field energy, whose behind
and ahead sums are finite. -/
theorem tendsto_rescaled_csch_sq_finsum {c : ℝ} (hc : 0 < c) {dist : ℕ → ℕ → ℝ}
    (count : ℕ → ℕ) (hcount : Tendsto count atTop atTop)
    (hpos : ∀ k : ℕ, ∀ᶠ n in atTop, 0 < dist n k)
    (hlb : ∀ n k : ℕ, 0 < n → k < count n → (c/(n:ℝ))*((k:ℝ)+1/2) ≤ dist n k)
    (hlim : ∀ k : ℕ, Tendsto (fun n : ℕ => (n:ℝ)*dist n k) atTop (𝓝 (c*((k:ℝ)+1/2)))) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (count n), (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2) atTop
      (𝓝 (2*π^2/c^2)) := by
  classical
  rw [← tsum_near_pole_bound hc]
  have hsumeq : ∀ n : ℕ, (∑ k ∈ Finset.range (count n), (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2)
      = ∑' k : ℕ, (if k < count n then (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2 else 0) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (count n))
      (fun k hk => by rw [Finset.mem_range] at hk; simp [hk])]
    exact Finset.sum_congr rfl (fun k hk => by rw [Finset.mem_range] at hk; simp [hk])
  simp_rw [hsumeq]
  apply tendsto_tsum_of_dominated_convergence (summable_near_pole_bound hc)
  · intro k
    have hev : (fun n : ℕ => (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2)
        =ᶠ[atTop] (fun n => if k < count n then (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2 else 0) := by
      filter_upwards [hcount.eventually_gt_atTop k] with n hn; simp [hn]
    exact (tendsto_rescaled_csch_sq_term (show (0:ℝ) < c*((k:ℝ)+1/2) by positivity)
      (hpos k) (hlim k)).congr' hev
  · filter_upwards [eventually_gt_atTop 0] with n hn k
    by_cases hkc : k < count n
    · rw [if_pos hkc, Real.norm_of_nonneg (by positivity)]
      have hdpos : 0 < dist n k := lt_of_lt_of_le (by positivity) (hlb n k hn hkc)
      exact rescaled_csch_sq_le hc k hn hdpos (hlb n k hn hkc)
    · rw [if_neg hkc, norm_zero]; positivity

/-- **Growing-finite-sum Tannery with a separate domination constant.** The domination lower bound uses
`b` (the ahead distances satisfy only `adist ≥ (c/2)(k+½)/n`, not the exact `(c/n)(k+½)`), while the
pointwise limit and the target sum use `c`; the sum still converges to `2π²/c²` — the near-pole value
of the *limit*, dominated by the summable `b`-bound `(2/(b(k+½)))²`. -/
theorem tendsto_rescaled_csch_sq_finsum_gen {c b : ℝ} (hc : 0 < c) (hb : 0 < b) {dist : ℕ → ℕ → ℝ}
    (count : ℕ → ℕ) (hcount : Tendsto count atTop atTop)
    (hpos : ∀ k : ℕ, ∀ᶠ n in atTop, 0 < dist n k)
    (hlb : ∀ n k : ℕ, 0 < n → k < count n → (b/(n:ℝ))*((k:ℝ)+1/2) ≤ dist n k)
    (hlim : ∀ k : ℕ, Tendsto (fun n : ℕ => (n:ℝ)*dist n k) atTop (𝓝 (c*((k:ℝ)+1/2)))) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (count n), (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2) atTop
      (𝓝 (2*π^2/c^2)) := by
  classical
  rw [← tsum_near_pole_bound hc]
  have hsumeq : ∀ n : ℕ, (∑ k ∈ Finset.range (count n), (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2)
      = ∑' k : ℕ, (if k < count n then (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2 else 0) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (count n))
      (fun k hk => by rw [Finset.mem_range] at hk; simp [hk])]
    exact Finset.sum_congr rfl (fun k hk => by rw [Finset.mem_range] at hk; simp [hk])
  simp_rw [hsumeq]
  apply tendsto_tsum_of_dominated_convergence (summable_near_pole_bound hb)
  · intro k
    have hev : (fun n : ℕ => (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2)
        =ᶠ[atTop] (fun n => if k < count n then (1/(n:ℝ)^2)*(rcsch (dist n k /2))^2 else 0) := by
      filter_upwards [hcount.eventually_gt_atTop k] with n hn; simp [hn]
    exact (tendsto_rescaled_csch_sq_term (show (0:ℝ) < c*((k:ℝ)+1/2) by positivity)
      (hpos k) (hlim k)).congr' hev
  · filter_upwards [eventually_gt_atTop 0] with n hn k
    by_cases hkc : k < count n
    · rw [if_pos hkc, Real.norm_of_nonneg (by positivity)]
      have hdpos : 0 < dist n k := lt_of_lt_of_le (by positivity) (hlb n k hn hkc)
      exact rescaled_csch_sq_le hb k hn hdpos (hlb n k hn hkc)
    · rw [if_neg hkc, norm_zero]; positivity

/-- **The behind-side steepness on the harmonic distances.** The rescaled behind `csch²` sum on the
exact harmonic pole distances `bdist_n(k) = c/(2n) + c·Σ_{j<k}1/(n−1−j)` converges to `2π²/c²` — the
literal near-pole steepness of the behind train (one side of `2W(m)δ/i → 2π²/c`), assembled from the
finite-sum Tannery limit, the near-pole distance limit `tendsto_behind_dist`, and the lower bound
`behind_dist_lb`. -/
theorem behind_csch_sum_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        (1/(n:ℝ)^2) * (rcsch ((c/(2*(n:ℝ)) + c*∑ j ∈ Finset.range k, 1/((n:ℝ)-1-(j:ℝ)))/2))^2)
      atTop (𝓝 (2*π^2/c^2)) := by
  exact tendsto_rescaled_csch_sq_finsum hc (fun n => n) tendsto_id
    (fun k => by
      filter_upwards [eventually_ge_atTop (k+1)] with n hn
      have hn0 : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range k, 1/((n:ℝ)-1-(j:ℝ)) := by
        apply Finset.sum_nonneg
        intro j hj
        rw [Finset.mem_range] at hj
        have : (j:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast (show j + 1 ≤ n by omega)
        have hpos : (0:ℝ) < (n:ℝ)-1-(j:ℝ) := by
          have : (j:ℝ) + 2 ≤ (n:ℝ) := by exact_mod_cast (show j + 2 ≤ n by omega)
          linarith
        exact one_div_nonneg.mpr hpos.le
      have hcn : (0:ℝ) < c/(2*(n:ℝ)) := div_pos hc (by positivity)
      nlinarith [mul_nonneg hc.le hsum])
    (fun n k _ hkn => behind_dist_lb hc hkn)
    (fun k => tendsto_behind_dist c k)

/-- **The forward harmonic sum limit** `i·Σ_{j<k} 1/(i+1+j) → k`: the ahead analogue of
`tendsto_backward_harmonic_sum`, squeezed between `ik/(i+k)` and `ik/(i+1)`, both `→ k`. -/
theorem tendsto_forward_harmonic_sum (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))) atTop (𝓝 (k:ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_mul_div_sub k (-(k:ℝ))) (tendsto_mul_div_sub k (-1))
  · filter_upwards [eventually_gt_atTop 0] with i hi
    have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
    have hlb : (k:ℝ) * (1/((i:ℝ)+(k:ℝ))) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ)) := by
      have hconst : ((k:ℝ)) * (1/((i:ℝ)+(k:ℝ))) = ∑ _x ∈ Finset.range k, (1:ℝ)/((i:ℝ)+(k:ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hconst]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : (j:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast (show j+1 ≤ k by omega)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    calc (i:ℝ)*(k:ℝ)/((i:ℝ)-(-(k:ℝ))) = (i:ℝ) * ((k:ℝ) * (1/((i:ℝ)+(k:ℝ)))) := by
          rw [sub_neg_eq_add]; field_simp
      _ ≤ (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ)) := mul_le_mul_of_nonneg_left hlb hi0.le
  · filter_upwards [eventually_gt_atTop 0] with i hi
    have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
    have hub : (∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))) ≤ (k:ℝ) * (1/((i:ℝ)+1)) := by
      have hconst : ((k:ℝ)) * (1/((i:ℝ)+1)) = ∑ _x ∈ Finset.range k, (1:ℝ)/((i:ℝ)+1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hconst]
      apply Finset.sum_le_sum
      intro j hj
      have hjnn : (0:ℝ) ≤ (j:ℝ) := by positivity
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    calc (i:ℝ) * ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))
        ≤ (i:ℝ) * ((k:ℝ) * (1/((i:ℝ)+1))) := mul_le_mul_of_nonneg_left hub hi0.le
      _ = (i:ℝ)*(k:ℝ)/((i:ℝ)-(-1)) := by rw [sub_neg_eq_add]; field_simp

/-- The ahead distance limit `i·adist_i(k) → c(k+½)`, `adist_i(k) = c/(2i) + c·Σ_{j<k}1/(i+1+j)`. -/
theorem tendsto_ahead_dist (c : ℝ) (k : ℕ) :
    Tendsto (fun i : ℕ => (i:ℝ) * (c/(2*(i:ℝ)) + c*∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))))
      atTop (𝓝 (c*((k:ℝ)+1/2))) := by
  have hbase := (tendsto_forward_harmonic_sum k).const_mul c
  have hsum : Tendsto (fun i : ℕ => c/2 + c*((i:ℝ)*∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))))
      atTop (𝓝 (c/2 + c*(k:ℝ))) := tendsto_const_nhds.add hbase
  rw [show c*((k:ℝ)+1/2) = c/2 + c*(k:ℝ) by ring]
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  have hi0 : (i:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- The ahead distance lower bound `adist_i(k) ≥ (c/2)(k+½)/i` (`k < i`): each term `1/(i+1+j) ≥ 1/(2i)`
(denominator `≤ 2i`), so the sum is `≥ k/(2i)`. The constant is `c/2`, not `c`: ahead distances are
slightly smaller than `(c/i)(k+½)`. -/
theorem ahead_dist_lb {c : ℝ} (hc : 0 < c) {i k : ℕ} (hik : k < i) :
    ((c/2)/(i:ℝ)) * ((k:ℝ) + 1/2)
      ≤ c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ)) := by
  have hi0 : (0:ℝ) < (i:ℝ) := Nat.cast_pos.mpr (by omega)
  have hsum : (∑ j ∈ Finset.range k, (1:ℝ)/(2*(i:ℝ)))
      ≤ (∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : (j:ℝ) + 1 ≤ (i:ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] at hsum
  have hstep : c * ((k:ℝ)/(2*(i:ℝ))) ≤ c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+1+(j:ℝ)) :=
    mul_le_mul_of_nonneg_left hsum hc.le
  have h1 : ((c/2)/(i:ℝ)) * ((k:ℝ)+1/2) = (c*(2*(k:ℝ)+1))/(4*(i:ℝ)) := by field_simp; ring
  have h2 : c/(2*(i:ℝ)) + c * ((k:ℝ)/(2*(i:ℝ))) = (c*(2*(k:ℝ)+2))/(4*(i:ℝ)) := by field_simp; ring
  have hgoal : ((c/2)/(i:ℝ)) * ((k:ℝ)+1/2) ≤ c/(2*(i:ℝ)) + c * ((k:ℝ)/(2*(i:ℝ))) := by
    rw [h1, h2]; gcongr; nlinarith [hc]
  linarith [hgoal, hstep]

/-- **The ahead-side steepness on the harmonic distances.** The rescaled near-ahead `csch²` sum on the
exact distances `adist_n(k) = c/(2n) + c·Σ_{j<k}1/(n+1+j)` (the `n` nearest ahead poles) converges to
`2π²/c²` — the ahead train's near-pole steepness, via the generalized finite-sum Tannery limit (bound
constant `c/2`) + `tendsto_ahead_dist` + `ahead_dist_lb`. -/
theorem ahead_csch_sum_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        (1/(n:ℝ)^2) * (rcsch ((c/(2*(n:ℝ)) + c*∑ j ∈ Finset.range k, 1/((n:ℝ)+1+(j:ℝ)))/2))^2)
      atTop (𝓝 (2*π^2/c^2)) := by
  exact tendsto_rescaled_csch_sq_finsum_gen hc (by positivity : (0:ℝ) < c/2) (fun n => n) tendsto_id
    (fun k => by
      filter_upwards [eventually_ge_atTop (k+1)] with n hn
      have hn0 : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      have hcn : (0:ℝ) < c/(2*(n:ℝ)) := div_pos hc (by linarith)
      have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range k, 1/((n:ℝ)+1+(j:ℝ)) := by
        apply Finset.sum_nonneg
        intro j _
        have h : (0:ℝ) < (n:ℝ)+1+(j:ℝ) := by
          have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          have h2 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
          linarith
        exact le_of_lt (one_div_pos.mpr h)
      nlinarith [mul_nonneg hc.le hsum])
    (fun n k _ hkn => ahead_dist_lb hc hkn)
    (fun k => tendsto_ahead_dist c k)

end RHTower
end
