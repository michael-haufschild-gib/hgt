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
    (hpos : ∀ n, 0 < dist n) (hlim : Tendsto (fun n : ℕ => (n : ℝ) * dist n) atTop (𝓝 L)) :
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
    · filter_upwards with n
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (half_pos (hpos n)).ne'
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
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0 : dist n ≠ 0 := ne_of_gt (hpos n)
  have hs0 : Real.sinh (dist n / 2) ≠ 0 := ne_of_gt (sinh_pos_of_pos (half_pos (hpos n)))
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
      (fun n => hpos n k) (hlim k)
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

end RHTower
end
