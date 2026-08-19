import Mathlib

/-!
# `(1+δ)`-adic blocks

A variable restricted to `[z₀, z₁]` is split into the geometric blocks
`(z₀(1+δ)^j, z₀(1+δ)^{j+1}]`.  The index of the block containing `q` is
`⌊log(q/z₀)/log(1+δ)⌋`, the number of blocks is at most `2log(z₁/z₀)/δ + 1`, and any sum over the
variable splits over the blocks.  This is the subdivision Matomäki–Teräväinen use throughout, with
`δ = δ_A = (log X)^{-10A}`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The index of the `(1+δ)`-adic block above `z₀` that contains `q`. -/
def adicIndex (δ z₀ q : ℝ) : ℕ := ⌊Real.log (q / z₀) / Real.log (1 + δ)⌋₊

/-- **The block containing `q`.** -/
theorem adicIndex_block {δ z₀ q : ℝ} (hδ : 0 < δ) (hz₀ : 0 < z₀) (hq : z₀ ≤ q) :
    z₀ * (1 + δ) ^ (adicIndex δ z₀ q) ≤ q ∧ q < z₀ * (1 + δ) ^ (adicIndex δ z₀ q + 1) := by
  have hlog : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le hz₀ hq
  have hratio : 1 ≤ q / z₀ := (one_le_div hz₀).2 hq
  have hqz : (0 : ℝ) < q / z₀ := by positivity
  have ht0 : 0 ≤ Real.log (q / z₀) := Real.log_nonneg hratio
  set j : ℕ := adicIndex δ z₀ q with hj
  have ht0' : (0 : ℝ) ≤ Real.log (q / z₀) / Real.log (1 + δ) := by positivity
  have hjt : (j : ℝ) ≤ Real.log (q / z₀) / Real.log (1 + δ) := by
    rw [hj, adicIndex]; exact Nat.floor_le ht0'
  have htj : Real.log (q / z₀) / Real.log (1 + δ) < (j : ℝ) + 1 := by
    rw [hj, adicIndex]; exact Nat.lt_floor_add_one _
  have hbase : (0 : ℝ) < 1 + δ := by linarith
  constructor
  · have hlogle : Real.log ((1 + δ) ^ j) ≤ Real.log (q / z₀) := by
      rw [Real.log_pow]
      rw [le_div_iff₀ hlog] at hjt
      exact hjt
    have hpos : (0 : ℝ) < (1 + δ) ^ j := by positivity
    have hstep : (1 + δ) ^ j ≤ q / z₀ := by
      calc (1 + δ) ^ j = Real.exp (Real.log ((1 + δ) ^ j)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (Real.log (q / z₀)) := Real.exp_le_exp.2 hlogle
        _ = q / z₀ := Real.exp_log hqz
    calc z₀ * (1 + δ) ^ j ≤ z₀ * (q / z₀) := by nlinarith [hstep, hz₀]
      _ = q := by field_simp
  · have hloglt : Real.log (q / z₀) < Real.log ((1 + δ) ^ (j + 1)) := by
      rw [Real.log_pow]
      rw [div_lt_iff₀ hlog] at htj
      push_cast
      linarith [htj]
    have hpos : (0 : ℝ) < (1 + δ) ^ (j + 1) := by positivity
    have hstep : q / z₀ < (1 + δ) ^ (j + 1) := by
      calc q / z₀ = Real.exp (Real.log (q / z₀)) := (Real.exp_log hqz).symm
        _ < Real.exp (Real.log ((1 + δ) ^ (j + 1))) := Real.exp_lt_exp.2 hloglt
        _ = (1 + δ) ^ (j + 1) := Real.exp_log hpos
    have : q = z₀ * (q / z₀) := by field_simp
    calc q = z₀ * (q / z₀) := this
      _ < z₀ * (1 + δ) ^ (j + 1) := by nlinarith [hstep, hz₀]

/-- The index is monotone in the variable. -/
theorem adicIndex_le_of_le {δ z₀ q q' : ℝ} (hδ : 0 < δ) (hz₀ : 0 < z₀) (hq : z₀ ≤ q)
    (hqq : q ≤ q') : adicIndex δ z₀ q ≤ adicIndex δ z₀ q' := by
  have hlog : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hq0 : 0 < q := lt_of_lt_of_le hz₀ hq
  refine Nat.floor_le_floor ?_
  refine div_le_div_of_nonneg_right ?_ hlog.le
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hqq hz₀.le)

/-- **The number of blocks.**  For `δ ≤ 1` the block index is at most `2log(z₁/z₀)/δ`. -/
theorem adicIndex_le_div {δ z₀ z₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz₀ : 0 < z₀) (hz : z₀ ≤ z₁) :
    (adicIndex δ z₀ z₁ : ℝ) ≤ 2 * Real.log (z₁ / z₀) / δ := by
  have hlog : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hratio : 1 ≤ z₁ / z₀ := (one_le_div hz₀).2 hz
  have ht0 : 0 ≤ Real.log (z₁ / z₀) := Real.log_nonneg hratio
  -- `log(1+δ) ≥ δ/(1+δ) ≥ δ/2`
  have hlow : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have h1 : (0 : ℝ) < 1 + δ := by linarith
    have h2 := Real.add_one_le_exp (-Real.log (1 + δ))
    have h3 : Real.exp (-Real.log (1 + δ)) = 1 / (1 + δ) := by
      rw [Real.exp_neg, Real.exp_log h1, one_div]
    rw [h3] at h2
    have h4 : 1 / (1 + δ) = 1 - δ / (1 + δ) := by
      have hone : 1 / (1 + δ) + δ / (1 + δ) = 1 := by
        rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h1), div_eq_one_iff_eq (by positivity)]
        ring
      linarith
    linarith [h2, h4]
  have hhalf : δ / 2 ≤ Real.log (1 + δ) := by
    have h1 : δ / 2 ≤ δ / (1 + δ) := by
      refine div_le_div_of_nonneg_left hδ.le (by linarith) (by linarith)
    linarith
  have hfl : (adicIndex δ z₀ z₁ : ℝ) ≤ Real.log (z₁ / z₀) / Real.log (1 + δ) := by
    rw [adicIndex]
    exact Nat.floor_le (by positivity)
  refine hfl.trans ?_
  rw [div_le_div_iff₀ hlog (by positivity)]
  nlinarith [hhalf, ht0, hδ]

/-- **Every sum over a variable splits over its blocks.** -/
theorem sum_adic_blocks {δ z₀ : ℝ} {J : ℕ} (S : Finset ℕ) (f : ℕ → ℝ)
    (hmaps : ∀ q ∈ S, adicIndex δ z₀ ((q : ℕ) : ℝ) ∈ Finset.range J) :
    ∑ j ∈ Finset.range J, ∑ q ∈ S.filter (fun q => adicIndex δ z₀ ((q : ℕ) : ℝ) = j), f q
      = ∑ q ∈ S, f q :=
  Finset.sum_fiberwise_of_maps_to hmaps f

/-- The block index of every element of a bounded set fits below `adicIndex δ z₀ z₁ + 1`. -/
theorem adicIndex_mem_range {δ z₀ z₁ : ℝ} (hδ : 0 < δ) (hz₀ : 0 < z₀) {S : Finset ℕ}
    (hS : ∀ q ∈ S, z₀ ≤ ((q : ℕ) : ℝ) ∧ ((q : ℕ) : ℝ) ≤ z₁) :
    ∀ q ∈ S, adicIndex δ z₀ ((q : ℕ) : ℝ) ∈ Finset.range (adicIndex δ z₀ z₁ + 1) := by
  intro q hq
  obtain ⟨h1, h2⟩ := hS q hq
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (adicIndex_le_of_le hδ hz₀ h1 h2))

/-! ## Dyadic blocks of an initial segment -/

/-- **A finite sum splits over its dyadic blocks.**  The block index of `n` is `⌊log₂ n⌋`, and the
blocks of `[1, M]` are indexed by `j ≤ ⌊log₂ M⌋`. -/
theorem sum_Icc_eq_sum_dyadic_blocks {M : ℕ} (f : ℕ → ℂ) :
    ∑ j ∈ Finset.range (Nat.log 2 M + 1),
        ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j), f n
      = ∑ n ∈ Finset.Icc 1 M, f n := by
  classical
  refine Finset.sum_fiberwise_of_maps_to (fun n hn => ?_) f
  rw [Finset.mem_Icc] at hn
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact Nat.log_mono_right hn.2

/-- **The triangle inequality over the dyadic blocks.**  This is the interface a two-regime
pointwise estimate is summed through: each block carries its own bound, and there are
`⌊log₂ M⌋ + 1` of them. -/
theorem norm_sum_Icc_le_sum_dyadic_blocks {M : ℕ} (f : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 M, f n‖
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j), f n‖ := by
  classical
  rw [← sum_Icc_eq_sum_dyadic_blocks f]
  exact norm_sum_le _ _

/-- Every element of the `j`-th dyadic block of `[1, M]` lies in `[2^j, 2^{j+1})`. -/
theorem mem_dyadic_block {M j n : ℕ} (hn : n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j)) :
    2 ^ j ≤ n ∧ n < 2 ^ (j + 1) := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, -⟩, hlog⟩ := hn
  constructor
  · rw [← hlog]
    exact Nat.pow_log_le_self 2 (by omega)
  · rw [← hlog]
    exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- **Summing a two-parameter per-block bound over the dyadic blocks.**  A bound of the shape
`a + b·2^j` on the `j`-th block — which is what the two regimes of the logarithmic phase produce,
with `a ≍ √t` and `b ≍ 1/√t` — sums to `(⌊log₂ M⌋ + 1)·a + 2b·M`: the first term is where
Halász–Montgomery's `log T` comes from, the second is the `N/√T`. -/
theorem norm_sum_Icc_le_of_dyadic_bounds {M : ℕ} (hM : 1 ≤ M) (f : ℕ → ℂ) {a b : ℝ}
    (hb : 0 ≤ b)
    (hblk : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.log 2 n = j), f n‖ ≤ a + b * 2 ^ j) :
    ‖∑ n ∈ Finset.Icc 1 M, f n‖ ≤ ((Nat.log 2 M : ℝ) + 1) * a + 2 * b * (M : ℝ) := by
  classical
  refine le_trans (norm_sum_Icc_le_sum_dyadic_blocks f) ?_
  refine le_trans (Finset.sum_le_sum hblk) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.card_range,
    nsmul_eq_mul]
  have hgeom : ∑ j ∈ Finset.range (Nat.log 2 M + 1), (2 : ℝ) ^ j
      = (2 : ℝ) ^ (Nat.log 2 M + 1) - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  rw [hgeom]
  have hpow : (2 : ℝ) ^ (Nat.log 2 M) ≤ (M : ℝ) := by
    have := Nat.pow_log_le_self 2 (by omega : M ≠ 0)
    exact_mod_cast this
  have hstep : (2 : ℝ) ^ (Nat.log 2 M + 1) - 1 ≤ 2 * (M : ℝ) := by
    rw [pow_succ]
    nlinarith [hpow]
  have hcast : ((Nat.log 2 M + 1 : ℕ) : ℝ) = (Nat.log 2 M : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  nlinarith [hstep, hb]

end

end RHTower.Sieve
