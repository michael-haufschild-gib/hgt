import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.PSeries

/-!
# The Hurwitz zeta function far to the right of the critical strip

For a shift `a ∈ (0,1)` the Hurwitz series `∑_{n ≥ 0} (n + a)^{-w}` is dominated by
its first term `a^{-w}`: normalising by `a^{w}` turns the series into
`∑_{n ≥ 0} (a/(n+a))^{w}`, whose leading term is one and whose tail is bounded by
`a^{Re w}` times a fixed constant.

So `a^{w} ζ(w, a) → 1` as `Re w → ∞`, which says that the Hurwitz zeta function
grows exactly like the geometric factor `a^{-Re w}` along a rightward shift.  That
geometric rate is the cusp gap of the standard twist at the shift `a`.
-/

open Complex HurwitzZeta Filter Topology Set

namespace RHTower

section HurwitzRight

variable {a : ℝ}

/-- The ratios of the Hurwitz series to its first term. -/
noncomputable def hurwitzRatio (a : ℝ) (n : ℕ) : ℝ := a / ((n : ℝ) + a)

theorem hurwitzRatio_zero (ha : 0 < a) : hurwitzRatio a 0 = 1 := by
  rw [hurwitzRatio, Nat.cast_zero, zero_add, div_self ha.ne']

theorem natCast_add_pos (ha : 0 < a) (n : ℕ) : (0 : ℝ) < (n : ℝ) + a := by
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem hurwitzRatio_pos (ha : 0 < a) (n : ℕ) : 0 < hurwitzRatio a n :=
  div_pos ha (natCast_add_pos ha n)

theorem hurwitzRatio_succ_le (ha : 0 < a) (n : ℕ) :
    hurwitzRatio a (n + 1) ≤ a / ((n : ℝ) + 1) := by
  rw [hurwitzRatio]
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + a := by push_cast; linarith
  exact div_le_div_of_nonneg_left ha.le h1 h2

/-- The normalising identity: dividing the Hurwitz series by its first term
replaces the summands by their ratios. -/
theorem cpow_hurwitzRatio (ha : 0 < a) (n : ℕ) (w : ℂ) :
    ((hurwitzRatio a n : ℝ) : ℂ) ^ w = (a : ℂ) ^ w * (1 / ((n : ℂ) + (a : ℂ)) ^ w) := by
  have hy : (0 : ℝ) < (n : ℝ) + a := natCast_add_pos ha n
  have hxy : hurwitzRatio a n * ((n : ℝ) + a) = a := by
    rw [hurwitzRatio, div_mul_cancel₀ _ hy.ne']
  have hcast : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
  have hne : ((((n : ℝ) + a : ℝ)) : ℂ) ^ w ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact_mod_cast hy.ne'
  have hmul : ((hurwitzRatio a n : ℝ) : ℂ) ^ w * ((((n : ℝ) + a : ℝ)) : ℂ) ^ w
      = (a : ℂ) ^ w := by
    rw [← Complex.mul_cpow_ofReal_nonneg (hurwitzRatio_pos ha n).le hy.le,
      ← Complex.ofReal_mul, hxy]
  rw [hcast, mul_one_div, eq_div_iff hne]
  exact hmul

/-- The normalized Hurwitz series. -/
theorem hasSum_hurwitzRatio (ha : 0 < a) (ha1 : a < 1) {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => ((hurwitzRatio a n : ℝ) : ℂ) ^ w)
      ((a : ℂ) ^ w * hurwitzZeta ((a : ℝ) : UnitAddCircle) w) := by
  have hbase := hasSum_hurwitzZeta_of_one_lt_re (a := a) ⟨ha.le, ha1.le⟩ hw
  have hmul := hbase.mul_left ((a : ℂ) ^ w)
  refine hmul.congr_fun fun n => ?_
  rw [cpow_hurwitzRatio ha n w]

/-- The comparison constant. -/
noncomputable def hurwitzTailConst : ℝ := ∑' n : ℕ, (((n : ℝ) + 1)) ^ (-2 : ℝ)

theorem summable_shifted_rpow_neg_two :
    Summable (fun n : ℕ => (((n : ℝ) + 1)) ^ (-2 : ℝ)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-2 : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
  push_cast
  ring_nf

theorem hurwitzTailConst_nonneg : 0 ≤ hurwitzTailConst :=
  tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _

/-- **The tail of the normalized Hurwitz series is geometrically small.** -/
theorem norm_normalizedHurwitz_sub_one_le (ha : 0 < a) (ha1 : a < 1) {w : ℂ}
    (hw : 2 ≤ w.re) :
    ‖(a : ℂ) ^ w * hurwitzZeta ((a : ℝ) : UnitAddCircle) w - 1‖
      ≤ a ^ w.re * hurwitzTailConst := by
  have hw1 : 1 < w.re := by linarith
  have hsum := hasSum_hurwitzRatio ha ha1 hw1
  set S : ℂ := (a : ℂ) ^ w * hurwitzZeta ((a : ℝ) : UnitAddCircle) w with hS
  have hzero : ((hurwitzRatio a 0 : ℝ) : ℂ) ^ w = 1 := by
    rw [hurwitzRatio_zero ha, Complex.ofReal_one, Complex.one_cpow]
  have hshift : HasSum (fun n : ℕ => ((hurwitzRatio a (n + 1) : ℝ) : ℂ) ^ w) (S - 1) := by
    refine (hasSum_nat_add_iff
      (f := fun n : ℕ => ((hurwitzRatio a n : ℝ) : ℂ) ^ w) 1).mpr ?_
    simpa [hzero] using hsum
  -- termwise norm bound
  have hbound : ∀ n : ℕ, ‖((hurwitzRatio a (n + 1) : ℝ) : ℂ) ^ w‖
      ≤ a ^ w.re * (((n : ℝ) + 1)) ^ (-2 : ℝ) := by
    intro n
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hurwitzRatio_pos ha (n + 1))]
    have hle : hurwitzRatio a (n + 1) ≤ a / ((n : ℝ) + 1) := hurwitzRatio_succ_le ha n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : (hurwitzRatio a (n + 1)) ^ w.re ≤ (a / ((n : ℝ) + 1)) ^ w.re :=
      Real.rpow_le_rpow (hurwitzRatio_pos ha (n + 1)).le hle (by linarith)
    have hdiv : a / ((n : ℝ) + 1) ≤ a := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have h2 : (a / ((n : ℝ) + 1)) ^ w.re
        = a ^ w.re * (((n : ℝ) + 1)) ^ (-w.re) := by
      rw [Real.div_rpow ha.le hpos.le, Real.rpow_neg hpos.le, div_eq_mul_inv]
    have h3 : (((n : ℝ) + 1)) ^ (-w.re) ≤ (((n : ℝ) + 1)) ^ (-2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h4 : (0 : ℝ) ≤ a ^ w.re := Real.rpow_nonneg ha.le _
    calc (hurwitzRatio a (n + 1)) ^ w.re ≤ (a / ((n : ℝ) + 1)) ^ w.re := h1
      _ = a ^ w.re * (((n : ℝ) + 1)) ^ (-w.re) := h2
      _ ≤ a ^ w.re * (((n : ℝ) + 1)) ^ (-2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left h3 h4
  have hnormsum : Summable (fun n : ℕ => ‖((hurwitzRatio a (n + 1) : ℝ) : ℂ) ^ w‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound ?_
    exact summable_shifted_rpow_neg_two.mul_left _
  rw [← hshift.tsum_eq]
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  refine le_trans (Summable.tsum_le_tsum hbound hnormsum
    (summable_shifted_rpow_neg_two.mul_left _)) ?_
  rw [hurwitzTailConst, ← tsum_mul_left]

/-- **The Hurwitz zeta function grows exactly geometrically to the right.** -/
theorem tendsto_normalizedHurwitz (ha : 0 < a) (ha1 : a < 1) (w₀ : ℂ) :
    Tendsto (fun k : ℕ => (a : ℂ) ^ (w₀ + (k : ℂ))
        * hurwitzZeta ((a : ℝ) : UnitAddCircle) (w₀ + (k : ℂ))) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hre : ∀ k : ℕ, (w₀ + (k : ℂ)).re = w₀.re + (k : ℝ) := by
    intro k
    simp
  have hgeom : Tendsto (fun k : ℕ => a ^ (w₀.re + (k : ℝ)) * hurwitzTailConst)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => a ^ (k : ℕ)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1
    have hsplit : ∀ k : ℕ, a ^ (w₀.re + (k : ℝ)) * hurwitzTailConst
        = (a ^ w₀.re * hurwitzTailConst) * a ^ (k : ℕ) := by
      intro k
      rw [Real.rpow_add ha, ← Real.rpow_natCast a k]
      ring
    have := hpow.const_mul (a ^ w₀.re * hurwitzTailConst)
    rw [mul_zero] at this
    exact this.congr fun k => (hsplit k).symm
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hgeom
  filter_upwards [eventually_ge_atTop (⌈2 - w₀.re⌉₊ + 1)] with k hk
  have hkR : ((⌈2 - w₀.re⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.le_of_succ_le hk
  have h2 : 2 ≤ (w₀ + (k : ℂ)).re := by
    rw [hre k]
    have hc := Nat.le_ceil (2 - w₀.re)
    linarith
  have hb := norm_normalizedHurwitz_sub_one_le ha ha1 h2
  rwa [hre k] at hb

end HurwitzRight

end RHTower
