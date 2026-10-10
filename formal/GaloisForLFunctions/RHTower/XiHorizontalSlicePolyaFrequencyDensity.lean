import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone
import GaloisForLFunctions.RHTower.XiHorizontalSliceLogConcaveDensity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper

/-!
# `PF_k` slices on a positive proportion of heights, for every `k ≤ 10`

The visibility cone of order `k` at height `t` is `|Re ρ − ½| ≤ tan (π/(2k+2)) |Im ρ − t|`.  It
holds at every height off the shadow `xiShadowScaled κ_k` of the off-line zeros dilated by
`κ_k = cot (π/(2k+2))`, so there the slice coefficients `c_{2n}(t)` form a `PF_k` sequence
(`xiSliceCoeff_pfSeq_of_not_mem_xiShadowScaled`).  The shadow occupies at most `2κ_k μ V + κ_k² μ`
of `[0, V]` when the off-line moment is at most `μ V`.  With the unconditional moment
`μ = 67/1000` (Selberg weights), for every `k ≥ 1` and all large `V`
(`eventually_volume_sliceCoeff_pfSeq_ge_upper`),

  `vol {t ∈ [0, V] : (c_{2n}(t))_n is PF_k} ≥ (1 − (67/500) cot (π/(2k+2))) V − (67/1000) cot² (π/(2k+2))`.

The proportion is `≈ 0.768` for `k = 2` (log-concavity), `≈ 0.677` for `k = 3`, `≈ 0.588` for
`k = 4`, and stays positive up to `k = 10`, where `cot (π/22) < 500/67`
(`eventually_volume_sliceCoeff_pfTen_pos`).  For `k = 11` it is negative: `cot (π/24) > 500/67`.
-/

open Filter Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- Off the `κ`-dilated shadow, with `κ² (1 − cos (π/(k+1))) = 1 + cos (π/(k+1))`, the slice
coefficients form a `PF_k` sequence. -/
theorem xiSliceCoeff_pfSeq_of_not_mem_xiShadowScaled {k : ℕ} (hk : 1 ≤ k) {κ : ℝ}
    (hκ : κ ^ 2 * (1 - Real.cos (Real.pi / ((k : ℝ) + 1))) =
      1 + Real.cos (Real.pi / ((k : ℝ) + 1)))
    {t : ℝ} (ht : t ∉ xiShadowScaled κ) :
    PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re) := by
  refine xiSliceCoeff_pfSeq_of_cone hk fun q => ?_
  have h := cone_of_not_mem_xiShadowScaled ht q
  have h1 : 0 ≤ 1 - Real.cos (Real.pi / ((k : ℝ) + 1)) := by
    linarith [Real.cos_le_one (Real.pi / ((k : ℝ) + 1))]
  have h2 := mul_le_mul_of_nonneg_right h h1
  nlinarith

/-- **`PF_k` slices from an off-line moment bound.** -/
theorem eventually_volume_sliceCoeff_pfSeq_ge_of_moment {k : ℕ} (hk : 1 ≤ k) {κ : ℝ}
    (hκ0 : 0 ≤ κ)
    (hκ : κ ^ 2 * (1 - Real.cos (Real.pi / ((k : ℝ) + 1))) =
      1 + Real.cos (Real.pi / ((k : ℝ) + 1)))
    {μ : ℝ} (hμ : 0 ≤ μ) (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, ENNReal.ofReal ((1 - 2 * κ * μ) * V - κ ^ 2 * μ) ≤
      volume {t ∈ Icc (0 : ℝ) V | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} := by
  filter_upwards [eventually_volume_xiShadowScaled_inter_Icc_le_of_moment hκ0 hmom,
    eventually_ge_atTop 0] with V hV hV0
  have h := ofReal_sub_le_volume_of_not_mem
    (fun t ht => xiSliceCoeff_pfSeq_of_not_mem_xiShadowScaled hk hκ ht) (by positivity) hV
  rwa [show V - (2 * κ * μ * V + κ ^ 2 * μ) = (1 - 2 * κ * μ) * V - κ ^ 2 * μ by ring] at h

/-- `cot (π/(2k+2))² (1 − cos (π/(k+1))) = 1 + cos (π/(k+1))`: the half-angle formulas. -/
theorem cot_sq_mul_one_sub_cos (k : ℕ) :
    Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) ^ 2 * (1 - Real.cos (Real.pi / ((k : ℝ) + 1))) =
      1 + Real.cos (Real.pi / ((k : ℝ) + 1)) := by
  set x := Real.pi / (2 * ((k : ℝ) + 1)) with hx
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2x : Real.pi / ((k : ℝ) + 1) = 2 * x := by
    rw [hx]
    field_simp
  have hxpos : 0 < x := by positivity
  have hxlt : x < Real.pi := by
    rw [hx, div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith
    nlinarith [Real.pi_pos]
  have hs : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hxpos hxlt).ne'
  have hsc := Real.sin_sq_add_cos_sq x
  rw [h2x, Real.cot_eq_cos_div_sin, Real.cos_two_mul, div_pow,
    show 1 - (2 * Real.cos x ^ 2 - 1) = 2 * Real.sin x ^ 2 by linarith]
  field_simp
  ring

/-- `cot (π/(2k+2)) ≥ 0`. -/
theorem cot_pi_div_nonneg (k : ℕ) : 0 ≤ Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) := by
  have hk : (2 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hxpos : 0 < Real.pi / (2 * ((k : ℝ) + 1)) := by positivity
  have hxle : Real.pi / (2 * ((k : ℝ) + 1)) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hk
  rw [Real.cot_eq_cos_div_sin]
  refine div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hxle⟩)
    (Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith [Real.pi_pos])).le

/-- **Unconditional `PF_k` slices on a positive proportion of heights.**  For every `k ≥ 1` and all
large `V`, at heights `t ∈ [0, V]` of total measure at least
`(1 − (67/500) cot (π/(2k+2))) V − (67/1000) cot² (π/(2k+2))`, every Toeplitz minor of order `≤ k`
of the slice coefficients `c_{2n}(t)` (with increasing rows and columns) is nonnegative. -/
theorem eventually_volume_sliceCoeff_pfSeq_ge_upper {k : ℕ} (hk : 1 ≤ k) :
    ∀ᶠ V in atTop, ENNReal.ofReal
        ((1 - 2 * Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) * (67 / 1000)) * V -
          Real.cot (Real.pi / (2 * ((k : ℝ) + 1))) ^ 2 * (67 / 1000)) ≤
      volume {t ∈ Icc (0 : ℝ) V | PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)} :=
  eventually_volume_sliceCoeff_pfSeq_ge_of_moment hk (cot_pi_div_nonneg k)
    (cot_sq_mul_one_sub_cos k) (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper

/-- `cot (π/22) < 500/67`, from `sin x > x − x³/6` and `3.14 < π < 3.15`. -/
theorem cot_pi_div_twentyTwo_lt :
    Real.cot (Real.pi / (2 * (((10 : ℕ) : ℝ) + 1))) < 500 / 67 := by
  rw [show (2 * (((10 : ℕ) : ℝ) + 1)) = 22 by norm_num, Real.cot_eq_cos_div_sin]
  set x := Real.pi / 22 with hx
  have hlo : 3.14 / 22 < x := div_lt_div_of_pos_right Real.pi_gt_d2 (by norm_num)
  have hhi : x < 3.15 / 22 := div_lt_div_of_pos_right Real.pi_lt_d2 (by norm_num)
  have hx0 : 0 < x := by linarith
  have hs := Real.sin_gt_sub_cube hx0
  have h3 : x ^ 3 < (3.15 / 22 : ℝ) ^ 3 := pow_lt_pow_left₀ hhi hx0.le (by norm_num)
  have hsin : (67 / 500 : ℝ) < Real.sin x := by
    norm_num at h3 hlo
    linarith
  have hc := Real.cos_le_one x
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **`PF_10` slices on a positive proportion of heights, unconditionally.** -/
theorem eventually_volume_sliceCoeff_pfTen_pos :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ᶠ V in atTop, ENNReal.ofReal (c * V - C) ≤
      volume {t ∈ Icc (0 : ℝ) V | PFSeq 10 (fun n => (xiSliceCoeff t (2 * n)).re)} := by
  refine ⟨_, ?_, _, eventually_volume_sliceCoeff_pfSeq_ge_upper (k := 10) (by norm_num)⟩
  have := cot_pi_div_twentyTwo_lt
  linarith

end

end RHTower.DeBruijn
