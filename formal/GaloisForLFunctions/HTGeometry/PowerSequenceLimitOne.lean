import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Powers of a sequence tending to one

If `r j → 1` and the exponent grows slowly enough that `m j · (r j − 1) → 0`, then `r j ^ m j → 1`.
The two-sided exponential bound `exp(−m(1/r−1)) ≤ r^m ≤ exp(m(r−1))` gives the squeeze.

A family of such terms, one for each of infinitely many fixed data, therefore has partial sums
exceeding any bound: the total sum diverges even though each summand stays bounded.  This is the
mechanism by which an absolute-value majorant of a spectral-radius separation fails at a scale
where the exponent is small compared with the separation.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The two-sided exponential squeeze: a slowly growing power of a sequence tending to one tends
to one. -/
theorem tendsto_pow_of_tendsto_one {r : ℕ → ℝ} {m : ℕ → ℕ}
    (hr : Tendsto r atTop (nhds 1))
    (hmr : Tendsto (fun j => (m j : ℝ) * (r j - 1)) atTop (nhds 0)) :
    Tendsto (fun j => (r j) ^ (m j)) atTop (nhds 1) := by
  have hposev : ∀ᶠ j in atTop, 0 < r j := hr.eventually_const_lt (by norm_num)
  have hupper : ∀ j, 0 < r j → (r j) ^ (m j) ≤ Real.exp ((m j : ℝ) * (r j - 1)) := by
    intro j hpos
    have h1 : r j ≤ Real.exp (r j - 1) := by
      have h := Real.add_one_le_exp (r j - 1)
      linarith
    calc (r j) ^ (m j) ≤ (Real.exp (r j - 1)) ^ (m j) :=
          pow_le_pow_left₀ hpos.le h1 _
      _ = Real.exp ((m j : ℝ) * (r j - 1)) := by rw [← Real.exp_nat_mul]
  have hlower : ∀ j, 0 < r j → Real.exp (-((m j : ℝ) * ((r j)⁻¹ - 1))) ≤ (r j) ^ (m j) := by
    intro j hpos
    have hinv : (r j)⁻¹ ≤ Real.exp ((r j)⁻¹ - 1) := by
      have h := Real.add_one_le_exp ((r j)⁻¹ - 1)
      linarith
    have h2 : ((r j)⁻¹) ^ (m j) ≤ Real.exp ((m j : ℝ) * ((r j)⁻¹ - 1)) := by
      calc ((r j)⁻¹) ^ (m j) ≤ (Real.exp ((r j)⁻¹ - 1)) ^ (m j) :=
            pow_le_pow_left₀ (inv_pos.2 hpos).le hinv _
        _ = Real.exp ((m j : ℝ) * ((r j)⁻¹ - 1)) := by rw [← Real.exp_nat_mul]
    have hrp : (0 : ℝ) < (r j) ^ (m j) := pow_pos hpos _
    rw [inv_pow] at h2
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) hrp]
    exact h2
  have hinvlim : Tendsto (fun j => (m j : ℝ) * ((r j)⁻¹ - 1)) atTop (nhds 0) := by
    have hne : ∀ᶠ j in atTop, r j ≠ 0 := hposev.mono fun j hj => hj.ne'
    have hrinv : Tendsto (fun j => (r j)⁻¹) atTop (nhds 1) := by
      simpa using hr.inv₀ one_ne_zero
    have hprod : Tendsto (fun j => -((m j : ℝ) * (r j - 1)) * (r j)⁻¹) atTop (nhds (-0 * 1)) :=
      (hmr.neg).mul hrinv
    rw [neg_zero, zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [hne] with j hj
    field_simp
    ring
  have hexp1 : Tendsto (fun j => Real.exp ((m j : ℝ) * (r j - 1))) atTop (nhds 1) := by
    have h : Tendsto (fun j => Real.exp ((m j : ℝ) * (r j - 1))) atTop (nhds (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp hmr
    rwa [Real.exp_zero] at h
  have hnegl : Tendsto (fun j => -((m j : ℝ) * ((r j)⁻¹ - 1))) atTop (nhds 0) := by
    simpa using hinvlim.neg
  have hexp2 : Tendsto (fun j => Real.exp (-((m j : ℝ) * ((r j)⁻¹ - 1)))) atTop (nhds 1) := by
    have h : Tendsto (fun j => Real.exp (-((m j : ℝ) * ((r j)⁻¹ - 1)))) atTop
        (nhds (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp hnegl
    rwa [Real.exp_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hexp2 hexp1 ?_ ?_
  · filter_upwards [hposev] with j hj
    exact hlower j hj
  · filter_upwards [hposev] with j hj
    exact hupper j hj

/-- **Divergence from partial sums.**  A family whose every fixed member tends to one has partial
sums exceeding any bound, so any majorant of all of them tends to infinity. -/
theorem tendsto_atTop_of_forall_partial_sum {T : ℕ → ℕ → ℝ} {S : ℕ → ℝ}
    (h1 : ∀ q, Tendsto (fun j => T j q) atTop (nhds 1))
    (hS : ∀ j M, ∑ q ∈ Finset.range M, T j q ≤ S j) :
    Tendsto S atTop atTop := by
  refine tendsto_atTop.2 fun C => ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, C ≤ (M : ℝ) / 2 := by
    obtain ⟨M, hM⟩ := exists_nat_ge (2 * C)
    exact ⟨M, by linarith⟩
  have hev : ∀ q ∈ Finset.range M, ∀ᶠ j in atTop, (1 : ℝ) / 2 ≤ T j q := by
    intro q _
    have hlt : (1 : ℝ) / 2 < 1 := by norm_num
    exact (h1 q).eventually_const_le hlt
  have hall : ∀ᶠ j in atTop, ∀ q ∈ Finset.range M, (1 : ℝ) / 2 ≤ T j q :=
    (Filter.eventually_all_finset _).2 hev
  filter_upwards [hall] with j hj
  have hsum : (M : ℝ) / 2 ≤ ∑ q ∈ Finset.range M, T j q := by
    have hconst : ∑ _q ∈ Finset.range M, (1 : ℝ) / 2 = (M : ℝ) / 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    calc (M : ℝ) / 2 = ∑ _q ∈ Finset.range M, (1 : ℝ) / 2 := hconst.symm
      _ ≤ ∑ q ∈ Finset.range M, T j q := Finset.sum_le_sum hj
  linarith [hS j M, hsum, hM]

/-! ## The absolute-divisor majorant -/

open Complex

/-- Each fixed divisor copy contributes a term tending to one. -/
theorem tendsto_norm_ratio_pow_one {y a : ℕ → ℝ} {m : ℕ → ℕ} (ζ : ℂ)
    (hy : Tendsto y atTop atTop) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ j, |a j| ≤ A)
    (hm : Tendsto (fun j => (m j : ℝ) / y j) atTop (nhds 0)) :
    Tendsto (fun j => ‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖ ^ (m j)) atTop (nhds 1) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = A + ‖ζ‖ + 1 := ⟨_, rfl⟩
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; have := norm_nonneg ζ; linarith
  have hev : ∀ᶠ j in atTop, 2 * B ≤ y j := hy.eventually_ge_atTop (2 * B)
  have hnormy : ∀ j, ‖((y j : ℝ) : ℂ)‖ = |y j| := fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hkey : ∀ᶠ j in atTop,
      |‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖ - 1| ≤ 2 * B / y j := by
    filter_upwards [hev] with j hj
    have hypos : 0 < y j := by linarith
    have hyabs : ‖((y j : ℝ) : ℂ)‖ = y j := by rw [hnormy, abs_of_pos hypos]
    have hlow : y j - ‖ζ‖ ≤ ‖(y j : ℂ) + ζ‖ := by
      have h := norm_sub_norm_le (((y j : ℝ) : ℂ)) (-ζ)
      rw [hyabs, norm_neg, sub_neg_eq_add] at h
      exact h
    have hz : ‖ζ‖ ≤ B - 1 := by rw [hB]; linarith
    have hden : B ≤ ‖(y j : ℂ) + ζ‖ := by linarith
    have hhalf : y j / 2 ≤ ‖(y j : ℂ) + ζ‖ := by linarith
    have hdenpos : 0 < ‖(y j : ℂ) + ζ‖ := lt_of_lt_of_le (by linarith) hden
    have hnum : ‖((y j : ℂ) - (a j : ℂ)) - ((y j : ℂ) + ζ)‖ ≤ B := by
      have heq : ((y j : ℂ) - (a j : ℂ)) - ((y j : ℂ) + ζ) = -((a j : ℂ) + ζ) := by ring
      rw [heq, norm_neg]
      have h1 : ‖((a j : ℝ) : ℂ)‖ = |a j| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have h2 := norm_add_le (((a j : ℝ) : ℂ)) ζ
      rw [h1] at h2
      have h3 := ha j
      rw [hB]
      linarith
    have hdiff : |‖(y j : ℂ) - (a j : ℂ)‖ - ‖(y j : ℂ) + ζ‖| ≤ B :=
      le_trans (abs_norm_sub_norm_le _ _) hnum
    have hratio : ‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖
        = ‖(y j : ℂ) - (a j : ℂ)‖ / ‖(y j : ℂ) + ζ‖ := norm_div _ _
    rw [hratio]
    have hsub : ‖(y j : ℂ) - (a j : ℂ)‖ / ‖(y j : ℂ) + ζ‖ - 1
        = (‖(y j : ℂ) - (a j : ℂ)‖ - ‖(y j : ℂ) + ζ‖) / ‖(y j : ℂ) + ζ‖ := by
      field_simp
    rw [hsub, abs_div, abs_of_pos hdenpos]
    have hbound : B / ‖(y j : ℂ) + ζ‖ ≤ 2 * B / y j := by
      rw [div_le_div_iff₀ hdenpos hypos]
      nlinarith [hhalf, hB1]
    calc |‖(y j : ℂ) - (a j : ℂ)‖ - ‖(y j : ℂ) + ζ‖| / ‖(y j : ℂ) + ζ‖
        ≤ B / ‖(y j : ℂ) + ζ‖ := by gcongr
      _ ≤ 2 * B / y j := hbound
  have hBy : Tendsto (fun j => 2 * B / y j) atTop (nhds 0) := by
    have h := hy.inv_tendsto_atTop
    have h2 := h.const_mul (2 * B)
    simpa [div_eq_mul_inv] using h2
  have hr1 : Tendsto (fun j => ‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖) atTop (nhds 1) := by
    rw [← sub_zero (1 : ℝ)]
    refine tendsto_sub_nhds_zero_iff.1 ?_
    refine squeeze_zero_norm' ?_ hBy
    filter_upwards [hkey] with j hj
    simpa [Real.norm_eq_abs] using hj
  have hmr : Tendsto
      (fun j => (m j : ℝ) * (‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖ - 1)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun j => 2 * B * ((m j : ℝ) / y j)) atTop (nhds 0))
    · filter_upwards [hkey, hev] with j hj hj2
      have hypos : 0 < y j := by linarith
      have hmnn : (0 : ℝ) ≤ (m j : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmnn]
      calc (m j : ℝ) * |‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ)‖ - 1|
          ≤ (m j : ℝ) * (2 * B / y j) := by
            exact mul_le_mul_of_nonneg_left hj hmnn
        _ = 2 * B * ((m j : ℝ) / y j) := by ring
    · have := hm.const_mul (2 * B)
      simpa using this
  exact tendsto_pow_of_tendsto_one hr1 hmr

/-- **(MPW.18) The absolute-divisor majorant diverges.**  When the exponent is small compared with
the aperture, every fixed divisor copy contributes a term tending to one, so any majorant of the
partial sums tends to infinity. -/
theorem tendsto_atTop_absoluteDivisorSum {y a : ℕ → ℝ} {m : ℕ → ℕ} (ζ : ℕ → ℂ) {S : ℕ → ℝ}
    (hy : Tendsto y atTop atTop) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ j, |a j| ≤ A)
    (hm : Tendsto (fun j => (m j : ℝ) / y j) atTop (nhds 0))
    (hS : ∀ j M, ∑ q ∈ Finset.range M,
      ‖((y j : ℂ) - (a j : ℂ)) / ((y j : ℂ) + ζ q)‖ ^ (m j) ≤ S j) :
    Tendsto S atTop atTop :=
  tendsto_atTop_of_forall_partial_sum
    (fun q => tendsto_norm_ratio_pow_one (ζ q) hy hA ha hm) hS

/-- **(GJRS.30) The hard-edge scale factor.**  With bounded shifts and an exponent small compared
with the centre, `(y/(y+u))^m → 1`. -/
theorem tendsto_centerRatio_pow_one {u y : ℕ → ℝ} {m : ℕ → ℕ} {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ j, |u j| ≤ U) (hy : Tendsto y atTop atTop)
    (hm : Tendsto (fun j => (m j : ℝ) / y j) atTop (nhds 0)) :
    Tendsto (fun j => (y j / (y j + u j)) ^ (m j)) atTop (nhds 1) := by
  have hev : ∀ᶠ j in atTop, 2 * (U + 1) ≤ y j := hy.eventually_ge_atTop _
  have hbound : ∀ᶠ j in atTop, |y j / (y j + u j) - 1| ≤ 2 * U / y j := by
    filter_upwards [hev] with j hj
    have hUj := hU j
    have hupos : |u j| ≤ U := hUj
    have hu1 : -U ≤ u j := by
      have := neg_abs_le (u j)
      linarith
    have hypos : (0 : ℝ) < y j := by linarith
    have hden : y j / 2 ≤ y j + u j := by linarith
    have hdenpos : (0 : ℝ) < y j + u j := by linarith
    have hdiff : y j / (y j + u j) - 1 = -(u j) / (y j + u j) := by
      field_simp
      ring
    rw [hdiff, abs_div, abs_neg, abs_of_pos hdenpos]
    rw [div_le_div_iff₀ hdenpos hypos]
    nlinarith [hupos, hypos, hden, abs_nonneg (u j)]
  have hbig : Tendsto (fun j => 2 * U / y j) atTop (nhds 0) := by
    have h := hy.inv_tendsto_atTop
    have h2 := h.const_mul (2 * U)
    simpa [div_eq_mul_inv] using h2
  have hr1 : Tendsto (fun j => y j / (y j + u j)) atTop (nhds 1) := by
    rw [← sub_zero (1 : ℝ)]
    refine tendsto_sub_nhds_zero_iff.1 ?_
    refine squeeze_zero_norm' ?_ hbig
    filter_upwards [hbound] with j hj
    simpa [Real.norm_eq_abs] using hj
  have hmr : Tendsto (fun j => (m j : ℝ) * (y j / (y j + u j) - 1)) atTop (nhds 0) := by
    have hub : Tendsto (fun j => 2 * U * ((m j : ℝ) / y j)) atTop (nhds 0) := by
      have h := hm.const_mul (2 * U)
      simpa using h
    refine squeeze_zero_norm' ?_ hub
    filter_upwards [hbound] with j hj
    have hk0 : (0 : ℝ) ≤ (m j : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    calc (m j : ℝ) * |y j / (y j + u j) - 1| ≤ (m j : ℝ) * (2 * U / y j) :=
          mul_le_mul_of_nonneg_left hj hk0
      _ = 2 * U * ((m j : ℝ) / y j) := by ring
  exact tendsto_pow_of_tendsto_one hr1 hmr

end GaloisForLFunctions.HTGeometry
