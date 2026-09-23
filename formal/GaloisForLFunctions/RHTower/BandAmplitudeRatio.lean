import GaloisForLFunctions.RHTower.BandNormalFormPassage

/-!
# The amplitude ratio of the band passage

The two substitutions that carry the prolate angular equation to the comparison equation multiply the
unknown by

```text
A = g / w = sqrt(m̃) / sqrt(1-y²) ,      A² = m̃/(1-y²) ,
```

so `Phi = U · A`.  On the collar `A` is bounded above and below by absolute constants, and — this is
what the endpoint normalisation needs — `A → 1` at the endpoint.  Both facts come from the sharp
two-sided bound on the Liouville weight, whose two sides

```text
sqrt 2 / sqrt(1+y)   ≤  A²  ≤  2 sqrt(1-s) / (sqrt(y²-s)(1+y))
```

meet at `1` when `y = 1`.  The value `A(1) = 1` is built into the definition, so `A` is continuous on
the closed collar.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The amplitude ratio of the band passage, extended by its endpoint value `1`. -/
def bandAmplitudeRatio (s y : ℝ) : ℝ :=
  if y = 1 then 1 else driftAmplitude (bandLiouvilleWeight s) y / bandNfWeight y

section

variable {s y : ℝ}

theorem bandAmplitudeRatio_one (s : ℝ) : bandAmplitudeRatio s 1 = 1 := if_pos rfl

theorem bandLiouvilleWeight_nonneg (s y : ℝ) : 0 ≤ bandLiouvilleWeight s y := by
  rw [bandLiouvilleWeight, prolateWKBProfile]
  exact div_nonneg (bandEndpointPhase_nonneg s y) (Real.sqrt_nonneg _)

theorem bandAmplitudeRatio_of_ne (h : y ≠ 1) :
    bandAmplitudeRatio s y
      = Real.sqrt (bandLiouvilleWeight s y) / Real.sqrt (1 - y ^ (2 : ℕ)) := by
  rw [bandAmplitudeRatio, if_neg h, driftAmplitude, bandNfWeight,
    abs_of_nonneg (bandLiouvilleWeight_nonneg s y)]

theorem bandAmplitudeRatio_nonneg (s y : ℝ) : 0 ≤ bandAmplitudeRatio s y := by
  rcases eq_or_ne y 1 with rfl | h
  · rw [bandAmplitudeRatio_one]; norm_num
  · rw [bandAmplitudeRatio_of_ne h]
    positivity

theorem bandAmplitudeRatio_sq (hy0 : 0 < y) (hy1 : y < 1) (hys : s < y ^ (2 : ℕ)) :
    bandAmplitudeRatio s y ^ (2 : ℕ) = bandLiouvilleWeight s y / (1 - y ^ (2 : ℕ)) := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hm : 0 < bandLiouvilleWeight s y := bandLiouvilleWeight_pos hy0 hy1 hys
  rw [bandAmplitudeRatio_of_ne (by linarith : y ≠ 1), div_pow,
    Real.sq_sqrt hm.le, Real.sq_sqrt hy.le]

/-! ## The squeeze -/

/-- The lower comparison function for `A²`; it equals `1` at the endpoint. -/
def bandAmplitudeLower (y : ℝ) : ℝ := Real.sqrt 2 / Real.sqrt (1 + y)

/-- The upper comparison function for `A²`; it equals `1` at the endpoint. -/
def bandAmplitudeUpper (s y : ℝ) : ℝ :=
  2 * Real.sqrt (1 - s) / (Real.sqrt (y ^ (2 : ℕ) - s) * (1 + y))

theorem bandAmplitudeLower_one : bandAmplitudeLower 1 = 1 := by
  rw [bandAmplitudeLower]
  norm_num

theorem bandAmplitudeUpper_one (hs : s < 1) : bandAmplitudeUpper s 1 = 1 := by
  have h : (0 : ℝ) < Real.sqrt (1 - s) := Real.sqrt_pos.2 (by linarith)
  rw [bandAmplitudeUpper]
  norm_num
  field_simp

theorem bandAmplitudeLower_le_sq (hy0 : 0 < y) (hy1 : y < 1) (hys : s < y ^ (2 : ℕ)) :
    bandAmplitudeLower y ≤ bandAmplitudeRatio s y ^ (2 : ℕ) := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (1 + y) := Real.sqrt_pos.2 (by linarith)
  have hq2 : Real.sqrt (1 + y) ^ (2 : ℕ) = 1 + y := Real.sq_sqrt (by linarith)
  have hsharp := sharp_le_bandLiouvilleWeight (s := s) hy0.le hy1.le hys
  have hq2' : Real.sqrt (1 + y) * Real.sqrt (1 + y) = 1 + y :=
    Real.mul_self_sqrt (by linarith)
  rw [bandAmplitudeRatio_sq hy0 hy1 hys, bandAmplitudeLower, div_le_div_iff₀ hq hy]
  have hcalc : Real.sqrt 2 * (1 - y ^ (2 : ℕ))
      = Real.sqrt 2 * (1 - y) * Real.sqrt (1 + y) * Real.sqrt (1 + y) := by
    linear_combination (-(Real.sqrt 2 * (1 - y))) * hq2'
  rw [hcalc]
  exact mul_le_mul_of_nonneg_right hsharp hq.le

theorem sq_le_bandAmplitudeUpper (hy0 : 0 < y) (hy1 : y < 1) (hys : s < y ^ (2 : ℕ)) :
    bandAmplitudeRatio s y ^ (2 : ℕ) ≤ bandAmplitudeUpper s y := by
  have hy : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hw : (0 : ℝ) < Real.sqrt (y ^ (2 : ℕ) - s) := Real.sqrt_pos.2 (by linarith)
  have hsharp := bandLiouvilleWeight_le_sharp (s := s) hy0.le hy1.le hys
  rw [bandAmplitudeRatio_sq hy0 hy1 hys, bandAmplitudeUpper,
    div_le_div_iff₀ hy (by positivity)]
  have hkey : bandLiouvilleWeight s y * Real.sqrt (y ^ (2 : ℕ) - s)
      ≤ 2 * Real.sqrt (1 - s) * (1 - y) := (le_div_iff₀ hw).mp hsharp
  nlinarith [hkey, hw, (by linarith : (0:ℝ) < 1 + y), (by linarith : (0:ℝ) < 1 - y)]

/-- **The amplitude ratio tends to one at the endpoint.** -/
theorem tendsto_bandAmplitudeRatio (hs1 : s ≤ 1 / 8) {α : ℝ} (hα : 1 / 2 < α)
    (hα1 : α < 1) :
    Filter.Tendsto (bandAmplitudeRatio s) (nhdsWithin 1 (Icc α 1)) (nhds 1) := by
  have hsqTendsto : Filter.Tendsto (fun y => bandAmplitudeRatio s y ^ (2 : ℕ))
      (nhdsWithin 1 (Icc α 1)) (nhds 1) := by
    have hlow : Filter.Tendsto bandAmplitudeLower (nhdsWithin (1:ℝ) (Icc α 1)) (nhds 1) := by
      have hc : ContinuousAt bandAmplitudeLower 1 := by
        refine ContinuousAt.div continuousAt_const ?_ ?_
        · exact (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt
        · have : (0 : ℝ) < Real.sqrt (1 + 1) := Real.sqrt_pos.2 (by norm_num)
          exact this.ne'
      have := hc.tendsto
      rw [bandAmplitudeLower_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hup : Filter.Tendsto (bandAmplitudeUpper s) (nhdsWithin (1:ℝ) (Icc α 1)) (nhds 1) := by
      have hc : ContinuousAt (bandAmplitudeUpper s) 1 := by
        refine ContinuousAt.div continuousAt_const (ContinuousAt.mul ?_ ?_) ?_
        · exact (Real.continuous_sqrt.comp ((continuous_pow 2).sub continuous_const)).continuousAt
        · exact (continuous_const.add continuous_id).continuousAt
        · have h1 : (0 : ℝ) < Real.sqrt (1 ^ (2 : ℕ) - s) := Real.sqrt_pos.2 (by norm_num; linarith)
          have : (0 : ℝ) < Real.sqrt (1 ^ (2 : ℕ) - s) * (1 + 1) := by positivity
          exact this.ne'
      have := hc.tendsto
      rw [bandAmplitudeUpper_one (by linarith)] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_forall
        (fun y (hy : y ∈ Icc α 1) => hy)] with y hy _
      rcases eq_or_lt_of_le hy.2 with rfl | hlt
      · rw [bandAmplitudeRatio_one, bandAmplitudeLower_one]
        norm_num
      · have hy0 : (0 : ℝ) < y := by linarith [hy.1]
        have hys : s < y ^ (2 : ℕ) := by nlinarith [hy.1]
        exact bandAmplitudeLower_le_sq hy0 hlt hys
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rcases eq_or_lt_of_le hy.2 with rfl | hlt
      · rw [bandAmplitudeRatio_one, bandAmplitudeUpper_one (by linarith)]
        norm_num
      · have hy0 : (0 : ℝ) < y := by linarith [hy.1]
        have hys : s < y ^ (2 : ℕ) := by nlinarith [hy.1]
        exact sq_le_bandAmplitudeUpper hy0 hlt hys
  have hsqrt : Filter.Tendsto (fun y => Real.sqrt (bandAmplitudeRatio s y ^ (2 : ℕ)))
      (nhdsWithin 1 (Icc α 1)) (nhds (Real.sqrt 1)) :=
    (Real.continuous_sqrt.continuousAt).tendsto.comp hsqTendsto
  rw [Real.sqrt_one] at hsqrt
  refine hsqrt.congr fun y => ?_
  rw [Real.sqrt_sq (bandAmplitudeRatio_nonneg s y)]

end

end GaloisForLFunctions.RHTower

end
