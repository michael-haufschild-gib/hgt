import Mathlib

/-!
# The infinite tail of the secular sandwich vanishes

The lower bound of the secular sandwich carries the term `T/(M-1)`, with `T` the infinite tail of
the coordinate masses and `M` the gap slack.  Only two facts about the family are needed for it to
vanish: the tail is bounded, and the slack grows without bound.

```text
0 ≤ T(c) ≤ C ,   M(c) → ∞    ⟹    T(c)/(M(c) - 1) → 0 .
```

The boundedness of the tail is a Bessel inequality: the coordinate masses of a normalised vector
against an orthonormal family sum to at most one, so *every* subfamily sum is bounded by the same
constant, uniformly in the family.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- Any subsum of a nonnegative family is bounded by a bound for the whole sum. -/
theorem sum_subset_le_of_sum_le {ι : Type*} [DecidableEq ι] {s t : Finset ι} {f : ι → ℝ} {C : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hsub : t ⊆ s) (h : ∑ i ∈ s, f i ≤ C) :
    ∑ i ∈ t, f i ≤ C :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hf i) h

/-- **The tail term of the secular sandwich vanishes.** -/
theorem tendsto_tail_div_slack {T M : ℝ → ℝ} {C : ℝ}
    (hT : ∀ᶠ c : ℝ in atTop, 0 ≤ T c ∧ T c ≤ C)
    (hM : Tendsto M atTop atTop) :
    Tendsto (fun c : ℝ => T c / (M c - 1)) atTop (𝓝 0) := by
  have hslack : Tendsto (fun c : ℝ => M c - 1) atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right _ (-1 : ℝ) hM |>.congr fun c => by ring
  have hinv : Tendsto (fun c : ℝ => (M c - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hslack
  have hmaj : Tendsto (fun c : ℝ => C * (M c - 1)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul C
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hT, hslack.eventually_ge_atTop (1 : ℝ)] with c hTc hMc
    have hpos : (0 : ℝ) < M c - 1 := lt_of_lt_of_le zero_lt_one hMc
    exact div_nonneg hTc.1 hpos.le
  · filter_upwards [hT, hslack.eventually_ge_atTop (1 : ℝ)] with c hTc hMc
    have hpos : (0 : ℝ) < M c - 1 := lt_of_lt_of_le zero_lt_one hMc
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hTc.2 (inv_nonneg.2 hpos.le)

end GaloisForLFunctions.RHTower

end
