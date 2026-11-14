import GaloisForLFunctions.HTGeometry.LogBelowLinear
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!+# Subexponential cost of fragmenting two sources

The cost `m log(2+m)` arises from `O(m²)` pairings, each of size
`O(log(2+m)/m)`. Its logarithmic size is controlled by `2 log(2+m)`.
Thus a subexponential fragment count loses arbitrarily little exponential
growth. This is the cost absorption in Lemma 2 of arXiv:2611.10726.
-/

noncomputable section
open Filter
open scoped Topology NNReal
namespace GaloisForLFunctions.BiScaleUncertainty

/-- Pair-count cost after the energy of each fragment is included. -/
def localizationCost (m : ℝ≥0) : ℝ := m * Real.log (2 + (m : ℝ))

theorem localizationCost_nonneg (m : ℝ≥0) : 0 ≤ localizationCost m :=
  mul_nonneg m.coe_nonneg (Real.log_nonneg (by linarith [m.coe_nonneg]))

/-- A quadratic envelope is enough to retain every strictly smaller exponential rate. -/
theorem localizationCost_le_sq (m : ℝ≥0) : localizationCost m ≤ (2 + (m : ℝ)) ^ 2 := by
  have hp : 0 < 2 + (m : ℝ) := by linarith [m.coe_nonneg]
  have hl := Real.log_le_sub_one_of_pos hp
  have hm := mul_le_mul_of_nonneg_left hl m.coe_nonneg
  unfold localizationCost
  nlinarith only [hm, m.coe_nonneg]

theorem localizationCost_le_exp_log (m : ℝ≥0) :
    localizationCost m ≤ Real.exp (2 * Real.log (2 + (m : ℝ))) := by
  have hp : 0 < 2 + (m : ℝ) := by linarith [m.coe_nonneg]
  calc
    _ ≤ (2 + (m : ℝ)) ^ 2 := localizationCost_le_sq m
    _ = _ := by rw [two_mul, Real.exp_add, Real.exp_log hp]; ring

/-- Subexponential fragment counts incur at most any prescribed positive exponential loss. -/
theorem localizationCost_eventually_le_exp (m : ℝ → ℝ≥0)
    (hm : Tendsto (fun t => Real.log (2 + (m t : ℝ)) / t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, localizationCost (m t) ≤ Real.exp (ε * t) := by
  have h := HTGeometry.eventually_sublinear_add_le_linear (half_pos hε) hm 0 0
  filter_upwards [h] with t ht
  apply (localizationCost_le_exp_log (m t)).trans
  apply Real.exp_le_exp.mpr
  linarith only [ht]

/-- The localization loss adds arbitrarily little to the original growth exponent. -/
theorem localizationCost_mul_exp_eventually_le (m : ℝ → ℝ≥0)
    (hm : Tendsto (fun t => Real.log (2 + (m t : ℝ)) / t) atTop (𝓝 0))
    (η : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      localizationCost (m t) * Real.exp (η * t) ≤ Real.exp ((η + ε) * t) := by
  filter_upwards [localizationCost_eventually_le_exp m hm hε] with t ht
  calc
    _ ≤ Real.exp (ε * t) * Real.exp (η * t) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Reciprocal-width intervals have a concrete fragment count with subexponential cost. -/
theorem reciprocalLocalizationCost_eventually_le_exp (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      localizationCost (⌈4 * (t + C)⌉₊ : ℝ≥0) ≤ Real.exp (ε * t) := by
  have hlog := HTGeometry.eventually_log_add_le_linear (half_pos hε) 0 (Real.log 11)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop |C|, hlog]
    with t ht htC hlogt
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hceil : (⌈4 * (t + C)⌉₊ : ℝ) < 4 * (t + C) + 1 :=
    Nat.ceil_lt_add_one (by linarith only [htC, neg_le_abs C])
  have hcount : 2 + (⌈4 * (t + C)⌉₊ : ℝ) ≤ 11 * t := by
    linarith only [hceil, ht, htC, le_abs_self C]
  have harg : 0 < 2 + (⌈4 * (t + C)⌉₊ : ℝ) := by positivity
  have hb := Real.log_le_log harg hcount
  rw [Real.log_mul (by norm_num : (11 : ℝ) ≠ 0) htpos.ne'] at hb
  apply (localizationCost_le_exp_log (⌈4 * (t + C)⌉₊ : ℝ≥0)).trans
  apply Real.exp_le_exp.mpr
  change 2 * Real.log (2 + (⌈4 * (t + C)⌉₊ : ℝ)) ≤ ε * t
  linarith only [hb, hlogt]

/-- The reciprocal-width specialization retains every exponent with positive slack. -/
theorem reciprocalLocalizationCost_mul_exp_eventually_le (C η : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      localizationCost (⌈4 * (t + C)⌉₊ : ℝ≥0) * Real.exp (η * t) ≤
        Real.exp ((η + ε) * t) := by
  filter_upwards [reciprocalLocalizationCost_eventually_le_exp C hε] with t ht
  calc
    _ ≤ Real.exp (ε * t) * Real.exp (η * t) :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end GaloisForLFunctions.BiScaleUncertainty

#print axioms GaloisForLFunctions.BiScaleUncertainty.localizationCost_mul_exp_eventually_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.reciprocalLocalizationCost_mul_exp_eventually_le
