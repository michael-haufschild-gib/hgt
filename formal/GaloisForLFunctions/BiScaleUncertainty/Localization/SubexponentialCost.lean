import GaloisForLFunctions.HTGeometry.LogBelowLinear
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Subexponential cost of fragmenting two sources

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

/-- Exponential fragmentation with a specified nonnegative rate. -/
def exponentialFragmentCount (c : ℝ≥0) (t : ℝ) : ℝ≥0 :=
  ⟨Real.exp ((c : ℝ) * t), (Real.exp_pos _).le⟩

/-- Exponential fragmentation has a linear prefactor, rather than a doubled exponent. -/
theorem exponentialLocalizationCost_bounds (c : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp ((c : ℝ) * t) * Real.log 3 ≤
      localizationCost (exponentialFragmentCount c t) ∧
    localizationCost (exponentialFragmentCount c t) ≤
      Real.exp ((c : ℝ) * t) * ((c : ℝ) * t + Real.log 3) := by
  have hx : 1 ≤ Real.exp ((c : ℝ) * t) :=
    by simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (mul_nonneg c.coe_nonneg ht)
  change Real.exp ((c : ℝ) * t) * Real.log 3 ≤
    Real.exp ((c : ℝ) * t) * Real.log (2 + Real.exp ((c : ℝ) * t)) ∧ _
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by norm_num) (by linarith only [hx])) (Real.exp_pos _).le
  · change Real.exp ((c : ℝ) * t) * Real.log (2 + Real.exp ((c : ℝ) * t)) ≤ _
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h := Real.log_le_log (by positivity : 0 < 2 + Real.exp ((c : ℝ) * t))
      (show 2 + Real.exp ((c : ℝ) * t) ≤ 3 * Real.exp ((c : ℝ) * t) by
        linarith only [hx])
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at h
    linarith only [h]

/-- The exact exponential rate of the localization cost equals the fragment-count rate. -/
theorem exponentialLocalizationCost_rate (c : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (((c : ℝ) - ε) * t) ≤ localizationCost (exponentialFragmentCount c t) ∧
      localizationCost (exponentialFragmentCount c t) ≤ Real.exp (((c : ℝ) + ε) * t) := by
  let K : ℝ := (c : ℝ) + Real.log 3 + 1
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; linarith only [c.coe_nonneg, hl]
  have hu := HTGeometry.eventually_log_add_le_linear hε 0 (Real.log K)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (-Real.log (Real.log 3) / ε), hu] with t ht htlo htu
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  obtain ⟨hlo, hhi⟩ := exponentialLocalizationCost_bounds c ht0
  constructor
  · have hexp : Real.exp (-ε * t) ≤ Real.log 3 := by
      apply (Real.exp_le_exp.mpr (show -ε * t ≤ Real.log (Real.log 3) by
        have h := (div_le_iff₀ hε).mp htlo
        linarith only [h])).trans_eq (Real.exp_log hl)
    calc
      _ = Real.exp ((c : ℝ) * t) * Real.exp (-ε * t) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((c : ℝ) * t) * Real.log 3 :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ ≤ _ := hlo
  · have hlin : (c : ℝ) * t + Real.log 3 ≤ K * t := by
      have hlt := mul_le_mul_of_nonneg_left ht hl.le
      dsimp [K]
      nlinarith only [hlt, ht0]
    have hKt : K * t ≤ Real.exp (ε * t) := by
      conv_lhs => rw [← Real.exp_log (mul_pos hK (lt_of_lt_of_le zero_lt_one ht))]
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul hK.ne' (ne_of_gt (lt_of_lt_of_le zero_lt_one ht))]
      linarith only [htu]
    calc
      _ ≤ Real.exp ((c : ℝ) * t) * ((c : ℝ) * t + Real.log 3) := hhi
      _ ≤ Real.exp ((c : ℝ) * t) * Real.exp (ε * t) :=
        mul_le_mul_of_nonneg_left (hlin.trans hKt) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end GaloisForLFunctions.BiScaleUncertainty

#print axioms GaloisForLFunctions.BiScaleUncertainty.localizationCost_mul_exp_eventually_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.reciprocalLocalizationCost_mul_exp_eventually_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.exponentialLocalizationCost_rate
