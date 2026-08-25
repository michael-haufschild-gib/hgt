import GaloisForLFunctions.RHTower.Sieve.ScaledCardLength
import GaloisForLFunctions.HTGeometry.RpowConcavity

/-!
# The window length is insensitive to a bounded dilation of the scale

The window `exp((log y)^β)` changes by a factor tending to `1` when `y` is divided by a fixed
constant: the exponent moves by `(log y)^β − (log y − c)^β ≤ c·(log y − c)^{β−1}`, which vanishes
because `β < 1`.  A family of dyadic marker blocks needs exactly this: its `k`-th block works at the
cofactor scale `y/4^k`, and its window has to stay comparable to `2^{-k}` times the window at `y`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **A concavity bound for the power function.** -/
theorem rpow_sub_rpow_le {A c β : ℝ} (hβ1 : β ≤ 1) (hc : 0 ≤ c) (hB : 0 < A - c) :
    A ^ β - (A - c) ^ β ≤ c * (A - c) ^ (β - 1) :=
  GaloisForLFunctions.HTGeometry.rpow_sub_rpow_le hβ1 hc hB

/-- The shifted logarithm still grows. -/
theorem tendsto_log_sub_const (c : ℝ) :
    Tendsto (fun y : ℝ => Real.log y - Real.log c) atTop atTop := by
  have h := Filter.tendsto_atTop_add_const_right atTop (-(Real.log c)) Real.tendsto_log_atTop
  exact h.congr fun y => by ring

/-- **The dilated window is eventually at least half the undilated one.** -/
theorem eventually_half_cardLength_le_dilated {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hc1 : 1 ≤ c) :
    ∀ᶠ y : ℝ in atTop, cardLength β y / 2 ≤ cardLength β (y / c) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hlogc : (0 : ℝ) ≤ Real.log c := Real.log_nonneg hc1
  have hneg : Tendsto (fun A : ℝ => A ^ (β - 1)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := 1 - β) (by linarith)
    exact h.congr fun A => by rw [show -(1 - β) = β - 1 by ring]
  have hdecay : Tendsto (fun A : ℝ => Real.log c * A ^ (β - 1)) atTop (𝓝 0) := by
    have := hneg.const_mul (Real.log c)
    simpa using this
  have hcomp : Tendsto (fun y : ℝ => Real.log c * (Real.log y - Real.log c) ^ (β - 1))
      atTop (𝓝 0) := hdecay.comp (tendsto_log_sub_const c)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hcomp.eventually_le_const hlog2,
    Real.tendsto_log_atTop.eventually_gt_atTop (Real.log c + 1),
    eventually_gt_atTop (0 : ℝ)] with y hbd hlog hy0
  have hB : (0 : ℝ) < Real.log y - Real.log c := by linarith
  have hdiv : Real.log (y / c) = Real.log y - Real.log c :=
    Real.log_div (ne_of_gt hy0) (ne_of_gt hc0)
  have hkey := rpow_sub_rpow_le (A := Real.log y) (c := Real.log c) (β := β) hβ1.le hlogc hB
  have hexp : (Real.log y) ^ β ≤ (Real.log y - Real.log c) ^ β + Real.log 2 := by
    linarith [hkey, hbd]
  rw [cardLength, cardLength, hdiv, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have hrw : Real.exp ((Real.log y - Real.log c) ^ β) * 2
      = Real.exp ((Real.log y - Real.log c) ^ β + Real.log 2) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [hrw]
  exact Real.exp_le_exp.2 hexp

end RHTower.Sieve
