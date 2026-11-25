import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula

/-! Jensen's inequality for a finite set with analytic multiplicities. -/

open Complex Metric Finset

namespace QH.PrimeProgressions

theorem sum_analyticOrderNatAt_le_jensen {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    (∑ z ∈ S, (analyticOrderNatAt f z : ℝ)) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c r)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hD (z : ℂ) (hz : z ∈ closedBall c r) : D z = (analyticOrderNatAt f z : ℤ) := by
    change MeromorphicOn.divisor f (closedBall c r) z = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (han.mono (Set.subset_univ _)) hz, analyticOrderNatAt]
    cases analyticOrderAt f z using ENat.recTopCoe <;> simp
  have hD₀ (z : ℂ) : 0 ≤ (D z : ℝ) := by
    by_cases hz : z ∈ closedBall c r
    · rw [hD z hz, Int.cast_natCast]
      exact Nat.cast_nonneg _
    · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hz, Int.cast_zero, le_refl]
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  let W := hfin.toFinset ∪ S
  have hw : D.support ⊆ ↑W := by
    intro z hz
    simp only [W, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hz
  have hJ := (han.mono (Set.subset_univ (closedBall c |R|))).sum_divisor_le
    (c := c) (r := r) (R := R) (M := M)
    (by rwa [abs_of_pos hr]) (by rwa [abs_of_pos hr, abs_of_pos (hr.trans hrR)])
    hM hc (by rwa [abs_of_pos (hr.trans hrR)])
  rw [abs_of_pos hr] at hJ
  change (↑(∑ᶠ z, D z) : ℝ) ≤ _ at hJ
  rw [finsum_eq_sum_of_support_subset D (s := W) hw] at hJ
  push_cast at hJ
  refine le_trans ?_ hJ
  refine (Finset.sum_congr rfl (fun z hz => ?_)).le.trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := hfin.toFinset)) fun z _ _ => hD₀ z)
  rw [hD z (hS z hz), Int.cast_natCast]

end QH.PrimeProgressions
