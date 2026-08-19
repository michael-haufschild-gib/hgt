import GaloisForLFunctions.RHTower.MobiusWeightedMomentZeroFree

/-!
# The half-unit exponential-moment tower

Every weight below `e^{t/2}` excludes zeta zeros from one more half plane, and their union is the
open right half of the critical strip.  Hence the full half-unit tower of weighted domains implies
the Riemann hypothesis.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- **Section 3, `(ii) → (i)`.**  The full half-unit moment tower implies the Riemann
hypothesis. -/
theorem riemannHypothesis_of_forall_weightedMertensMoment
    (h : ∀ α : ℝ, 0 ≤ α → α < 1 / 2 → WeightedMertensMoment α) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxis
  have hhalf : (1 : ℝ) / 2 < s.re := mem_rightHalf.mp hs
  have hs1 : s ≠ 1 := by
    intro hsone
    subst s
    rw [xi_one] at hxis
    norm_num at hxis
  have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
  have hzeta : riemannZeta s = 0 := (xi_eq_zero_iff hspos hs1).mp hxis
  set α : ℝ := max 0 ((3 / 2 - s.re) / 2) with hαdef
  have hα0 : 0 ≤ α := le_max_left _ _
  have hαhalf : α < 1 / 2 := by
    refine max_lt (by norm_num) ?_
    linarith
  have hlt : 1 - α < s.re := by
    rcases le_or_gt ((3 / 2 - s.re) / 2) 0 with hc | hc
    · have hz : α = 0 := by rw [hαdef]; exact max_eq_left hc
      rw [hz]
      linarith
    · have hz : α = (3 / 2 - s.re) / 2 := by rw [hαdef]; exact max_eq_right hc.le
      rw [hz]
      linarith
  exact zeta_ne_zero_of_weightedMertensMoment hα0 (h α hα0 hαhalf) hlt hs1 hzeta

end

end RHTower
