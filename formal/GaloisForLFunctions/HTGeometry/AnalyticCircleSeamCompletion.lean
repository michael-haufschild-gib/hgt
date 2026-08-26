import GaloisForLFunctions.HTGeometry.CoalescingLimitObstruction
import GaloisForLFunctions.HTGeometry.MeasurableAnalyticGerm

/-!
# Analytic completion from local unit-circle seam germs

Compatible analytic germs crossing the unit circle determine one function analytic at every seam
point except the Cayley point `1`.  Compatibility is automatic when every germ agrees with fixed
interior and exterior functions on the two open sides.
-/

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The open unit disk accumulates at every unit-circle point. -/
theorem frequently_norm_lt_one_nhds_of_norm_eq_one
    {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ᶠ w : ℂ in nhds z, ‖w‖ < 1 := by
  have hzcl : z ∈ closure (ball (0 : ℂ) 1) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ := min (ε / 2) (1 / 2 : ℝ)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδe : δ < ε := by
      exact (min_le_left _ _).trans_lt (by linarith)
    have hδ1 : δ < 1 := by
      exact (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨((1 - δ : ℝ) : ℂ) * z, ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), hz]
      linarith
    · rw [dist_eq, show z - ((1 - δ : ℝ) : ℂ) * z = (δ : ℂ) * z by
          push_cast
          ring,
        norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hδ, hz, mul_one]
      simpa only [ofReal_one, ofReal_sub, one_mul] using hδe
  have hfreq : ∃ᶠ w : ℂ in nhds z, w ∈ ball (0 : ℂ) 1 :=
    mem_closure_iff_frequently.mp hzcl
  exact hfreq.mono fun w hw => by
    simpa only [mem_ball, dist_zero_right] using hw

/-- Local analytic crossings of fixed interior and exterior functions glue to one function
analytic at every unit-circle point except `1`. -/
theorem exists_analyticAt_circleSeam_completion
    (inside outside : ℂ → ℂ)
    (hlocal : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧
        (∀ w : ℂ, ‖w‖ < 1 → G w = inside w) ∧
        (∀ w : ℂ, 1 < ‖w‖ → G w = outside w)) :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → AnalyticAt ℂ F z) ∧
      (∀ z : ℂ, ‖z‖ < 1 → F z = inside z) ∧
      (∀ z : ℂ, 1 < ‖z‖ → F z = outside z) := by
  classical
  let good : ℂ → Prop := fun z => ‖z‖ = 1 ∧ z ≠ 1
  let germ : ℂ → ℂ → ℂ := fun z =>
    if hz : good z then Classical.choose (hlocal z hz.1 hz.2) else 0
  have hgerm (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
      AnalyticAt ℂ (germ z) z ∧
        (∀ w : ℂ, ‖w‖ < 1 → germ z w = inside w) ∧
        (∀ w : ℂ, 1 < ‖w‖ → germ z w = outside w) := by
    dsimp only [germ]
    rw [dif_pos ⟨hz, hz1⟩]
    exact Classical.choose_spec (hlocal z hz hz1)
  let F : ℂ → ℂ := fun z =>
    if ‖z‖ < 1 then inside z
    else if 1 < ‖z‖ then outside z
    else germ z z
  refine ⟨F, ?_, ?_, ?_⟩
  · intro z hz hz1
    have hG := hgerm z hz hz1
    have hGdiff : ∀ᶠ w in nhds z, DifferentiableAt ℂ (germ z) w :=
      Complex.analyticAt_iff_eventually_differentiableAt.mp hG.1
    have hneOne : ∀ᶠ w in nhds z, w ≠ 1 :=
      continuousAt_id.eventually_ne hz1
    have hFG : F =ᶠ[nhds z] germ z := by
      filter_upwards [hGdiff, hneOne] with w hGdiffw hw1
      dsimp only [F]
      by_cases hwin : ‖w‖ < 1
      · rw [if_pos hwin, hG.2.1 w hwin]
      · rw [if_neg hwin]
        by_cases hwout : 1 < ‖w‖
        · rw [if_pos hwout, hG.2.2 w hwout]
        · rw [if_neg hwout]
          have hwNorm : ‖w‖ = 1 :=
            le_antisymm (le_of_not_gt hwout) (le_of_not_gt hwin)
          have hGw := hgerm w hwNorm hw1
          let D : ℂ → ℂ := fun t => germ w t - germ z t
          have hDcont : ContinuousAt D w :=
            hGw.1.continuousAt.sub hGdiffw.continuousAt
          have hDzero : ∃ᶠ t : ℂ in nhds w, D t = 0 :=
            (frequently_norm_lt_one_nhds_of_norm_eq_one hwNorm).mono fun t ht => by
              dsimp only [D]
              rw [hGw.2.1 t ht, hG.2.1 t ht, sub_self]
          have hzero := eq_of_frequently_of_continuousAt hDcont hDzero
          exact sub_eq_zero.mp hzero.symm
    exact hG.1.congr hFG.symm
  · intro z hz
    simp [F, hz]
  · intro z hz
    have hnot : ¬ ‖z‖ < 1 := not_lt.mpr hz.le
    simp [F, hnot, hz]

end

end GaloisForLFunctions.HTGeometry
