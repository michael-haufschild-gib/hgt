import Mathlib.Analysis.Convex.Deriv

/-! Right derivatives provide ordered supporting slopes for every real convex observable. -/

noncomputable section
namespace RHTower

theorem finiteWeilConvex_rightDeriv_monotone
    (φ : {f : ℝ → ℝ // ConvexOn ℝ Set.univ f}) :
    Monotone (fun x => derivWithin φ.val (Set.Ioi x) x) := by
  intro x y hxy
  exact φ.property.monotoneOn_rightDeriv (by simp) (by simp) hxy

theorem finiteWeilConvex_right_support
    (φ : {f : ℝ → ℝ // ConvexOn ℝ Set.univ f}) (x y : ℝ) :
    derivWithin φ.val (Set.Ioi y) y * (x - y) ≤ φ.val x - φ.val y := by
  rcases lt_trichotomy y x with hyx | heq | hxy
  · have h := φ.property.rightDeriv_le_slope_of_mem_interior (by simp) (Set.mem_univ x) hyx
    rw [slope_def_field] at h
    exact (le_div_iff₀ (sub_pos.mpr hyx)).mp h
  · subst x
    simp
  · have h := (φ.property.slope_le_leftDeriv_of_mem_interior (Set.mem_univ x) (by simp) hxy).trans
      (φ.property.leftDeriv_le_rightDeriv_of_mem_interior (by simp))
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hxy)).mp h
    nlinarith only [hm]

end RHTower
