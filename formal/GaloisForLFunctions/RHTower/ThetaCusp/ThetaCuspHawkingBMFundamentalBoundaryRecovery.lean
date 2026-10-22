import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalJacobiRecurrence

/-! Exact recovery of the retained boundary from the original second and fourth moments. -/
namespace RHTower.D4BMJointSource
open Complex
noncomputable section
set_option autoImplicit false

/-- A finite combination of the admitted moments recovers the original nonzero boundary. -/
theorem fundamentalJacobiMoment_boundary_recovery (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    let d := 2*s-w
    let e := w+2*s+2
    (e+d^(2 : ℕ))*(e+2)*(e+3)*fundamentalJacobiMoment 4 w s-
      (d^(4 : ℕ)+(6*e+8)*d^(2 : ℕ)+3*e*(e+2))*fundamentalJacobiMoment 2 w s = 2*d := by
  let d := 2*s-w
  let e := w+2*s+2
  have h1 := fundamentalJacobiMoment_recurrence 1 w s hw hw1
  have h2 := fundamentalJacobiMoment_recurrence 2 w s hw hw1
  have h3 := fundamentalJacobiMoment_recurrence 3 w s hw hw1
  have hs := fundamentalJacobiMoment_second w s hw hw1
  norm_num only at h1 h2 h3
  have h0 : 2*fundamentalJacobiMoment 0 w s =
      (d^(2 : ℕ)+5*e+8)*fundamentalJacobiMoment 2 w s-
        (e+2)*(e+3)*fundamentalJacobiMoment 4 w s := by
    dsimp only [d,e]
    linear_combination 2*h1-(2*s-w)*h2-(w+2*s+2+2)*h3
  dsimp only [d,e] at h0
  dsimp only at hs ⊢
  linear_combination 2*hs+(w+2*s+2+(2*s-w)^(2 : ℕ))*h0

/-- This inequality retains complex phases until the exact boundary has been recovered. -/
theorem fundamentalJacobiMoment_boundary_lower_bound (w s : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    let d := 2*s-w
    let e := w+2*s+2
    2*‖d‖ ≤ ‖(e+d^(2 : ℕ))*(e+2)*(e+3)‖*‖fundamentalJacobiMoment 4 w s‖+
      ‖d^(4 : ℕ)+(6*e+8)*d^(2 : ℕ)+3*e*(e+2)‖*‖fundamentalJacobiMoment 2 w s‖ := by
  have he := fundamentalJacobiMoment_boundary_recovery w s hw hw1
  dsimp only at he ⊢
  rw [← show ‖(2:ℂ)*(2*s-w)‖=2*‖2*s-w‖ by rw [norm_mul]; norm_num,← he]
  exact (norm_sub_le _ _).trans_eq (by simp only [norm_mul])

end
end RHTower.D4BMJointSource
