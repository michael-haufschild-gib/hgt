import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-! # Cubic scale of the centered logarithmic curvature

A quartic correction gives matching upper and lower bounds with leading
coefficient one sixth. Both bounds retain the complete logarithmic expression.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Set

private def quarticLogModel (c R x : ℝ) : ℝ :=
  x * Real.log x - x ^ 2 / (2 * c) + (x - c) ^ 3 / (6 * c ^ 2) -
    (x - c) ^ 4 / (12 * c ^ 2 * R)

private def quarticLogDeriv (c R x : ℝ) : ℝ :=
  Real.log x + 1 - x / c + (x - c) ^ 2 / (2 * c ^ 2) -
    (x - c) ^ 3 / (3 * c ^ 2 * R)

private theorem quarticLogModel_deriv {c R x : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hx : 0 < x) : HasDerivAt (quarticLogModel c R) (quarticLogDeriv c R x) x := by
  have h := (((Real.hasDerivAt_mul_log hx.ne').sub
    (((hasDerivAt_id' x).pow 2).div_const (2 * c))).add
    ((((hasDerivAt_id' x).sub_const c).pow 3).div_const (6 * c ^ 2))).sub
    ((((hasDerivAt_id' x).sub_const c).pow 4).div_const (12 * c ^ 2 * R))
  convert! h using 1
  dsimp only [quarticLogDeriv]
  field_simp
  ring

private theorem quarticLogModel_deriv2 {c R x : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hx : 0 < x) : HasDerivAt (quarticLogDeriv c R)
      ((x - c) ^ 2 * (R - x) / (c ^ 2 * x * R)) x := by
  have h := ((((Real.hasDerivAt_log hx.ne').add_const 1).sub
    ((hasDerivAt_id' x).div_const c)).add
    ((((hasDerivAt_id' x).sub_const c).pow 2).div_const (2 * c ^ 2))).sub
    ((((hasDerivAt_id' x).sub_const c).pow 3).div_const (3 * c ^ 2 * R))
  convert! h using 1
  field_simp
  ring

private theorem quarticLogModel_convex {c : ℝ} (hc : 1 < c) :
    ConvexOn ℝ (Icc (c - 1) (c + 1)) (quarticLogModel c (c + 1)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := quarticLogDeriv c (c + 1))
    (f'' := fun x => (x - c) ^ 2 * (c + 1 - x) / (c ^ 2 * x * (c + 1)))
    (convex_Icc _ _)
  · intro x hx
    exact (quarticLogModel_deriv (by linarith) (by linarith)
      (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact (quarticLogModel_deriv (by linarith) (by linarith)
      (by linarith [hxI.1])).hasDerivWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact (quarticLogModel_deriv2 (by linarith) (by linarith)
      (by linarith [hxI.1])).hasDerivWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hxI.2]))
      (by
        have hx0 : 0 < x := by linarith [hxI.1]
        have hc0 : 0 < c := by linarith
        have hcm : 0 < c - 1 := by linarith
        positivity)

private theorem quarticLogModel_concave {c : ℝ} (hc : 1 < c) :
    ConcaveOn ℝ (Icc (c - 1) (c + 1)) (quarticLogModel c (c - 1)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := quarticLogDeriv c (c - 1))
    (f'' := fun x => (x - c) ^ 2 * (c - 1 - x) / (c ^ 2 * x * (c - 1)))
    (convex_Icc _ _)
  · intro x hx
    exact (quarticLogModel_deriv (by linarith) (by linarith)
      (by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact (quarticLogModel_deriv (by linarith) (by linarith)
      (by linarith [hxI.1])).hasDerivWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact (quarticLogModel_deriv2 (by linarith) (by linarith)
      (by linarith [hxI.1])).hasDerivWithinAt
  · intro x hx
    have hxI := interior_subset hx
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hxI.1]))
      (by
        have hx0 : 0 < x := by linarith [hxI.1]
        have hc0 : 0 < c := by linarith
        have hcm : 0 < c - 1 := by linarith
        positivity)

private theorem quarticLogModel_centered (c R : ℝ) :
    quarticLogModel c R (c + 1) - 2 * quarticLogModel c R c +
      quarticLogModel c R (c - 1) =
      (c + 1) * Real.log (c + 1) - 2 * (c * Real.log c) +
        (c - 1) * Real.log (c - 1) - 1 / c - 1 / (6 * c ^ 2 * R) := by
  dsimp [quarticLogModel]
  ring

theorem centered_mul_log_bounds {c : ℝ} (hc : 1 < c) :
    1 / (6 * c ^ 2 * (c + 1)) ≤
        (c + 1) * Real.log (c + 1) - 2 * (c * Real.log c) +
          (c - 1) * Real.log (c - 1) - 1 / c ∧
      (c + 1) * Real.log (c + 1) - 2 * (c * Real.log c) +
        (c - 1) * Real.log (c - 1) - 1 / c ≤ 1 / (6 * c ^ 2 * (c - 1)) := by
  have hl : c - 1 ∈ Icc (c - 1) (c + 1) := ⟨le_rfl, by linarith⟩
  have hr : c + 1 ∈ Icc (c - 1) (c + 1) := ⟨by linarith, le_rfl⟩
  have hlo := (quarticLogModel_convex hc).2 hl hr
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  have hup := (quarticLogModel_concave hc).2 hl hr
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  simp only [smul_eq_mul] at hlo hup
  rw [show (1 / 2 : ℝ) * (c - 1) + (1 / 2 : ℝ) * (c + 1) = c by ring] at hlo hup
  constructor
  · linarith only [hlo, quarticLogModel_centered c (c + 1)]
  · linarith only [hup, quarticLogModel_centered c (c - 1)]

end
end GaloisForLFunctions.HTGeometry
