import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Linear differential inequalities and finite triangular cones

This module records the source-independent integrating-factor lemma needed to turn a triangular
cooperative differential system into a genuine finite-section maximum principle.  A pointwise
inward derivative on the boundary is not enough by itself, because a flat crossing can have zero
derivative.  The full differential inequality supplies the integrating factor that excludes such
crossings.
-/

open Set Filter MeasureTheory intervalIntegral

namespace HTGeometry

noncomputable section

/-- **Scalar integrating-factor cone lemma.**  If `f' - r f` is nonnegative on the interior of a
compact interval and `f` starts nonnegative, then `f` remains nonnegative. -/
theorem nonnegativeOn_Icc_of_deriv_sub_reaction_nonnegative
    {a b : ℝ} (hab : a ≤ b) {f r : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hr : ContinuousOn r (Icc a b))
    (hfdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hineq : ∀ x ∈ Ioo a b, 0 ≤ deriv f x - r x * f x)
    (ha : 0 ≤ f a) :
    ∀ x ∈ Icc a b, 0 ≤ f x := by
  rcases hab.eq_or_lt with rfl | hablt
  · intro x hx
    have hxa : x = a := le_antisymm hx.2 hx.1
    simpa [hxa] using ha
  let I : ℝ → ℝ := fun x => ∫ t in a..x, r t
  let g : ℝ → ℝ := fun x => Real.exp (-I x) * f x
  have hrint : IntervalIntegrable r volume a b :=
    hr.intervalIntegrable_of_Icc hablt.le
  have hIcont : ContinuousOn I (Icc a b) := by
    simpa only [I, uIcc_of_le hablt.le] using
      (intervalIntegral.continuousOn_primitive_interval' hrint
        (show a ∈ uIcc a b by rw [uIcc_of_le hablt.le]; exact ⟨le_rfl, hablt.le⟩))
  have hgcont : ContinuousOn g (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn hIcont.neg).mul hf
  have hgderiv : ∀ x ∈ Ioo a b,
      HasDerivAt g
        (Real.exp (-I x) * (deriv f x - r x * f x)) x := by
    intro x hx
    have hxIcc : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
    have hrx : ContinuousAt r x :=
      (hr x hxIcc).continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hrmeas : StronglyMeasurableAtFilter r (nhds x) volume := by
      exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun y hy => (hr y ⟨hy.1.le, hy.2.le⟩).continuousAt
          (Icc_mem_nhds hy.1 hy.2)) x hx
    have hrax : IntervalIntegrable r volume a x :=
      (hr.mono (Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le
    have hIderiv : HasDerivAt I (r x) x := by
      dsimp only [I]
      exact intervalIntegral.integral_hasDerivAt_right hrax hrmeas hrx
    have hexp : HasDerivAt (fun y => Real.exp (-I y))
        (Real.exp (-I x) * (-r x)) x := by
      have hcomp := (Real.hasDerivAt_exp (-I x)).comp x hIderiv.neg
      rw [show (fun y => Real.exp (-I y)) = Real.exp ∘ (-I) by rfl]
      exact hcomp
    have hmul := hexp.mul (hfdiff x hx).hasDerivAt
    rw [show g = (fun y => Real.exp (-I y)) * f by
      funext y
      rfl]
    apply hmul.congr_deriv
    ring
  have hmono : MonotoneOn g (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hgcont
    · rw [interior_Icc]
      intro x hx
      exact (hgderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hgderiv x hx).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hineq x hx)
  intro x hx
  have hga : g a ≤ g x :=
    hmono ⟨le_rfl, hablt.le⟩ hx hx.1
  have hga0 : g a = f a := by simp [g, I]
  have hga_nonneg : 0 ≤ g a := by rw [hga0]; exact ha
  have hgx : 0 ≤ Real.exp (-I x) * f x := by
    rw [← show g x = Real.exp (-I x) * f x from rfl]
    exact hga_nonneg.trans hga
  rw [mul_comm] at hgx
  exact nonneg_of_mul_nonneg_left hgx (Real.exp_pos _)

/-- **Finite triangular cone maximum principle.**  A finite triangular differential system with
nonnegative forcing and transport preserves its nonnegative cone when the initial section and its
single outgoing boundary channel are nonnegative. -/
theorem finiteTriangularCone_nonnegative
    {a b : ℝ} (hab : a ≤ b) (J : ℕ)
    {S A B R : ℕ → ℝ → ℝ}
    (hScont : ∀ j, j ≤ J → ContinuousOn (S j) (Icc a b))
    (hRcont : ∀ j, j ≤ J → ContinuousOn (R j) (Icc a b))
    (hSdiff : ∀ j, j ≤ J → ∀ x ∈ Ioo a b, DifferentiableAt ℝ (S j) x)
    (hflow : ∀ j, j ≤ J → ∀ x ∈ Ioo a b,
      deriv (S j) x = A j x + B j x * S (j + 1) x + R j x * S j x)
    (hA : ∀ j, j ≤ J → ∀ x ∈ Ioo a b, 0 ≤ A j x)
    (hB : ∀ j, j ≤ J → ∀ x ∈ Ioo a b, 0 ≤ B j x)
    (hinit : ∀ j, j ≤ J → 0 ≤ S j a)
    (hboundary : ∀ x ∈ Icc a b, 0 ≤ S (J + 1) x) :
    ∀ j, j ≤ J → ∀ x ∈ Icc a b, 0 ≤ S j x := by
  let P : ℕ → Prop := fun j => ∀ x ∈ Icc a b, 0 ≤ S j x
  have hall : ∀ j, j ≤ J + 1 → P j := by
    intro j hj
    apply Nat.decreasingInduction (n := J + 1)
      (motive := fun k _hk => P k) (m := j) (mn := hj)
    · intro k hk hnext
      have hkJ : k ≤ J := by omega
      apply nonnegativeOn_Icc_of_deriv_sub_reaction_nonnegative hab
        (hScont k hkJ) (hRcont k hkJ) (hSdiff k hkJ)
      · intro x hx
        rw [hflow k hkJ x hx]
        have hnextx : 0 ≤ S (k + 1) x :=
          hnext x ⟨hx.1.le, hx.2.le⟩
        have htransport : 0 ≤ B k x * S (k + 1) x :=
          mul_nonneg (hB k hkJ x hx) hnextx
        linarith [hA k hkJ x hx]
      · exact hinit k hkJ
    · exact hboundary
  intro j hj
  exact hall j (hj.trans (Nat.le_succ J))

end

end HTGeometry
