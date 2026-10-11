import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver
import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence
import Mathlib.Topology.Maps.Proper.Basic

/-! # Sharp profiles of deterministic zeta returns

The disc carries only geometric admissibility. No recurrence or zero-free premise
is used to place the literal return indicator in the proven Fourier endpoint.
-/

namespace RHTower
noncomputable section
open Complex Metric Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

/-- An actual closed disc in the open right half of the critical strip. -/
structure PaperZetaReturnDisc where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  strip : ∀ s ∈ closedBall center radius, 1 / 2 < s.re ∧ s.re < 1

/-- Actual deterministic self-return shifts on the disc. -/
def paperZetaReturnTimes (D : PaperZetaReturnDisc) (ε : ℝ) : Set ℝ :=
  zetaReturnSet (closedBall D.center D.radius) ε

theorem paperZetaReturnTimes_isOpen (D : PaperZetaReturnDisc) (ε : ℝ) :
    IsOpen (paperZetaReturnTimes D ε) := by
  let K := ↥(closedBall D.center D.radius)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_closedBall D.center D.radius)
  let F : ℝ × K → ℝ := fun p =>
    ‖riemannZeta (p.2.val + (p.1 : ℂ) * I) - riemannZeta p.2.val‖
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hs : (p.2.val : ℂ) ≠ 1 := by
      intro h
      have := (D.strip p.2.val p.2.property).2
      simp [h] at this
    have ht : p.2.val + (p.1 : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        zero_mul, sub_self, add_zero, one_re] at this
      exact (ne_of_lt (D.strip p.2.val p.2.property).2) this
    have hshift : ContinuousAt (fun q : ℝ × K => q.2.val + (q.1 : ℂ) * I) p := by
      dsimp [K]
      fun_prop
    have hbase : ContinuousAt (fun q : ℝ × K => q.2.val) p := by
      dsimp [K]
      fun_prop
    exact (((differentiableAt_riemannZeta ht).continuousAt.comp
      (f := fun q : ℝ × K => q.2.val + (q.1 : ℂ) * I) hshift).sub
      ((differentiableAt_riemannZeta hs).continuousAt.comp
        (f := fun q : ℝ × K => q.2.val) hbase)).norm
  have hb : IsClosed (Prod.fst '' {p | ε ≤ F p}) :=
    isClosedMap_fst_of_compactSpace _ (isClosed_le continuous_const hc)
  have he : paperZetaReturnTimes D ε = (Prod.fst '' {p | ε ≤ F p})ᶜ := by
    ext τ
    simp only [paperZetaReturnTimes, zetaReturnSet, mem_setOf_eq, mem_compl_iff,
      mem_image, Prod.exists]
    simp [F, K, not_le]
  rw [he]
  exact hb.isOpen_compl

theorem paperZetaReturnTimes_measurable (D : PaperZetaReturnDisc) (ε : ℝ) :
    MeasurableSet (paperZetaReturnTimes D ε) :=
  (paperZetaReturnTimes_isOpen D ε).measurableSet

/-- The sharp return indicator on a window of physical length `T`. -/
def paperZetaReturnProfile (D : PaperZetaReturnDisc) (ε T x : ℝ) : ℂ :=
  (paperZetaReturnTimes D ε).indicator (fun _ => 1) (T * x)

theorem paperZetaReturnProfile_measurable (D : PaperZetaReturnDisc) (ε T : ℝ) :
    Measurable (paperZetaReturnProfile D ε T) :=
  (measurable_const.indicator (paperZetaReturnTimes_measurable D ε)).comp
    (measurable_const.mul measurable_id)

theorem paperZetaReturnProfile_norm_le (D : PaperZetaReturnDisc) (ε T x : ℝ) :
    ‖paperZetaReturnProfile D ε T x‖ ≤ 1 := by
  classical
  by_cases h : T * x ∈ paperZetaReturnTimes D ε <;>
    simp [paperZetaReturnProfile, h]

theorem paperZetaReturnProfile_memLp (D : PaperZetaReturnDisc) (ε T : ℝ) :
    MemLp (paperZetaReturnProfile D ε T) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (paperZetaReturnProfile_measurable D ε T).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (paperZetaReturnProfile_norm_le D ε T))

end
end RHTower
