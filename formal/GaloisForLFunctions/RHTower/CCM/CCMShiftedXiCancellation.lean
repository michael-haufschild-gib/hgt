import GaloisForLFunctions.RHTower.CCM.CCMRectangularDirichletLandau
import Mathlib.Analysis.Calculus.DSlope

/-!
# Xi cancellation of the rectangular shifted-zeta poles

Multiplication by the translated completed Xi factor cancels every shifted
zeta pole at the actual Xi divisor.  This module begins the multiplicity-safe
pole-jet contradiction required by the rectangular CCM route.
-/

open Complex Filter Function

namespace RHTower

noncomputable section

/-- Zeta with its pole at `1` filled by its residue. -/
def regularizedRiemannZeta : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

@[simp] theorem regularizedRiemannZeta_one :
    regularizedRiemannZeta 1 = 1 := by
  rw [regularizedRiemannZeta, Function.update_self]

theorem regularizedRiemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    regularizedRiemannZeta s = (s - 1) * riemannZeta s := by
  rw [regularizedRiemannZeta, Function.update_of_ne hs]

/-- The pole-filled zeta function is entire. -/
theorem differentiable_regularizedRiemannZeta :
    Differentiable ℂ regularizedRiemannZeta := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hraw : DifferentiableAt ℂ
          (fun z => (z - 1) * riemannZeta z) t :=
        (differentiableAt_id.sub_const 1).mul
          (differentiableAt_riemannZeta ht)
      apply hraw.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne.mem_nhds ht)] with z hz
      exact regularizedRiemannZeta_of_ne_one hz
    · simpa only [regularizedRiemannZeta, continuousAt_update_same] using
        riemannZeta_residue_one
  · have hraw : DifferentiableAt ℂ
        (fun z => (z - 1) * riemannZeta z) s :=
      (differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta hs)
    apply hraw.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne.mem_nhds hs)] with z hz
    exact regularizedRiemannZeta_of_ne_one hz

/-- The shifted zeta pole belonging to a right-half Xi copy. -/
def xiRightShiftedPole (q : XiRightZeroCopy) : ℂ :=
  1 + xiRightCenteredZero q

/-- **A uniform shifted-pole bound bounds the transverse supremum.**  The shift is by one, so
`Re (pole) ≤ σ` reads `Re (centered zero) ≤ σ - 1` at every copy, and the supremum of the centered
real parts inherits the bound. -/
theorem xiRightTransverseSup_le_of_shiftedPole_re_le {σ : ℝ}
    (hne : Nonempty XiRightZeroCopy)
    (hpole : ∀ q : XiRightZeroCopy, (xiRightShiftedPole q).re ≤ σ) :
    xiRightTransverseSup ≤ σ - 1 := by
  haveI := hne
  apply csSup_le (Set.range_nonempty _)
  intro x hx
  obtain ⟨q, rfl⟩ := hx
  have hq := hpole q
  rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hq
  linarith

theorem xiRightCenteredZero_eq_support_sub_half (q : XiRightZeroCopy) :
    xiRightCenteredZero q = (q.1.1 : ℂ) - 1 / 2 := by
  exact I_mul_xiSpectralPoint q.1

theorem xiRightShiftedPole_sub_half (q : XiRightZeroCopy) :
    xiRightShiftedPole q - 1 / 2 = (q.1.1 : ℂ) := by
  rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
  ring

theorem xiRightShiftedPole_sub_centeredZero (q : XiRightZeroCopy) :
    xiRightShiftedPole q - xiRightCenteredZero q = 1 := by
  rw [xiRightShiftedPole]
  ring

/-- One Xi-multiplied shifted-zeta term, filled at its removable singularity
with the derivative of Xi at the corresponding divisor point. -/
def xiShiftedZetaCancelledTerm (q : XiRightZeroCopy) : ℂ → ℂ :=
  Function.update
    (fun s => xi (s - 1 / 2) *
      riemannZeta (s - xiRightCenteredZero q))
    (xiRightShiftedPole q) (deriv xi (q.1.1 : ℂ))

/-- The cancelled term is exactly a Xi divided difference times pole-filled
zeta. -/
theorem xiShiftedZetaCancelledTerm_eq_dslope_mul_regularized
    (q : XiRightZeroCopy) (s : ℂ) :
    xiShiftedZetaCancelledTerm q s =
      dslope xi (q.1.1 : ℂ) (s - 1 / 2) *
        regularizedRiemannZeta (s - xiRightCenteredZero q) := by
  by_cases hs : s = xiRightShiftedPole q
  · subst s
    rw [xiShiftedZetaCancelledTerm, Function.update_self,
      xiRightShiftedPole_sub_half, dslope_same,
      xiRightShiftedPole_sub_centeredZero, regularizedRiemannZeta_one,
      mul_one]
  · rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hs]
    have hu : s - 1 / 2 ≠ (q.1.1 : ℂ) := by
      intro heq
      apply hs
      rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
      linear_combination heq
    have hz : s - xiRightCenteredZero q ≠ 1 := by
      intro heq
      apply hs
      rw [xiRightShiftedPole]
      linear_combination heq
    rw [dslope_of_ne xi hu, regularizedRiemannZeta_of_ne_one hz,
      slope_def_module]
    have hxi : xi (q.1.1 : ℂ) = 0 :=
      xi_eq_zero_of_mem_divisor_support q.1.1
    rw [hxi, sub_zero]
    have hcoord :
        (s - 1 / 2) - (q.1.1 : ℂ) =
          (s - xiRightCenteredZero q) - 1 := by
      rw [xiRightCenteredZero_eq_support_sub_half]
      ring
    rw [hcoord]
    change xi (s - 1 / 2) * riemannZeta (s - xiRightCenteredZero q) =
      (((s - xiRightCenteredZero q) - 1)⁻¹ * xi (s - 1 / 2)) *
        (((s - xiRightCenteredZero q) - 1) *
          riemannZeta (s - xiRightCenteredZero q))
    have hden : (s - xiRightCenteredZero q) - 1 ≠ 0 :=
      sub_ne_zero.mpr hz
    field_simp

/-- Every individually Xi-cancelled shifted-zeta term is entire. -/
theorem differentiable_xiShiftedZetaCancelledTerm
    (q : XiRightZeroCopy) :
    Differentiable ℂ (xiShiftedZetaCancelledTerm q) := by
  intro s
  rcases eq_or_ne s (xiRightShiftedPole q) with rfl | hs
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htne : t ≠ xiRightShiftedPole q := by simpa using ht
      have hz : t - xiRightCenteredZero q ≠ 1 := by
        intro heq
        apply htne
        rw [xiRightShiftedPole]
        linear_combination heq
      have hraw : DifferentiableAt ℂ
          (fun z => xi (z - 1 / 2) *
            riemannZeta (z - xiRightCenteredZero q)) t :=
        ((xi_analyticOnNhd_univ (t - 1 / 2) (Set.mem_univ _)).differentiableAt.comp t
          (differentiableAt_id.sub_const (1 / 2))).mul
            ((differentiableAt_riemannZeta hz).comp t
              (differentiableAt_id.sub_const (xiRightCenteredZero q)))
      apply hraw.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne.mem_nhds htne)] with z hz
      rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hz]
    · rw [show xiShiftedZetaCancelledTerm q =
          fun s => dslope xi (q.1.1 : ℂ) (s - 1 / 2) *
            regularizedRiemannZeta (s - xiRightCenteredZero q) by
        funext z
        exact xiShiftedZetaCancelledTerm_eq_dslope_mul_regularized q z]
      apply ContinuousAt.mul
      · have hxiDiff : DifferentiableAt ℂ xi (q.1.1 : ℂ) :=
          (xi_analyticOnNhd_univ (q.1.1 : ℂ) (Set.mem_univ _)).differentiableAt
        have hds : ContinuousAt (dslope xi (q.1.1 : ℂ)) (q.1.1 : ℂ) :=
          continuousAt_dslope_same.mpr hxiDiff
        have hu : ContinuousAt (fun z : ℂ => z - 1 / 2)
            (xiRightShiftedPole q) := continuousAt_id.sub_const _
        simpa only [Function.comp_apply] using!
          hds.comp_of_eq hu (xiRightShiftedPole_sub_half q)
      · have hzcont : ContinuousAt regularizedRiemannZeta 1 :=
          differentiable_regularizedRiemannZeta.continuous.continuousAt
        have hu : ContinuousAt (fun z : ℂ => z - xiRightCenteredZero q)
            (xiRightShiftedPole q) := continuousAt_id.sub_const _
        simpa only [Function.comp_apply] using!
          hzcont.comp_of_eq hu (xiRightShiftedPole_sub_centeredZero q)
  · have hraw : DifferentiableAt ℂ
        (fun z => xi (z - 1 / 2) *
          riemannZeta (z - xiRightCenteredZero q)) s := by
      have hz : s - xiRightCenteredZero q ≠ 1 := by
        intro heq
        apply hs
        rw [xiRightShiftedPole]
        linear_combination heq
      exact ((xi_analyticOnNhd_univ (s - 1 / 2) (Set.mem_univ _)).differentiableAt.comp s
        (differentiableAt_id.sub_const (1 / 2))).mul
          ((differentiableAt_riemannZeta hz).comp s
            (differentiableAt_id.sub_const (xiRightCenteredZero q)))
    apply hraw.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne.mem_nhds hs)] with z hz
    rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hz]

end

end RHTower
