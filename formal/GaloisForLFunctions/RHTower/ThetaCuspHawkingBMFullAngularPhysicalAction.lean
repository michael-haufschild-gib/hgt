import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularJointJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleAction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Literal physical-height action of the full theta-circle response.

`angularMean_laplacian_equation` is proved in the logarithmic height `k`.
The Peierls current, however, contracts physical `(X,Y)` two-jets.  This file
proves the exact log-chart transport, including the indispensable `-∂k`
connection term.  It neither replaces the circle field by a mode nor asserts
any global tail or cap-limit estimate.
-/

namespace RHTower.D4BMFullAngularPhysicalAction

open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMNativeCircle D4BMCausalKernel D4BMGlobalAngularResponse
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularCircleJointJets

noncomputable section
set_option autoImplicit false

private theorem logLift_first (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => g (Real.log t))
      (deriv g (Real.log y) * (y : ℂ)⁻¹) y := by
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have hg' := (hg.differentiable (by simp) (Real.log y)).hasDerivAt
  apply (hg'.scomp y hlog).congr_deriv
  simp only [Complex.real_smul, Complex.ofReal_inv]
  ring

private theorem smooth_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (deriv g) :=
  (contDiff_infty_iff_deriv.mp hg).2

private theorem logLift_second (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => g (Real.log s)) t)
      ((deriv (deriv g) (Real.log y) - deriv g (Real.log y)) * (y : ℂ)⁻¹ ^ (2 : ℕ)) y := by
  have hpos : ∀ᶠ t in 𝓝 y, 0 < t := by
    exact (isOpen_lt continuous_const continuous_id).mem_nhds hy
  have he : (fun t : ℝ => deriv (fun s : ℝ => g (Real.log s)) t) =ᶠ[𝓝 y]
      fun t => deriv g (Real.log t) * (t : ℂ)⁻¹ := by
    filter_upwards [hpos] with t ht
    exact (logLift_first g hg t ht).deriv
  have ha := logLift_first (deriv g) (smooth_deriv g hg) y hy
  have hb : HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-(y : ℂ)⁻¹ ^ (2 : ℕ)) y := by
    convert (hasDerivAt_inv hy.ne').ofReal_comp using 1
    · ext t
      simp only [Complex.ofReal_inv]
    · push_cast
      field_simp [hy.ne']
  convert (ha.mul hb).congr_of_eventuallyEq he using 1 <;> first | rfl | ring

private def physicalLift (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := F x (Real.log y)

private theorem physicalLift_action (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) (x y : ℝ) (hy : 0 < y) :
    (y : ℂ)^(2 : ℕ) *
        (deriv (deriv (fun u : ℝ => physicalLift F u y)) x +
          deriv (deriv (fun v : ℝ => physicalLift F x v)) y) =
      (Real.exp (Real.log y) : ℂ)^(2 : ℕ) * deriv (deriv (fun u : ℝ => F u (Real.log y))) x +
        deriv (deriv (fun v : ℝ => F x v)) (Real.log y) -
          deriv (fun v : ℝ => F x v) (Real.log y) := by
  have hg : ContDiff ℝ ∞ (fun v : ℝ => F x v) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hv := (logLift_second (fun v : ℝ => F x v) hg y hy).deriv
  change (y : ℂ)^(2 : ℕ) *
      (deriv (deriv (fun u : ℝ => F u (Real.log y))) x +
        deriv (deriv (fun v : ℝ => F x (Real.log v))) y) = _
  rw [hv]
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Real.exp_log hy]
  field_simp [hy0]
  ring

private theorem angularMean_base_smooth (q : XiZeroCopy) (branch : Bool) (d : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => angularMean q branch d p.1 p.2) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ![d, p.1, p.2]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_fst
    · exact contDiff_snd
  simpa [Function.comp_def] using (angularMean_joint_smooth q branch).comp hmap

/-- The literal full circle response in the physical base chart, as its actual two-jet. -/
def physicalMeanJet (q : XiZeroCopy) (branch : Bool) (d : ℝ) (z : Point) :
    ScalarTwoJet (Fin 2) ℂ :=
  ScalarTwoJet.ofField (physicalMean q branch d) z

/-- The physical `(X,Y)` action density of the literal circle response. -/
def physicalMeanAction (q : XiZeroCopy) (branch : Bool) (d x y : ℝ) : ℂ :=
  (y : ℂ)^(2 : ℕ) *
    (deriv (deriv (fun u : ℝ => physicalMean q branch d ![u,y])) x +
      deriv (deriv (fun v : ℝ => physicalMean q branch d ![x,v])) y)

/-- The native forcing mean expressed in the same physical chart. -/
def physicalNativeMean (q : XiZeroCopy) (d x y : ℝ) : ℂ :=
  D4BMNativeCircle.mean q d x (Real.log y)

/-- Exact physical-height form of the full-circle forced action.

This converts the pre-existing logarithmic-height equation to the actual
`(X,Y)` field used by the Peierls two-jet.  The `-∂k` contribution is retained
through `logLift_second`; omitting it would produce a false physical action. -/
theorem physicalMean_action_equation (q : XiZeroCopy) (branch : Bool) (d x y : ℝ)
    (hy : 0 < y) :
    physicalMeanAction q branch d x y =
      parameter q branch *
        (physicalMean q branch d ![x,y] + physicalNativeMean q d x y) := by
  unfold physicalMeanAction physicalNativeMean physicalMean
  change (y : ℂ)^(2 : ℕ) *
      (deriv (deriv (fun u : ℝ => angularMean q branch d u (Real.log y))) x +
        deriv (deriv (fun v : ℝ => angularMean q branch d x (Real.log v))) y) = _
  calc
    _ = (Real.exp (Real.log y) : ℂ)^(2 : ℕ) *
        deriv (deriv (fun u : ℝ => angularMean q branch d u (Real.log y))) x +
        deriv (deriv (fun v : ℝ => angularMean q branch d x v)) (Real.log y) -
          deriv (fun v : ℝ => angularMean q branch d x v) (Real.log y) :=
      physicalLift_action (fun u v => angularMean q branch d u v)
        (angularMean_base_smooth q branch d) x y hy
    _ = _ := angularMean_laplacian_equation q branch d x (Real.log y)

end
end RHTower.D4BMFullAngularPhysicalAction
