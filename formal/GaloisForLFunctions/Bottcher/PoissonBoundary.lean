/-
# Poisson kernel: positivity, continuity, unit mass (toward Dirichlet ingredient 3/3)

Foundational facts about the Poisson kernel on the circle, for the harmonic Schwarz reflection
principle.  These feed the approximate-identity argument that the Poisson integral attains its
continuous boundary values (the last Dirichlet ingredient).

* `poissonKernel_continuousOn_sphere` — `z ↦ poissonKernel c w z` is continuous on `sphere c R`
  (denominator `‖z - w‖² ≠ 0` there, `w` interior);
* `poissonKernel_nonneg` — the kernel is `≥ 0` (mathlib's lower bound `le_re_herglotzRieszKernel`);
* `poissonKernel_circleAverage_eq_one` — the kernel has unit mass (the reproducing property
  `DiffContOnCl.circleAverage_poissonKernel_smul` applied to the constant `1`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib

open Complex Set Metric MeasureTheory

namespace Bottcher

theorem poissonKernel_continuousOn_sphere {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) : ContinuousOn (poissonKernel c w) (sphere c R) := by
  have hzw : ∀ z ∈ sphere c R, (z - c) - (w - c) ≠ 0 := by
    intro z hz
    rw [show (z - c) - (w - c) = z - w by ring, sub_ne_zero]
    intro h; subst h
    rw [mem_sphere, dist_comm] at hz; rw [mem_ball, dist_comm] at hw
    rw [hz] at hw; exact lt_irrefl R hw
  have hrw : poissonKernel c w = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 := by
    funext z; exact poissonKernel_def c w z
  rw [hrw]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hzw z hz))

theorem poissonKernel_nonneg {c w z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 ≤ poissonKernel c w z := by
  have hwc : ‖w - c‖ < R := by rw [mem_ball, dist_eq_norm] at hw; exact hw
  have hbound := le_re_herglotzRieszKernel hz hw
  have hpk : poissonKernel c w z = ((z - c + (w - c)) / ((z - c) - (w - c))).re := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
  rw [hpk]
  refine le_trans ?_ hbound
  apply div_nonneg <;> [linarith; linarith [norm_nonneg (w - c)]]

theorem poissonKernel_circleAverage_eq_one {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w) c R = 1 := by
  have hdc : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball c R) :=
    ⟨differentiableOn_const 1, continuousOn_const⟩
  have h := DiffContOnCl.circleAverage_poissonKernel_smul hdc hw
  have hfun : (poissonKernel c w • fun _ : ℂ => (1 : ℂ)) = (fun z => ((poissonKernel c w z : ℝ) : ℂ)) := by
    funext z; simp
  rw [hfun] at h
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp hw)
  have hci : CircleIntegrable (poissonKernel c w) c R :=
    (show ContinuousOn (poissonKernel c w) (sphere c |R|) by
      rw [abs_of_pos hR]; exact poissonKernel_continuousOn_sphere hw).circleIntegrable'
  have hcomm := ContinuousLinearMap.circleAverage_comp_comm Complex.ofRealCLM hci
  have hfun2 : (⇑Complex.ofRealCLM ∘ poissonKernel c w) = (fun z => ((poissonKernel c w z : ℝ) : ℂ)) := rfl
  rw [hfun2, h] at hcomm
  have h1 : ((Real.circleAverage (poissonKernel c w) c R : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofRealCLM_apply]; exact hcomm.symm
  exact_mod_cast h1

end Bottcher
