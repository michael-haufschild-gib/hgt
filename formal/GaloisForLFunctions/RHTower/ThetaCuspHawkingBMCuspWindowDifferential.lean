import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPeriodization
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
Exact cancellation of the horizontal partition derivatives before reconstructing cusp wave packets.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

def complexCuspWindow (x : ℝ) : ℂ := cuspWindow x

theorem complexCuspWindow_smooth : ContDiff ℝ ∞ complexCuspWindow :=
  Complex.ofRealCLM.contDiff.comp cuspWindow_smooth

/-- The compact window and its two neighbors form an exact unit partition. -/
theorem complexCuspWindow_triple (x : ℝ) (hx : |x| ≤ 1) :
    complexCuspWindow (x-1)+complexCuspWindow x+complexCuspWindow (x+1) = 1 := by
  have h := abs_le.mp hx
  simp only [complexCuspWindow,cuspWindow,Complex.ofReal_sub]
  rw [show x-1+1=x by ring,
    Real.smoothTransition.zero_of_nonpos (x := x-1) (by linarith),
    Real.smoothTransition.one_of_one_le (x := x+1+1) (by linarith)]
  simp only [Complex.ofReal_zero,Complex.ofReal_one]
  ring

/-- The literal second derivatives of the horizontal partition cancel exactly.
Thus cusp test reconstruction creates no horizontal Laplacian remainder. -/
theorem complexCuspWindow_second_triple (x : ℝ) (hx : |x| ≤ 1/2) :
    deriv (deriv complexCuspWindow) (x-1)+deriv (deriv complexCuspWindow) x+
      deriv (deriv complexCuspWindow) (x+1) = 0 := by
  let a := complexCuspWindow
  let F : ℝ → ℂ := fun t => a (t-1)+a t+a (t+1)
  have ha : ContDiff ℝ ∞ a := complexCuspWindow_smooth
  have hd : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdda : Differentiable ℝ (deriv a) := hd.differentiable (by simp)
  have hG : F =ᶠ[𝓝 x] (fun _ => 1) := by
    have hx' : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx'] with t ht
    exact complexCuspWindow_triple t ht.le
  have hzero := hG.deriv.deriv_eq
  have hfirst : deriv F = fun t => deriv a (t-1)+deriv a t+deriv a (t+1) := by
    funext t
    dsimp [F]
    rw [deriv_fun_add,deriv_fun_add,deriv_comp_sub_const,deriv_comp_add_const]
    all_goals fun_prop
  rw [hfirst,deriv_fun_add,deriv_fun_add,deriv_comp_sub_const,deriv_comp_add_const] at hzero
  · simpa [a] using hzero
  all_goals fun_prop

theorem complexCuspWindow_second_support :
    tsupport (deriv (deriv complexCuspWindow)) ⊆ Icc (-1) 1 := by
  apply tsupport_deriv_subset.trans (tsupport_deriv_subset.trans _)
  apply (closure_mono (show Function.support complexCuspWindow ⊆ Function.support cuspWindow from ?_)).trans cuspWindow_support
  intro x hx
  simpa only [complexCuspWindow,Function.mem_support,Complex.ofReal_ne_zero] using hx

end
end RHTower.D4BMModularCore
