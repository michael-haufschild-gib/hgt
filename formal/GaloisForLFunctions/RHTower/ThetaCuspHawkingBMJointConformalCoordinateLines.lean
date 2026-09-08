import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointConformalCurveJets
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual coordinate second derivatives recovered from affine coordinate lines. -/
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMJointConformal
noncomputable section
attribute [-instance] NormedSpace.complexToReal

def coordinateLine {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (s : ℝ) : Fin n → ℝ :=
  Function.update p i s

theorem coordinateLine_base {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    coordinateLine p i (p i) = p := Function.update_eq_self _ _

theorem coordinateLine_hasDerivAt {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    HasDerivAt (coordinateLine p i) (Pi.single i 1) s := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa [coordinateLine,id_eq] using! hasDerivAt_id s
  · simpa [coordinateLine,h,Ne.symm h,Pi.single_apply] using! hasDerivAt_const s (p j)

theorem coordinateLine_smooth {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    ContDiff ℝ ∞ (coordinateLine p i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa [coordinateLine,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun s : ℝ => s))
  · simpa [coordinateLine,h,Ne.symm h] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p j))

/-- Coordinate second derivatives are those of the actual field restricted to an affine line. -/
theorem coordinate_secondDerivative {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (p : Fin n → ℝ) (i : Fin n) (hF : ContDiffAt ℝ 2 F p) :
    coordDeriv i (coordDeriv i F) p =
      deriv (deriv (fun s => F (coordinateLine p i s))) (p i) := by
  have hg : deriv (coordinateLine p i) = fun _ => Pi.single i 1 :=
    funext (fun s => (coordinateLine_hasDerivAt p i s).deriv)
  have he := weightedCurve_second F (fun _ => 1) (coordinateLine p i) (p i)
    (by simpa [coordinateLine_base] using hF) contDiffAt_const
    (((contDiff_infty.mp (coordinateLine_smooth p i)) 2).contDiffAt)
  have h1 : deriv (fun _ : ℝ => (1:ℂ)) = fun _ => 0 :=
    funext (fun x => (hasDerivAt_const x (1:ℂ)).deriv)
  simp [h1,hg,coordinateLine_base] at he
  rw [he]
  exact congrArg (fun L => L (Pi.single i 1)) (coordDeriv_hasFDerivAt hF i).fderiv

end
end RHTower.D4BMJointConformal
