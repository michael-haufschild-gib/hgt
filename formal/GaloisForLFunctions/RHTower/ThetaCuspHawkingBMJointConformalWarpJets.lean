import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceRadialUnit
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual hyperbolic coordinate and square-root weight derivatives for the joint wave. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointConformal
open D4BMJointSource
noncomputable section

def warp (t : ℝ) : ℝ := (Real.cosh t)⁻¹
def radialRoot (t : ℝ) : ℝ := Real.sqrt (Real.cosh t)
def heightRootFirst (y : ℝ) : ℝ := Real.sqrt y/(2*y)

theorem warp_pos (t : ℝ) : 0 < warp t := inv_pos.mpr (Real.cosh_pos t)

theorem warp_relation (t : ℝ) : radialUnit t^(2 : ℕ)+warp t^(2 : ℕ) = 1 := by
  have hc := ne_of_gt (Real.cosh_pos t)
  unfold warp radialUnit
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem warp_hasDerivAt (t : ℝ) : HasDerivAt warp (warp t*radialUnit t) t := by
  apply ((Real.hasDerivAt_cosh t).inv (ne_of_gt (Real.cosh_pos t))).congr_deriv
  dsimp [warp,radialUnit]
  field_simp

theorem radialUnit_warp_derivative (t : ℝ) : HasDerivAt radialUnit (-(warp t)^(2 : ℕ)) t := by
  convert radialUnit_hasDerivAt t using 1
  linarith [warp_relation t]

theorem warpFirst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x => warp x*radialUnit x) (warp t*(2*radialUnit t^(2 : ℕ)-1)) t := by
  apply ((warp_hasDerivAt t).mul (radialUnit_hasDerivAt t)).congr_deriv
  ring

theorem radialRoot_pos (t : ℝ) : 0 < radialRoot t := Real.sqrt_pos.mpr (Real.cosh_pos t)

theorem radialRoot_hasDerivAt (t : ℝ) :
    HasDerivAt radialRoot (-radialUnit t/2*radialRoot t) t := by
  apply ((Real.hasDerivAt_cosh t).sqrt (ne_of_gt (Real.cosh_pos t))).congr_deriv
  dsimp [radialRoot,radialUnit]
  have hc := ne_of_gt (Real.cosh_pos t)
  have hs := ne_of_gt (Real.sqrt_pos.mpr (Real.cosh_pos t))
  field_simp
  rw [Real.sq_sqrt (Real.cosh_pos t).le]

theorem radialRootFirst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x => -radialUnit x/2*radialRoot x)
      ((warp t^(2 : ℕ)/2+radialUnit t^(2 : ℕ)/4)*radialRoot t) t := by
  apply (((radialUnit_warp_derivative t).neg.div_const 2).mul
    (radialRoot_hasDerivAt t)).congr_deriv
  simp only [Pi.neg_apply]
  ring

theorem heightRoot_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt Real.sqrt (heightRootFirst y) y := by
  apply (Real.hasDerivAt_sqrt (ne_of_gt hy)).congr_deriv
  unfold heightRootFirst
  have hs := ne_of_gt (Real.sqrt_pos.mpr hy)
  field_simp
  exact (Real.sq_sqrt hy.le).symm

theorem heightRootFirst_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt heightRootFirst (-Real.sqrt y/(4*y^(2 : ℕ))) y := by
  apply ((heightRoot_hasDerivAt y hy).div ((hasDerivAt_id y).const_mul 2)
    (by positivity : (2:ℝ)*y ≠ 0)).congr_deriv
  dsimp [heightRootFirst]
  field_simp
  ring

theorem warp_smooth : ContDiff ℝ ∞ warp :=
  Real.contDiff_cosh.inv (fun t => ne_of_gt (Real.cosh_pos t))

theorem radialUnit_smooth : ContDiff ℝ ∞ radialUnit :=
  Real.contDiff_sinh.neg.div Real.contDiff_cosh (fun t => ne_of_gt (Real.cosh_pos t))

theorem radialRoot_smooth : ContDiff ℝ ∞ radialRoot :=
  Real.contDiff_cosh.sqrt (fun t => ne_of_gt (Real.cosh_pos t))

end
end RHTower.D4BMJointConformal
