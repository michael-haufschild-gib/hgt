import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinHeatRepresentation
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability in height for the actual continued Epstein field follows
from its Gaussian tails. The argument uses the measurable lattice count,
so no pointwise convergence of a continued Dirichlet series is required. -/

open Complex Real Set Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerEpsteinQuadrants MayerEpsteinHeatRepresentation
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeightMeasurability

private theorem measurable_thetaSum : Measurable thetaSum := by
  unfold thetaSum
  apply Measurable.tsum
  intro n
  fun_prop

private theorem measurable_rectTheta : Measurable (fun p : ℝ × ℝ => rectTheta p.1 p.2) := by
  unfold rectTheta
  exact (measurable_thetaSum.comp measurable_snd).mul
    (measurable_thetaSum.comp ((measurable_fst.pow_const 2).mul measurable_snd))

/-- The original Gaussian tail is measurable in its height parameter. -/
theorem measurable_originalTail (w : ℂ) : Measurable (originalTail w) := by
  have hf : Measurable (fun p : ℝ × ℝ =>
      (p.2 : ℂ)^(w/2-1)*((rectTheta p.1 p.2 : ℂ)-1)) := by
    have hθ := Complex.measurable_ofReal.comp measurable_rectTheta
    have hp : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ)^(w/2-1)) := by fun_prop
    exact hp.mul (hθ.sub measurable_const)
  exact hf.stronglyMeasurable.integral_prod_right.measurable

/-- The dual Gaussian tail is measurable in height, including its covolume factor. -/
theorem measurable_dualTail (w : ℂ) : Measurable (dualTail w) := by
  have hθ : Measurable (fun p : ℝ × ℝ => (rectTheta (1/p.1) p.2 : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_rectTheta.comp
      ((measurable_const.div measurable_fst).prodMk measurable_snd))
  have hf : Measurable (fun p : ℝ × ℝ =>
      (p.1 : ℂ)⁻¹*(p.2 : ℂ)^(-w/2)*((rectTheta (1/p.1) p.2 : ℂ)-1)) := by
    have hp : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹*(p.2 : ℂ)^(-w/2)) := by fun_prop
    exact hp.mul (hθ.sub measurable_const)
  exact hf.stronglyMeasurable.integral_prod_right.measurable

/-- The Poisson-defined Epstein field is measurable in height away from its source poles. -/
theorem measurable_epsteinField {w : ℂ} (hw0 : w ≠ 0) (hw2 : w ≠ 2) :
    Measurable (epsteinField w) := by
  have he : epsteinField w = fun y : ℝ => if 0 < y then
      ((Real.pi : ℂ)^(w/2)/(2*Complex.Gamma (w/2)))*
        (originalTail w y+dualTail w y-2/w+2/((y : ℂ)*(w-2))) else 0 := by
    funext y
    by_cases hy : 0 < y
    · rw [epsteinField,dif_pos hy,if_pos hy,epsteinLambda_heat_expansion hw0 hw2 hy]
    · simp only [epsteinField,dif_neg hy,if_neg hy]
  rw [he]
  apply Measurable.ite measurableSet_Ioi _ measurable_const
  apply measurable_const.mul
  exact (((measurable_originalTail w).add (measurable_dualTail w)).sub measurable_const).add
    (measurable_const.div ((Complex.measurable_ofReal).mul measurable_const))

#print axioms measurable_originalTail
#print axioms measurable_dualTail
#print axioms measurable_epsteinField
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeightMeasurability
