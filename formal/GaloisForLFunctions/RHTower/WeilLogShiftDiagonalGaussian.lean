import GaloisForLFunctions.RHTower.WeilLogShiftJointProbabilityLaw
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The limiting joint law is the diagonal image of a real Gaussian of variance one quarter. -/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace RHTower

def finiteWeilDiagonalPoint (z : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![z, z]

theorem continuous_finiteWeilDiagonalPoint : Continuous finiteWeilDiagonalPoint := by
  unfold finiteWeilDiagonalPoint
  fun_prop

theorem finiteWeilDiagonalPoint_inner (z : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (finiteWeilDiagonalPoint z) v = (v 0 + v 1) * z := by
  simp only [finiteWeilDiagonalPoint, PiLp.inner_apply, Fin.sum_univ_two,
    Real.inner_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def finiteWeilDiagonalGaussian : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ProbabilityMeasure.map (⟨gaussianReal 0 (1 / 4), inferInstance⟩ : ProbabilityMeasure ℝ)
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable

theorem finiteWeilDiagonalGaussian_charFun (v : EuclideanSpace ℝ (Fin 2)) :
    charFun (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) v =
      (Real.exp (-((v 0 + v 1) ^ 2 / 8)) : ℂ) := by
  change charFun (Measure.map finiteWeilDiagonalPoint (gaussianReal 0 (1 / 4))) v = _
  rw [charFun_apply, integral_map
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable (by fun_prop)]
  simp_rw [finiteWeilDiagonalPoint_inner, Complex.ofReal_mul]
  rw [← charFun_apply_real, charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem finiteWeilDiagonalGaussian_diagonal_mass :
    (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2)))
      {v | v 0 = v 1} = 1 := by
  change (Measure.map finiteWeilDiagonalPoint (gaussianReal 0 (1 / 4))) {v | v 0 = v 1} = 1
  rw [Measure.map_apply continuous_finiteWeilDiagonalPoint.measurable
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet]
  simp [finiteWeilDiagonalPoint]

end RHTower
