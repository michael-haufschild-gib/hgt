import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelDecay
import GaloisForLFunctions.goldbach.LiLiu.Boundary.TwoEdges
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-! # The compact selfadjoint integral operator on both arithmetic boundaries

Clipping the real coordinate extends the kernel continuously off the two
lines. This extension agrees with the arithmetic formula throughout the
closed strip. The quarter-power bounds give square integrability on each
of the four pairs of edges.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter HTGeometry
open scoped ENNReal ComplexConjugate
noncomputable section

def edgeDecay (t : ℝ) := (1+|t|)^(-(3/4:ℝ))

theorem edgeDecay_nonneg (t : ℝ) : 0 ≤ edgeDecay t := Real.rpow_nonneg (by positivity) _

theorem edgeDecay_sq_line_integrable : Integrable (fun t : ℝ => edgeDecay t ^ 2) := by
  have H := HTGeometry.TestFunctionPerron.integrable_one_add_abs_rpow (r := -(3/2:ℝ)) (by norm_num)
  have h (t : ℝ) : edgeDecay t ^ 2 = (1+|t|)^(-(3/2:ℝ)) := by
    rw [edgeDecay,← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    norm_num
  simpa only [h] using H

theorem edgeDecay_sq_integrable (a b : ℝ) :
    Integrable (fun z : ℂ => edgeDecay z.im ^ 2) (boundaryMeasure a b) := by
  have hm : Measurable (fun z : ℂ => edgeDecay z.im ^ 2) :=
    ((measurable_const.add continuous_im.measurable.abs).pow_const _).pow_const 2
  rw [integrable_boundaryMeasure_iff hm]
  simpa only [mellinLine_im] using And.intro edgeDecay_sq_line_integrable edgeDecay_sq_line_integrable

def extendedKernel (N : ℕ) [NeZero N] (a : ℝ) (s z : ℂ) : ℂ :=
  boundaryKernel N (clippedPoint a (1/8) s) (clippedPoint a (1/8) z)

theorem extendedKernel_continuous {n : ℕ} (h : modulusGRH (n+1)) {a : ℝ}
    (ha : 0 < a) (hab : a ≤ 1/8) : Continuous (Function.uncurry (extendedKernel (n+1) a)) := by
  have hc := clippedPoint_continuous a (1/8)
  have hstrip (z : ℂ) : (clippedPoint a (1/8) z).re ∈ Ioo (0:ℝ) (3/2) :=
    ⟨ha.trans_le (clippedPoint_re hab z).1,lt_of_le_of_lt (clippedPoint_re hab z).2 (by norm_num)⟩
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (boundaryKernel_continuousAt h (p := (clippedPoint a (1/8) p.1,clippedPoint a (1/8) p.2))
    (hstrip _) (hstrip _)).comp
      (f := fun q : ℂ × ℂ => (clippedPoint a (1/8) q.1,clippedPoint a (1/8) q.2))
      ((hc.comp continuous_fst).prodMk (hc.comp continuous_snd)).continuousAt

theorem extendedKernel_sq_integrable {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) :
    Integrable (fun p : ℂ × ℂ => ‖extendedKernel (n+1) a p.1 p.2‖^2)
      ((boundaryMeasure a (1/8)).prod (boundaryMeasure a (1/8))) := by
  obtain ⟨B,hB,hb⟩ := boundaryKernel_strip_decay hN h ha
  have hw := edgeDecay_sq_integrable a (1/8)
  apply ((hw.mul_prod hw).const_mul (B^2)).mono'
    ((extendedKernel_continuous h ha hab).norm.pow 2).aestronglyMeasurable
  filter_upwards with p
  change ‖‖extendedKernel (n+1) a p.1 p.2‖^2‖ ≤ B^2*(edgeDecay p.1.im^2*edgeDecay p.2.im^2)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have he := hb (clippedPoint a (1/8) p.1) (clippedPoint a (1/8) p.2)
    (clippedPoint_re hab _) (clippedPoint_re hab _)
  simp only [clippedPoint_im] at he
  have H := pow_le_pow_left₀ (norm_nonneg _) he 2
  simpa only [extendedKernel,edgeDecay,mul_pow,mul_assoc] using H

/-- Actual arithmetic kernel, with positive arc length on each of the two edges. -/
def arithmeticSqKernel {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) :
    SqIntKernel (boundaryMeasure a (1/8)) (boundaryMeasure a (1/8)) where
  toFun := extendedKernel (n+1) a
  measurable := (extendedKernel_continuous h ha hab).measurable
  energy_lt_top := by
    have hM := (extendedKernel_continuous h ha hab).measurable
    have hL := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).mpr
      (extendedKernel_sq_integrable hN h ha hab)
    have H := hL.eLpNorm_lt_top
    rw [SchurKernel.eLpNorm_two_eq] at H
    have hI := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ)<1/2)).mp H
    rw [lintegral_prod _ (hM.enorm.pow_const 2).aemeasurable] at hI
    exact hI

theorem arithmeticSqKernel_compact {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) : IsCompactOperator (arithmeticSqKernel hN h ha hab).op :=
  (arithmeticSqKernel hN h ha hab).isHilbertSchmidt_op.isCompactOperator

theorem arithmeticSqKernel_symmetric {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) : (arithmeticSqKernel hN h ha hab).op.IsSymmetric := by
  let K := arithmeticSqKernel hN h ha hab
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  change ContinuousLinearMap.adjoint K.op=K.op
  rw [K.adjoint_op]
  apply K.adjoint.op_congr
  filter_upwards with s
  filter_upwards with z
  exact boundaryKernel_hermitian _ (ha.trans_le (clippedPoint_re hab s).1)
    (ha.trans_le (clippedPoint_re hab z).1)

#print axioms arithmeticSqKernel_compact
#print axioms arithmeticSqKernel_symmetric
end
end GaloisForLFunctions.Goldbach.LiLiu
