import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairHeat
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite normalization defects converge to the zeta response

The repaired kernel is dominated by the original kernel and has an exact
exponential error. Every finite response has an absolutely convergent Mellin
integral on the open unit strip. Dominated convergence identifies the limit of
these actual finite-defect responses with -Gamma(s) zeta(s).
-/

open Complex Set Filter MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section


theorem cubicFiniteKernel_norm_le (k : ℕ) (t : ℝ) :
    ‖cubicFiniteKernel k t‖ ≤ ‖cubicCuspKernel t‖ := by
  by_cases ht : 0<t
  · rw [cubicFiniteKernel_factor,norm_mul]
    have he : Real.exp (-(k:ℝ)*t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have hk := Nat.cast_nonneg (α := ℝ) k; nlinarith)
    have hf : ‖(1:ℂ)-(Real.exp (-(k:ℝ)*t):ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr he)]
      have := Real.exp_pos (-(k:ℝ)*t)
      linarith
    simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg (cubicCuspKernel t))
  · simp [cubicFiniteKernel,cubicCuspKernel,ht]

theorem cubicFiniteKernel_error (k : ℕ) (t : ℝ) :
    ‖cubicCuspKernel t-cubicFiniteKernel k t‖=
      Real.exp (-(k:ℝ)*t)*‖cubicCuspKernel t‖ := by
  rw [cubicFiniteKernel_factor]
  have h : cubicCuspKernel t-(1-(Real.exp (-(k:ℝ)*t):ℂ))*cubicCuspKernel t=
      (Real.exp (-(k:ℝ)*t):ℂ)*cubicCuspKernel t := by ring
  rw [h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem cubicFiniteKernel_tendsto (t : ℝ) :
    Tendsto (fun k : ℕ => cubicFiniteKernel k t) atTop (𝓝 (cubicCuspKernel t)) := by
  by_cases ht : 0<t
  · have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-t)).le
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    have he : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ)*t)) atTop (𝓝 (0:ℝ)) := by
      convert hp using 1
      ext k
      rw [neg_mul,← mul_neg,Real.exp_nat_mul]
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp he
    have h := ((tendsto_const_nhds (x := (1:ℂ))).sub hc).mul (tendsto_const_nhds (x := cubicCuspKernel t))
    simpa only [Function.comp_apply,Complex.ofReal_zero,sub_zero,one_mul,cubicFiniteKernel_factor] using h
  · simp only [cubicFiniteKernel,cubicCuspKernel,if_neg ht]
    exact tendsto_const_nhds

theorem cubicFiniteKernel_converges (k : ℕ) :
    ∀ s ∈ fusionMellinStrip, MellinConvergent (cubicFiniteKernel k) s := by
  intro s hs
  have hc : Integrable (fun t : ℝ => (t:ℂ)^(s-1) • cubicCuspKernel t)
      (volume.restrict (Ioi 0)) := cubicCuspKernel_converges s hs
  have hfac : Continuous (fun t : ℝ => (1:ℂ)-(Real.exp (-(k:ℝ)*t):ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable
      (fun t : ℝ => (t:ℂ)^(s-1) • cubicFiniteKernel k t) (volume.restrict (Ioi 0)) := by
    have heq : (fun t : ℝ => (t:ℂ)^(s-1) • cubicFiniteKernel k t)=
        (fun t : ℝ => ((1:ℂ)-(Real.exp (-(k:ℝ)*t):ℂ))*
          ((t:ℂ)^(s-1) • cubicCuspKernel t)) := by
      ext t
      simp only [smul_eq_mul,cubicFiniteKernel_factor]
      ring
    rw [heq]
    exact hfac.aestronglyMeasurable.mul hc.aestronglyMeasurable
  apply MeasureTheory.Integrable.mono hc hm
  filter_upwards [] with t
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (cubicFiniteKernel_norm_le k t) (norm_nonneg _)

theorem cubicFiniteKernel_mellin_tendsto :
    ∀ s ∈ fusionMellinStrip,
      Tendsto (fun k : ℕ => mellin (cubicFiniteKernel k) s) atTop
        (𝓝 (-Complex.Gamma s*riemannZeta s)) := by
  intro s hs
  have hc := cubicCuspKernel_converges s hs
  have h := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => ‖(t:ℂ)^(s-1) • cubicCuspKernel t‖)
    (fun k => (cubicFiniteKernel_converges k s hs).aestronglyMeasurable)
    hc.norm
    (fun k => Eventually.of_forall fun t => by
      simp only [norm_smul]
      exact mul_le_mul_of_nonneg_left (cubicFiniteKernel_norm_le k t) (norm_nonneg _))
    (Eventually.of_forall fun t => (cubicFiniteKernel_tendsto t).const_smul ((t:ℂ)^(s-1)))
  change Tendsto (fun k : ℕ => mellin (cubicFiniteKernel k) s) atTop
    (𝓝 (mellin cubicCuspKernel s)) at h
  rw [cubicCuspKernel_mellin hs] at h
  exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
