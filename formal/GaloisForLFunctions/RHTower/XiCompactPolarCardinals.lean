import GaloisForLFunctions.RHTower.XiCompactPolarApproximation
import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.CHMDShiftedFourierReadout

/-! # Translated theta-cardinal vectors in the compact polar spectral closure -/

open Complex MeasureTheory Filter Topology Set Zeta23
noncomputable section
namespace RHTower

theorem ExponentialFirstJet.translate {f : ℝ → ℂ} (hf : ExponentialFirstJet f) (t : ℝ) :
    ExponentialFirstJet (fun x => f (x-t)) := by
  obtain ⟨hs, C, hC, hb⟩ := hf
  refine ⟨hs.comp (contDiff_id.sub contDiff_const), C*Real.exp |t|, by positivity, fun x => ?_⟩
  have htrans : HasDerivAt (fun y : ℝ => y-t) 1 x := by
    simpa using (hasDerivAt_id x).sub_const t
  have hd : deriv (fun y => f (y-t)) x = deriv f (x-t) := by
    have hcomp : HasDerivAt (fun y => f (y-t)) (deriv f (x-t)) x := by
      simpa only [one_smul] using!
        ((hs.differentiable (by norm_num) (x-t)).hasDerivAt.scomp x htrans)
    exact hcomp.deriv
  have he : Real.exp (-|x-t|) ≤ Real.exp |t| * Real.exp (-|x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := abs_add_le (x-t) t
    rw [sub_add_cancel] at h
    linarith
  rw [hd]
  have hce := mul_le_mul_of_nonneg_left he hC
  constructor
  · exact (hb (x-t)).1.trans (by nlinarith only [hce])
  · exact (hb (x-t)).2.trans (by nlinarith only [hce])

theorem translated_cardinal_mem_compactXiPolar_closure {a : ℂ}
    (ha : 0 < a.re) (hz : XiC a = 0) (t : ℝ) :
    exp (I*a*t) • xiWeilFiberIndicatorLp a + exp (-(I*a)*t) • xiWeilFiberIndicatorLp (-a) ∈
      compactXiPolarEvaluation.range.topologicalClosure := by
  obtain ⟨_, hj, _, heven, _⟩ := divisorCardinalSource_regularity ha hz
  have ht := hj.translate t
  let f := fun x => divisorCardinalSource a (x-t)
  have hp : paperFT f (I/2) = 0 ∧ paperFT f (-I/2) = 0 := by
    have h := divisorCardinalSource_poles ha hz
    constructor
    · rw [show paperFT f (I/2) = exp (I*(I/2)*t)*paperFT (divisorCardinalSource a) (I/2)
        from paperFT_comp_sub _ _ _, paperFT_eq_sourceTransform_of_even heven, h.1, mul_zero]
    · rw [show paperFT f (-I/2) = exp (I*(-I/2)*t)*paperFT (divisorCardinalSource a) (-I/2)
        from paperFT_comp_sub _ _ _, paperFT_eq_sourceTransform_of_even heven, h.2, mul_zero]
  have hv := complexXiEvaluation_mem_compactPolar_closure ht.1 ht.re ht.im hp.1 hp.2
  have hne : a ≠ -a := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.neg_re] at hr
    linarith
  convert hv using 1
  apply Subtype.ext
  funext q
  rw [complexXiEvaluation_apply]
  change (exp (I*a*t)*xiWeilFiberIndicatorLp a q +
    exp (-(I*a)*t)*xiWeilFiberIndicatorLp (-a) q) = paperFT f (xiSpectralPoint q)
  rw [paperFT_comp_sub, paperFT_eq_sourceTransform_of_even heven,
    divisorCardinalSource_transform ha hz (XiC_xiSpectralPoint_eq_zero q)]
  by_cases hqa : xiSpectralPoint q = a
  · simp [xiWeilFiberIndicatorLp_apply, hqa, hne]
  · by_cases hqn : xiSpectralPoint q = -a
    · simp [xiWeilFiberIndicatorLp_apply, hqn, Ne.symm hne, mul_neg, neg_mul]
    · simp [xiWeilFiberIndicatorLp_apply, hqa, hqn]

end RHTower
