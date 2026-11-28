import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Evolution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Classification

/-! # Continuity of a probability response from one positive-energy ray -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Filter Topology
open scoped NNReal

/-- Addition transports right continuity at the origin to both sides
of every positive time, using the quotient of the two forward increments. -/
private theorem ray_continuous (A : Response) (n : ℕ+)
    (origin : ContinuousAt (survivalAmplitude A n) 0) : Continuous (survivalAmplitude A n) := by
  let C := survivalAmplitude A n
  apply continuous_iff_continuousAt.mpr
  intro x
  let d (t : ℝ≥0) := (t:ℝ) - (x:ℝ)
  have dc : Continuous d := continuous_subtype_val.sub continuous_const
  have plus : Tendsto (fun t => (d t).toNNReal) (𝓝 x) (𝓝 0) := by
    have cont : Continuous (fun t => (d t).toNNReal) := continuous_real_toNNReal.comp dc
    have h := (cont.continuousAt (x := x)).tendsto
    change Tendsto (fun t => (d t).toNNReal) (𝓝 x) (𝓝 (d x).toNNReal) at h
    rwa [show d x = 0 from sub_self _, Real.toNNReal_zero] at h
  have minus : Tendsto (fun t => (-(d t)).toNNReal) (𝓝 x) (𝓝 0) := by
    have cont : Continuous (fun t => (-(d t)).toNNReal) := continuous_real_toNNReal.comp dc.neg
    have h := (cont.continuousAt (x := x)).tendsto
    change Tendsto (fun t => (-(d t)).toNNReal) (𝓝 x) (𝓝 (-(d x)).toNNReal) at h
    rwa [show d x = 0 from sub_self _, neg_zero, Real.toNNReal_zero] at h
  have quot (t : ℝ≥0) : C t = C x * C (d t).toNNReal / C (-(d t)).toNNReal := by
    apply (eq_div_iff (survival_ne A n _)).mpr
    change survivalAmplitude A n t * _ = survivalAmplitude A n x * _
    rw [← survival_add, ← survival_add]
    congr 1
    apply NNReal.coe_injective
    simp only [NNReal.coe_add]
    have split := HTGeometry.posPart_negPart_real (d t)
    dsimp only [d] at split ⊢
    linarith only [split]
  have hp := origin.tendsto.comp plus
  have hm := origin.tendsto.comp minus
  have lim := (hp.const_mul (C x)).div hm (survival_ne A n 0)
  simp only [survival_zero, mul_one, div_one] at lim
  exact lim.congr' (Filter.Eventually.of_forall fun t => (quot t).symm)

/-- A single occupied positive energy samples every positive branch share.
Continuity of its forward vacuum amplitude at zero fixes response regularity. -/
theorem continuous_from_mode (A : Response) {n : ℕ+} (energy_pos : 0 < energy n)
    (origin : ContinuousAt (survivalAmplitude A n) 0) : ContinuousOn A.val Shares := by
  let time (x : ℝ) := (-Real.log x / energy n).toNNReal
  have logc : ContinuousOn Real.log Shares :=
    fun x hx => (Real.continuousAt_log hx.1.ne').continuousWithinAt
  have tc : ContinuousOn time Shares :=
    continuous_real_toNNReal.comp_continuousOn (logc.neg.div_const _)
  apply ((ray_continuous A n origin).comp_continuousOn tc).congr
  intro x hx
  have pos : 0 ≤ -Real.log x / energy n :=
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)) energy_pos.le
  change A.val x = A.val (Real.exp (-((time x : ℝ≥0):ℝ) * energy n))
  rw [show ((time x : ℝ≥0):ℝ) = -Real.log x / energy n from Real.coe_toNNReal _ pos,
    neg_div, neg_neg, div_mul_cancel₀ _ energy_pos.ne', Real.exp_log hx.1]

#print axioms continuous_from_mode

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
