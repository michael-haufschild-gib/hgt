import GaloisForLFunctions.HilbertMetric.Correlation.DopplerClusterKernel
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The exact initial curvature of Gaussian cluster aging

The second derivative of squared temporal coherence is minus twice the
Gaussian mixture's second-moment defect. Intrinsic angular spread and
dispersion of cluster means therefore have separate nonnegative effects.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]

private def clusterVelocity (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) : ℂ :=
  ∑ i, (w i : ℂ) * ((mean i : ℂ) * Complex.I - (variance i : ℂ) * t) *
    Complex.exp ((t : ℂ) * mean i * Complex.I - (variance i : ℂ) * (t : ℂ) ^ 2 / 2)

private def clusterAcceleration (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) : ℂ :=
  ∑ i, (w i : ℂ) * (((mean i : ℂ) * Complex.I - (variance i : ℂ) * t) ^ 2 - variance i) *
    Complex.exp ((t : ℂ) * mean i * Complex.I - (variance i : ℂ) * (t : ℂ) ^ 2 / 2)

private theorem clusterPhase_deriv (mean : ℝ) (variance : NNReal) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * mean * Complex.I - (variance : ℂ) * (s : ℂ) ^ 2 / 2)
      ((mean : ℂ) * Complex.I - (variance : ℂ) * t) t := by
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp
  exact (((hid.mul_const (mean : ℂ)).mul_const Complex.I).sub
    (((hid.pow 2).const_mul (variance : ℂ)).div_const 2)).congr_deriv (by ring)

private theorem clusterKernel_deriv (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) :
    HasDerivAt (dopplerClusterKernel w mean variance) (clusterVelocity w mean variance t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact ((clusterPhase_deriv (mean i) (variance i) t).cexp.const_mul (w i : ℂ)).congr_deriv
    (by ring)

private theorem clusterVelocity_deriv (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) :
    HasDerivAt (clusterVelocity w mean variance) (clusterAcceleration w mean variance t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp
  have hv : HasDerivAt
      (fun s : ℝ => (mean i : ℂ) * Complex.I - (variance i : ℂ) * s) (-(variance i : ℂ)) t := by
    simpa only [mul_one] using
      ((hid.const_mul (variance i : ℂ)).const_sub ((mean i : ℂ) * Complex.I))
  exact ((hv.const_mul (w i : ℂ)).mul
    (clusterPhase_deriv (mean i) (variance i) t).cexp).congr_deriv (by ring)

private theorem clusterKernel_zero (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) :
    dopplerClusterKernel w mean variance 0 = ((∑ i, (w i : ℝ)) : ℂ) := by
  simp only [dopplerClusterKernel, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one]

private theorem clusterVelocity_zero (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) :
    clusterVelocity w mean variance 0 = ((∑ i, (w i : ℝ) * mean i) : ℂ) * Complex.I := by
  simp only [clusterVelocity, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one, Finset.sum_mul, mul_assoc]

private theorem clusterAcceleration_zero (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) :
    clusterAcceleration w mean variance 0 = -((∑ i, (w i : ℝ) * (mean i ^ 2 + variance i)) : ℂ) := by
  simp only [clusterAcceleration, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one, mul_pow, Complex.I_sq]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem coherence_curvature_scalar (m p q : ℝ) :
    ((-(q : ℂ)) * star (m : ℂ) + (p * Complex.I) * star (p * Complex.I) +
      ((p * Complex.I) * star (p * Complex.I) + (m : ℂ) * star (-(q : ℂ)))).re =
      -2 * (m * q - p ^ 2) := by
  simp only [star_mul, star_neg, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The actual second derivative of squared temporal coherence is the negative variance defect. -/
theorem deriv_deriv_normSq_dopplerClusterKernel_zero (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    deriv (deriv (fun t : ℝ => ‖dopplerClusterKernel w mean variance t‖ ^ 2)) 0 =
      -2 * dopplerAgingDefect w mean variance := by
  let K := dopplerClusterKernel w mean variance
  let V := clusterVelocity w mean variance
  let A := clusterAcceleration w mean variance
  have hK (t : ℝ) : HasDerivAt K (V t) t := clusterKernel_deriv w mean variance t
  have hV (t : ℝ) : HasDerivAt V (A t) t := clusterVelocity_deriv w mean variance t
  have hnorm (t : ℝ) :
      HasDerivAt (fun s : ℝ => ‖K s‖ ^ 2) ((V t * star (K t) + K t * star (V t)).re) t := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hK t).mul (hK t).star)
    have h' : HasDerivAt (fun s : ℝ => (K s * star (K s)).re)
        ((V t * star (K t) + K t * star (V t)).re) t := by
      simpa only [Function.comp_def, Pi.mul_apply, Complex.reCLM_apply] using h
    apply h'.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro s
    change ‖K s‖ ^ 2 = (K s * conj (K s)).re
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hderiv : deriv (fun t : ℝ => ‖K t‖ ^ 2) =
      fun t => (V t * star (K t) + K t * star (V t)).re := funext fun t => (hnorm t).deriv
  rw [hderiv]
  have hh := ((hV 0).mul (hK 0).star).add ((hK 0).mul (hV 0).star)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hh
  have hre' : HasDerivAt (fun t : ℝ => (V t * star (K t) + K t * star (V t)).re)
      ((A 0 * star (K 0) + V 0 * star (V 0) +
        (V 0 * star (V 0) + K 0 * star (A 0))).re) 0 := by
    simpa only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Complex.reCLM_apply] using hre
  rw [hre'.deriv]
  dsimp only [K, V, A]
  rw [clusterKernel_zero, clusterVelocity_zero, clusterAcceleration_zero]
  simpa only [dopplerAgingDefect, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow] using
    coherence_curvature_scalar (∑ i, (w i : ℝ)) (∑ i, (w i : ℝ) * mean i)
      (∑ i, (w i : ℝ) * (mean i ^ 2 + variance i))

end HilbertMetric.Correlation

#print axioms HilbertMetric.Correlation.deriv_deriv_normSq_dopplerClusterKernel_zero
