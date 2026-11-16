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
    dopplerClusterKernel w mean variance 0 = Complex.ofReal (∑ i, (w i : ℝ)) := by
  simp only [dopplerClusterKernel, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one, Complex.ofReal_sum]

private theorem clusterVelocity_zero (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) :
    clusterVelocity w mean variance 0 = Complex.ofReal (∑ i, (w i : ℝ) * mean i) * Complex.I := by
  simp only [clusterVelocity, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one, Finset.sum_mul, mul_assoc,
    Complex.ofReal_sum, Complex.ofReal_mul]

private theorem clusterAcceleration_zero (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal) :
    clusterAcceleration w mean variance 0 =
      -Complex.ofReal (∑ i, (w i : ℝ) * (mean i ^ 2 + variance i)) := by
  simp only [clusterAcceleration, Complex.ofReal_zero, zero_mul, zero_pow (by omega : 2 ≠ 0),
    mul_zero, zero_div, sub_zero, Complex.exp_zero, mul_one, mul_pow, Complex.I_sq,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
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

private theorem norm_square_deriv (K V : ℝ → ℂ) (t : ℝ)
    (hK : HasDerivAt K (V t) t) :
    HasDerivAt (fun s : ℝ => ‖K s‖ ^ 2)
      ((V t * star (K t) + K t * star (V t)).re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hK.mul hK.star)
  have h' : HasDerivAt (fun s : ℝ => (K s * star (K s)).re)
      ((V t * star (K t) + K t * star (V t)).re) t := by
    simpa only [Function.comp_def, Pi.mul_apply, Complex.reCLM_apply] using h
  apply h'.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  change ‖K s‖ ^ 2 = (K s * conj (K s)).re
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem norm_square_second_deriv (K V A : ℝ → ℂ)
    (hK : ∀ t, HasDerivAt K (V t) t) (hV : HasDerivAt V (A 0) 0) :
    deriv (deriv (fun t : ℝ => ‖K t‖ ^ 2)) 0 =
      (A 0 * star (K 0) + V 0 * star (V 0) +
        (V 0 * star (V 0) + K 0 * star (A 0))).re := by
  have hderiv : deriv (fun t : ℝ => ‖K t‖ ^ 2) =
      fun t => (V t * star (K t) + K t * star (V t)).re :=
    funext fun t => (norm_square_deriv K V t (hK t)).deriv
  rw [hderiv]
  have hh := (hV.mul (hK 0).star).add ((hK 0).mul hV.star)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hh
  have hre' : HasDerivAt (fun t : ℝ => (V t * star (K t) + K t * star (V t)).re)
      ((A 0 * star (K 0) + V 0 * star (V 0) +
        (V 0 * star (V 0) + K 0 * star (A 0))).re) 0 := by
    simpa only [Function.comp_def, Pi.add_apply, Pi.mul_apply, Complex.reCLM_apply] using hre
  exact hre'.deriv

private theorem coherence_curvature_at_zero (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    (clusterAcceleration w mean variance 0 * star (dopplerClusterKernel w mean variance 0) +
      clusterVelocity w mean variance 0 * star (clusterVelocity w mean variance 0) +
      (clusterVelocity w mean variance 0 * star (clusterVelocity w mean variance 0) +
        dopplerClusterKernel w mean variance 0 * star (clusterAcceleration w mean variance 0))).re =
      -2 * dopplerAgingDefect w mean variance := by
  simp only [clusterKernel_zero, clusterVelocity_zero, clusterAcceleration_zero]
  exact coherence_curvature_scalar (∑ i, (w i : ℝ)) (∑ i, (w i : ℝ) * mean i)
    (∑ i, (w i : ℝ) * (mean i ^ 2 + variance i))

/-- The actual second derivative of squared temporal coherence is the negative variance defect. -/
theorem deriv_deriv_normSq_dopplerClusterKernel_zero (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    deriv (deriv (fun t : ℝ => ‖dopplerClusterKernel w mean variance t‖ ^ 2)) 0 =
      -2 * dopplerAgingDefect w mean variance :=
  (norm_square_second_deriv (dopplerClusterKernel w mean variance)
    (clusterVelocity w mean variance) (clusterAcceleration w mean variance)
    (clusterKernel_deriv w mean variance) (clusterVelocity_deriv w mean variance 0)).trans
      (coherence_curvature_at_zero w mean variance)

end HilbertMetric.Correlation

namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]

/-- Zero initial aging is equivalent to no loss of coherence at any time. -/
theorem dopplerAgingDefect_zero_iff_constant_coherence (w : ι → NNReal)
    (mean : ι → ℝ) (variance : ι → NNReal) :
    dopplerAgingDefect w mean variance = 0 ↔
      ∀ t, ‖dopplerClusterKernel w mean variance t‖ = ∑ i, (w i : ℝ) := by
  constructor
  · intro hz t
    have hzero := (dopplerAgingDefect_eq_zero_iff w mean variance).mp hz
    by_cases hi : ∃ i, w i ≠ 0
    · obtain ⟨i, hi⟩ := hi
      have hK : dopplerClusterKernel w mean variance t =
          Complex.ofReal (∑ j, (w j : ℝ)) * Complex.exp ((t : ℂ) * mean i * Complex.I) := by
        rw [dopplerClusterKernel, Complex.ofReal_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : w j = 0
        · simp only [hj, NNReal.coe_zero, Complex.ofReal_zero, zero_mul]
        · have hv := (hzero.1 j).resolve_left hj
          have hm := ((hzero.2 j i).resolve_left hj).resolve_left hi
          simp only [hv, hm, NNReal.coe_zero, Complex.ofReal_zero, zero_mul,
            zero_div, sub_zero]
      have hmass : 0 ≤ ∑ j, (w j : ℝ) := Finset.sum_nonneg fun j _ => (w j).coe_nonneg
      rw [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmass,
        Complex.norm_exp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Real.exp_zero, mul_one]
    · have hw : ∀ i, w i = 0 := by simpa only [not_exists, not_not] using hi
      simp only [dopplerClusterKernel, hw, NNReal.coe_zero, Complex.ofReal_zero,
        zero_mul, Finset.sum_const_zero, norm_zero]
  · intro h
    have he : (fun t : ℝ => ‖dopplerClusterKernel w mean variance t‖ ^ 2) =
        fun _ => (∑ i, (w i : ℝ)) ^ 2 := funext fun t => congrArg (fun x : ℝ => x ^ 2) (h t)
    have hc := deriv_deriv_normSq_dopplerClusterKernel_zero w mean variance
    rw [he] at hc
    have hd : deriv (fun _ : ℝ => (∑ i, (w i : ℝ)) ^ 2) = fun _ => 0 :=
      funext fun t => deriv_const t _
    rw [hd, deriv_const] at hc
    linarith only [hc]

end HilbertMetric.Correlation

