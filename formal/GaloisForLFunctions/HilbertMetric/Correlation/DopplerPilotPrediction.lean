import GaloisForLFunctions.HilbertMetric.Correlation.DopplerClusterKernel

/-!
# Optimal scalar prediction from a noisy Doppler pilot

The Gaussian cluster kernel determines the prediction quadratic exactly.
Completing the square classifies all minimizers and splits its residual
into pilot noise and loss of temporal coherence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate
namespace HilbertMetric.Correlation
variable {ι : Type*} [Fintype ι]

/-- Total spectral power of the cluster mixture. -/
def dopplerMass (w : ι → NNReal) : ℝ := ∑ i, (w i : ℝ)

theorem dopplerMass_nonneg (w : ι → NNReal) : 0 ≤ dopplerMass w :=
  Finset.sum_nonneg fun i _ => (w i).coe_nonneg

/-- Temporal coherence never exceeds the total cluster power. -/
theorem norm_dopplerClusterKernel_le_mass (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (t : ℝ) :
    ‖dopplerClusterKernel w mean variance t‖ ≤ dopplerMass w := by
  rw [dopplerClusterKernel_eq_charFun_sum]
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  have hw : ‖(w i : ℂ)‖ = (w i : ℝ) := by
    exact Complex.norm_of_nonneg (w i).coe_nonneg
  rw [hw]
  exact mul_le_of_le_one_right (w i).coe_nonneg (norm_charFun_le_one t)

/-- Total observation variance from cluster power and pilot noise. -/
def dopplerPilotVariance (w : ι → NNReal) (noise : NNReal) : ℝ :=
  dopplerMass w + noise

theorem dopplerPilotVariance_nonneg (w : ι → NNReal) (noise : NNReal) :
    0 ≤ dopplerPilotVariance w noise := add_nonneg (dopplerMass_nonneg w) noise.coe_nonneg

private theorem kernel_zero_of_pilotVariance_zero (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (noise : NNReal) (t : ℝ)
    (hv : dopplerPilotVariance w noise = 0) :
    dopplerMass w = 0 ∧ dopplerClusterKernel w mean variance t = 0 := by
  have hm : dopplerMass w = 0 := by
    have hn := noise.coe_nonneg
    have hp := dopplerMass_nonneg w
    dsimp only [dopplerPilotVariance] at hv
    linarith only [hn, hp, hv]
  refine ⟨hm, norm_eq_zero.mp ?_⟩
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hm] using norm_dopplerClusterKernel_le_mass w mean variance t

/-- Mean-square prediction quadratic determined by the pilot covariance. -/
def dopplerPilotRisk (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    (noise : NNReal) (t : ℝ) (a : ℂ) : ℝ :=
  dopplerMass w - 2 * (conj a * dopplerClusterKernel w mean variance t).re +
    dopplerPilotVariance w noise * Complex.normSq a

/-- Optimal coefficient multiplying the noisy pilot. -/
def dopplerPilotGain (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    (noise : NNReal) (t : ℝ) : ℂ :=
  dopplerClusterKernel w mean variance t / (dopplerPilotVariance w noise : ℂ)

/-- Prediction residual after the optimal scalar projection. -/
def dopplerPilotResidual (w : ι → NNReal) (mean : ι → ℝ) (variance : ι → NNReal)
    (noise : NNReal) (t : ℝ) : ℝ :=
  dopplerMass w - Complex.normSq (dopplerClusterKernel w mean variance t) /
    dopplerPilotVariance w noise

private theorem complex_prediction_square (m v : ℝ) (k a : ℂ) (hv : v ≠ 0) :
    m - 2 * (conj a * k).re + v * Complex.normSq a =
      m - Complex.normSq k / v + v * Complex.normSq (a - k / (v : ℂ)) := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  field_simp [hv]
  ring

/-- Exact error decomposition for every pilot coefficient, including zero observation variance. -/
theorem dopplerPilotRisk_completion (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (noise : NNReal) (t : ℝ) (a : ℂ) :
    dopplerPilotRisk w mean variance noise t a =
      dopplerPilotResidual w mean variance noise t + dopplerPilotVariance w noise *
        Complex.normSq (a - dopplerPilotGain w mean variance noise t) := by
  by_cases hv : dopplerPilotVariance w noise = 0
  · have hk := (kernel_zero_of_pilotVariance_zero w mean variance noise t hv).2
    simp only [dopplerPilotRisk, dopplerPilotResidual, hv, hk, mul_zero,
      Complex.zero_re, Complex.normSq_zero, zero_div, zero_mul, sub_zero, add_zero]
  · exact complex_prediction_square _ _ _ _ hv

/-- Positive observation variance gives a unique minimizer; at zero variance every coefficient
  minimizes the risk. -/
theorem dopplerPilotRisk_minimizer_iff (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (noise : NNReal) (t : ℝ) (a : ℂ) :
    (∀ b, dopplerPilotRisk w mean variance noise t a ≤
      dopplerPilotRisk w mean variance noise t b) ↔
      dopplerPilotVariance w noise = 0 ∨ a = dopplerPilotGain w mean variance noise t := by
  constructor
  · intro h
    by_cases hv : dopplerPilotVariance w noise = 0
    · exact Or.inl hv
    · right
      have hh := h (dopplerPilotGain w mean variance noise t)
      rw [dopplerPilotRisk_completion, dopplerPilotRisk_completion, sub_self,
        Complex.normSq_zero, mul_zero, add_zero] at hh
      have hvpos := lt_of_le_of_ne (dopplerPilotVariance_nonneg w noise) (Ne.symm hv)
      have hz : Complex.normSq (a - dopplerPilotGain w mean variance noise t) = 0 := by
        have hn := Complex.normSq_nonneg (a - dopplerPilotGain w mean variance noise t)
        nlinarith only [hh, hvpos, hn]
      exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
  · rintro (hv | rfl) b
    · simp only [dopplerPilotRisk_completion, hv, zero_mul, add_zero, le_refl]
    · rw [dopplerPilotRisk_completion, dopplerPilotRisk_completion, sub_self,
        Complex.normSq_zero, mul_zero, add_zero]
      exact le_add_of_nonneg_right (mul_nonneg (dopplerPilotVariance_nonneg w noise)
        (Complex.normSq_nonneg _))

/-- Residual separates unavoidable pilot noise from temporal decorrelation. -/
theorem dopplerPilotResidual_decomposition (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (noise : NNReal) (t : ℝ) :
    dopplerPilotResidual w mean variance noise t =
      dopplerMass w * noise / dopplerPilotVariance w noise +
        (dopplerMass w ^ 2 - Complex.normSq (dopplerClusterKernel w mean variance t)) /
          dopplerPilotVariance w noise := by
  by_cases hv : dopplerPilotVariance w noise = 0
  · have hm := (kernel_zero_of_pilotVariance_zero w mean variance noise t hv).1
    simp only [dopplerPilotResidual, hv, hm, div_zero, zero_mul, sub_zero, add_zero]
  · unfold dopplerPilotResidual
    field_simp [hv]
    dsimp only [dopplerPilotVariance]
    ring

/-- Noise gives a universal lower bound, while predicting zero gives the total-power upper bound. -/
theorem dopplerPilotResidual_bounds (w : ι → NNReal) (mean : ι → ℝ)
    (variance : ι → NNReal) (noise : NNReal) (t : ℝ) :
    dopplerMass w * noise / dopplerPilotVariance w noise ≤
      dopplerPilotResidual w mean variance noise t ∧
    dopplerPilotResidual w mean variance noise t ≤ dopplerMass w := by
  have hv := dopplerPilotVariance_nonneg w noise
  constructor
  · rw [dopplerPilotResidual_decomposition]
    apply le_add_of_nonneg_right
    apply div_nonneg _ hv
    rw [← Complex.sq_norm]
    have hb := norm_dopplerClusterKernel_le_mass w mean variance t
    have hn := norm_nonneg (dopplerClusterKernel w mean variance t)
    nlinarith only [hb, hn]
  · exact sub_le_self _ (div_nonneg (Complex.normSq_nonneg _) hv)

end HilbertMetric.Correlation

