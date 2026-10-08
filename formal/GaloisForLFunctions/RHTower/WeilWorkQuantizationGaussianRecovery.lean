import GaloisForLFunctions.RHTower.WeilWorkQuantizationCenteredGaussian
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianFourier

/-!
# Absolute Gaussian coefficient extraction from the actual critical trace

The pole-free boundary contour is expanded only on Re(s)=3/2. Its absolute
Dirichlet series pays the interchange before the scalar Gaussian integral
produces the logarithmic frequency kernel.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilSpectral
open GaussZeroSum WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

private def recoveryTerm (hW : WeilPositiveFull lam) (T ℓ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((ℓ : ℂ) * (1 + t * I)) *
    LSeries.term (quantizationCenteredCoeff hW) ((3 / 2 : ℂ) + t * I) n *
      quantizationGaussianFourierKernel T 0 t

private theorem recoveryTerm_eq (hW : WeilPositiveFull lam) (T ℓ : ℝ) (n : ℕ) (t : ℝ) :
    recoveryTerm hW T ℓ n t =
      (quantizationCenteredCoeff hW n * Complex.exp (-(Real.log (n : ℝ) : ℂ) / 2)) *
        quantizationGaussianFourierKernel T (ℓ - Real.log (n : ℝ)) t := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [recoveryTerm, LSeries.term, quantizationCenteredCoeff_zero]
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hl : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [recoveryTerm, LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnc, hl]
  simp only [quantizationGaussianFourierKernel, ofReal_zero, zero_mul, zero_add]
  calc
    _ = quantizationCenteredCoeff hW n *
        (Complex.exp ((ℓ : ℂ) * (1 + t * I)) *
          Complex.exp (-(Real.log (n : ℝ) : ℂ) * ((3 / 2 : ℂ) + t * I)) *
            Complex.exp ((1 + t * I) ^ 2 / T ^ 2)) := by
      rw [neg_mul, Complex.exp_neg]
      ring
    _ = quantizationCenteredCoeff hW n *
        Complex.exp ((ℓ : ℂ) * (1 + t * I) -
          (Real.log (n : ℝ) : ℂ) * ((3 / 2 : ℂ) + t * I) + (1 + t * I) ^ 2 / T ^ 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

private theorem integrable_recoveryTerm (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) (ℓ : ℝ) (n : ℕ) : Integrable (recoveryTerm hW T ℓ n) := by
  have he : recoveryTerm hW T ℓ n = fun t =>
      (quantizationCenteredCoeff hW n * Complex.exp (-(Real.log (n : ℝ) : ℂ) / 2)) *
        quantizationGaussianFourierKernel T (ℓ - Real.log (n : ℝ)) t :=
    funext (recoveryTerm_eq hW T ℓ n)
  rw [he]
  exact (integrable_quantizationGaussianFourierKernel hT _).const_mul _

private theorem norm_recoveryTerm (hW : WeilPositiveFull lam) (T ℓ : ℝ) (n : ℕ) (t : ℝ) :
    ‖recoveryTerm hW T ℓ n t‖ =
      (Real.exp ℓ * ‖LSeries.term (quantizationCenteredCoeff hW) (3 / 2) n‖) *
        ‖quantizationGaussianFourierKernel T 0 t‖ := by
  rw [recoveryTerm, norm_mul, norm_mul, Complex.norm_exp]
  have he : ((ℓ : ℂ) * (1 + t * I)).re = ℓ := by simp
  rw [he]
  congr 2
  simp only [LSeries.norm_term_eq]
  congr 1
  simp

private theorem recoveryTerm_sum (hW : WeilPositiveFull lam) (T ℓ t : ℝ) :
    (∑' n : ℕ, recoveryTerm hW T ℓ n t) =
      quantizationCenteredGaussianIntegrand hW T ℓ ((3 / 2 : ℂ) + t * I) := by
  have hs : 1 < ((3 / 2 : ℂ) + t * I).re := by norm_num
  have hp : ((3 / 2 : ℂ) + t * I) - 1 / 2 = 1 + t * I := by ring
  simp only [recoveryTerm, tsum_mul_right, tsum_mul_left]
  rw [show (∑' n : ℕ, LSeries.term (quantizationCenteredCoeff hW)
    ((3 / 2 : ℂ) + t * I) n) = LSeries (quantizationCenteredCoeff hW)
      ((3 / 2 : ℂ) + t * I) from rfl, quantizationCenteredCoeff_LSeries hW hs]
  simp only [quantizationCenteredGaussianIntegrand, hp, gaussWeight,
    quantizationGaussianFourierKernel, ofReal_zero, zero_mul, zero_add]

/-- The normalized Gaussian Fourier moment of the actual centered source. -/
def quantizationCenteredGaussianMoment (hW : WeilPositiveFull lam) (T ℓ : ℝ) : ℂ :=
  ((T * Real.sqrt Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, quantizationCenteredGaussianTrace hW T ℓ t

/-- The absolutely summable logarithmic Gaussian kernel after coefficient extraction. -/
def quantizationCenteredGaussianCoeff (hW : WeilPositiveFull lam)
    (T ℓ : ℝ) (n : ℕ) : ℂ :=
  quantizationCenteredCoeff hW n * Complex.exp (-(Real.log (n : ℝ) : ℂ) / 2) *
    Complex.exp (-((T * (ℓ - Real.log (n : ℝ))) ^ 2 / 4 : ℝ))

theorem hasSum_quantizationCenteredGaussianCoeff (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    HasSum (quantizationCenteredGaussianCoeff hW T ℓ)
      (quantizationCenteredGaussianMoment hW T ℓ) := by
  have hT0 : 0 < T := by linarith
  have ha := quantizationCenteredCoeff_summable hW (s := 3 / 2) (by norm_num)
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ, ‖recoveryTerm hW T ℓ n t‖) := by
    refine (ha.norm.mul_right (Real.exp ℓ *
      ∫ t : ℝ, ‖quantizationGaussianFourierKernel T 0 t‖)).congr fun n => ?_
    simp_rw [norm_recoveryTerm, integral_const_mul]
    ring
  have hi := hasSum_integral_of_summable_integral_norm
    (fun n => integrable_recoveryTerm hW hT0 ℓ n) hnorm
  have hsingle (n : ℕ) : (∫ t : ℝ, recoveryTerm hW T ℓ n t) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) * quantizationCenteredGaussianCoeff hW T ℓ n := by
    simp_rw [recoveryTerm_eq]
    rw [integral_const_mul, integral_quantizationGaussianFourierKernel hT0]
    unfold quantizationCenteredGaussianCoeff
    ring
  have he : (fun t : ℝ => ∑' n : ℕ, recoveryTerm hW T ℓ n t) =
      fun t : ℝ => quantizationCenteredGaussianIntegrand hW T ℓ ((3 / 2 : ℂ) + t * I) :=
    funext (recoveryTerm_sum hW T ℓ)
  rw [he, ← quantizationCenteredGaussian_boundary_shift hW hT ℓ] at hi
  have hc : ((T * Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (mul_ne_zero hT0.ne' (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hh := hi.mul_left ((T * Real.sqrt Real.pi : ℝ) : ℂ)⁻¹
  simpa only [hsingle, ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
    quantizationCenteredGaussianMoment] using hh

theorem quantizationCenteredGaussianMoment_eq_tsum (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) :
    quantizationCenteredGaussianMoment hW T ℓ =
      ∑' n : ℕ, quantizationCenteredGaussianCoeff hW T ℓ n :=
  (hasSum_quantizationCenteredGaussianCoeff hW hT ℓ).tsum_eq.symm

end RHTower.WeilSpectral
