import GaloisForLFunctions.HTGeometry.SchwartzRowRecombination

/-!
Row-dependent smooth windows are removed by an exact Fourier integral before
taking the family mean square. The remaining oscillatory sums keep all signed
coefficients and row dependencies. This also separates a coupled bilinear
window `h_r(x_i + y_j)` into independent row and column phases.
This applies the smooth-separation and recombination mechanisms of paper2,
Appendix B, to a coupled logarithmic window without a derivative-budget hypothesis.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex
open scoped BigOperators FourierTransform BoundedContinuousFunction NNReal

def recombinationFourierPhase (x : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => Complex.exp (((2 * Real.pi * u * x : ℝ) : ℂ) * I))
    (by fun_prop) 1
    (fun u => (Complex.norm_exp_ofReal_mul_I _).le)

theorem recombinationFourierPhase_add (x y u : ℝ) :
    recombinationFourierPhase (x + y) u =
      recombinationFourierPhase x u * recombinationFourierPhase y u := by
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem integral_fourier_mul_recombinationPhase (h : SchwartzMap ℝ ℂ) (x : ℝ) :
    (∫ u : ℝ, (𝓕 h) u * recombinationFourierPhase x u) = h x := by
  have hf : (𝓕⁻ (𝓕 (h : ℝ → ℂ))) x = h x :=
    congrFun (h.continuous.fourierInv_fourier_eq h.integrable (𝓕 h).integrable) x
  rw [Real.fourierInv_eq'] at hf
  simpa only [SchwartzMap.fourier_coe, real_inner_comm, RCLike.inner_apply,
    conj_trivial, smul_eq_mul, recombinationFourierPhase,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, mul_comm, mul_assoc] using hf

def finiteFourierResponse {ι : Type*} (s : Finset ι) (a : ι → ℂ) (x : ι → ℝ) : ℝ →ᵇ ℂ :=
  ∑ i ∈ s, a i • recombinationFourierPhase (x i)

theorem finiteFourierResponse_apply {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (x : ι → ℝ) (u : ℝ) :
    finiteFourierResponse s a x u = ∑ i ∈ s, a i * recombinationFourierPhase (x i) u := by
  simp [finiteFourierResponse, smul_eq_mul]

theorem integral_fourier_mul_finiteFourierResponse {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (x : ι → ℝ) (h : SchwartzMap ℝ ℂ) :
    (∫ u : ℝ, (𝓕 h) u * finiteFourierResponse s a x u) = ∑ i ∈ s, a i * h (x i) := by
  have hi (i : ι) : Integrable (fun u : ℝ =>
      (𝓕 h) u * (a i * recombinationFourierPhase (x i) u)) := by
    have hh : Integrable (fun u : ℝ => (𝓕 h) u) := (𝓕 h).integrable
    apply hh.mul_bdd (c := ‖a i‖ * ‖recombinationFourierPhase (x i)‖)
      ((recombinationFourierPhase (x i)).continuous.const_mul _).aestronglyMeasurable
    filter_upwards with u
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((recombinationFourierPhase (x i)).norm_coe_le_norm u) (norm_nonneg _)
  simp_rw [finiteFourierResponse_apply, Finset.mul_sum]
  rw [integral_finsetSum s (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_left_comm ((𝓕 h) _) (a i)]
  rw [integral_const_mul, integral_fourier_mul_recombinationPhase]

/-- Smoothing each row costs a common Fourier-envelope mass; all energies remain coupled. -/
theorem sum_weight_norm_schwartz_sum_sq_le_fourier_envelope
    {ρ ι : Type*} [Fintype ρ] (s : Finset ι)
    (w : ρ → ℝ≥0) (h : ρ → SchwartzMap ℝ ℂ) (a : ρ → ι → ℂ) (x : ρ → ι → ℝ) :
    (∑ r, (w r : ℝ) * ‖∑ i ∈ s, a r i * h r (x r i)‖ ^ 2) ≤
      (∫ u : ℝ, schwartzRowEnvelope (fun r => 𝓕 (h r)) u) *
        ∫ u : ℝ, schwartzRowEnvelope (fun r => 𝓕 (h r)) u *
          ∑ r, (w r : ℝ) *
            ‖∑ i ∈ s, a r i * recombinationFourierPhase (x r i) u‖ ^ 2 := by
  have hh := sum_weight_norm_integral_schwartz_smul_sq_le_row_envelope
    (fun r => 𝓕 (h r)) (fun r => finiteFourierResponse s (a r) (x r)) w
  simp only [smul_eq_mul] at hh
  simp_rw [integral_fourier_mul_finiteFourierResponse] at hh
  simpa only [finiteFourierResponse_apply] using hh

/-- Fourier separation of a genuinely coupled bilinear window, in family mean square. -/
theorem sum_weight_norm_schwartz_bilinear_sq_le_fourier_envelope
    {ρ ι κ : Type*} [Fintype ρ] (s : Finset ι) (t : Finset κ)
    (w : ρ → ℝ≥0) (h : ρ → SchwartzMap ℝ ℂ)
    (a : ρ → ι → ℂ) (b : ρ → κ → ℂ) (M : ρ → ι → κ → ℂ)
    (x : ρ → ι → ℝ) (y : ρ → κ → ℝ) :
    (∑ r, (w r : ℝ) *
      ‖∑ i ∈ s, ∑ j ∈ t, a r i * b r j * M r i j * h r (x r i + y r j)‖ ^ 2) ≤
      (∫ u : ℝ, schwartzRowEnvelope (fun r => 𝓕 (h r)) u) *
        ∫ u : ℝ, schwartzRowEnvelope (fun r => 𝓕 (h r)) u *
          ∑ r, (w r : ℝ) *
            ‖∑ i ∈ s, ∑ j ∈ t,
              (a r i * recombinationFourierPhase (x r i) u) *
                (b r j * recombinationFourierPhase (y r j) u) * M r i j‖ ^ 2 := by
  have hh := sum_weight_norm_schwartz_sum_sq_le_fourier_envelope (s ×ˢ t) w h
    (fun r ij => a r ij.1 * b r ij.2 * M r ij.1 ij.2)
    (fun r ij => x r ij.1 + y r ij.2)
  simp only [Finset.sum_product, recombinationFourierPhase_add] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GaloisForLFunctions.HTGeometry
