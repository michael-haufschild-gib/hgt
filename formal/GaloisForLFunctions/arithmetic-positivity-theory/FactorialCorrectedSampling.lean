import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzZeroSideLimit

/-! Absolute square sampling for the literal corrected source. Its exact zero
readout is a single reciprocal mode, so the whole zero divisor costs only
`1/(n+1)`, uniformly under normalized smoothing. -/

open MeasureTheory Set Filter
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- A literal square-sampling summand, including the actual zero multiplicity. -/
def zetaZeroSquareSummand (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ)*‖paperFT f (gammaOf ρ)‖^2

/-- The absolute sampling mass. Every application below separately proves summability. -/
def zetaZeroSquareMass (f : ℝ → ℂ) : ℝ := ∑' ρ, zetaZeroSquareSummand f ρ

private theorem zero_reciprocal_square_bound (ρ : zetaZeroConfig.carrier) :
    0 < ‖(ρ : ℂ)‖^2 ∧
      1+Complex.normSq (gammaOf (ρ : ℂ)) ≤ 2*‖(ρ : ℂ)‖^2 := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  have h4 := _root_.RHTower.four_le_abs_im_of_zeta_zero hz.2.1 hz.2.2 hz.1
  have ha := Complex.abs_im_le_norm (ρ : ℂ)
  have hIm := WeilEF.abs_gammaOf_im_lt ⟨hz.2.1,hz.2.2⟩
  have hg : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im^2+1/4 := by
    rw [Complex.normSq_apply,WeilEF.gammaOf_re]
    nlinarith [sq_abs (gammaOf (ρ : ℂ)).im,abs_nonneg (gammaOf (ρ : ℂ)).im]
  have hsq : (ρ : ℂ).im^2 ≤ ‖(ρ : ℂ)‖^2 := by
    nlinarith [sq_abs (ρ : ℂ).im,abs_nonneg (ρ : ℂ).im,norm_nonneg (ρ : ℂ)]
  constructor
  · nlinarith [sq_abs (ρ : ℂ).im]
  · nlinarith [sq_abs (ρ : ℂ).im]

private theorem corrected_square_summand_bound (n k : ℕ) (ρ : zetaZeroConfig.carrier) :
    zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ ≤
      (Real.exp 1)^2*factorialMuntzZeroMajorant n ρ := by
  have hρ := zetaZeroConfig.strip _ ρ.2
  have hk := factorialMuntzKernelReadout_bound k hρ.1 hρ.2
  have hk2 : ‖factorialMuntzKernelReadout k (ρ : ℂ)‖^2 ≤ (Real.exp 1)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mpr hk
  obtain ⟨hnorm,hd⟩ := zero_reciprocal_square_bound ρ
  have hden : 0 < 1+Complex.normSq (gammaOf (ρ : ℂ)) := by
    linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  have hm : 0 ≤ (zetaZeroConfig.mult ρ : ℝ)*(factorialMuntzBoundaryCoefficient n)^2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have hfrac : (zetaZeroConfig.mult ρ : ℝ)*(factorialMuntzBoundaryCoefficient n)^2/
      ‖(ρ : ℂ)‖^2 ≤ factorialMuntzZeroMajorant n ρ := by
    unfold factorialMuntzZeroMajorant
    rw [← mul_div_assoc,div_le_div_iff₀ hnorm hden]
    nlinarith [mul_le_mul_of_nonneg_left hd hm]
  unfold zetaZeroSquareSummand
  rw [factorialMuntzSmoothed_paperFT_gamma]
  simp only [norm_mul,norm_div,mul_pow,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ (zetaZeroConfig.mult ρ : ℝ)*
        ((Real.exp 1)^2*((factorialMuntzBoundaryCoefficient n)^2/‖(ρ : ℂ)‖^2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hk2 (div_nonneg (sq_nonneg _) hnorm.le)) (by positivity)
    _ = (Real.exp 1)^2*((zetaZeroConfig.mult ρ : ℝ)*
        (factorialMuntzBoundaryCoefficient n)^2/‖(ρ : ℂ)‖^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)

/-- Absolute square summability of the actual corrected source for every scale and smoothing. -/
theorem factorialCorrected_zeroSquare_summable (n k : ℕ) :
    Summable (zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed n k x : ℂ))) := by
  apply Summable.of_norm_bounded ((summable_factorialMuntzZeroMajorant n).mul_left ((Real.exp 1)^2))
  intro ρ
  rw [Real.norm_eq_abs,abs_of_nonneg
    (show 0 ≤ zetaZeroSquareSummand (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ from
      mul_nonneg (by positivity) (sq_nonneg _))]
  exact corrected_square_summand_bound n k ρ

/-- Fixed zero-divisor mass, independent of both arithmetic and smoothing scales. -/
def factorialCorrectedSamplingConstant : ℝ :=
  1+(Real.exp 1)^2/2*(∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ)))

theorem factorialCorrectedSamplingConstant_pos : 0 < factorialCorrectedSamplingConstant := by
  have hs : 0 ≤ ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ)) :=
    tsum_nonneg (fun ρ => div_nonneg (by positivity)
      (add_nonneg zero_le_one (Complex.normSq_nonneg (gammaOf ρ))))
  unfold factorialCorrectedSamplingConstant
  positivity

private theorem boundary_coefficient_sq (n : ℕ) :
    (factorialMuntzBoundaryCoefficient n)^2 = 1/(4*((n+1 : ℕ) : ℝ)) := by
  unfold factorialMuntzBoundaryCoefficient
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
  norm_num

/-- The corrected-source sampling cost is one logarithm smaller than the tail's. -/
theorem factorialCorrected_zeroSquare_le (n k : ℕ) :
    zetaZeroSquareMass (fun x => (factorialMuntzSmoothed n k x : ℂ)) ≤
      factorialCorrectedSamplingConstant/((n+1 : ℕ) : ℝ) := by
  let S : ℝ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ))
  calc
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, (Real.exp 1)^2*factorialMuntzZeroMajorant n ρ :=
      (factorialCorrected_zeroSquare_summable n k).tsum_le_tsum
        (corrected_square_summand_bound n k)
        ((summable_factorialMuntzZeroMajorant n).mul_left ((Real.exp 1)^2))
    _ = ((Real.exp 1)^2/2*S)/((n+1 : ℕ) : ℝ) := by
      unfold factorialMuntzZeroMajorant
      rw [tsum_mul_left,tsum_mul_left,boundary_coefficient_sq]
      dsimp only [S]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      change (Real.exp 1)^2/2*S ≤ 1+(Real.exp 1)^2/2*S
      linarith

end
end GaloisForLFunctions.ArithmeticPositivityTheory
