import GaloisForLFunctions.RHTower.XiHeatMonomialPhaseBudget
import GaloisForLFunctions.HTGeometry.VandermondeSamplingEnergy

/-!
# Full finite Xi heat-Hankel energy and phase decomposition

Every finite coefficient vector defines an actual polynomial Gaussian trace.
The complete Hankel form is its positive norm energy minus twice its imaginary
square energy. All divisor copies, multiplicities and polynomial cross terms
are retained. The already vanishing finite-degree phase budget therefore
bounds the negative part of the literal Hankel form.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

def xiHeatScaledCoefficients {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (j : ℕ) : ℝ :=
  if h : j < N then a ⟨j, h⟩ * (Real.exp τ) ^ j else 0

def xiHeatFinitePolynomial {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range N, Polynomial.C (xiHeatScaledCoefficients a τ j) * Polynomial.X ^ j

def xiHeatFiniteAmplitude {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (q : XiZeroCopy) : ℂ :=
  ∑ j, (a j : ℂ) * xiHeatMonomialAmplitude j τ q

def xiHeatFiniteNormEnergy {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) : ℝ :=
  ∑' q, ‖xiHeatFiniteAmplitude a τ q‖ ^ 2

theorem xiHeatFiniteAmplitude_eq_sample {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (q : XiZeroCopy) :
    xiHeatFiniteAmplitude a τ q =
      heatPhaseAmplitude
        (polynomialSample (fun j => (a j : ℂ)) ((Real.exp τ : ℂ) * xiSpectralPoint q ^ 2))
        1 ((Real.exp τ : ℂ) * xiSpectralPoint q ^ 2) := by
  unfold xiHeatFiniteAmplitude xiHeatMonomialAmplitude polynomialSample heatPhaseAmplitude
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem eval_xiHeatFinitePolynomial {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (z : ℂ) :
    evalRealPolynomial (xiHeatFinitePolynomial a τ) z =
      polynomialSample (fun j => (a j : ℂ)) ((Real.exp τ : ℂ) * z) := by
  rw [xiHeatFinitePolynomial, evalRealPolynomial_rangeSum,
    ← Fin.sum_univ_eq_sum_range]
  unfold polynomialSample
  apply Finset.sum_congr rfl
  intro j _
  simp only [xiHeatScaledCoefficients, dif_pos j.isLt, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_pow]
  ring

theorem xiHeatFiniteAmplitude_sq {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (q : XiZeroCopy) :
    xiHeatFiniteAmplitude a τ q ^ 2 =
      xiPolynomialGaussianHeatTerm (xiHeatFinitePolynomial a τ) (Real.exp τ) q := by
  rw [xiHeatFiniteAmplitude_eq_sample, heatPhaseAmplitude_sq,
    xiPolynomialGaussianHeatTerm, eval_xiHeatFinitePolynomial, xiGaussianHeatTerm]
  congr 1
  congr 1
  simp

theorem xiHeatFiniteAmplitude_im {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) (q : XiZeroCopy) :
    (xiHeatFiniteAmplitude a τ q).im =
      ∑ j, a j * (xiHeatMonomialAmplitude j τ q).im := by
  simp [xiHeatFiniteAmplitude, Complex.im_sum, Complex.mul_im]

theorem summable_xiHeatFiniteAmplitude_norm_sq {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    Summable (fun q => ‖xiHeatFiniteAmplitude a τ q‖ ^ 2) := by
  have h (q : XiZeroCopy) : ‖xiHeatFiniteAmplitude a τ q‖ ^ 2 =
      ‖xiPolynomialGaussianHeatTerm (xiHeatFinitePolynomial a τ) (Real.exp τ) q‖ := by
    rw [← xiHeatFiniteAmplitude_sq, norm_pow]
  simpa only [h] using
    (summable_xiPolynomialGaussianHeatTerm (Real.exp_pos τ) (xiHeatFinitePolynomial a τ)).norm

theorem summable_xiHeatFiniteAmplitude_im_sq {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    Summable (fun q => (xiHeatFiniteAmplitude a τ q).im ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => ?_) (summable_xiHeatFiniteAmplitude_norm_sq a τ)
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (xiHeatFiniteAmplitude a τ q).re]

theorem xiHeatFiniteNormEnergy_nonneg {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    0 ≤ xiHeatFiniteNormEnergy a τ := tsum_nonneg fun _ => sq_nonneg _

/-- The literal full finite Hankel form equals norm energy minus phase debt. -/
theorem xiHeatHankelForm_scaled_eq_energy_sub_debt {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) =
      xiHeatFiniteNormEnergy a τ - xiHeatFinitePhaseDebt a τ := by
  rw [← xiPolynomialGaussianHeatTraceReal_rangeSum (Real.exp_pos τ)]
  change xiPolynomialGaussianHeatTraceReal (xiHeatFinitePolynomial a τ) (Real.exp τ) = _
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
    Complex.re_tsum (summable_xiPolynomialGaussianHeatTerm (Real.exp_pos τ) _)]
  have hterm (q : XiZeroCopy) :
      (xiPolynomialGaussianHeatTerm (xiHeatFinitePolynomial a τ) (Real.exp τ) q).re =
        ‖xiHeatFiniteAmplitude a τ q‖ ^ 2 - 2 * (xiHeatFiniteAmplitude a τ q).im ^ 2 := by
    rw [← xiHeatFiniteAmplitude_sq, Complex.sq_norm, Complex.normSq_apply,
      pow_two, Complex.mul_re]
    ring
  simp_rw [hterm]
  rw [Summable.tsum_sub (summable_xiHeatFiniteAmplitude_norm_sq a τ)
    ((summable_xiHeatFiniteAmplitude_im_sq a τ).mul_left 2), tsum_mul_left]
  simp only [xiHeatFiniteNormEnergy, xiHeatFinitePhaseDebt, xiHeatFiniteAmplitude_im]

/-- All coefficient directions share the same vanishing error budget at each finite order. -/
theorem xiHeatHankelForm_scaled_lower_bound {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    xiHeatFiniteNormEnergy a τ - (∑ j, a j ^ 2) * xiHeatFinitePhaseBudget N τ ≤
      xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  rw [xiHeatHankelForm_scaled_eq_energy_sub_debt]
  exact sub_le_sub_left (xiHeatFinitePhaseDebt_le_budget a τ) _

end
end RHTower
