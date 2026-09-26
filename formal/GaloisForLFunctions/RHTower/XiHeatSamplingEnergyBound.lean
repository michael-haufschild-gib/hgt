import GaloisForLFunctions.RHTower.XiHeatFiniteDecomposition

/-!
# An unconditional sampling bound for actual Xi polynomial energy

At every positive heat time, every finite list of actual divisor copies gives
a determinant-weighted coefficient bound. The denominator uses the exact
inverse Gaussian weights of those samples. No node separation, positivity
assumption, or heat-time restriction is a premise.
-/

namespace RHTower
noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

/-- Full actual norm energy controls coefficients at every heat time and every sample list. -/
theorem xiHeatFiniteNormEnergy_sampling_bound {N : ℕ} (a : Fin N → ℝ) (τ : ℝ)
    (q : Fin N → XiZeroCopy) :
    let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
    ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, a j ^ 2) ≤
      (N : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 *
        (∑ i, Real.exp (z i).re) * xiHeatFiniteNormEnergy a τ := by
  classical
  let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
  let v : Fin N → ℂ := fun j => (a j : ℂ)
  change ‖(Matrix.vandermonde z).det‖ ^ 2 * (∑ j, a j ^ 2) ≤ _
  have hsample := polynomialSample_energy_bound z v
  have hv : (∑ j, ‖v j‖ ^ 2) = ∑ j, a j ^ 2 := by
    simp [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hv] at hsample
  have hatom (i : Fin N) : ‖polynomialSample v (z i)‖ ^ 2 ≤
      Real.exp (z i).re * xiHeatFiniteNormEnergy a τ := by
    have hn : ‖xiHeatFiniteAmplitude a τ (q i)‖ ^ 2 =
        Real.exp (-(z i).re) * ‖polynomialSample v (z i)‖ ^ 2 := by
      rw [xiHeatFiniteAmplitude_eq_sample, heatPhaseAmplitude_norm_sq]
      dsimp only [v, z]
      rw [one_mul, mul_comm]
    have hs := (summable_xiHeatFiniteAmplitude_norm_sq a τ).sum_le_tsum {q i}
      (fun _ _ => sq_nonneg _)
    simp only [Finset.sum_singleton] at hs
    calc
      _ = Real.exp (z i).re * ‖xiHeatFiniteAmplitude a τ (q i)‖ ^ 2 := by
        rw [hn, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hatom i)
  rw [← Finset.sum_mul] at hs
  have h := hsample.trans (mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (N : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 by positivity))
  simpa only [mul_assoc] using h

end
end RHTower
