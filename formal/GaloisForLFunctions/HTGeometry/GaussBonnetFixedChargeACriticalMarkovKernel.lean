import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalQFTSpectrum
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTDynamics
import GaloisForLFunctions.HTGeometry.MarkedVariationDynamics

/-!
The critical Gibbs profile derived from arXiv:2609.00025 defines an explicit
finite Markov kernel after normalization. This is a mathematical use of the
critical profile, with no stochastic assumption on the finite-temperature model.
-/
namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized nonnegative critical Gibbs transition weights. -/
def egbFixedChargeACriticalMarkovWeight (n : ℕ) (i j : Fin (2 ^ (n + 3))) : ℝ :=
  (8 / (3 * (2 : ℝ) ^ (n + 3))) *
    Real.cos (egbFixedChargeAFourierGrid (n + 3) i -
      egbFixedChargeAFourierGrid (n + 3) j) ^ 4

/-- Exact critical row mass before Markov normalization. -/
theorem egbFixedChargeACriticalGram_real_row_sum
    (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    ∑ j : Fin (2 ^ (n + 3)), Real.cos (egbFixedChargeAFourierGrid (n + 3) i -
      egbFixedChargeAFourierGrid (n + 3) j) ^ 4 = (2 : ℝ) ^ (n + 3) * (3 / 8) := by
  have h := egbFixedChargeAQFTMultiplier_row_sum (n + 3)
    (egbFixedChargeACriticalFourierSpectrum n) i
  rw [← egbFixedChargeACriticalGram_QFT_multiplier] at h
  have hm : egbFixedChargeACriticalFourierSpectrum n 0 =
      ((2 : ℝ) ^ (n + 3) * (3 / 8) : ℂ) := by
    simpa [egbFixedChargeAFiveFourierModes, egbFixedChargeAFourierWeights] using
      egbFixedChargeACriticalFourierSpectrum_mode n 0
  rw [hm] at h
  change (∑ j : Fin (2 ^ (n + 3)),
    (Real.cos (egbFixedChargeAFourierGrid (n + 3) i -
      egbFixedChargeAFourierGrid (n + 3) j) ^ 4 : ℂ)) = _ at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat] using h

/-- The transition weights are nonnegative for every pair of states. -/
theorem egbFixedChargeACriticalMarkovWeight_nonneg
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    0 ≤ egbFixedChargeACriticalMarkovWeight n i j := by
  unfold egbFixedChargeACriticalMarkovWeight
  exact mul_nonneg (le_of_lt (div_pos (by norm_num)
    (mul_pos (by norm_num) (pow_pos (by norm_num) _)))) (by positivity)

/-- Symmetry gives detailed balance against the uniform law. -/
theorem egbFixedChargeACriticalMarkovWeight_symm
    (n : ℕ) (i j : Fin (2 ^ (n + 3))) :
    egbFixedChargeACriticalMarkovWeight n i j = egbFixedChargeACriticalMarkovWeight n j i := by
  unfold egbFixedChargeACriticalMarkovWeight
  rw [← neg_sub (egbFixedChargeAFourierGrid (n + 3) j)
    (egbFixedChargeAFourierGrid (n + 3) i), Real.cos_neg]

/-- Every row sums to one, with normalization proved from the zero Fourier mode. -/
theorem egbFixedChargeACriticalMarkovWeight_row_sum
    (n : ℕ) (i : Fin (2 ^ (n + 3))) :
    ∑ j : Fin (2 ^ (n + 3)), egbFixedChargeACriticalMarkovWeight n i j = 1 := by
  simp only [egbFixedChargeACriticalMarkovWeight, ← Finset.mul_sum,
    egbFixedChargeACriticalGram_real_row_sum]
  field_simp

/-- Every column sums to one, as required by the corpus Markov-kernel interface. -/
theorem egbFixedChargeACriticalMarkovWeight_column_sum
    (n : ℕ) (j : Fin (2 ^ (n + 3))) :
    ∑ i : Fin (2 ^ (n + 3)), egbFixedChargeACriticalMarkovWeight n i j = 1 := by
  simp_rw [egbFixedChargeACriticalMarkovWeight_symm n _ j]
  exact egbFixedChargeACriticalMarkovWeight_row_sum n j

/-- The critical Gibbs transition as an existing corpus finite Markov kernel. -/
def egbFixedChargeACriticalMarkovKernel (n : ℕ) :
    FiniteMarkovKernel (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) where
  weight := egbFixedChargeACriticalMarkovWeight n
  nonneg := egbFixedChargeACriticalMarkovWeight_nonneg n
  column_sum := egbFixedChargeACriticalMarkovWeight_column_sum n

/-- The kernel conserves every real profile's total mass. -/
theorem egbFixedChargeACriticalMarkovKernel_mass
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i : Fin (2 ^ (n + 3)),
      (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyReal f i =
        ∑ i : Fin (2 ^ (n + 3)), f i :=
  FiniteMarkovKernel.sum_applyReal _ _

/-- Uniform probability is fixed by one transition. -/
theorem egbFixedChargeACriticalMarkovKernel_uniform_stationary (n : ℕ) :
    (egbFixedChargeACriticalMarkovKernel n).toFinitePositiveKernel.applyReal
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) = fun _ => ((2 : ℝ) ^ (n + 3))⁻¹ := by
  funext i
  change (∑ j : Fin (2 ^ (n + 3)), egbFixedChargeACriticalMarkovWeight n i j *
    ((2 : ℝ) ^ (n + 3))⁻¹) = _
  rw [← Finset.sum_mul, egbFixedChargeACriticalMarkovWeight_row_sum, one_mul]

end

end GaloisForLFunctions.HTGeometry
