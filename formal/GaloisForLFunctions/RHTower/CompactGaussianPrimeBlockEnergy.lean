import GaloisForLFunctions.RHTower.SmoothAFEReflectedCompactChannel

open Filter Topology Finset
noncomputable section
namespace RHTower

/-- Exact squared amplitude mass of one reciprocal prime block. -/
def compactGaussianPrimeBlockEnergy (M N : ℕ) (t tau : ℝ) (A : ℂ) : ℝ :=
  ∑ p ∈ cofactorPrimeBlock M N, ‖compactGaussianPrimeAmplitude N p t tau A‖ ^ 2

/-- Every amplitude lies between the two literal cofactor-scale endpoints. -/
theorem compactGaussianPrimeAmplitude_block_bounds {M N p : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hp : p ∈ cofactorPrimeBlock M N)
    (t tau : ℝ) (A : ℂ) :
    (M : ℝ) * ‖A‖ / Real.sqrt N ≤ ‖compactGaussianPrimeAmplitude N p t tau A‖ ∧
      ‖compactGaussianPrimeAmplitude N p t tau A‖ ≤ 2 * (M : ℝ) * ‖A‖ / Real.sqrt N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast (cofactorPrimeBlock_mem_bounds hM hp).1.pos
  have hscale := cofactorPrimeBlock_real_scale_bounds hM hp
  rw [norm_compactGaussianPrimeAmplitude hNR hpR]
  constructor
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale.1 (norm_nonneg A)) (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale.2.le (norm_nonneg A)) (Real.sqrt_nonneg _)

/-- Prime counting supplies the actual logarithmic amplitude-energy floor uniformly
in both coherent frequencies and in the chosen mean scalar. -/
theorem eventually_compactGaussianPrimeBlockEnergy_lower {M : ℕ} (hM : 0 < M) :
    ∀ᶠ N : ℕ in atTop, ∀ t tau : ℝ, ∀ A : ℂ,
      (M : ℝ) * ‖A‖ ^ 2 / (4 * Real.log N) ≤ compactGaussianPrimeBlockEnergy M N t tau A := by
  filter_upwards [eventually_cofactorPrimeBlock_card_lower hM, eventually_ge_atTop 2]
    with N hcount hN2
  intro t tau A
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Q : ℝ := (M : ℝ) ^ 2 * ‖A‖ ^ 2 / N
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hterm : ∀ p ∈ cofactorPrimeBlock M N,
      Q ≤ ‖compactGaussianPrimeAmplitude N p t tau A‖ ^ 2 := by
    intro p hp
    have hb := (compactGaussianPrimeAmplitude_block_bounds hM hN hp t tau A).1
    calc
      Q = ((M : ℝ) * ‖A‖ / Real.sqrt N) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hNR.le]
      _ ≤ _ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hb
  calc
    (M : ℝ) * ‖A‖ ^ 2 / (4 * Real.log N) =
        ((N : ℝ) / (4 * M * Real.log N)) * Q := by
      dsimp only [Q]
      field_simp
    _ ≤ ((cofactorPrimeBlock M N).card : ℝ) * Q := mul_le_mul_of_nonneg_right hcount hQ
    _ = ∑ _p ∈ cofactorPrimeBlock M N, Q := by simp
    _ ≤ compactGaussianPrimeBlockEnergy M N t tau A := Finset.sum_le_sum hterm

end RHTower
