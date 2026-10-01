import GaloisForLFunctions.RHTower.CompactGaussianPrimeBlockEnergy
import GaloisForLFunctions.RHTower.SteinhausScalarAmplitudeSynthesis

open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- On each actual reciprocal prime block, explicit scalar biases attain any mode
coefficient with arbitrarily small individual means, logarithmic total cost, and
uniform mode-error control, at every pair of coherent frequencies. -/
theorem eventually_exists_compactGaussianPrimeBlock_biases
    {M : ℕ} (hM : 0 < M) {A : ℂ} (hA : A ≠ 0) (γ : ℂ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ t tau : ℝ, ∃ μ : ℕ → ℂ,
      (∀ p ∉ cofactorPrimeBlock M N, μ p = 0) ∧
      (∑ p ∈ cofactorPrimeBlock M N, μ p * compactGaussianPrimeAmplitude N p t tau A) = γ ∧
      (∑ p ∈ cofactorPrimeBlock M N, ‖μ p‖ ^ 2) ≤
        4 * ‖γ‖ ^ 2 * Real.log N / ((M : ℝ) * ‖A‖ ^ 2) ∧
      (∀ p, ‖μ p‖ < η) ∧
      ∀ (v : ℕ → ℂ) (g : ℂ) (ε : ℝ),
        (∀ p ∈ cofactorPrimeBlock M N, ‖v p - g‖ ≤ ε) →
        ‖(∑ p ∈ cofactorPrimeBlock M N,
          μ p * (compactGaussianPrimeAmplitude N p t tau A * v p)) - γ * g‖ ≤ ‖γ‖ * ε := by
  classical
  have hAnorm : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hbase : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      8 * ‖γ‖ * Real.log N / (‖A‖ * Real.sqrt N)) atTop (𝓝 0) := by
    convert hbase.mul_const (8 * ‖γ‖ / ‖A‖) using 1
    · ext N
      rw [Real.sqrt_eq_rpow]
      ring_nf
    · ring_nf
  filter_upwards [eventually_compactGaussianPrimeBlockEnergy_lower hM,
    eventually_ge_atTop 2, hlim.eventually (Iio_mem_nhds hη)] with N hfloor hN2 hsmall
  intro t tau
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let E := compactGaussianPrimeBlockEnergy M N t tau A
  let c : ℝ := (M : ℝ) * ‖A‖ ^ 2 / (4 * Real.log N)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcE : c ≤ E := hfloor t tau A
  have hE : 0 < E := hc.trans_le hcE
  obtain ⟨μ, hsupp, hmean, hcost, hnorm, herror⟩ := exists_finiteScalarAmplitudeBiases
    (cofactorPrimeBlock M N) (fun p => compactGaussianPrimeAmplitude N p t tau A) hE γ
  refine ⟨μ, hsupp, hmean, ?_, ?_, herror⟩
  · change (∑ p ∈ cofactorPrimeBlock M N, ‖μ p‖ ^ 2) = ‖γ‖ ^ 2 / E at hcost
    rw [hcost]
    calc
      _ ≤ ‖γ‖ ^ 2 / c := div_le_div_of_nonneg_left (sq_nonneg _) hc hcE
      _ = _ := by dsimp only [c]; field_simp
  · intro p
    by_cases hp : p ∈ cofactorPrimeBlock M N
    · have hu := (compactGaussianPrimeAmplitude_block_bounds hM hN hp t tau A).2
      have hpn : ‖μ p‖ ≤ 8 * ‖γ‖ * Real.log N / (‖A‖ * Real.sqrt N) := by
        rw [hnorm p hp]
        change ‖γ‖ * ‖compactGaussianPrimeAmplitude N p t tau A‖ / E ≤ _
        calc
          _ ≤ (‖γ‖ * (2 * (M : ℝ) * ‖A‖ / Real.sqrt N)) / c :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) hc hcE
          _ = _ := by dsimp only [c]; field_simp; ring_nf
      exact hpn.trans_lt hsmall
    · simpa only [hsupp p hp, norm_zero] using hη

end RHTower
