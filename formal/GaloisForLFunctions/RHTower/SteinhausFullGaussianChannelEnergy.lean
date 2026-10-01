import GaloisForLFunctions.RHTower.SteinhausFullGaussianModeCells
import GaloisForLFunctions.RHTower.SteinhausFullGaussianNormalizedChannel
import GaloisForLFunctions.RHTower.SmoothAFEGaussianCofactorModeCoercivity
import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells


open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- Full Gaussian cofactor channels have arbitrarily large every-direction energy on one
fixed character cell, using the actual reciprocal prime blocks. Literal conditional-channel
truncation and conductor transfer remain separate statements. -/
theorem exists_normalizedFullGaussianCofactorChannel_energy_cell_lower
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (H : ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ K B : ℕ, ∃ δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ eta ∈ steinhausCharacterCell B omega' δ,
          ∀ u : Fin J → ℂ,
            H * (N : ℝ) / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, normalizedFullGaussianCofactorChannel s ((N : ℝ) / p) eta j * u j‖ ^ 2 := by
  classical
  obtain ⟨t, ε, c, hε, hc, hframe⟩ := exists_gaussianCofactorMode_robust_row_lower hJ s hs hinj
  obtain ⟨omega', hp, M, A, B, δ, _hB, hδ, hsep, hblocks⟩ :=
    exists_fullGaussianCofactor_mode_cell_blocks hJ s hs hs1 S omega 1 (4 * H / c ^ 2)
      (ε / 2) (by positivity) hJ t
  let K : ℕ := 1 + ∑ i, M i
  have hK : 0 < K := by dsimp only [K]; omega
  have hMK : ∀ i, M i ≤ K := by
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (M j)) (mem_univ i)
    dsimp only [K]
    omega
  have hcounts : ∀ᶠ N : ℕ in atTop, ∀ i : Fin J,
      (N : ℝ) / (4 * M i * Real.log N) ≤ ((cofactorPrimeBlock (M i) N).card : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    exact eventually_cofactorPrimeBlock_card_lower (hblocks i).2.1
  refine ⟨omega', hp, K, B, δ, hK, hδ, ?_⟩
  filter_upwards [hcounts, eventually_cofactorPrimeBlock_conditioning_seam hK,
    eventually_ge_atTop 2] with N hcount hseam hN
  refine ⟨hseam.1, ?_⟩
  intro eta heta u
  obtain ⟨i, hi⟩ := hframe u
  have hMi : 0 < M i := (hblocks i).2.1
  have hAi := (hblocks i).2.2.1
  have hbudget := (hblocks i).2.2.2.1
  have hMR : (0 : ℝ) < M i := by exact_mod_cast hMi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Q : ℝ := (M i : ℝ) ^ 2 * ‖A i‖ ^ 2 * c ^ 2 * ‖u‖ ^ 2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hterm : ∀ p ∈ cofactorPrimeBlock (M i) N,
      Q ≤ ‖∑ j, normalizedFullGaussianCofactorChannel s ((N : ℝ) / p) eta j * u j‖ ^ 2 := by
    intro p hpblock
    have hreal := cofactorPrimeBlock_real_scale_bounds hMi hpblock
    have hR : 0 < (N : ℝ) / p := hMR.trans_le hreal.1
    have hcorr := (hblocks i).2.2.2.2.2 eta heta ((N : ℝ) / p) hreal.1 hreal.2.le
    have hrow := hi (relativeFullGaussianCofactorMode s (t i) (A i) ((N : ℝ) / p) eta)
      (hcorr.le.trans (by linarith))
    have hnorm : (M i : ℝ) * ‖A i‖ * c * ‖u‖ ≤
        ‖∑ j, normalizedFullGaussianCofactorChannel s ((N : ℝ) / p) eta j * u j‖ := by
      rw [norm_normalizedFullGaussianCofactorChannel_dot_eq s (t i) hAi hR eta u]
      calc
        _ = ((M i : ℝ) * ‖A i‖) * (c * ‖u‖) := by ring
        _ ≤ (((N : ℝ) / p) * ‖A i‖) * (c * ‖u‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hreal.1 (norm_nonneg _))
            (mul_nonneg hc.le (norm_nonneg _))
        _ ≤ _ := mul_le_mul_of_nonneg_left hrow (by positivity)
    have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hnorm
    calc
      Q = ((M i : ℝ) * ‖A i‖ * c * ‖u‖) ^ 2 := by dsimp only [Q]; ring
      _ ≤ _ := hsq
  have hscale : H ≤ ((M i : ℝ) * ‖A i‖ ^ 2 * c ^ 2) / 4 := by
    have hb := (div_le_iff₀ (sq_pos_of_pos hc)).mp hbudget
    linarith
  calc
    H * (N : ℝ) / Real.log N * ‖u‖ ^ 2 ≤
        (((M i : ℝ) * ‖A i‖ ^ 2 * c ^ 2) / 4) * N / Real.log N * ‖u‖ ^ 2 := by
      gcongr
    _ = ((N : ℝ) / (4 * M i * Real.log N)) * Q := by
      dsimp only [Q]
      field_simp
    _ ≤ ((cofactorPrimeBlock (M i) N).card : ℝ) * Q := mul_le_mul_of_nonneg_right (hcount i) hQ
    _ = ∑ _p ∈ cofactorPrimeBlock (M i) N, Q := by simp
    _ ≤ ∑ p ∈ cofactorPrimeBlock (M i) N,
        ‖∑ j, normalizedFullGaussianCofactorChannel s ((N : ℝ) / p) eta j * u j‖ ^ 2 := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (cofactorPrimeBlock_subset_largePrimes hMi (hMK i)) (fun _ _ _ => sq_nonneg _)


end RHTower
