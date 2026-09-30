import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells
import GaloisForLFunctions.RHTower.SteinhausCofactorModeCoercivity
import GaloisForLFunctions.RHTower.SteinhausCofactorPrimeBlocks

/-!
# Normalized cofactor channel energy on fixed phase cells

Prescribed coherent blocks, exact floor corrections, robust Cauchy rows, and actual reciprocal
prime counts combine to give any requested positive constant times `N / log N` in every node
coefficient direction. One finite phase extension and one conditioning cutoff work for all
sufficiently large `N` and all sufficiently small positive smoothing scales.

The construction holds throughout one fixed positive-radius finite-character cell. Its centre
recovers the original pointwise statement. The actual conductor transfer, simultaneous centre
control, and deterministic recurrence are separate steps.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- The literal reflected channel after removing its node conductor scale and common row phase. -/
def normalizedCofactorChannel {J : ℕ} (s : Fin J → ℂ) (r : ℝ) (N p : ℕ)
    (omega : SteinhausModel.Omega) : Fin J → ℂ := fun j =>
  (N / p : ℕ) * (primeCofactorFloorRatio N p : ℂ) ^ (s j - 1) *
    smoothCofactorNodeVector s (r * primeCofactorFloorRatio N p) (N / p) omega j

/-- A relative mode retains the exact common scalar of the normalized literal channel. -/
theorem normalizedCofactorChannel_eq_mode {J : ℕ} (s : Fin J → ℂ)
    (t r : ℝ) {A : ℂ} (hA : A ≠ 0) (N p : ℕ) (hL : 0 < N / p)
    (omega : SteinhausModel.Omega) (j : Fin J) :
    normalizedCofactorChannel s r N p omega j =
      (((N / p : ℕ) : ℂ) * A * ((N / p : ℕ) : ℂ) ^ ((t : ℂ) * I)) *
        correctedCofactorMode s t A r N p omega j := by
  have hLC : ((N / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hpow : ((N / p : ℕ) : ℂ) ^ ((t : ℂ) * I) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hLC]
    exact Complex.exp_ne_zero _
  simp only [normalizedCofactorChannel, correctedCofactorMode, relativeSmoothCofactorMode,
    Pi.smul_apply, smul_eq_mul, Complex.cpow_neg]
  field_simp

/-- Removing the common coherent phase leaves precisely the cofactor length and mean norm. -/
theorem norm_normalizedCofactorChannel_dot_eq {J : ℕ} (s : Fin J → ℂ)
    (t r : ℝ) {A : ℂ} (hA : A ≠ 0) (N p : ℕ) (hL : 0 < N / p)
    (omega : SteinhausModel.Omega) (u : Fin J → ℂ) :
    ‖∑ j, normalizedCofactorChannel s r N p omega j * u j‖ =
      (N / p : ℕ) * ‖A‖ * ‖∑ j, correctedCofactorMode s t A r N p omega j * u j‖ := by
  have heq : (∑ j, normalizedCofactorChannel s r N p omega j * u j) =
      (((N / p : ℕ) : ℂ) * A * ((N / p : ℕ) : ℂ) ^ ((t : ℂ) * I)) *
        (∑ j, correctedCofactorMode s t A r N p omega j * u j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [normalizedCofactorChannel_eq_mode s t r hA N p hL omega j]
    ring
  rw [heq, norm_mul]
  simp only [norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos hL, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.rpow_zero, mul_one]

/-- Arbitrarily large conditional energy throughout one fixed finite-character cell.
Its centre extends any finite prescription and one conditioning cutoff works for all directions. -/
theorem exists_normalizedCofactorChannel_energy_cell_lower
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (H : ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ r₀ : ℝ, ∃ K B : ℕ, ∃ δ : ℝ, 0 < r₀ ∧ 0 < K ∧ 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ eta ∈ steinhausCharacterCell B omega' δ,
          ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : Fin J → ℂ,
            H * (N : ℝ) / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, normalizedCofactorChannel s r N p eta j * u j‖ ^ 2 := by
  classical
  obtain ⟨ε, c, hε, hc, hframe⟩ := exists_cofactorCauchyMode_robust_row_lower hJ s hs hinj
  obtain ⟨omega', hp, M, A, r₀, B, δ, hr₀, hδ, hsep, hblocks⟩ :=
    exists_corrected_cofactor_mode_cell_blocks s hs hs1 S omega 1 (4 * H / c ^ 2)
      (ε / 2) (by positivity) hJ (fun i => i.val)
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
  refine ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, ?_⟩
  filter_upwards [hcounts, eventually_cofactorPrimeBlock_conditioning_seam hK,
    eventually_ge_atTop 2] with N hcount hseam hN
  refine ⟨hseam.1, ?_⟩
  intro eta heta r hr hrle u
  obtain ⟨i, hi⟩ := hframe u
  have hMi := (hblocks i).2.1
  have hAi := (hblocks i).2.2.1
  have hbudget := (hblocks i).2.2.2.1
  have hMR : (0 : ℝ) < M i := by exact_mod_cast hMi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Q : ℝ := (M i : ℝ) ^ 2 * ‖A i‖ ^ 2 * c ^ 2 * ‖u‖ ^ 2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hterm : ∀ p ∈ cofactorPrimeBlock (M i) N,
      Q ≤ ‖∑ j, normalizedCofactorChannel s r N p eta j * u j‖ ^ 2 := by
    intro p hpblock
    obtain ⟨hpp, hLM, hLU⟩ := cofactorPrimeBlock_mem_bounds hMi hpblock
    have hL : 0 < N / p := hMi.trans_le hLM
    have hcorr := (hblocks i).2.2.2.2.2 eta heta N p (by omega) hpp.pos hLM hLU.le r hr hrle
    have hrow := hi (correctedCofactorMode s (i.val : ℝ) (A i) r N p eta)
      (hcorr.le.trans (by linarith))
    have hnorm : (M i : ℝ) * ‖A i‖ * c * ‖u‖ ≤
        ‖∑ j, normalizedCofactorChannel s r N p eta j * u j‖ := by
      rw [norm_normalizedCofactorChannel_dot_eq s (i.val : ℝ) r hAi N p hL eta u]
      calc
        _ = ((M i : ℝ) * ‖A i‖) * (c * ‖u‖) := by ring
        _ ≤ (((N / p : ℕ) : ℝ) * ‖A i‖) * (c * ‖u‖) := by gcongr
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
        ‖∑ j, normalizedCofactorChannel s r N p eta j * u j‖ ^ 2 := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (cofactorPrimeBlock_subset_largePrimes hMi (hMK i)) (fun _ _ _ => sq_nonneg _)

/-- The centre of the fixed positive-radius phase cell gives the pointwise energy bound. -/
theorem exists_normalizedCofactorChannel_energy_lower
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (H : ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ r₀ : ℝ, ∃ K : ℕ, 0 < r₀ ∧ 0 < K ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : Fin J → ℂ,
          H * (N : ℝ) / Real.log N * ‖u‖ ^ 2 ≤
            ∑ p ∈ largePrimes N (N / (2 * K)),
              ‖∑ j, normalizedCofactorChannel s r N p omega' j * u j‖ ^ 2 := by
  obtain ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, hcell⟩ :=
    exists_normalizedCofactorChannel_energy_cell_lower hJ s hs hs1 hinj S omega H
  refine ⟨omega', hp, r₀, K, hr₀, hK, ?_⟩
  filter_upwards [hcell] with N hN
  refine ⟨hN.1, hN.2 omega' ?_⟩
  intro n _
  simpa using hδ

end RHTower
