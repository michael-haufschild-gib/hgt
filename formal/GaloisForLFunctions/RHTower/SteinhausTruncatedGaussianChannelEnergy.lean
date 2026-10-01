import GaloisForLFunctions.RHTower.SteinhausFullGaussianTruncation
import GaloisForLFunctions.RHTower.SteinhausFullGaussianChannelEnergy



open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- The literal truncated Gaussian channel after removing the node's conductor factor. -/
def normalizedTruncatedGaussianCofactorChannel {J : ℕ} (s : Fin J → ℂ) (R : ℝ) (L : ℕ)
    (ω : SteinhausModel.Omega) : Fin J → ℂ :=
  fun j => (R : ℂ) * (truncatedFullGaussianCofactor (s j) R L ω * (R : ℂ) ^ (-s j))

/-- The truncated normalized channel retains exactly the real cofactor scale and common phase. -/
theorem normalizedTruncatedGaussianCofactorChannel_eq_mode {J : ℕ} (s : Fin J → ℂ)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) {R : ℝ} (hR : 0 < R) (L : ℕ)
    (ω : SteinhausModel.Omega) (j : Fin J) :
    normalizedTruncatedGaussianCofactorChannel s R L ω j =
      ((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
        relativeTruncatedFullGaussianCofactorMode s t A R L ω j := by
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hpow : (R : ℂ) ^ ((t : ℂ) * I) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hRC)
  simp only [normalizedTruncatedGaussianCofactorChannel, relativeTruncatedFullGaussianCofactorMode,
    Complex.cpow_neg]
  field_simp

/-- Pairing a truncated normalized channel removes the common coherent phase without loss. -/
theorem norm_normalizedTruncatedGaussianCofactorChannel_dot_eq {J : ℕ} (s : Fin J → ℂ)
    (t : ℝ) {A : ℂ} (hA : A ≠ 0) {R : ℝ} (hR : 0 < R) (L : ℕ)
    (ω : SteinhausModel.Omega) (u : Fin J → ℂ) :
    ‖∑ j, normalizedTruncatedGaussianCofactorChannel s R L ω j * u j‖ =
      R * ‖A‖ * ‖∑ j, relativeTruncatedFullGaussianCofactorMode s t A R L ω j * u j‖ := by
  have heq : (∑ j, normalizedTruncatedGaussianCofactorChannel s R L ω j * u j) =
      ((R : ℂ) * A * (R : ℂ) ^ ((t : ℂ) * I)) *
        (∑ j, relativeTruncatedFullGaussianCofactorMode s t A R L ω j * u j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [normalizedTruncatedGaussianCofactorChannel_eq_mode s t hA hR L ω j]
    ring
  rw [heq, norm_mul]
  simp only [norm_mul, Complex.norm_of_nonneg hR.le,
    Complex.norm_cpow_eq_rpow_re_of_pos hR, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_self,
    Real.rpow_zero, mul_one]

/-- Exact conductor normalization of a literal truncated Gaussian prime channel; no floor factor remains. -/
theorem truncatedGaussian_prime_channel_factor {J : ℕ} (s : Fin J → ℂ)
    {N p : ℝ} (hN : 0 < N) (hp : 0 < p) (L : ℕ) (ω : SteinhausModel.Omega) (j : Fin J) :
    (p : ℂ) ^ (s j - 1) * truncatedFullGaussianCofactor (s j) (N / p) L ω =
      (N : ℂ) ^ (s j - 1) * normalizedTruncatedGaussianCofactorChannel s (N / p) L ω j := by
  let R : ℝ := N / p
  have hR : 0 < R := div_pos hN hp
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hNR : N = p * R := by dsimp only [R]; field_simp
  have hpowers : (R : ℂ) ^ (s j - 1) * (R : ℂ) * (R : ℂ) ^ (-s j) = 1 := by
    calc
      _ = (R : ℂ) ^ (s j - 1) * (R : ℂ) ^ (1 : ℂ) * (R : ℂ) ^ (-s j) := by
        rw [Complex.cpow_one]
      _ = (R : ℂ) ^ ((s j - 1) + 1 + (-s j)) := by
        rw [← Complex.cpow_add _ _ hRC, ← Complex.cpow_add _ _ hRC]
      _ = 1 := by rw [show (s j - 1) + 1 + (-s j) = 0 by ring, Complex.cpow_zero]
  change (p : ℂ) ^ (s j - 1) * truncatedFullGaussianCofactor (s j) R L ω =
    (N : ℂ) ^ (s j - 1) * ((R : ℂ) *
      (truncatedFullGaussianCofactor (s j) R L ω * (R : ℂ) ^ (-s j)))
  conv_rhs => rw [hNR, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hp.le hR.le]
  calc
    _ = ((p : ℂ) ^ (s j - 1) * truncatedFullGaussianCofactor (s j) R L ω) *
        ((R : ℂ) ^ (s j - 1) * (R : ℂ) * (R : ℂ) ^ (-s j)) := by rw [hpowers, mul_one]
    _ = _ := by ring


/-- One fixed character cell supports every prescribed mode for all sufficiently long
literal cofactor truncations, uniformly over each real scale block. -/
theorem exists_truncatedGaussianCofactor_mode_cell_blocks
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (ω : SteinhausModel.Omega) (B₀ : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ, ∃ B D : ℕ, ∃ δ : ℝ,
        B₀ ≤ B ∧ 0 < δ ∧ (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B₀ ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          2 * M i ≤ B ∧ ∀ η : SteinhausModel.Omega,
            (∀ n ∈ Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω'‖ < δ) →
            ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) → ∀ L : ℕ, D ≤ L →
              ‖relativeTruncatedFullGaussianCofactorMode s (t i) (A i) R L η -
                (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * I))‖ < ε := by
  classical
  obtain ⟨ω', hp, M, A, B, δ, hB, hδ, hsep, hblocks⟩ :=
    exists_fullGaussianCofactor_mode_cell_blocks hJ s hs hs1 S ω B₀ K (ε / 2)
      (by positivity) hk t
  have herrors : ∀ᶠ L : ℕ in atTop, ∀ i : Fin k, ∀ R : ℝ, 1 ≤ R → R ≤ 2 * (M i : ℝ) →
      ∀ η : SteinhausModel.Omega,
        ‖relativeTruncatedFullGaussianCofactorMode s (t i) (A i) R L η -
          relativeFullGaussianCofactorMode s (t i) (A i) R η‖ < ε / 2 :=
    Filter.eventually_all.mpr (fun i =>
      eventually_relativeTruncatedFullGaussianCofactorMode_uniform_error s (fun j => (hs j).le)
        (t i) (hblocks i).2.2.1 (2 * (M i : ℝ)) (show 0 < ε / 2 by positivity))
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp herrors
  refine ⟨ω', hp, M, A, B, D, δ, hB, hδ, hsep, ?_⟩
  intro i
  obtain ⟨hB₀, hMi, hAi, hbudget, hMB, hmode⟩ := hblocks i
  refine ⟨hB₀, hMi, hAi, hbudget, hMB, ?_⟩
  intro η hcell R hlo hhi L hL
  have hR1 : 1 ≤ R := le_trans (by exact_mod_cast hMi) hlo
  have hpert := hD L hL i R hR1 hhi η
  have hbase := hmode η hcell R hlo hhi
  calc
    _ ≤ ‖relativeTruncatedFullGaussianCofactorMode s (t i) (A i) R L η -
          relativeFullGaussianCofactorMode s (t i) (A i) R η‖ +
        ‖relativeFullGaussianCofactorMode s (t i) (A i) R η -
          (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * I))‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (relativeTruncatedFullGaussianCofactorMode s (t i) (A i) R L η)
        (relativeFullGaussianCofactorMode s (t i) (A i) R η)
        (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * I))
    _ < ε / 2 + ε / 2 := add_lt_add hpert hbase
    _ = ε := by ring

/-- Literal truncated Gaussian cofactor channels have arbitrarily large every-direction energy
on one fixed character cell for every sufficiently long polynomial cutoff. Smoothing scale N
and polynomial length L are independent; only L >= N*D is required here. -/
theorem exists_normalizedTruncatedGaussianCofactorChannel_energy_cell_lower
    {J : ℕ} (hJ : 0 < J) (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (hinj : Function.Injective s)
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (H : ℝ) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ K B D : ℕ, ∃ δ : ℝ, 0 < K ∧ 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        N < (N / (2 * K)) * (N / (2 * K)) ∧
        ∀ L : ℕ, N * D ≤ L → ∀ eta ∈ steinhausCharacterCell B omega' δ,
          ∀ u : Fin J → ℂ,
            H * (N : ℝ) / Real.log N * ‖u‖ ^ 2 ≤
              ∑ p ∈ largePrimes N (N / (2 * K)),
                ‖∑ j, normalizedTruncatedGaussianCofactorChannel s ((N : ℝ) / p) (L / p) eta j * u j‖ ^ 2 := by
  classical
  obtain ⟨t, ε, c, hε, hc, hframe⟩ := exists_gaussianCofactorMode_robust_row_lower hJ s hs hinj
  obtain ⟨omega', hp, M, A, B, D, δ, _hB, hδ, hsep, hblocks⟩ :=
    exists_truncatedGaussianCofactor_mode_cell_blocks hJ s hs hs1 S omega 1 (4 * H / c ^ 2)
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
  refine ⟨omega', hp, K, B, D, δ, hK, hδ, ?_⟩
  filter_upwards [hcounts, eventually_cofactorPrimeBlock_conditioning_seam hK,
    eventually_ge_atTop 2] with N hcount hseam hN
  refine ⟨hseam.1, ?_⟩
  intro L hL eta heta u
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
      Q ≤ ‖∑ j, normalizedTruncatedGaussianCofactorChannel s ((N : ℝ) / p) (L / p) eta j * u j‖ ^ 2 := by
    intro p hpblock
    have hreal := cofactorPrimeBlock_real_scale_bounds hMi hpblock
    have hR : 0 < (N : ℝ) / p := hMR.trans_le hreal.1
    have hpp := (cofactorPrimeBlock_mem_bounds hMi hpblock).1
    have hpN := (mem_largePrimes.mp
      (cofactorPrimeBlock_subset_largePrimes hMi (hMK i) hpblock)).1.1
    have hcut : D ≤ L / p := (Nat.le_div_iff_mul_le hpp.pos).mpr
      ((Nat.mul_le_mul_left D hpN).trans (by simpa only [Nat.mul_comm] using hL))
    have hcorr := (hblocks i).2.2.2.2.2 eta heta ((N : ℝ) / p) hreal.1 hreal.2.le (L / p) hcut
    have hrow := hi (relativeTruncatedFullGaussianCofactorMode s (t i) (A i) ((N : ℝ) / p) (L / p) eta)
      (hcorr.le.trans (by linarith))
    have hnorm : (M i : ℝ) * ‖A i‖ * c * ‖u‖ ≤
        ‖∑ j, normalizedTruncatedGaussianCofactorChannel s ((N : ℝ) / p) (L / p) eta j * u j‖ := by
      rw [norm_normalizedTruncatedGaussianCofactorChannel_dot_eq s (t i) hAi hR (L / p) eta u]
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
        ‖∑ j, normalizedTruncatedGaussianCofactorChannel s ((N : ℝ) / p) (L / p) eta j * u j‖ ^ 2 := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (cofactorPrimeBlock_subset_largePrimes hMi (hMK i)) (fun _ _ _ => sq_nonneg _)


end RHTower
