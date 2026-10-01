import GaloisForLFunctions.RHTower.CompactGaussianPrimeBlockBiases
import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannel
import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactTruncation

open Filter Topology Finset Complex Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- A fixed finite Gaussian catalogue is synthesized by the literal normalized
prime-window mean at arbitrarily small logarithmic bias cost. The same biases
work for every retained phase in one fixed cell and every sufficiently long cutoff. -/
theorem exists_compactGaussianWindow_mode_synthesis
    (S : Finset ℕ) (ω : Omega) (B0 : ℕ) {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1)
    {k : ℕ} (hk : 0 < k) (t : Fin k → ℝ) (γ : Fin k → ℂ) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧ ∃ B D : ℕ, ∃ δ : ℝ,
      B0 ≤ B ∧ 0 < δ ∧
      ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∃ μ : ℕ → ℂ,
        (∀ p ∉ largePrimes N (N / (2 * (B + 1))), μ p = 0) ∧
        (∀ p, ‖μ p‖ ≤ 1 / 2) ∧
        (∑ p ∈ largePrimes N (N / (2 * (B + 1))), ‖μ p‖ ^ 2) ≤ κ * Real.log N ∧
        ∀ η : Omega, (∀ n ∈ Icc 1 B, ‖X n η - X n ω'‖ < δ) →
          ∀ L : ℕ, N * D ≤ L → ∀ s ∈ closedBall c r,
            ‖(∑ p ∈ largePrimes N (N / (2 * (B + 1))),
              μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η) -
              ∑ i, γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ < ε := by
  classical
  let Q : ℝ := ∑ i, ‖γ i‖ ^ 2
  have hQ : 0 ≤ Q := sum_nonneg (fun _ _ => sq_nonneg _)
  let K : ℝ := max 1 (4 * k * Q / κ)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbudgetK : 4 * k * Q ≤ κ * K := by
    have h := (div_le_iff₀ hκ).mp (le_max_right 1 (4 * k * Q / κ))
    simpa only [K, mul_comm] using h
  let ζ : ℝ := ε / (2 * (1 + ∑ i, ‖γ i‖))
  have hsum0 : 0 ≤ ∑ i, ‖γ i‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  have hζerr : (∑ i, ‖γ i‖) * ζ < ε := by
    dsimp only [ζ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + ∑ i, ‖γ i‖))).mpr
    nlinarith
  obtain ⟨ω', hprefix, M, A, B, D, δ, hB, hδ, _, hblocks⟩ :=
    exists_truncatedGaussianCofactor_compact_mode_cell_blocks S ω B0 K ζ hζ
      hρ hrρ hc0 hc1 hk t
  let θ : ℝ := 1 / (2 * (k + 1))
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθhalf : (k : ℝ) * θ < 1 / 2 := by
    dsimp only [θ]
    rw [← mul_div_assoc, mul_one]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (k + 1))).mpr
    nlinarith
  have hbias : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k, ∀ t tau : ℝ, ∃ μ : ℕ → ℂ,
      (∀ p ∉ cofactorPrimeBlock (M i) N, μ p = 0) ∧
      (∑ p ∈ cofactorPrimeBlock (M i) N, μ p * compactGaussianPrimeAmplitude N p t tau (A i)) = γ i ∧
      (∑ p ∈ cofactorPrimeBlock (M i) N, ‖μ p‖ ^ 2) ≤
        4 * ‖γ i‖ ^ 2 * Real.log N / ((M i : ℝ) * ‖A i‖ ^ 2) ∧
      (∀ p, ‖μ p‖ < θ) ∧
      ∀ (v : ℕ → ℂ) (g : ℂ) (e : ℝ),
        (∀ p ∈ cofactorPrimeBlock (M i) N, ‖v p - g‖ ≤ e) →
        ‖(∑ p ∈ cofactorPrimeBlock (M i) N,
          μ p * (compactGaussianPrimeAmplitude N p t tau (A i) * v p)) - γ i * g‖ ≤ ‖γ i‖ * e :=
    Filter.eventually_all.mpr (fun i => eventually_exists_compactGaussianPrimeBlock_biases
      (by have h := (hblocks i).2.1; omega) (hblocks i).2.2.1 (γ i) hθ)
  refine ⟨ω', hprefix, B, D, δ, hB, hδ, ?_⟩
  filter_upwards [hbias, eventually_ge_atTop 2] with N hbiasN hN2
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  intro tau
  choose μ hsupp hmean hcost hnorm herror using fun i => hbiasN i (t i) tau
  let W := largePrimes N (N / (2 * (B + 1)))
  have hsub (i : Fin k) : cofactorPrimeBlock (M i) N ⊆ W := by
    have hMi := (hblocks i).2.1
    have hMB := (hblocks i).2.2.2.2.1
    exact cofactorPrimeBlock_subset_largePrimes (by omega) (by omega)
  have hcostW (i : Fin k) : (∑ p ∈ W, ‖μ i p‖ ^ 2) ≤ 4 * ‖γ i‖ ^ 2 * Real.log N / K := by
    have heq : (∑ p ∈ cofactorPrimeBlock (M i) N, ‖μ i p‖ ^ 2) =
        ∑ p ∈ W, ‖μ i p‖ ^ 2 :=
      sum_subset (hsub i) (fun p _ hp => by rw [hsupp i p hp, norm_zero, zero_pow (by decide)])
    rw [← heq]
    exact (hcost i).trans (div_le_div_of_nonneg_left (by positivity) hK (hblocks i).2.2.2.1)
  refine ⟨fun p => ∑ i, μ i p, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact sum_eq_zero (fun i _ => hsupp i p (fun h => hp (hsub i h)))
  · intro p
    calc
      _ ≤ ∑ i, ‖μ i p‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, θ := sum_le_sum (fun i _ => (hnorm i p).le)
      _ = (k : ℝ) * θ := by simp
      _ ≤ 1 / 2 := hθhalf.le
  · have hpoint (p : ℕ) : ‖∑ i, μ i p‖ ^ 2 ≤ (k : ℝ) * ∑ i, ‖μ i p‖ ^ 2 := by
      calc
        _ ≤ (∑ i, ‖μ i p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one] using sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin k => (1 : ℝ)) (fun i => ‖μ i p‖)
    calc
      _ ≤ ∑ p ∈ W, (k : ℝ) * ∑ i, ‖μ i p‖ ^ 2 := sum_le_sum (fun p _ => hpoint p)
      _ = (k : ℝ) * ∑ i, ∑ p ∈ W, ‖μ i p‖ ^ 2 := by rw [← mul_sum, sum_comm]
      _ ≤ (k : ℝ) * ∑ i, 4 * ‖γ i‖ ^ 2 * Real.log N / K :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hcostW i)) (Nat.cast_nonneg _)
      _ = (4 * k * Q / K) * Real.log N := by
        simp only [Q, div_eq_mul_inv, ← sum_mul, ← mul_sum]
        ring
      _ ≤ κ * Real.log N := mul_le_mul_of_nonneg_right ((div_le_iff₀ hK).mpr hbudgetK) hlog
  · intro η hcell L hL s hs
    have hblock (i : Fin k) :
        ‖(∑ p ∈ W, μ i p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η) -
          γ i * smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ ≤ ‖γ i‖ * ζ := by
      have hMi : 0 < M i := by have h := (hblocks i).2.1; omega
      have heq : (∑ p ∈ cofactorPrimeBlock (M i) N,
          μ i p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η) =
          ∑ p ∈ W, μ i p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η :=
        sum_subset (hsub i) (fun p _ hp => by rw [hsupp i p hp, zero_mul])
      rw [← heq]
      have hchannel : (∑ p ∈ cofactorPrimeBlock (M i) N,
          μ i p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η) =
          ∑ p ∈ cofactorPrimeBlock (M i) N, μ i p *
            (compactGaussianPrimeAmplitude N p (t i) tau (A i) *
              relativeTruncatedFullGaussianCofactorScalarMode s (t i) (A i) ((N : ℝ) / p) (L / p) η) := by
        apply sum_congr rfl
        intro p hp
        rw [compactGaussianNormalizedPrimeChannel_eq_mode hNR
          (by exact_mod_cast (cofactorPrimeBlock_mem_bounds hMi hp).1.pos) s tau (t i) (hblocks i).2.2.1]
      rw [hchannel]
      apply herror i
      intro p hp
      have hscale := cofactorPrimeBlock_real_scale_bounds hMi hp
      have hpW := mem_largePrimes.mp (hsub i hp)
      have hmul : D * p ≤ N * D := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_right D hpW.1.1
      have hcut : D ≤ L / p := (Nat.le_div_iff_mul_le hpW.1.2.pos).mpr (hmul.trans hL)
      exact ((hblocks i).2.2.2.2.2 η hcell ((N : ℝ) / p) hscale.1 hscale.2.le
        (L / p) hcut s hs).le
    have heq : (∑ p ∈ W, (∑ i, μ i p) *
        compactGaussianNormalizedPrimeChannel s N p tau (L / p) η) =
        ∑ i, ∑ p ∈ W, μ i p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) η := by
      simp_rw [sum_mul]
      exact sum_comm
    rw [heq, ← sum_sub_distrib]
    exact ((norm_sum_le _ _).trans (sum_le_sum (fun i _ => hblock i))).trans_lt
      (by simpa only [sum_mul] using hζerr)

end RHTower
