import GaloisForLFunctions.RHTower.CompactGaussianFrequencyWeightedBias
import GaloisForLFunctions.RHTower.SteinhausSpectralProductCost

open Complex Finset Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower

/-- Every normalized spectral factor that realizes an actual compact-window
bias pays the conductor-times-logarithm frequency cost of that displacement.
This is a cost of a mean-value certificate, not a lower bound on signed orbit error. -/
theorem exists_compactGaussianWindow_spectralTransport_cost_lower
    (b₀ : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ,
      ∀ ω : SteinhausModel.Omega, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b₀ →
      ∀ μ a b : ℕ → ℂ,
      (∀ p ∈ largePrimes N (N / D), ‖a p‖ ^ 2 + ‖b p‖ ^ 2 = 1) →
      (∀ p ∈ largePrimes N (N / D), a p * conj (b p) = μ p) →
      (N : ℝ) * Real.log N *
        ‖∑ p ∈ largePrimes N (N / D),
          μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ^ 2 ≤
        C * ∑ T ∈ (largePrimes N (N / D)).powerset, ((∏ p ∈ T, p : ℕ) : ℝ) *
          ‖steinhausSpectralSubsetCoefficient (largePrimes N (N / D)) a b T‖ ^ 2 := by
  obtain ⟨K, hK, hbias⟩ := exists_compactGaussianWindow_frequencyWeightedBias_lower b₀ hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨4 * D * K, by positivity, ?_⟩
  filter_upwards [hbias, eventually_ge_atTop (max D 2)] with N hbound hN
  have hND : D ≤ N := (le_max_left D 2).trans hN
  have hN2 : 2 ≤ N := (le_max_right D 2).trans hN
  have hY : 1 ≤ N / D := (Nat.le_div_iff_mul_le hD).mpr (by simpa using hND)
  have hfloor : (N : ℝ) ≤ 2 * D * ((N / D : ℕ) : ℝ) := by
    have heq := Nat.div_add_mod N D
    have hrem := Nat.mod_lt N hD
    have hnat : N ≤ 2 * D * (N / D) := by nlinarith
    exact_mod_cast hnat
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  intro tau L ω s hs0 hsb μ a b hnorm hmean
  let P := largePrimes N (N / D)
  let E := ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) * ‖steinhausSpectralSubsetCoefficient P a b T‖ ^ 2
  have hp2 (p : ℕ) (hp : p ∈ P) : 2 ≤ p := (mem_largePrimes.mp hp).1.2.two_le
  have hmu (p : ℕ) (hp : p ∈ P) : ‖μ p‖ ^ 2 ≤ ‖b p‖ ^ 2 := by
    have heq : ‖μ p‖ ^ 2 = ‖a p‖ ^ 2 * ‖b p‖ ^ 2 := by
      rw [← hmean p hp, norm_mul, norm_conj, mul_pow]
    have ha : ‖a p‖ ^ 2 ≤ 1 := by nlinarith [hnorm p hp, sq_nonneg ‖b p‖]
    rw [heq]
    exact mul_le_of_le_one_left (sq_nonneg _) ha
  have hc := steinhausSpectralProduct_frequencyWeightedCost_lower P
    (fun p hp => (by norm_num : 1 ≤ 2).trans (hp2 p hp)) a b μ hnorm hmu
  have hweights : (∑ p ∈ P, (p : ℝ) * ‖μ p‖ ^ 2) ≤ 2 * E := by
    have ht : (∑ p ∈ P, (p : ℝ) * ‖μ p‖ ^ 2) ≤
        2 * ∑ p ∈ P, ((p : ℝ) - 1) * ‖μ p‖ ^ 2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2 p hp
      nlinarith [sq_nonneg ‖μ p‖]
    dsimp only [E]
    linarith
  have hb := hbound tau L ω s hs0 hsb μ
  calc
    _ ≤ (2 * D) * (((N / D : ℕ) : ℝ) * Real.log N *
        ‖∑ p ∈ P, μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hfloor
        (mul_nonneg hlog (sq_nonneg ‖∑ p ∈ P, μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖))]
    _ ≤ (2 * D) * (K * (2 * E)) :=
      mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hweights hK.le)) (by positivity)
    _ = _ := by dsimp only [E]; ring

end RHTower
