import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannelEnergy
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.WeightedPortCapacity

open Complex Filter Topology Finset
noncomputable section
namespace RHTower
open HTGeometry.ConstraintMotiveRelativity

/-- Every actual compact-window bias pays a frequency-weighted synthesis cost.
This is a necessary arithmetic budget, not an orbit-equidistribution premise. -/
theorem exists_compactGaussianWindow_frequencyWeightedBias_lower
    (b : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ,
      ∀ ω : SteinhausModel.Omega, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ μ : ℕ → ℂ,
        ((N / D : ℕ) : ℝ) * Real.log N *
          ‖∑ p ∈ largePrimes N (N / D),
            μ p * compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ^ 2 ≤
          C * ∑ p ∈ largePrimes N (N / D), (p : ℝ) * ‖μ p‖ ^ 2 := by
  obtain ⟨C, hC, henergy⟩ := exists_compactGaussianNormalizedWindow_energy_upper b hD
  refine ⟨C, hC, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (2 : ℕ)] with N henergyN hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  intro tau L ω s hs0 hsb μ
  let W := largePrimes N (N / D)
  let a : ℕ → ℂ := fun p => compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω
  let B : ℝ := ∑ p ∈ W, ‖μ p‖ ^ 2
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs : ‖∑ p ∈ W, μ p * a p‖ ^ 2 ≤ B * (∑ p ∈ W, ‖a p‖ ^ 2) := by
    simpa only [portValue, portEnergy, portCap, one_mul, mul_one, div_one, mul_comm, B] using
      (portValue_normSq_le (w := fun _ : ℕ => (1 : ℝ)) (a := a) (coef := a)
        (fun _ => one_pos) (fun _ => rfl) μ W)
  have hupper : ‖∑ p ∈ W, μ p * a p‖ ^ 2 ≤ (B * C) / Real.log N := by
    calc
      _ ≤ B * (∑ p ∈ W, ‖a p‖ ^ 2) := hcs
      _ ≤ B * (C / Real.log N) := mul_le_mul_of_nonneg_left (henergyN tau L ω s hs0 hsb) hB
      _ = _ := (mul_div_assoc B C (Real.log N)).symm
  have hweight : ((N / D : ℕ) : ℝ) * B ≤ ∑ p ∈ W, (p : ℝ) * ‖μ p‖ ^ 2 := by
    dsimp only [B]
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (mem_largePrimes.mp hp).2.le
  have hlogsum := (le_div_iff₀ hlog).mp hupper
  change ((N / D : ℕ) : ℝ) * Real.log N * ‖∑ p ∈ W, μ p * a p‖ ^ 2 ≤ _
  calc
    _ = ((N / D : ℕ) : ℝ) * (‖∑ p ∈ W, μ p * a p‖ ^ 2 * Real.log N) := by ring
    _ ≤ ((N / D : ℕ) : ℝ) * (B * C) :=
      mul_le_mul_of_nonneg_left hlogsum (Nat.cast_nonneg _)
    _ = C * (((N / D : ℕ) : ℝ) * B) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight hC.le

end RHTower
