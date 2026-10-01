import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannelUpper

open Filter Topology Finset Complex
noncomputable section
namespace RHTower

/-- Actual normalized free-window energy is O(1/log N) on the whole abscissa band,
uniformly in imaginary part, common height, retained phases and polynomial cutoff. -/
theorem exists_compactGaussianNormalizedWindow_energy_upper
    (b : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ,
      ∀ ω : SteinhausModel.Omega, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b →
        (∑ p ∈ largePrimes N (N / D),
          ‖compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ^ 2) ≤ C / Real.log N := by
  obtain ⟨C, hC, hcolumn⟩ := exists_compactGaussianNormalizedPrimeChannel_uniform_bound b D
  have hcount : ∀ᶠ N : ℕ in atTop, (Nat.primeCounting N : ℝ) ≤ 2 * N / Real.log N := by
    have h := GaloisForLFunctions.HTGeometry.isLittleO_primeCounting_sub.bound (c := 1) zero_lt_one
    have hnat := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually h
    filter_upwards [hnat, eventually_ge_atTop 2] with N hN hN2
    have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hmain : 0 < (N : ℝ) / Real.log N := div_pos (by linarith) (Real.log_pos hNR)
    simp only [Nat.floor_natCast, Real.norm_eq_abs, one_mul, abs_of_pos hmain] at hN
    have hupper := (abs_le.mp hN).2
    rw [mul_div_assoc]
    linarith
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop 2] with N hcountN hN2
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : ((largePrimes N (N / D)).card : ℝ) ≤ 2 * N / Real.log N := by
    refine le_trans ?_ hcountN
    exact_mod_cast (show (largePrimes N (N / D)).card ≤ Nat.primeCounting N from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Nat.primesLE_card_eq_primeCounting N))
  intro tau L ω s hs0 hsb
  have hterm (p : ℕ) (hp : p ∈ largePrimes N (N / D)) :
      ‖compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ≤ C / Real.sqrt N := by
    obtain ⟨⟨hpN, hprime⟩, hpD⟩ := mem_largePrimes.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hNp : N < D * p := by
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hD).mp hpD
    have hR1 : (1 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hpR).mpr (by simpa using (show (p : ℝ) ≤ N by exact_mod_cast hpN))
    have hRU : (N : ℝ) / p ≤ D := by
      rw [div_le_iff₀ hpR]
      exact_mod_cast hNp.le
    exact hcolumn N p hNR hpR hR1 hRU s hs0 hsb tau (L / p) ω
  calc
    _ ≤ ∑ _p ∈ largePrimes N (N / D), (C / Real.sqrt N) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hterm p hp)
    _ = ((largePrimes N (N / D)).card : ℝ) * (C ^ 2 / N) := by
      simp only [sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt hNR.le]
    _ ≤ (2 * N / Real.log N) * (C ^ 2 / N) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (2 * C ^ 2) / Real.log N := by field_simp

end RHTower
