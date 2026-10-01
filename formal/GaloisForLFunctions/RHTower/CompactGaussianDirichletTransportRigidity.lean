import GaloisForLFunctions.RHTower.SteinhausDirichletLogCost
import GaloisForLFunctions.RHTower.CompactGaussianFrequencyWeightedBias

open Complex MeasureTheory Filter Topology Finset
noncomputable section
namespace RHTower
open SteinhausModel HTGeometry.ConstraintMotiveRelativity

/-- Every prime in the fixed-ratio upper window eventually has logarithm
at least half the conductor logarithm, with the integer floor retained. -/
theorem eventually_largePrimes_log_lower {D : ℕ} (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ ∀ p ∈ largePrimes N (N / D),
      Real.log N ≤ 2 * Real.log p := by
  filter_upwards [eventually_ge_atTop (2 * D ^ 2)] with N hNlarge
  have hY : 2 * D ≤ N / D := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith)
  have hN2 : 2 ≤ N := by nlinarith [sq_pos_of_pos hD]
  have hfloor : N ≤ 2 * D * (N / D) := by
    have h := Nat.div_add_mod N D
    have hr := Nat.mod_lt N hD
    nlinarith
  have hNsq : N ≤ (N / D) ^ 2 := by
    have hm := Nat.mul_le_mul_right (N / D) hY
    nlinarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN2, ?_⟩
  intro p hp
  have hNp : N ≤ p ^ 2 := hNsq.trans (Nat.pow_le_pow_left (mem_largePrimes.mp hp).2.le _)
  have hNpR : (N : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hNp
  have h := Real.log_le_log hNR hNpR
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- Every original Dirichlet square density pays exponential-in-log-squared
frequency cost to create a fixed normalized compact-window mean displacement. -/
theorem exists_compactGaussianWindow_dirichletDensity_logCost_lower
    (b : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ,
      ∀ ω : Omega, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b →
      ∀ S : Finset ℕ, ∀ a : ℕ → ℂ, (∀ n ∈ S, n ≠ 0) → (∑ n ∈ S, ‖a n‖ ^ 2 = 1) →
        (Real.log N) ^ 2 * ‖∑ p ∈ largePrimes N (N / D),
          (∫ ξ, X p ξ * ((‖∑ n ∈ S, a n * X n ξ‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure) *
            compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ ^ 2 ≤
          C * Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
  obtain ⟨C, hC, henergy⟩ := exists_compactGaussianNormalizedWindow_energy_upper b hD
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [henergy, eventually_largePrimes_log_lower hD] with N henergyN hprimeLog
  obtain ⟨hN2, hlogp⟩ := hprimeLog
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  intro tau L ω s hs0 hsb S a hS hnorm
  let P := largePrimes N (N / D)
  let μ : ℕ → ℂ := fun p =>
    ∫ ξ, X p ξ * ((‖∑ n ∈ S, a n * X n ξ‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure
  let u : ℕ → ℂ := fun p => compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω
  let B := ∑ p ∈ P, ‖μ p‖ ^ 2
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hprime (p : ℕ) (hp : p ∈ P) : Nat.Prime p := (mem_largePrimes.mp hp).1.2
  have hcost := dirichletDensity_primeMoment_logCost_lower S P a hS hprime hnorm
  have hweights : Real.log N * B ≤ 2 * Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) := by
    calc
      _ = ∑ p ∈ P, Real.log N * ‖μ p‖ ^ 2 := by dsimp only [B]; rw [mul_sum]
      _ ≤ 2 * ∑ p ∈ P, Real.log p * ‖μ p‖ ^ 2 := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        nlinarith [mul_le_mul_of_nonneg_right (hlogp p hp) (sq_nonneg ‖μ p‖)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by norm_num)
  have hcs : ‖∑ p ∈ P, μ p * u p‖ ^ 2 ≤ B * (∑ p ∈ P, ‖u p‖ ^ 2) := by
    simpa only [portValue, portEnergy, portCap, one_mul, mul_one, div_one, mul_comm, B] using
      (portValue_normSq_le (w := fun _ : ℕ => (1 : ℝ)) (a := u) (coef := u)
        (fun _ => one_pos) (fun _ => rfl) μ P)
  have hb : ‖∑ p ∈ P, μ p * u p‖ ^ 2 ≤ B * C / Real.log N := by
    calc
      _ ≤ B * (∑ p ∈ P, ‖u p‖ ^ 2) := hcs
      _ ≤ B * (C / Real.log N) := mul_le_mul_of_nonneg_left (henergyN tau L ω s hs0 hsb) hB
      _ = _ := (mul_div_assoc _ _ _).symm
  have hbl := (le_div_iff₀ hlog).mp hb
  have hmul := mul_le_mul_of_nonneg_left hbl hlog.le
  have hmulcost := mul_le_mul_of_nonneg_left hweights hC.le
  change (Real.log N) ^ 2 * ‖∑ p ∈ P, μ p * u p‖ ^ 2 ≤ _
  nlinarith

/-- A fixed polynomial frequency-cost budget forces the mean synthesized by
any normalized Dirichlet square density to vanish uniformly. -/
theorem eventually_compactGaussian_polynomialDirichletCost_target_small
    (b : ℝ) {D : ℕ} (hD : 0 < D) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : Omega,
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ S : Finset ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ S, n ≠ 0) → (∑ n ∈ S, ‖a n‖ ^ 2 = 1) →
      (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) ≤ (N : ℝ) ^ A →
      ‖∑ p ∈ largePrimes N (N / D),
        (∫ ξ, X p ξ * ((‖∑ n ∈ S, a n * X n ξ‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure) *
          compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖ < ε := by
  obtain ⟨C, hC, hcost⟩ := exists_compactGaussianWindow_dirichletDensity_logCost_lower b hD
  have hlim : Tendsto (fun N : ℕ => C * A / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hcost, hlim.eventually (Iio_mem_nhds (sq_pos_of_pos hε)),
    eventually_ge_atTop (2 : ℕ)] with N hbound hsmall hN2
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  intro tau L ω s hs0 hsb S a hS hnorm hbudget
  have hE : 1 ≤ ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
    rw [← hnorm]
    apply sum_le_sum
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hS n hn)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn1 (sq_nonneg ‖a n‖)
  have hlogE := Real.log_le_log (lt_of_lt_of_le zero_lt_one hE) hbudget
  rw [Real.log_rpow hNR] at hlogE
  have h := (hbound tau L ω s hs0 hsb S a hS hnorm).trans
    (mul_le_mul_of_nonneg_left hlogE hC.le)
  let v := ‖∑ p ∈ largePrimes N (N / D),
    (∫ ξ, X p ξ * ((‖∑ n ∈ S, a n * X n ξ‖ ^ 2 : ℝ) : ℂ) ∂steinhausMeasure) *
      compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω‖
  have hc : Real.log N * v ^ 2 ≤ C * A := by
    apply (mul_le_mul_iff_right₀ hlog).mp
    nlinarith [h]
  have hv : v ^ 2 ≤ C * A / Real.log N := (le_div_iff₀ hlog).mpr (by nlinarith [hc])
  change v < ε
  have hv0 : 0 ≤ v := norm_nonneg _
  nlinarith [hv.trans_lt hsmall]

end RHTower
