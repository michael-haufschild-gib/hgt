import GaloisForLFunctions.RHTower.SteinhausDirichletDensityEnergy
import GaloisForLFunctions.RHTower.CompactGaussianDirichletTransportRigidity

open Complex MeasureTheory Filter Topology Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Every fixed polynomial frequency-cost budget forces the actual normalized
compact-window second moment to vanish under arbitrary Dirichlet square densities. -/
theorem eventually_compactGaussian_polynomialDirichletCost_energy_small
    (b : ℝ) {D : ℕ} (hD : 0 < D) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, ∀ L : ℕ, ∀ ω : Omega,
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ S : Finset ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ S, n ≠ 0) → (∑ n ∈ S, ‖a n‖ ^ 2 = 1) →
      (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) ≤ (N : ℝ) ^ A →
      (∫ ξ, ‖∑ p ∈ largePrimes N (N / D),
        compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω * X p ξ‖ ^ 2 *
          ‖∑ n ∈ S, a n * X n ξ‖ ^ 2 ∂steinhausMeasure) < ε := by
  obtain ⟨C, hC, henergy⟩ := exists_compactGaussianNormalizedWindow_energy_upper b hD
  have hlim : Tendsto (fun N : ℕ => C * (1 + 2 * |A|) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [henergy, eventually_largePrimes_log_lower hD,
    hlim.eventually (Iio_mem_nhds hε)] with N henergyN hlogp hsmall
  obtain ⟨hN2, hprimeLog⟩ := hlogp
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  intro tau L ω s hs0 hsb S a hS hnorm hbudget
  have hE : 1 ≤ ∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2 := by
    have h := dirichletDensity_primeMoment_frequencyCost_lower S ∅ a hS
      (fun p hp => by simp at hp) hnorm
    simpa using h
  have hlogE := Real.log_le_log (lt_of_lt_of_le zero_lt_one hE) hbudget
  rw [Real.log_rpow hNR] at hlogE
  have hquot : Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) / (Real.log N / 2) ≤ 2 * |A| := by
    apply (div_le_iff₀ (half_pos hlog)).mpr
    have hA := mul_le_mul_of_nonneg_right (le_abs_self A) hlog.le
    nlinarith
  let P := largePrimes N (N / D)
  let v : ℕ → ℂ := fun p => compactGaussianNormalizedPrimeChannel s N p tau (L / p) ω
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp => (mem_largePrimes.mp hp).1.2
  have h := integral_normSq_primePoly_mul_density_le_logCost P S v a hP hS hnorm
    (half_pos hlog) (fun p hp => by linarith [hprimeLog p hp])
  calc
    _ ≤ (∑ p ∈ P, ‖v p‖ ^ 2) *
        (1 + Real.log (∑ n ∈ S, (n : ℝ) * ‖a n‖ ^ 2) / (Real.log N / 2)) := h
    _ ≤ (∑ p ∈ P, ‖v p‖ ^ 2) * (1 + 2 * |A|) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hquot) (sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ (C / Real.log N) * (1 + 2 * |A|) :=
      mul_le_mul_of_nonneg_right (henergyN tau L ω s hs0 hsb) (by positivity)
    _ = C * (1 + 2 * |A|) / Real.log N := by ring
    _ < ε := hsmall

end RHTower
