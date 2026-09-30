import GaloisForLFunctions.RHTower.SteinhausGaussianWeightedMean
import GaloisForLFunctions.RHTower.SteinhausEulerVerticalBarrier

open MeasureTheory Filter Complex
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The existing unit-cell rotation supplies the logarithmic phase at every positive integer. -/
theorem steinhausCharacter_verticalRotation {n : ℕ} (hn : n ≠ 0) (t : ℝ) (ω : Omega) :
    X n (steinhausEulerVerticalRotation t ω) = X n ω * (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold steinhausEulerVerticalRotation
  rw [steinhausCharacter_coordinateRotation, steinhausCharacter_add_phase]
  congr 1
  have hphase : (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
      (-t * Real.log p / (2 * Real.pi))) = -t / (2 * Real.pi) * Real.log n := by
    rw [Real.log_nat_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  unfold X
  rw [hphase, Complex.cpow_def_of_ne_zero hnC, hlog]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Logarithmic twisting preserves the actual first mean of every positive-index finite sum. -/
theorem integral_norm_steinhausFiniteSum_verticalPhase (a : ℕ → ℂ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (t : ℝ) :
    (∫ ω, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-(t : ℂ) * I) * X n ω‖ ∂steinhausMeasure) =
      ∫ ω, ‖∑ n ∈ S, a n * X n ω‖ ∂steinhausMeasure := by
  have hm : Measurable (fun ω => ‖∑ n ∈ S, a n * X n ω‖) :=
    (Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))).norm
  have hmap := integral_map_of_stronglyMeasurable (μ := steinhausMeasure)
    (measurable_steinhausEulerVerticalRotation t) hm.stronglyMeasurable
  rw [map_steinhausEulerVerticalRotation] at hmap
  calc
    _ = ∫ ω, ‖∑ n ∈ S, a n * X n (steinhausEulerVerticalRotation t ω)‖ ∂steinhausMeasure := by
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [steinhausCharacter_verticalRotation (hS n hn)]
      ring
    _ = _ := hmap.symm

/-- Exact phase stationarity of the literal Gaussian Dirichlet polynomial. -/
theorem integral_norm_steinhausGaussianSummatory_phase_eq (β r t : ℝ) (N : ℕ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
      (n : ℂ) ^ (-(β : ℂ) - (t : ℂ) * I) *
        smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) =
    ∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
      (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖
        ∂steinhausMeasure := by
  have hS (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  rw [← integral_norm_steinhausFiniteSum_verticalPhase
    (fun n => (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)))
    (Finset.Icc 1 N) hS t]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hS n hn
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hnC]
  congr 1
  rw [neg_mul]
  ring

/-- Gaussian first-mean decay is uniform over all real heights and all positive smoothing scales. -/
theorem eventually_integral_norm_steinhausGaussianSummatory_phase_div_rpow_le
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
        (n : ℂ) ^ (-(β : ℂ) - (t : ℂ) * I) *
          smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) /
            (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  filter_upwards [eventually_integral_norm_steinhausGaussianSummatory_div_rpow_le hβ hβhalf hδ]
    with N hN
  intro r hr t
  rw [integral_norm_steinhausGaussianSummatory_phase_eq]
  exact hN r hr

end RHTower
