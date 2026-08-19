import GaloisForLFunctions.RHTower.Sieve.DampedSaving

/-!
# The damped smoothed sum on a fixed line

The damped analogue of `Sieve/MoebiusPerron`: the Perron formula against the uniform bound for
`dampedInvZeta` on the line `Re s = σ > 1`, which is the `invZeta` bound times the Euler correction.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

noncomputable section

/-- The damped Perron series is the damped analytic continuation. -/
theorem tsum_damped_cpow_eq_dampedInvZeta {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, dampedOmegaMoebius P t n * (n : ℂ) ^ (-s)) = dampedInvZeta P t s := by
  have hser := tsum_damped_eq_prod_mul_tsum_moebius hPprime ht0 ht1 hs
  have hmu : ∑' n : ℕ, twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s n = invZeta s := by
    rw [show (fun n : ℕ => twistedSummand (fun m => ((moebius m : ℤ) : ℂ)) s n)
        = fun n : ℕ => ((moebius n : ℂ)) * (n : ℂ) ^ (-s) from rfl]
    exact tsum_moebius_cpow_eq_invZeta hs
  have hlhs : (∑' n : ℕ, dampedOmegaMoebius P t n * (n : ℂ) ^ (-s))
      = ∑' n : ℕ, twistedSummand (dampedOmegaMoebius P t) s n := rfl
  rw [hlhs, hser, hmu, dampedInvZeta]
  ring

/-- **The smoothed damped sum on a fixed line.** -/
theorem norm_tsum_damped_smoothWeight_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H σ : ℝ} (hN : 0 < N) (hH : 0 < H) (hσ : 1 < σ) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ (Real.exp (22 / 4) * (1 + 1 / (σ - 1)) * dampedCorrBound P σ)
          * ∫ y : ℝ, ‖mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  rw [tsum_dampedOmegaMoebius_smoothWeight_eq_integral ht0 ht1 hN hH hσ]
  have hpt : ∀ y : ℝ,
      ‖(∑' n : ℕ, dampedOmegaMoebius P t n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)))
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ (Real.exp (22 / 4) * (1 + 1 / (σ - 1)) * dampedCorrBound P σ)
          * ‖mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
    intro y
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hre : ((σ : ℂ) + (y : ℝ) * Complex.I).re = σ := by simp
    have hs : 1 < ((σ : ℂ) + (y : ℝ) * Complex.I).re := by rw [hre]; exact hσ
    rw [tsum_damped_cpow_eq_dampedInvZeta hPprime ht0 ht1 hs]
    have hbase : ‖invZeta ((σ : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1)) := by
      have h := norm_invZeta_right_le (d := σ) (y := y) hσ
      simpa using h
    have hM0 : (0 : ℝ) ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1)) := by
      have : (0 : ℝ) < 1 / (σ - 1) := by positivity
      positivity
    exact norm_dampedInvZeta_le hP2 ht0 ht1 hσhalf (by rw [hre]) hM0 hbase
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hInt : Integrable (fun y : ℝ =>
      (Real.exp (22 / 4) * (1 + 1 / (σ - 1)) * dampedCorrBound P σ)
        * ‖mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I)‖) :=
    ((verticalIntegrable_mellin_smoothWeight hN hH (by linarith)).norm).const_mul _
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    hInt (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul]

end

end RHTower.Sieve
