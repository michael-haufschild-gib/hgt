import GaloisForLFunctions.RHTower.Sieve.DampedShiftBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistPerron

/-!
# The twisted damped smoothed sum on a fixed line

The damped analogue of `Sieve/MoebiusTwistPerron`.  The twisted damped series at `s` is
`dampedInvZeta P t (s + iτ)`, whose modulus is the `invZeta` one times `dampedCorrBound P σ` by
`Sieve/DampedShiftBound`, the correction being insensitive to the vertical shift.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

theorem dampedTwist_zero (P : Finset ℕ) (t τ : ℝ) : dampedTwist P t τ 0 = 0 := by
  rw [dampedTwist, dampedOmegaMoebius_zero, zero_mul]

/-- **The twisted damped smoothed sum on a fixed line.** -/
theorem norm_tsum_dampedTwist_smoothWeight_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H σ : ℝ} (hN : 0 < N) (hH : 0 < H) (hσ : 1 < σ)
    (τ : ℝ) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ (Real.exp (22 / 4) * (1 + 1 / (σ - 1)) * dampedCorrBound P σ)
          * ∫ y : ℝ, ‖mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
              ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have hperron := tsum_mul_smoothWeight_eq_integral (a := dampedTwist P t τ)
    (norm_dampedTwist_le_one ht0 ht1 τ) (dampedTwist_zero P t τ) hN hH hσ
  rw [hperron]
  have hpt : ∀ y : ℝ,
      ‖(∑' n : ℕ, dampedTwist P t τ n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)))
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
    rw [tsum_dampedTwist_cpow hPprime ht0 ht1 τ hs]
    have hM0 : (0 : ℝ) ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1)) := by
      have : (0 : ℝ) < 1 / (σ - 1) := by positivity
      positivity
    have hbase : ‖invZeta (((σ : ℂ) + (y : ℝ) * Complex.I) + (τ : ℂ) * Complex.I)‖
        ≤ Real.exp (22 / 4) * (1 + 1 / (σ - 1)) := by
      rw [show ((σ : ℂ) + (y : ℝ) * Complex.I) + (τ : ℂ) * Complex.I
          = (σ : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      have h := norm_invZeta_right_le (d := σ) (y := y + τ) hσ
      simpa using h
    exact norm_dampedInvZeta_shift_le hP2 ht0 ht1 hσhalf (by rw [hre]) τ hM0 hbase
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
