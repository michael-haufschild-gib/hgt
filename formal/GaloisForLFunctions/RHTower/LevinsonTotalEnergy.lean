import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongRangeSplit
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedEnergy
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortEnergyMain

/-!
# The total mollified coefficient energy in one statement

The mean-value theorem turns the direct×direct part of Levinson's mollified mean square into
`(T₂−T₁)` times the *total* coefficient energy `∑_{r < L·M} |c_r|²`.  The corpus splits that exactly
into the short range `k ≤ L` and the long tail, and approximates the long tail by an explicit
polynomial main term with an error that is `O(M²/L)` once `8M² ≤ L`.

This file records the two facts as a single quantitative statement about the total energy — the form
the assembly of `LevinsonMeanSquareGate` consumes.  At the Levinson scaling `L ≍ T^{1/2+θ}`,
`M = T^θ` the hypothesis `8M² ≤ L` is exactly `θ < 1/2`, and the error is `≍ T^{θ−1/2} → 0`.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The total mollified coefficient energy, short range plus polynomial main.** -/
theorem abs_levinsonCriticalDetectorTotalEnergy_sub_le
    (lam : ℝ) {L M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ (2 : ℕ) ≤ L) :
    |(∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r)
        - ((∑ k ∈ Finset.Icc 1 L,
              ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ))
            + Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M)|
      ≤ (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) +
          2 * |lam| * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ))) +
          lam ^ (2 : ℕ) * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
            (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)))) /
        Real.log M ^ (2 : ℕ) := by
  have hM1 : 1 ≤ M := le_of_lt hM
  rw [sum_levinsonCriticalDetectorFiniteEnergyTerm_eq_short_add_long lam L M hM1]
  have hlong := Sieve.abs_levinsonCriticalDetectorLongEnergy_sub_includedPolynomialMain_le
    lam hM hscale
  have hrw : (∑ k ∈ Finset.Icc 1 L,
        ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ))
        + levinsonCriticalDetectorLongEnergy lam L M
      - ((∑ k ∈ Finset.Icc 1 L,
            ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ))
          + Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M)
      = levinsonCriticalDetectorLongEnergy lam L M
        - Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M := by
    ring
  rw [hrw]
  exact hlong


/-- The error of the total-energy approximation collapses to `27·M²/L` once the Levinson parameter
satisfies `|λ|·log(LM+1) ≤ 1` — which it does, since `|λ| ≍ 1/log T` and `log(LM+1) ≍ (1/2+2θ)log T`
give `|λ|log(LM+1) = O(1)`. -/
theorem levinsonTotalEnergy_error_le_of_lam_small
    {lam : ℝ} {L M : ℕ} (hM : 1 < M) (hL : 0 < L)
    (hlam : |lam| * Real.log (L * M + 1 : ℕ) ≤ 1) :
    (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) +
        2 * |lam| * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
          (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ))) +
        lam ^ (2 : ℕ) * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
          (12 * Real.log (L * M + 1 : ℕ) ^ (2 : ℕ) / (L : ℝ)))) /
      Real.log M ^ (2 : ℕ)
      ≤ 27 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : (0 : ℝ) < Real.log M := Real.log_pos (by linarith)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  set A : ℝ := Real.log (L * M + 1 : ℕ) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ L * M + 1 := by omega
    exact_mod_cast this
  have hlam0 : (0 : ℝ) ≤ |lam| := abs_nonneg _
  have hsq : lam ^ (2 : ℕ) * A ^ (2 : ℕ) ≤ 1 := by
    have hprod : |lam| * A ≤ 1 := hlam
    have hnn : (0 : ℝ) ≤ |lam| * A := by positivity
    have hlamsq : lam ^ (2 : ℕ) = |lam| ^ (2 : ℕ) := (sq_abs lam).symm
    nlinarith [hprod, hnn]
  have hnum : ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (3 / (L : ℝ)) +
      2 * |lam| * (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (6 * A / (L : ℝ))) +
      lam ^ (2 : ℕ) * (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (12 * A ^ (2 : ℕ) / (L : ℝ)))
      = (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) *
        (3 + 12 * (|lam| * A) + 12 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ))) := by
    field_simp
    ring
  rw [hnum]
  have hfac : (0 : ℝ) < ((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ) := by positivity
  have hbr : (3 : ℝ) + 12 * (|lam| * A) + 12 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)) ≤ 27 := by
    linarith [hlam, hsq]
  have hstep : (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) *
      (3 + 12 * (|lam| * A) + 12 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)))
      ≤ (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) * 27 :=
    mul_le_mul_of_nonneg_left hbr hfac.le
  have hdiv : ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) * 27) / Real.log M ^ (2 : ℕ)
      = 27 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
    field_simp
  calc ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) *
        (3 + 12 * (|lam| * A) + 12 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)))) / Real.log M ^ (2 : ℕ)
      ≤ ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (L : ℝ)) * 27) / Real.log M ^ (2 : ℕ) := by
        exact div_le_div_of_nonneg_right hstep (by positivity)
    _ = 27 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := hdiv

/-- **The total mollified coefficient energy with a clean error.** -/
theorem abs_levinsonCriticalDetectorTotalEnergy_sub_le_sq_div
    (lam : ℝ) {L M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ (2 : ℕ) ≤ L)
    (hlam : |lam| * Real.log (L * M + 1 : ℕ) ≤ 1) :
    |(∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r)
        - ((∑ k ∈ Finset.Icc 1 L,
              ‖Sieve.levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ))
            + Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M)|
      ≤ 27 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
  have hMpos : 0 < M := by omega
  have hL : 0 < L := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  exact le_trans (abs_levinsonCriticalDetectorTotalEnergy_sub_le lam hM hscale)
    (levinsonTotalEnergy_error_le_of_lam_small hM hL hlam)


/-- **The total mollified coefficient energy against two explicit main terms.**

The short range contributes the origin-based lcm quadratic form, the long range the included-head
polynomial main term, and the whole error is `O(M²/L)`.  Under the Levinson scaling
`L ≍ T^{1/2+θ}`, `M = T^θ` with `θ < 1/2` this error tends to zero, so the mollified coefficient
energy is exactly the sum of the two explicit quadratic forms in the limit. -/
theorem abs_levinsonCriticalDetectorTotalEnergy_sub_shortMain_add_longMain_le
    (lam : ℝ) {L M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ (2 : ℕ) ≤ L)
    (hlam : |lam| * Real.log (L * M + 1 : ℕ) ≤ 1) :
    |(∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r)
        - (Sieve.barbanVehovShortEnergyMain lam L M +
            Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M)|
      ≤ 36 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := by
  have hM1 : 1 ≤ M := le_of_lt hM
  have hMsq : M ≤ M ^ (2 : ℕ) := by nlinarith [hM1]
  have hML : M ≤ L := by omega
  have hL : 0 < L := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hlamL : |lam| * Real.log ((L + 1 : ℕ) : ℝ) ≤ 1 := by
    refine le_trans ?_ hlam
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg lam)
    refine Real.log_le_log (by positivity) ?_
    have : L + 1 ≤ L * M + 1 := by
      have := Nat.le_mul_of_pos_right L (Nat.zero_lt_of_lt hM)
      omega
    exact_mod_cast this
  have hshort := Sieve.abs_barbanVehovShortEnergyLcm_sub_main_le_sq_div lam hM hscale hlamL
  have heq := Sieve.sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_shortEnergyLcm
    lam (X := L) (M := M) hM hML
  have htotal := abs_levinsonCriticalDetectorTotalEnergy_sub_le_sq_div lam hM hscale hlam
  rw [heq] at htotal
  have hsplit :
      (∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r)
          - (Sieve.barbanVehovShortEnergyMain lam L M +
              Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M)
        = ((∑ r : Fin (L * M), levinsonCriticalDetectorFiniteEnergyTerm lam L M r)
              - (Sieve.barbanVehovShortEnergyLcm lam L M +
                Sieve.barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M))
          + (Sieve.barbanVehovShortEnergyLcm lam L M -
              Sieve.barbanVehovShortEnergyMain lam L M) := by
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have : 27 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) + 9 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ)
      = 36 * (M : ℝ) ^ (2 : ℕ) / (L : ℝ) := by ring
  linarith [htotal, hshort]

end RHTower

end
