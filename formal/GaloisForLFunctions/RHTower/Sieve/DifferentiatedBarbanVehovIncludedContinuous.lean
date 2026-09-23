import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedLcmExpansion
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedContinuous

/-!
# Continuous main terms for the included detector-head boundary

The cancellation-preserving lcm fibre runs from `L` to `L * min(q,r)`.  Its continuous kernels
therefore depend on `log(min(q,r))`, rather than the complementary maximum endpoint appearing in
the separately omitted head.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Continuous included-head quadratic form for the base moment. -/
def barbanVehovIncludedLongBaseContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernelContinuous
        L (L * min p.1 p.2) p.1 p.2

/-- Continuous included-head base/differentiated cross form. -/
def barbanVehovIncludedLongCrossContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelContinuous
        L (L * min p.1 p.2) p.1 p.2

/-- Continuous included-head differentiated-square form. -/
def barbanVehovIncludedLongDerivativeContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernelContinuous
        L (L * min p.1 p.2) p.1 p.2

/-- Closed harmonic kernel at the included-head minimum endpoint. -/
theorem barbanVehovLongHarmonicKernelContinuous_minEndpoint_eq
    {L q r : ℕ} (hL : 0 < L) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongHarmonicKernelContinuous L (L * min q r) q r =
      Real.log ((min q r : ℕ) : ℝ) / (Nat.lcm q r : ℝ) := by
  have hm : 0 < min q r := lt_min hq hr
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongHarmonicKernelContinuous,
    log_nat_mul_div hL hm he, log_nat_div hL he]
  ring

/-- Closed first-log kernel at the included-head minimum endpoint. -/
theorem barbanVehovLongFirstLogKernelContinuous_minEndpoint_eq
    {L q r : ℕ} (hL : 0 < L) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongFirstLogKernelContinuous L (L * min q r) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log ((min q r : ℕ) : ℝ) *
            Real.log ((L : ℝ) / (r : ℝ)) +
          Real.log ((min q r : ℕ) : ℝ) ^ (2 : ℕ) / 2) := by
  have hm : 0 < min q r := lt_min hq hr
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have her := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_right q r)
  rw [barbanVehovLongFirstLogKernelContinuous, her,
    log_nat_mul_div hL hm he, log_nat_div hL he,
    log_nat_div hL hr]
  ring

/-- Closed second-log kernel at the included-head minimum endpoint. -/
theorem barbanVehovLongSecondLogKernelContinuous_minEndpoint_eq
    {L q r : ℕ} (hL : 0 < L) (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongSecondLogKernelContinuous L (L * min q r) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log ((min q r : ℕ) : ℝ) *
            Real.log ((L : ℝ) / (q : ℝ)) *
            Real.log ((L : ℝ) / (r : ℝ)) +
          Real.log ((min q r : ℕ) : ℝ) ^ (2 : ℕ) / 2 *
            (Real.log ((L : ℝ) / (q : ℝ)) +
              Real.log ((L : ℝ) / (r : ℝ))) +
          Real.log ((min q r : ℕ) : ℝ) ^ (3 : ℕ) / 3) := by
  have hm : 0 < min q r := lt_min hq hr
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have heq := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_left q r)
  have her := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_right q r)
  rw [barbanVehovLongSecondLogKernelContinuous, heq, her,
    log_nat_mul_div hL hm he, log_nat_div hL he,
    log_nat_div hL hq, log_nat_div hL hr]
  ring

/-- Polynomial main term for the included-head base moment. -/
def barbanVehovIncludedLongBasePolynomialMain (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ) * Real.log ((min p.1 p.2 : ℕ) : ℝ)

/-- Polynomial main term for the included-head base/differentiated cross moment. -/
def barbanVehovIncludedLongCrossPolynomialMain (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ)) *
        (Real.log ((min p.1 p.2 : ℕ) : ℝ) *
            (ell - Real.log (p.2 : ℝ)) +
          Real.log ((min p.1 p.2 : ℕ) : ℝ) ^ (2 : ℕ) / 2)

/-- Polynomial main term for the included-head differentiated-square moment. -/
def barbanVehovIncludedLongDerivativePolynomialMain (ell : ℝ) (M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 /
      (Nat.lcm p.1 p.2 : ℝ) *
        (Real.log ((min p.1 p.2 : ℕ) : ℝ) *
            (ell - Real.log (p.1 : ℝ)) * (ell - Real.log (p.2 : ℝ)) +
          Real.log ((min p.1 p.2 : ℕ) : ℝ) ^ (2 : ℕ) / 2 *
            (2 * ell - Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ)) +
          Real.log ((min p.1 p.2 : ℕ) : ℝ) ^ (3 : ℕ) / 3)

theorem barbanVehovIncludedLongBaseContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) :
    barbanVehovIncludedLongBaseContinuous L M =
      barbanVehovIncludedLongBasePolynomialMain M := by
  rw [barbanVehovIncludedLongBaseContinuous,
    barbanVehovIncludedLongBasePolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  rw [barbanVehovLongHarmonicKernelContinuous_minEndpoint_eq
    hL hp1.1 hp2.1]
  ring

theorem barbanVehovIncludedLongCrossContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) :
    barbanVehovIncludedLongCrossContinuous L M =
      barbanVehovIncludedLongCrossPolynomialMain (Real.log L) M := by
  rw [barbanVehovIncludedLongCrossContinuous,
    barbanVehovIncludedLongCrossPolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  rw [barbanVehovLongFirstLogKernelContinuous_minEndpoint_eq
    hL hp1.1 hp2.1, log_nat_div hL hp2.1]
  ring

theorem barbanVehovIncludedLongDerivativeContinuous_eq_polynomialMain
    {L M : ℕ} (hL : 0 < L) :
    barbanVehovIncludedLongDerivativeContinuous L M =
      barbanVehovIncludedLongDerivativePolynomialMain (Real.log L) M := by
  rw [barbanVehovIncludedLongDerivativeContinuous,
    barbanVehovIncludedLongDerivativePolynomialMain]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  rw [barbanVehovLongSecondLogKernelContinuous_minEndpoint_eq
    hL hp1.1 hp2.1, log_nat_div hL hp1.1, log_nat_div hL hp2.1]
  ring

end

end RHTower.Sieve
