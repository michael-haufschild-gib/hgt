import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortContinuousMain
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovHigherSelbergForms
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogSquareTwoOneAsymptotic

/-!
# Exact asymptotic of the continuous short Barban--Vehov main

The continuous lcm fibres are expanded without discarding their three harmonic-moment constants.
At logarithmic separation `log X = (2 + τ) log M`, every term becomes one of the ordinary,
gcd-logarithmic, or higher-gcd-logarithmic Selberg moments.  The two asymmetric
`log(gcd)^(2 : ℕ)` moments are supplied by `SelbergGcdLogSquareTwoOneAsymptotic`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

private theorem log_lcm_eq_add_sub_log_gcd
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    Real.log (Nat.lcm q r : ℝ) =
      Real.log q + Real.log r - Real.log (Nat.gcd q r : ℝ) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hgR : (Nat.gcd q r : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have heR : (Nat.lcm q r : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hprod : (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) = (q : ℝ) * (r : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  have hleft := Real.log_mul hgR heR
  have hright := Real.log_mul hqR hrR
  rw [hprod] at hleft
  linarith

/-- Exact ordinary/gcd-moment expansion of the continuous base fibre. -/
def barbanVehovShortBaseContinuousPolynomial (τ : ℝ) (M : ℕ) : ℝ :=
  let L := Real.log M
  (τ * L + harmonicLogMomentTotalConstant 0) *
      selbergOriginalLogMonomial 1 1 M +
    selbergOriginalLogMonomial 2 1 M +
    selbergOriginalLogMonomial 1 2 M +
    selbergOriginalGcdLogMonomial 1 1 M

/-- Exact ordinary/gcd-moment expansion of the continuous cross fibre. -/
def barbanVehovShortCrossContinuousPolynomial (τ : ℝ) (M : ℕ) : ℝ :=
  let L := Real.log M
  (-1 : ℝ) * (τ + τ ^ (2 : ℕ) / 2) * L ^ (2 : ℕ) * selbergOriginalLogMonomial 1 1 M -
      L * selbergOriginalLogMonomial 2 1 M -
      L * selbergOriginalGcdLogMonomial 1 1 M -
      (1 + τ) * L * selbergOriginalLogMonomial 1 2 M +
      (1 / 2 : ℝ) * selbergOriginalLogMonomial 3 1 M +
      selbergOriginalGcdLogMonomial 2 1 M +
      (1 / 2 : ℝ) * selbergOriginalGcdLogPowerMonomial 2 M -
      (1 / 2 : ℝ) * selbergOriginalLogMonomial 1 3 M -
      harmonicLogMomentTotalConstant 0 *
        (L * selbergOriginalLogMonomial 1 1 M -
          selbergOriginalLogMonomial 2 1 M -
          selbergOriginalGcdLogMonomial 1 1 M) -
      harmonicLogMomentTotalConstant 1 * selbergOriginalLogMonomial 1 1 M

/-- Exact ordinary/gcd-moment expansion of the continuous differentiated-square fibre. -/
def barbanVehovShortDerivativeContinuousPolynomial (τ : ℝ) (M : ℕ) : ℝ :=
  let L := Real.log M
  (τ + τ ^ (2 : ℕ) + τ ^ (3 : ℕ) / 3) * L ^ (3 : ℕ) * selbergOriginalLogMonomial 1 1 M +
    (1 + τ + τ ^ (2 : ℕ) / 2) * L ^ (2 : ℕ) *
      (selbergOriginalLogMonomial 2 1 M + selbergOriginalLogMonomial 1 2 M) +
    L ^ (2 : ℕ) * selbergOriginalGcdLogMonomial 1 1 M +
    τ * L * selbergOriginalLogMonomial 2 2 M -
    L * (selbergOriginalGcdLogMonomial 2 1 M +
      selbergOriginalGcdLogMonomial 1 2 M +
      selbergOriginalGcdLogPowerMonomial 2 M) +
    (1 / 2 : ℝ) * (selbergOriginalLogMonomial 3 2 M +
      selbergOriginalLogMonomial 2 3 M) -
    (1 / 6 : ℝ) * (selbergOriginalLogMonomial 4 1 M +
      selbergOriginalLogMonomial 1 4 M) +
    selbergOriginalGcdLogMonomial 2 2 M +
    (1 / 2 : ℝ) * (selbergOriginalGcdLogSquareTwoOneMonomial M +
      selbergOriginalGcdLogSquareOneTwoMonomial M) +
    (1 / 3 : ℝ) * selbergOriginalGcdLogPowerMonomial 3 M +
    harmonicLogMomentTotalConstant 0 *
      (L ^ (2 : ℕ) * selbergOriginalLogMonomial 1 1 M -
        L * (selbergOriginalLogMonomial 2 1 M +
          selbergOriginalLogMonomial 1 2 M +
          2 * selbergOriginalGcdLogMonomial 1 1 M) +
        selbergOriginalLogMonomial 2 2 M +
        selbergOriginalGcdLogMonomial 2 1 M +
        selbergOriginalGcdLogMonomial 1 2 M +
        selbergOriginalGcdLogPowerMonomial 2 M) +
    harmonicLogMomentTotalConstant 1 *
      (2 * L * selbergOriginalLogMonomial 1 1 M -
        selbergOriginalLogMonomial 2 1 M -
        selbergOriginalLogMonomial 1 2 M -
        2 * selbergOriginalGcdLogMonomial 1 1 M) +
    harmonicLogMomentTotalConstant 2 * selbergOriginalLogMonomial 1 1 M

private theorem continuous_log_coordinates
    {X M q r : ℕ} (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hr : 0 < r)
    {τ : ℝ} (hlog : Real.log X = (2 + τ) * Real.log M) :
    Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) =
        τ * Real.log M + Real.log ((M : ℝ) / (q : ℝ)) +
          Real.log ((M : ℝ) / (r : ℝ)) + Real.log (Nat.gcd q r : ℝ) ∧
      Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) =
        Real.log M - Real.log ((M : ℝ) / (r : ℝ)) -
          Real.log (Nat.gcd q r : ℝ) ∧
      Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) =
        Real.log M - Real.log ((M : ℝ) / (q : ℝ)) -
          Real.log (Nat.gcd q r : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have heR : (Nat.lcm q r : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hlcm := log_lcm_eq_add_sub_log_gcd hq hr
  have hXM := Real.log_div hXR heR
  have hMq := Real.log_div hMR hqR
  have hMr := Real.log_div hMR hrR
  have heq := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_left q r)
  have her := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_right q r)
  constructor
  · linarith
  constructor <;> linarith

theorem barbanVehovShortBaseContinuous_eq_polynomial
    {X M : ℕ} (hX : 0 < X) (hM : 0 < M) {τ : ℝ}
    (hlog : Real.log X = (2 + τ) * Real.log M) :
    barbanVehovShortBaseContinuous X M =
      barbanVehovShortBaseContinuousPolynomial τ M := by
  rw [barbanVehovShortBaseContinuous, barbanVehovShortBaseContinuousPolynomial,
    Finset.sum_product]
  dsimp only
  simp only [selbergOriginalLogMonomial, Finset.sum_product,
    selbergOriginalGcdLogMonomial, selbergOriginalGcdLogCoeff]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hrmem
  obtain ⟨hq, hqM⟩ := Finset.mem_Icc.mp hqmem
  obtain ⟨hr, hrM⟩ := Finset.mem_Icc.mp hrmem
  have hweight := barbanVehovWeight_mul_div_lcm_eq_originalCoeff hq hr hqM hrM
  obtain ⟨hz, ha, hb⟩ := continuous_log_coordinates hX hM hq hr hlog
  rw [barbanVehovShortHarmonicKernelContinuous]
  rw [show barbanVehovWeight M q * barbanVehovWeight M r *
      (1 / (Nat.lcm q r : ℝ) *
        (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
          harmonicLogMomentTotalConstant 0)) =
      (barbanVehovWeight M q * barbanVehovWeight M r /
        (Nat.lcm q r : ℝ)) *
        (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
          harmonicLogMomentTotalConstant 0) by ring, hweight, hz]
  ring

theorem barbanVehovShortCrossContinuous_eq_polynomial
    {X M : ℕ} (hX : 0 < X) (hM : 0 < M) {τ : ℝ}
    (hlog : Real.log X = (2 + τ) * Real.log M) :
    barbanVehovShortCrossContinuous X M =
      barbanVehovShortCrossContinuousPolynomial τ M := by
  rw [barbanVehovShortCrossContinuous, barbanVehovShortCrossContinuousPolynomial,
    Finset.sum_product]
  dsimp only
  simp only [selbergOriginalLogMonomial, selbergOriginalGcdLogMonomial,
    selbergOriginalGcdLogCoeff, selbergOriginalGcdLogPowerMonomial,
    Finset.sum_product]
  ring_nf
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  apply Finset.sum_congr rfl
  intro r hrmem
  obtain ⟨hq, hqM⟩ := Finset.mem_Icc.mp hqmem
  obtain ⟨hr, hrM⟩ := Finset.mem_Icc.mp hrmem
  have hweight := barbanVehovWeight_mul_div_lcm_eq_originalCoeff hq hr hqM hrM
  obtain ⟨hz, ha, hb⟩ := continuous_log_coordinates hX hM hq hr hlog
  rw [barbanVehovShortFirstLogKernelContinuous]
  rw [show barbanVehovWeight M q * barbanVehovWeight M r *
      (1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
            (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
              harmonicLogMomentTotalConstant 0) +
          (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (2 : ℕ) / 2 +
            harmonicLogMomentTotalConstant 1))) =
      (barbanVehovWeight M q * barbanVehovWeight M r /
        (Nat.lcm q r : ℝ)) *
        (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
            (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
              harmonicLogMomentTotalConstant 0) +
          (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (2 : ℕ) / 2 +
            harmonicLogMomentTotalConstant 1)) by ring, hweight, hz, hb]
  ring

theorem barbanVehovShortDerivativeContinuous_eq_polynomial
    {X M : ℕ} (hX : 0 < X) (hM : 0 < M) {τ : ℝ}
    (hlog : Real.log X = (2 + τ) * Real.log M) :
    barbanVehovShortDerivativeContinuous X M =
      barbanVehovShortDerivativeContinuousPolynomial τ M := by
  rw [barbanVehovShortDerivativeContinuous,
    barbanVehovShortDerivativeContinuousPolynomial, Finset.sum_product]
  dsimp only
  simp only [selbergOriginalLogMonomial, selbergOriginalGcdLogMonomial,
    selbergOriginalGcdLogCoeff, selbergOriginalGcdLogPowerMonomial,
    selbergOriginalGcdLogSquareTwoOneMonomial,
    selbergOriginalGcdLogSquareOneTwoMonomial, Finset.sum_product]
  ring_nf
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  apply Finset.sum_congr rfl
  intro r hrmem
  obtain ⟨hq, hqM⟩ := Finset.mem_Icc.mp hqmem
  obtain ⟨hr, hrM⟩ := Finset.mem_Icc.mp hrmem
  have hweight := barbanVehovWeight_mul_div_lcm_eq_originalCoeff hq hr hqM hrM
  obtain ⟨hz, ha, hb⟩ := continuous_log_coordinates hX hM hq hr hlog
  rw [barbanVehovShortSecondLogKernelContinuous]
  rw [show barbanVehovWeight M q * barbanVehovWeight M r *
      (1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
            Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
              (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
                harmonicLogMomentTotalConstant 0) +
          (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
            (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (2 : ℕ) / 2 +
              harmonicLogMomentTotalConstant 1) +
          (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (3 : ℕ) / 3 +
            harmonicLogMomentTotalConstant 2))) =
      (barbanVehovWeight M q * barbanVehovWeight M r /
        (Nat.lcm q r : ℝ)) *
        (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
            Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
              (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) +
                harmonicLogMomentTotalConstant 0) +
          (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
            (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (2 : ℕ) / 2 +
              harmonicLogMomentTotalConstant 1) +
          (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) ^ (3 : ℕ) / 3 +
            harmonicLogMomentTotalConstant 2)) by ring, hweight, hz, ha, hb]
  ring

end

end RHTower.Sieve
