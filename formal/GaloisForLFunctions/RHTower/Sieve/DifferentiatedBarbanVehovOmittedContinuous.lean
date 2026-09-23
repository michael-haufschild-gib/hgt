import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedKernels
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovContinuousKernels

/-!
# Continuous main terms for the omitted detector-head boundary

The continuous lcm fibre runs from `L * max(q,r)` to `L * M`. Its logarithmic width is exactly
`log(M / max(q,r))`. Integrating zero, one, and two complementary logarithms gives the closed
boundary kernels below.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- Continuous lcm quadratic form for the omitted-head base moment. -/
def barbanVehovOmittedLongBaseContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernelContinuous
        (L * max p.1 p.2) (L * M) p.1 p.2

/-- Continuous lcm form for the omitted-head base/differentiated cross moment. -/
def barbanVehovOmittedLongCrossContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelContinuous
        (L * max p.1 p.2) (L * M) p.1 p.2

/-- Continuous lcm form for the omitted-head differentiated square moment. -/
def barbanVehovOmittedLongDerivativeContinuous (L M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernelContinuous
        (L * max p.1 p.2) (L * M) p.1 p.2

/-- Logarithm of a positive natural product divided by a positive natural denominator. -/
theorem log_nat_mul_div
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log ((((a * b : ℕ) : ℝ) / (c : ℝ))) =
      Real.log a + Real.log b - Real.log c := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  rw [Real.log_div (mul_ne_zero haR hbR) hcR, Real.log_mul haR hbR]

/-- Logarithm of a quotient of positive naturals. -/
theorem log_nat_div
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (((a : ℝ) / (b : ℝ))) = Real.log a - Real.log b := by
  exact Real.log_div (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')

/-- Closed continuous harmonic kernel for the omitted boundary. -/
theorem barbanVehovLongHarmonicKernelContinuous_maxEndpoint_eq
    {L M q r : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongHarmonicKernelContinuous
        (L * max q r) (L * M) q r =
      Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) /
        (Nat.lcm q r : ℝ) := by
  have hm : 0 < max q r := lt_max_iff.mpr (Or.inl hq)
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongHarmonicKernelContinuous,
    log_nat_mul_div hL hM he, log_nat_mul_div hL hm he,
    log_nat_div hM hm]
  ring

/-- Closed continuous first-log kernel for the omitted boundary. -/
theorem barbanVehovLongFirstLogKernelContinuous_maxEndpoint_eq
    {L M q r : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongFirstLogKernelContinuous
        (L * max q r) (L * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) *
            Real.log (((L * max q r : ℕ) : ℝ) / (r : ℝ)) +
          Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) ^ (2 : ℕ) / 2) := by
  have hm : 0 < max q r := lt_max_iff.mpr (Or.inl hq)
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have her := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_right q r)
  rw [barbanVehovLongFirstLogKernelContinuous]
  rw [her, log_nat_mul_div hL hM he, log_nat_mul_div hL hm he,
    log_nat_mul_div hL hm hr, log_nat_div hM hm]
  ring

/-- Closed continuous second-log kernel for the omitted boundary. -/
theorem barbanVehovLongSecondLogKernelContinuous_maxEndpoint_eq
    {L M q r : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongSecondLogKernelContinuous
        (L * max q r) (L * M) q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) *
            Real.log (((L * max q r : ℕ) : ℝ) / (q : ℝ)) *
            Real.log (((L * max q r : ℕ) : ℝ) / (r : ℝ)) +
          Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) ^ (2 : ℕ) / 2 *
            (Real.log (((L * max q r : ℕ) : ℝ) / (q : ℝ)) +
              Real.log (((L * max q r : ℕ) : ℝ) / (r : ℝ))) +
          Real.log ((M : ℝ) / (((max q r : ℕ) : ℝ))) ^ (3 : ℕ) / 3) := by
  have hm : 0 < max q r := lt_max_iff.mpr (Or.inl hq)
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have heq := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_left q r)
  have her := log_natDiv_eq_sub_log_of_dvd he (Nat.dvd_lcm_right q r)
  rw [barbanVehovLongSecondLogKernelContinuous]
  rw [heq, her, log_nat_mul_div hL hM he, log_nat_mul_div hL hm he,
    log_nat_mul_div hL hm hq, log_nat_mul_div hL hm hr,
    log_nat_div hM hm]
  ring

end

end RHTower.Sieve
