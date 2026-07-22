import GaloisForLFunctions.RHTower.CCMCriticalMellinApertureResolvent
import GaloisForLFunctions.RHTower.MobiusLogDivisorParaproduct

/-!
# Unit-aperture Riesz resonance and complete Möbius renewal

Unit-rate exponential aperture averaging has a second, arithmetic resonance.  Its integrated
causal profile is `2 (exp (-x/2) - exp (-x))`; after critical half-density normalization and the
substitution `x = log (X / n)`, the first exponential loses every dependence on `n`.  The resulting
weight is exactly the order-one Riesz weight

`2 / sqrt X * (1 - sqrt (n / X))`.

The complete Möbius--log future dressing of this weight has no hidden probabilistic cancellation:
the divisor cube collapses exactly, with fixed sign, to the positive von-Mangoldt renewal.  Thus
the unresolved cancellation is only between that prime-power renewal and the polar continuum.

These are known-derived exact identities recorded as corpus infrastructure.  This module makes no
novelty claim and proves no RH estimate.
-/

open Nat ArithmeticFunction Finset
open scoped BigOperators Moebius

namespace RHTower

noncomputable section

/-- Real unit-aperture profile obtained by integrating the averaged causal kernel. -/
def unitApertureRieszProfile (x : ℝ) : ℝ :=
  2 * (Real.exp (-x / 2) - Real.exp (-x))

/-- The previously formalized Volterra primitive is exactly the real unit-aperture profile. -/
theorem re_integral_criticalMellinApertureCausalKernel_eq_unitApertureRieszProfile
    (x : ℝ) :
    (∫ s : ℝ in 0..x, criticalMellinApertureCausalKernel s).re =
      unitApertureRieszProfile x := by
  have hhalf : Complex.exp (-(x : ℂ) / 2) = (Real.exp (-x / 2) : ℂ) := by
    rw [show (-(x : ℂ) / 2) = ((-x / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hfull : Complex.exp (-(x : ℂ)) = (Real.exp (-x) : ℂ) := by
    rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hhalfRe : (Complex.exp (-(x : ℂ) / 2)).re = Real.exp (-x / 2) := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hhalf
  have hfullRe : (Complex.exp (-(x : ℂ))).re = Real.exp (-x) := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hfull
  rw [integral_criticalMellinApertureCausalKernel]
  norm_num [Complex.mul_re, unitApertureRieszProfile]
  rw [hhalfRe, hfullRe]

/-- Critical half-density normalization of the unit-aperture profile. -/
def unitApertureCriticalPrimeWeight (X n : ℝ) : ℝ :=
  unitApertureRieszProfile (Real.log (X / n)) / Real.sqrt n

/-- **Unit-rate arithmetic resonance.**  On the physical range `0 < n <= X`, exponential aperture
averaging produces exactly the first Riesz weight.  In particular, its leading monomial is the
`n`-independent value `2 / sqrt X`. -/
theorem unitApertureCriticalPrimeWeight_eq_riesz
    {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    unitApertureCriticalPrimeWeight X n =
      2 / Real.sqrt X * (1 - Real.sqrt (n / X)) := by
  have hratio : 0 < n / X := div_pos hn hX
  have hratio' : 0 < X / n := div_pos hX hn
  have hsqrtRatio :
      Real.exp (-Real.log (X / n) / 2) = Real.sqrt (n / X) := by
    have hlog : -Real.log (X / n) = Real.log (n / X) := by
      rw [Real.log_div hX.ne' hn.ne', Real.log_div hn.ne' hX.ne']
      ring
    rw [hlog]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hratio]
    congr 1
    ring
  have hfullRatio : Real.exp (-Real.log (X / n)) = n / X := by
    have hlog : -Real.log (X / n) = Real.log (n / X) := by
      rw [Real.log_div hX.ne' hn.ne', Real.log_div hn.ne' hX.ne']
      ring
    rw [hlog, Real.exp_log hratio]
  have hsqrtDiv : Real.sqrt (n / X) = Real.sqrt n / Real.sqrt X := by
    exact Real.sqrt_div hn.le X
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn).ne'
  have hsX : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
  have hsnSq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  have hsXSq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
  rw [unitApertureCriticalPrimeWeight, unitApertureRieszProfile,
    hsqrtRatio, hfullRatio, hsqrtDiv]
  field_simp [hsn, hsX, hX.ne', hn.ne']
  nlinarith

/-- The finite unit-Riesz von-Mangoldt renewal. -/
def unitRieszVonMangoldtRenewal (X : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ArithmeticFunction.vonMangoldt k * unitApertureCriticalPrimeWeight X k

/-- Complete all-grade Möbius--log dressing of the same unit-Riesz profile. -/
def unitRieszMobiusFutureDressing (X : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, ∑ d ∈ k.divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d *
      unitApertureCriticalPrimeWeight X k

/-- **Complete future-dressing collapse.**  The full Möbius divisor cube is exactly the negative
von-Mangoldt renewal.  There is no residual Euler probability factor after all grades are joined. -/
theorem unitRieszMobiusFutureDressing_eq_neg_vonMangoldtRenewal
    (X : ℝ) (K : ℕ) :
    unitRieszMobiusFutureDressing X K = -unitRieszVonMangoldtRenewal X K := by
  rw [unitRieszMobiusFutureDressing, unitRieszVonMangoldtRenewal,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  have hmuLog :
      (∑ d ∈ k.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d) =
        -ArithmeticFunction.vonMangoldt k := by
    simpa only [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := k))
  rw [← Finset.sum_mul, hmuLog]
  ring

/-- On the physical support, every atom of the collapsed renewal is nonnegative.  The only
remaining signed comparison is therefore with the polar continuum, not among future Euler grades. -/
theorem unitRieszVonMangoldtRenewal_atom_nonneg
    {X : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkX : (k : ℝ) ≤ X) :
    0 ≤ ArithmeticFunction.vonMangoldt k * unitApertureCriticalPrimeWeight X k := by
  have hX : 0 < X := lt_of_lt_of_le (by exact_mod_cast hk) hkX
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  rw [unitApertureCriticalPrimeWeight_eq_riesz hX hkpos]
  have hratio : (k : ℝ) / X ≤ 1 := (div_le_one hX).2 hkX
  have hsqrt : Real.sqrt ((k : ℝ) / X) ≤ 1 := by
    exact Real.sqrt_le_one.mpr hratio
  have hfront : 0 ≤ 2 / Real.sqrt X := by positivity
  have hback : 0 ≤ 1 - Real.sqrt ((k : ℝ) / X) := sub_nonneg.mpr hsqrt
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (mul_nonneg hfront hback)

end

end RHTower
