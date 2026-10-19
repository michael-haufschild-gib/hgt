import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalCorrelationLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission

/-!
# Complete critical prime limit for one factorial source

The actual logarithmic source at scale `n+1` has a complete prime-channel limit.
The proof uses the existing critical correlation bound uniformly in `n`, then
passes through every prime power by dominated convergence. The limiting physical
correlation is positive at odd dilations, negative at dilations congruent to two
modulo four, and zero at multiples of four.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private theorem criticalCorrelation_uniform_bound (n r : ℕ) (hr : 0 < r) :
    |factorialCriticalCorrelation n r| ≤ 264 / (r : ℝ) := by
  have hraw := critical_factorial_physical_correlation_bound {n} (fun _ => 1) (r-1)
  rw [Nat.sub_add_cancel (show 1 ≤ r by omega)] at hraw
  have h : |factorialCriticalCorrelation n r| ≤
      criticalFactorialPrimeConstant {n} (fun _ => 1) / (r : ℝ) := by
    simpa [factorialCriticalCorrelation, factorialPhaseCombination] using hraw
  have hK : criticalFactorialPrimeConstant {n} (fun _ => 1) ≤ 264 := by
    simp only [criticalFactorialPrimeConstant, Finset.sum_singleton, abs_one, mul_one]
    have hN : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hNp : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    calc 12 * (1 / ((n+1 : ℕ) : ℝ)) * (8 + 14 * ((n+1 : ℕ) : ℝ)) =
        (96 + 168 * ((n+1 : ℕ) : ℝ)) / ((n+1 : ℕ) : ℝ) := by ring
      _ ≤ 264 := (div_le_iff₀ hNp).2 (by nlinarith)
  exact h.trans (div_le_div_of_nonneg_right hK (Nat.cast_nonneg r))

private def limitPrimePhysicalAtom (n r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    factorialCriticalCorrelation n r else 0

private def limitPrimeAtom (r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    factorialCriticalCorrelationLimit r else 0

private theorem limit_prime_atom_tendsto (r : ℕ) :
    Tendsto (fun n => limitPrimePhysicalAtom n r) atTop (𝓝 (limitPrimeAtom r)) := by
  by_cases hr : 2 ≤ r
  · simpa only [limitPrimePhysicalAtom, limitPrimeAtom, if_pos hr] using
      (factorialCriticalCorrelation_tendsto r (by omega)).const_mul
        ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ))
  · simp only [limitPrimePhysicalAtom, limitPrimeAtom, if_neg hr]
    exact tendsto_const_nhds

private theorem limit_prime_atom_bound (n r : ℕ) :
    ‖limitPrimePhysicalAtom n r‖ ≤ 264 * envelopePrimeMajorant (3 / 2) r := by
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hc := criticalCorrelation_uniform_bound n r (by omega)
    simp only [limitPrimePhysicalAtom, envelopePrimeMajorant, if_pos hr,
      show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num, Real.rpow_two,
      norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrp.le)]
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) * |factorialCriticalCorrelation n r|
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) * (264 / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hc
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrp.le)
      _ = 264 * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ 2) := by ring
  · simp [limitPrimePhysicalAtom, envelopePrimeMajorant, hr]

/-- The complete logarithmic prime channel of the actual singleton critical source. -/
def factorialCriticalPrimeEnergy (n : ℕ) : ℝ :=
  ∑' r : ℕ, (if 2 ≤ r then
    (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
      ∫ x : ℝ, criticalFactorialSource {n} (fun _ => 1) x *
        criticalFactorialSource {n} (fun _ => 1) (x - Real.log (r : ℝ))

/-- The limiting prime channel retains all prime powers and every harmonic. -/
def factorialCriticalPrimeLimit : ℝ :=
  ∑' r : ℕ, if 2 ≤ r then
    (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) * factorialCriticalCorrelationLimit r else 0

private theorem critical_prime_energy_eq (n : ℕ) :
    factorialCriticalPrimeEnergy n = ∑' r, limitPrimePhysicalAtom n r := by
  unfold factorialCriticalPrimeEnergy
  apply tsum_congr
  intro r
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
    have hbridge := criticalFactorialSource_correlation_eq {n} (fun _ => 1) hr1
    have hc : (∫ x : ℝ, criticalFactorialSource {n} (fun _ => 1) x *
        criticalFactorialSource {n} (fun _ => 1) (x - Real.log (r : ℝ))) =
        (Real.sqrt (r : ℝ))⁻¹ * factorialCriticalCorrelation n r := by
      simpa [factorialCriticalCorrelation, factorialPhaseCombination] using hbridge
    simp only [limitPrimePhysicalAtom, if_pos hr]
    rw [hc]
    have hfac : ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ))⁻¹ = (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) := by
      have hsq := Real.sq_sqrt hrp.le
      field_simp [ne_of_gt hs, ne_of_gt hrp]
      linear_combination -((ArithmeticFunction.vonMangoldt r : ℝ)) * hsq
    rw [← mul_assoc, hfac]
  · simp [limitPrimePhysicalAtom, hr]

/-- The limiting series is absolutely convergent, independently of the source-scale limit. -/
theorem summable_factorialCriticalPrimeLimit_atoms :
    Summable (fun r : ℕ => |if 2 ≤ r then
      (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalCorrelationLimit r else 0|) := by
  have hbound (r : ℕ) : ‖limitPrimeAtom r‖ ≤ 264 * envelopePrimeMajorant (3 / 2) r :=
    le_of_tendsto (limit_prime_atom_tendsto r).norm
      (Eventually.of_forall fun n => limit_prime_atom_bound n r)
  have h : Summable (fun r => ‖limitPrimeAtom r‖) :=
    (summable_canonicalPrimeMajorant.mul_left 264).of_nonneg_of_le
      (fun _ => norm_nonneg _) hbound
  simpa only [limitPrimeAtom, Real.norm_eq_abs] using h

/-- The actual complete critical prime channel converges without truncating primes or harmonics. -/
theorem factorialCriticalPrimeEnergy_tendsto :
    Tendsto factorialCriticalPrimeEnergy atTop (𝓝 factorialCriticalPrimeLimit) := by
  have h := tendsto_tsum_of_dominated_convergence
    (summable_canonicalPrimeMajorant.mul_left 264) limit_prime_atom_tendsto
    (Eventually.of_forall fun n r => limit_prime_atom_bound n r)
  change Tendsto (fun n => ∑' r, limitPrimePhysicalAtom n r) atTop
    (𝓝 factorialCriticalPrimeLimit) at h
  exact h.congr (fun n => (critical_prime_energy_eq n).symm)

private theorem primeLimit_weight_bound (k : ℕ) : |dyadicHarmonicWeight k| ≤ 1 := by
  cases k with
  | zero => simp only [dyadicHarmonicWeight_zero, abs_zero, zero_le_one]
  | succ k =>
      refine (abs_dyadicHarmonicWeight_le (k+1)).trans ?_
      have hk : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      have hk2 : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) ^ 2 := by nlinarith
      simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hk2

private theorem primeLimit_harmonic_summable (r : ℕ) :
    Summable (fun l : ℕ => dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
      factorialCriticalHarmonicDefect (r*l)) := by
  apply (summable_abs_dyadicHarmonicWeight.mul_left 2).of_norm_bounded
  intro l
  have hJ := factorialCriticalHarmonicDefect_bounds (r*l)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hJ.1]
  calc |dyadicHarmonicWeight (r*l)| * |dyadicHarmonicWeight l| *
      factorialCriticalHarmonicDefect (r*l) ≤ 1 * |dyadicHarmonicWeight l| * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (primeLimit_weight_bound _) (abs_nonneg _))
          hJ.2 hJ.1 (by positivity)
    _ = _ := by ring

private theorem primeLimit_chi_product (r l : ℕ) :
    dyadicHarmonicChi (r*l) * dyadicHarmonicChi l =
      if r % 2 = 1 then (dyadicHarmonicChi l) ^ 2
      else if r % 4 = 2 then (if l % 2 = 1 then -1 else 0) else 0 := by
  have hr2 : r % 2 = (r % 4) % 2 := by omega
  have hl2 : l % 2 = (l % 4) % 2 := by omega
  have hr4 := Nat.mod_lt r (by norm_num : 0 < 4)
  have hl4 := Nat.mod_lt l (by norm_num : 0 < 4)
  interval_cases hR : r % 4 <;> interval_cases hL : l % 4 <;>
    norm_num [dyadicHarmonicChi, Nat.mul_mod, hr2, hl2, hR, hL]

/-- Odd dilations retain a strictly positive complete limiting physical correlation. -/
theorem factorialCriticalCorrelationLimit_pos_of_odd (r : ℕ) (hr : r % 2 = 1) :
    0 < factorialCriticalCorrelationLimit r := by
  let f (l : ℕ) := dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
    factorialCriticalHarmonicDefect (r*l)
  have hf (l : ℕ) : 0 ≤ f l := by
    have hchi := primeLimit_chi_product r l
    rw [if_pos hr] at hchi
    have hw : 0 ≤ dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l := by
      unfold dyadicHarmonicWeight
      rw [div_mul_div_comm, hchi]
      exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact mul_nonneg hw (factorialCriticalHarmonicDefect_bounds _).1
  have hrp : 0 < r := by omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrp
  have hchi : dyadicHarmonicChi r = 1 := by simp only [dyadicHarmonicChi, if_pos hr]
  have hf1 : 0 < f 1 := by
    dsimp only [f]
    simp only [mul_one, dyadicHarmonicWeight_one]
    rw [dyadicHarmonicWeight, hchi]
    exact mul_pos (div_pos zero_lt_one (by positivity)) (factorialCriticalHarmonicDefect_pos r hrp)
  have hsum : 0 < ∑' l, f l := hf1.trans_le
    ((primeLimit_harmonic_summable r).le_tsum 1 (fun l _ => hf l))
  exact mul_pos (by positivity : 0 < 4 / Real.pi ^ 4) hsum

/-- Exactly one factor of two reverses the sign of every surviving limiting harmonic. -/
theorem factorialCriticalCorrelationLimit_neg_of_two_mod_four (r : ℕ) (hr : r % 4 = 2) :
    factorialCriticalCorrelationLimit r < 0 := by
  let f (l : ℕ) := dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l *
    factorialCriticalHarmonicDefect (r*l)
  have hodd : ¬r % 2 = 1 := by omega
  have hf (l : ℕ) : f l ≤ 0 := by
    have hchi := primeLimit_chi_product r l
    rw [if_neg hodd, if_pos hr] at hchi
    have hchi0 : dyadicHarmonicChi (r*l) * dyadicHarmonicChi l ≤ 0 := by
      rw [hchi]
      split_ifs <;> norm_num
    have hw : dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l ≤ 0 := by
      unfold dyadicHarmonicWeight
      rw [div_mul_div_comm]
      exact div_nonpos_of_nonpos_of_nonneg hchi0 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact mul_nonpos_of_nonpos_of_nonneg hw (factorialCriticalHarmonicDefect_bounds _).1
  have hrp : 0 < r := by omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrp
  have hchi : dyadicHarmonicChi r = -1 := by
    simp only [dyadicHarmonicChi, if_neg hodd, if_pos hr]
  have hf1 : f 1 < 0 := by
    dsimp only [f]
    simp only [mul_one, dyadicHarmonicWeight_one]
    rw [dyadicHarmonicWeight, hchi]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) (by positivity))
      (factorialCriticalHarmonicDefect_pos r hrp)
  have hnegSum : 0 < ∑' l, -f l := (neg_pos.mpr hf1).trans_le
    ((primeLimit_harmonic_summable r).neg.le_tsum 1 (fun l _ => neg_nonneg.mpr (hf l)))
  rw [tsum_neg] at hnegSum
  have hsum : (∑' l, f l) < 0 := by linarith
  exact mul_neg_of_pos_of_neg (by positivity : 0 < 4 / Real.pi ^ 4) hsum

/-- Multiples of four have zero complete limiting physical correlation. -/
theorem factorialCriticalCorrelationLimit_zero_of_four_mod_zero (r : ℕ) (hr : r % 4 = 0) :
    factorialCriticalCorrelationLimit r = 0 := by
  have hodd : ¬r % 2 = 1 := by omega
  have htwo : ¬r % 4 = 2 := by omega
  have hw (l : ℕ) : dyadicHarmonicWeight (r*l) * dyadicHarmonicWeight l = 0 := by
    unfold dyadicHarmonicWeight
    rw [div_mul_div_comm, primeLimit_chi_product, if_neg hodd, if_neg htwo, zero_div]
  unfold factorialCriticalCorrelationLimit
  simp only [hw, zero_mul, tsum_zero, mul_zero]

end
end GaloisForLFunctions.ArithmeticPositivityTheory
