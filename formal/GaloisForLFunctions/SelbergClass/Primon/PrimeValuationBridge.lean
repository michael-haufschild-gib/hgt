import GaloisForLFunctions.SelbergClass.Primon.AveragedPrimePowers
import GaloisForLFunctions.SelbergClass.Primon.ArithmeticAverage
import GaloisForLFunctions.HTGeometry.PrimeValuationLevelStructure

/-!
# Phase-averaged prime powers as valuation probabilities

The averaged mass at `p^(2*(m+1))`, divided by `log(p)`, is exactly the
geometric valuation probability `(1-1/p)/p^m`. Finite prime-power towers
are therefore valuation distribution functions, and their missing mass
is a valuation-tail probability. Finite products of the normalized weights
are cylinder probabilities in the prime-valuation product sector.

The same law also connects the arithmetic phase mean to a probability
generating function: `E[z^K] = (1-1/p)/(1-z/p)`. At `z=r²`, this is the
Kesten–McKay mean of the charged local factor multiplied by `1-1/p`.
-/

open MeasureTheory ProbabilityTheory Set Finset
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Each averaged even-power mass is `log(p)` times one geometric valuation atom. -/
theorem averagedPrimePowerWeight_eq_valuationMass (p : Nat.Primes) (m : ℕ) :
    averagedPrimePowerWeight p m =
      Real.log (p : ℝ) * (primeValuationLaw p).real {m} := by
  rw [averagedPrimePowerWeight_eq_difference, primeValuationLaw,
    geometricMeasure_real_singleton (primeValuationParam_ne_zero p),
    primeValuationParam_coe, sub_sub_cancel, pow_succ]
  ring

/-- Averaged prime-power weights are nonnegative because they are positive multiples of masses. -/
theorem averagedPrimePowerWeight_nonneg (p : Nat.Primes) (m : ℕ) :
    0 ≤ averagedPrimePowerWeight p m := by
  rw [averagedPrimePowerWeight_eq_valuationMass]
  exact mul_nonneg (Real.log_nonneg (one_lt_prime_cast p).le) measureReal_nonneg

/-- Normalizing a prime-power weight by the total mass gives the actual valuation atom. -/
theorem primeValuationLaw_singleton_eq_averagedWeight (p : Nat.Primes) (m : ℕ) :
    primeValuationLaw p {m} =
      ENNReal.ofReal (averagedPrimePowerWeight p m / Real.log (p : ℝ)) := by
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (one_lt_prime_cast p)).ne'
  have he : Real.log (p : ℝ) * (primeValuationLaw p).real {m} / Real.log (p : ℝ) =
      (primeValuationLaw p).real {m} := by field_simp [hl]
  rw [averagedPrimePowerWeight_eq_valuationMass, he, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A complete prime-power tower has total mass exactly `log(p)`. -/
theorem hasSum_averagedPrimePowerWeight (p : Nat.Primes) :
    HasSum (fun m => averagedPrimePowerWeight p m) (Real.log (p : ℝ)) := by
  have h := (hasSum_one_geometricMeasure (primeValuationParam_ne_zero p)).mul_left
    (Real.log (p : ℝ))
  simp only [mul_one] at h
  have he : (fun m => averagedPrimePowerWeight p m) =
      fun m => Real.log (p : ℝ) *
        ((1 - (primeValuationParam p : ℝ)) ^ m * (primeValuationParam p : ℝ)) := by
    funext m
    rw [averagedPrimePowerWeight_eq_difference, primeValuationParam_coe,
      sub_sub_cancel, pow_succ]
    ring
  rw [he]
  exact h

/-- The missing mass above a tower cutoff is the corresponding valuation tail. -/
theorem primePowerDefect_eq_valuationTail (p : Nat.Primes) (M : ℕ) :
    Real.log (p : ℝ) / (p : ℝ) ^ M =
      Real.log (p : ℝ) * (primeValuationLaw p).real {k : ℕ | M ≤ k} := by
  rw [measureReal_def, primeValuationLaw_Ici,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [div_eq_mul_inv, inv_pow]

/-- Finite averaged prime-power towers are weighted valuation distribution functions. -/
theorem sum_averagedPrimePowerWeight_eq_valuationCDF (p : Nat.Primes) (M : ℕ) :
    (∑ m ∈ range M, averagedPrimePowerWeight p m) =
      Real.log (p : ℝ) * (primeValuationLaw p).real {k : ℕ | k < M} := by
  have hc : (primeValuationLaw p).real (Set.Iio M) =
      1 - (primeValuationLaw p).real (Set.Ici M) := by
    simpa using (measureReal_compl (μ := primeValuationLaw p)
      (measurableSet_Ici (a := M)))
  have ht : (primeValuationLaw p).real (Set.Ici M) = ((p : ℝ)⁻¹) ^ M := by
    exact (congrArg ENNReal.toReal (primeValuationLaw_Ici p M)).trans
      (ENNReal.toReal_ofReal (by positivity))
  rw [sum_averagedPrimePowerWeight, show {k : ℕ | k < M} = Set.Iio M from rfl, hc, ht]

/-- Products of normalized averaged weights are finite valuation-cylinder probabilities. -/
theorem primeValuationMeasure_cylinder_eq_averagedWeights
    (S : Finset Nat.Primes) (m : Nat.Primes → ℕ) :
    primeValuationMeasure (Set.pi (↑S) (fun p => {m p})) =
      ENNReal.ofReal (∏ p ∈ S, averagedPrimePowerWeight p (m p) / Real.log (p : ℝ)) := by
  rw [primeValuationMeasure, Measure.infinitePi_pi primeValuationLaw
    (fun p _ => measurableSet_singleton (m p)), ENNReal.ofReal_prod_of_nonneg]
  · exact Finset.prod_congr rfl fun p _ => primeValuationLaw_singleton_eq_averagedWeight p (m p)
  · intro p _
    exact div_nonneg (averagedPrimePowerWeight_nonneg p (m p))
      (Real.log_nonneg (one_lt_prime_cast p).le)

/-- The valuation probability generating function is the normalized prime Euler factor. -/
theorem integral_primeValuation_pow (p : Nat.Primes) (z : unitInterval) :
    (∫ k : ℕ, (z : ℝ) ^ k ∂primeValuationLaw p) =
      (1 - (p : ℝ)⁻¹) * (1 - (z : ℝ) / (p : ℝ))⁻¹ := by
  have hp : (0 : ℝ) < (p : ℝ) := (zero_lt_one.trans (one_lt_prime_cast p))
  have hz : (z : ℝ) / (p : ℝ) < 1 :=
    (div_lt_one hp).mpr (z.property.2.trans_lt (one_lt_prime_cast p))
  have hg := (hasSum_geometric_of_lt_one (div_nonneg z.property.1 hp.le) hz).mul_left
    (1 - (p : ℝ)⁻¹)
  rw [primeValuationLaw, integral_geometricMeasure (primeValuationParam_ne_zero p)]
  calc
    _ = ∑' k : ℕ, (1 - (p : ℝ)⁻¹) * ((z : ℝ) / (p : ℝ)) ^ k := by
      apply tsum_congr
      intro k
      simp only [primeValuationParam_coe, sub_sub_cancel, smul_eq_mul,
        div_eq_mul_inv, inv_pow]
      ring
    _ = _ := hg.tsum_eq

/-- Valuation averaging and phase averaging give the same local factor after normalization. -/
theorem integral_primeValuation_phasePowers (p : Nat.Primes) (s : ℝ) :
    (∫ k : ℕ, cavityDiskCoordinate s ^ (2 * k) ∂primeValuationLaw p) =
      (1 - (p : ℝ)⁻¹) *
        (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseLocalFactor s t) := by
  have hr : cavityDiskCoordinate s ^ 2 ≤ 1 := by
    have h := pow_lt_one₀ (abs_nonneg (cavityDiskCoordinate s))
      (abs_cavityDiskCoordinate_lt_one s) (by decide : (2 : ℕ) ≠ 0)
    simpa only [sq_abs] using h.le
  have h := integral_primeValuation_pow p ⟨cavityDiskCoordinate s ^ 2, sq_nonneg _, hr⟩
  simpa only [pow_mul, integral_kesten_local_factor] using h

end
end GaloisForLFunctions.SelbergClass.Primon
