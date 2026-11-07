import GaloisForLFunctions.SelbergClass.Primon.ArithmeticAverage
import GaloisForLFunctions.SelbergClass.Primon.ThermalLocalFactor
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic

/-!
# The zeta product of arithmetic thermal averages

The arithmetic mean of each charged-primon factor is an Euler factor of
`ζ(2β+1)`. Thus the product of local means converges at every positive inverse
temperature. This is a different averaging operation from the prime sum of
mean logarithms, whose half-logarithmic singularity occurs at `β = 1/2`.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The thermal logarithm is the logarithm of the same charged local factor. -/
theorem thermalLocalLog_eq_log_localFactor (p : Nat.Primes) (β t : ℝ) :
    thermalLocalLog p β t =
      Real.log (phaseLocalFactor (thermalDiskParameter p β) t) := by
  simp only [thermalLocalLog, phaseLocalFactor, cavityDiskCoordinate_thermal, Real.log_inv]

/-- The thermal arithmetic phase mean is a zeta Euler factor at the shifted temperature. -/
theorem integral_kesten_thermalFactor (p : Nat.Primes) (β : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t) =
      (1 - (p : ℝ) ^ (-(2 * Real.exp β + 1)))⁻¹ := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [integral_kesten_local_factor, cavityDiskCoordinate_thermal,
    thermalRatio_square_div_prime, Real.rpow_def_of_pos hp,
    mul_comm (Real.log (p : ℝ)) (-(2 * Real.exp β + 1))]

/-- The product of local arithmetic means is `ζ(2 exp β + 1)` for every real `β`. -/
theorem hasProd_thermalArithmeticMeans (β : ℝ) :
    HasProd (fun p : Nat.Primes => ∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t)
      (riemannZeta ((2 * Real.exp β + 1 : ℝ) : ℂ)).re := by
  have hs : 1 < 2 * Real.exp β + 1 := by have := Real.exp_pos β; linarith
  simpa only [integral_kesten_thermalFactor] using RHTower.hasProd_primeEulerFactor hs

/-- Logarithms of the local arithmetic means sum to the logarithm of shifted zeta. -/
theorem hasSum_log_thermalArithmeticMeans (β : ℝ) :
    HasSum (fun p : Nat.Primes => Real.log (∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t))
      (Real.log (riemannZeta ((2 * Real.exp β + 1 : ℝ) : ℂ)).re) := by
  have hs : 1 < 2 * Real.exp β + 1 := by have := Real.exp_pos β; linarith
  simpa only [integral_kesten_thermalFactor, Real.log_inv] using
    RHTower.hasSum_negLog_primeEulerFactor hs

/-- Every positive-temperature arithmetic phase mean is strictly greater than one. -/
theorem one_lt_integral_kesten_thermalFactor (p : Nat.Primes) (β : ℝ) :
    1 < ∫ t in Ioo (0 : ℝ) 1,
      kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t := by
  rw [integral_kesten_thermalFactor]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hx : 0 < (p : ℝ) ^ (-(2 * Real.exp β + 1)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hx1 : (p : ℝ) ^ (-(2 * Real.exp β + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by have := Real.exp_pos β; linarith)
  rw [← one_div, lt_div_iff₀ (sub_pos.mpr hx1)]
  linarith

/-- The gap between logarithm of the mean and mean logarithm is explicit. -/
theorem thermal_log_average_gap_eq (p : Nat.Primes) (β : ℝ) :
    Real.log (∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t) -
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * thermalLocalLog p β t) =
      -((p : ℝ) + 1) / 2 * Real.log (1 - (p : ℝ) ^ (-(2 * Real.exp β + 1))) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [integral_kesten_thermalFactor, integral_kesten_thermalLocalLog, Real.log_inv]
  simp only [Real.rpow_def_of_pos hp,
    mul_comm (Real.log (p : ℝ)) (-(2 * Real.exp β + 1))]
  ring

/-- The exact phase formulas give a strict logarithmic averaging gap at every prime. -/
theorem thermal_log_average_gap_pos (p : Nat.Primes) (β : ℝ) :
    0 < Real.log (∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * phaseLocalFactor (thermalDiskParameter p β) t) -
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * thermalLocalLog p β t) := by
  have ha := Real.log_pos (one_lt_integral_kesten_thermalFactor p β)
  have hg := integral_kesten_thermalLocalLog_neg p β
  linarith

end
end GaloisForLFunctions.SelbergClass.Primon
