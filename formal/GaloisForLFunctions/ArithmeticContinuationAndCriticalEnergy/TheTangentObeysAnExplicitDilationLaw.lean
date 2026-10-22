import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationCalculusOnIntegerPrefixes

/-!
# The tangent obeys an explicit dilation law

The source is pinned by the inversion law; the tangent is pinned too, and by the same calculus.
The tangent is the prime dilation of the source with an explicit correction, the damped unit
dilation composes with the prime dilation into the logarithmic one, and the logarithmic dilation of
the source is explicit.  Composing the three gives, for every horizon and every positive damping,

`Σ_{j ≤ n} j^{-ε} E_ε(⌊n/j⌋) = [Ψ_ε(n) − m₀(ε) Σ_{j ≤ n} Λ(j) j^{-ε} Φ_ε(⌊n/j⌋)]
    + Σ_{j ≤ n} j^{-ε} (m₀(ε) Ψ_ε(⌊n/j⌋) − m(ε) ⌊n/j⌋)`

(`prefixDilation_dampedUnit_dampedChebyshevError`), where every term on the right is built from the
von Mangoldt weights, integer parts and the two densities — the Möbius row has disappeared.

So both the centred source and its damping tangent satisfy exact linear laws against positive
dilation kernels.  That is the structural input the indefiniteness of the quotient incidence kernel
demands, now available on both sides of the signed work.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The damped unit and prime rows convolve to the damped logarithm, in the order the dilation
calculus needs. -/
theorem sum_divisors_rpow_mul_dampedPrime (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ j ∈ m.divisors, (j : ℝ) ^ (-ε) * dampedPrimeWeight ε (m / j)) =
      Real.log m * (m : ℝ) ^ (-ε) := by
  rw [← sum_divisors_dampedPrime_mul_rpow ε hm]
  rw [← Nat.sum_div_divisors m (fun d => (d : ℝ) ^ (-ε) * dampedPrimeWeight ε (m / d))]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (by omega : m ≠ 0)]
  ring

/-- **The explicit dilation law of the tangent.**  The damped unit dilation of the centred damped
Chebyshev function is a Möbius-free expression in the von Mangoldt weights, the integer parts and
the two densities. -/
theorem prefixDilation_dampedUnit_dampedChebyshevError (ε : ℝ) (n : ℕ) :
    prefixDilation (fun j => (j : ℝ) ^ (-ε)) (dampedChebyshevError ε) n =
      (dampedPrimeFloorSum ε n -
          (pmPowerDampedDivisorDensity ε).re *
            ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * dampedUnitFloorSum ε (n / j)) +
        ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) *
          ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε (n / j) -
            dampedReadout ε * ((n / j : ℕ) : ℝ)) := by
  -- split the tangent into its dilation part and its explicit correction
  have hsplit : prefixDilation (fun j => (j : ℝ) ^ (-ε)) (dampedChebyshevError ε) n =
      prefixDilation (fun j => (j : ℝ) ^ (-ε))
          (prefixDilation (dampedPrimeWeight ε) (pmPowerDampedCenteredDivisorPrefix ε)) n +
        ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) *
          ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε (n / j) -
            dampedReadout ε * ((n / j : ℕ) : ℝ)) := by
    rw [prefixDilation, prefixDilation, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dampedChebyshevError_eq_dilation ε (n / j), prefixDilation]
    ring
  rw [hsplit]
  congr 1
  -- the two dilations compose into the logarithmic one, which is explicit
  have hcomp := prefixDilation_comp (fun j => (j : ℝ) ^ (-ε)) (dampedPrimeWeight ε)
    (pmPowerDampedCenteredDivisorPrefix ε) n
  rw [hcomp]
  have hkernel : prefixDilation (fun m => ∑ j ∈ m.divisors,
      (j : ℝ) ^ (-ε) * dampedPrimeWeight ε (m / j))
      (pmPowerDampedCenteredDivisorPrefix ε) n =
      prefixDilation (fun j => Real.log j * (j : ℝ) ^ (-ε))
        (pmPowerDampedCenteredDivisorPrefix ε) n := by
    rw [prefixDilation, prefixDilation]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [sum_divisors_rpow_mul_dampedPrime ε (mem_Icc.mp hm).1]
  rw [hkernel, prefixDilation_dampedLog_centeredPrefix]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
