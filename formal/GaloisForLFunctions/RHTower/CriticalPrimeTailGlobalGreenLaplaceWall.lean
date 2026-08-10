import GaloisForLFunctions.RHTower.CriticalPrimeTailGlobalGreenLaplaceSymbol
import GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationNoGo

/-!
# Sharp Laplace wall of the global critical prime-tail Green potential

The positive source behind the global Green potential has exact absolute-convergence abscissa
`1 / 2` in the shifted Laplace variable.  Sufficiency was used in the global Fubini theorem.
Necessity is forced already by ordinary primes: at the boundary their damped masses are exactly
`1 / p`.

This is the sharp obstruction to extending the raw positive-source/passive realization toward the
critical line.  Any continuation across this wall must use cancellation or a non-positive
renormalization; stronger majorants cannot move the wall.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

namespace RHTower

noncomputable section

/-- Ordinary primes embedded as the first Euler layer of the Deninger prime-power comb. -/
def criticalPrimeTailPrimeIndex (p : Nat.Primes) : DeningerPrimePowerIndex :=
  deningerEulerPrimePowerIndex (p, 0)

theorem criticalPrimeTailPrimeIndex_injective :
    Function.Injective criticalPrimeTailPrimeIndex := by
  intro p q hpq
  have hpq' : (p, 0) = (q, 0) :=
    deningerEulerPrimePowerIndex_injective hpq
  exact congrArg Prod.fst hpq'

/-- Real positive Laplace mass of one critical source atom. -/
def criticalPrimeTailLaplaceMass (r : ℝ) (n : DeningerPrimePowerIndex) : ℝ :=
  criticalPrimeTailAtomWeight n *
    Real.exp (-(r * deningerPrimePowerTime n))

/-- On the first Euler layer, critical Laplace mass is the exact prime power
`p^(-(r+1/2))`. -/
theorem criticalPrimeTailLaplaceMass_prime (r : ℝ) (p : Nat.Primes) :
    criticalPrimeTailLaplaceMass r (criticalPrimeTailPrimeIndex p) =
      (p : ℝ) ^ (-(r + 1 / 2)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  have hweight :
      criticalPrimeTailAtomWeight (criticalPrimeTailPrimeIndex p) =
        (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [criticalPrimeTailAtomWeight, criticalMellinAtomWeight]
    simp only [criticalPrimeTailPrimeIndex, deningerEulerPrimePowerIndex,
      Nat.zero_add, Nat.pow_one, deningerPrimePowerTime,
      ArithmeticFunction.vonMangoldt_apply_prime p.property]
    field_simp
  rw [criticalPrimeTailLaplaceMass, hweight]
  have htime : deningerPrimePowerTime (criticalPrimeTailPrimeIndex p) =
      Real.log (p : ℝ) := by
    simpa [criticalPrimeTailPrimeIndex] using
      deningerPrimePowerTime_euler (p, 0)
  rw [htime, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0,
    ← Real.exp_add]
  congr 1
  ring

/-- At and left of the half-density wall, the positive Laplace source is not summable. -/
theorem not_summable_criticalPrimeTailLaplaceMass_of_le_half
    {r : ℝ} (hr : r ≤ 1 / 2) :
    ¬ Summable (criticalPrimeTailLaplaceMass r) := by
  intro hsum
  have hprime := hsum.comp_injective criticalPrimeTailPrimeIndex_injective
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(r + 1 / 2))) :=
    hprime.congr fun p => criticalPrimeTailLaplaceMass_prime r p
  exact not_summable_primeRpow_of_negOne_le (by linarith) hpow

/-- **C43 sharp wall.**  The full positive critical source has absolute Laplace abscissa exactly
`1/2`; this is an iff, not only a one-sided convergence estimate. -/
theorem summable_criticalPrimeTailLaplaceMass_iff (r : ℝ) :
    Summable (criticalPrimeTailLaplaceMass r) ↔ 1 / 2 < r := by
  constructor
  · intro hsum
    exact lt_of_not_ge fun hr =>
      not_summable_criticalPrimeTailLaplaceMass_of_le_half hr hsum
  · intro hr
    exact summable_criticalPrimeTailAtomWeight_mul_exp_neg hr

/-- Complex Laplace atoms have the same exact absolute-convergence wall. -/
theorem summable_norm_criticalPrimeTailComplexLaplaceAtom_iff (z : ℂ) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ‖(criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))‖) ↔
      1 / 2 < z.re := by
  have hpoint : (fun n : DeningerPrimePowerIndex =>
      ‖(criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-(z * (deningerPrimePowerTime n : ℂ)))‖) =
      criticalPrimeTailLaplaceMass z.re := by
    funext n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (criticalPrimeTailAtomWeight_nonneg n), Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  rw [hpoint, summable_criticalPrimeTailLaplaceMass_iff]

/-- At positive real Laplace rate, atomwise Green absolute Fubini is possible exactly to the right
of the same half-density wall. -/
theorem summable_integral_norm_exp_mul_zeroGreenAtom_iff
    {r : ℝ} (hr : 0 < r) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ∫ L : ℝ, ‖Complex.exp (-((r : ℂ) * (L : ℂ))) *
        criticalPrimeTailZeroGreenAtom n L‖) ↔
      1 / 2 < r := by
  have hterm : (fun n : DeningerPrimePowerIndex =>
      ∫ L : ℝ, ‖Complex.exp (-((r : ℂ) * (L : ℂ))) *
        criticalPrimeTailZeroGreenAtom n L‖) =
      fun n => criticalPrimeTailLaplaceMass r n / r ^ 2 := by
    funext n
    simpa [criticalPrimeTailLaplaceMass] using
      integral_norm_exp_mul_criticalPrimeTailZeroGreenAtom
        (z := (r : ℂ)) (by simpa using hr) n
  rw [hterm]
  constructor
  · intro hsum
    have hscaled := hsum.mul_right (r ^ 2)
    have hmass : Summable (criticalPrimeTailLaplaceMass r) := by
      refine hscaled.congr ?_
      intro n
      field_simp
    exact (summable_criticalPrimeTailLaplaceMass_iff r).mp hmass
  · intro hhalf
    have hmass := (summable_criticalPrimeTailLaplaceMass_iff r).mpr hhalf
    exact hmass.mul_right (r ^ 2)⁻¹ |>.congr fun n => by
      rw [div_eq_mul_inv]

/-- The critical boundary already contains the full divergent prime harmonic trace. -/
theorem criticalPrimeTailLaplaceMass_prime_half (p : Nat.Primes) :
    criticalPrimeTailLaplaceMass (1 / 2)
        (criticalPrimeTailPrimeIndex p) = (p : ℝ)⁻¹ := by
  rw [criticalPrimeTailLaplaceMass_prime]
  norm_num [Real.rpow_neg_one]

end

end RHTower
