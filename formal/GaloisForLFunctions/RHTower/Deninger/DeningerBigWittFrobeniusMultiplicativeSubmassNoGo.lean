import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusRingEndomorphism
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusCalkinEnergyBridge

/-!
# Multiplicative big-Witt repair cannot produce Route L submass

The canonical Frobenius RingHom permits source multiplication before
transgression. This module computes that entire multiplicative hierarchy.
For every power `m`, its normalized first-ghost ground converges to

`(-4 * orbitwisePrimeSeamWeightedNormSq rho)^m`.

Consequently no finite multiplicative power can supply the missing Route L
submass at an off-critical strip point. The exact nonzero residue is retained
as the positive survivor of the no-go.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- `m`-fold Witt multiplication of the finite polarized source, followed by
the canonical Frobenius-two RingHom. -/
def deningerBigWittFrobeniusMultiplicativePowerSource
    (rho : ℂ) (s : Finset Nat.Primes) (m : ℕ) :
    DeningerBigWittRing ℂ :=
  deningerBigWittFrobeniusTwoRingHom
    ((deningerBigWittPolarizedPrimeSeamAggregateSource
      (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s) ^ m)

/-- Multiplication creates the `m`th power of the exact finite Calkin-energy
coefficient; it creates no cross-pair cancellation. -/
theorem deningerBigWittFrobeniusMultiplicativePowerSource_ghost_one
    (rho : ℂ) (s : Finset Nat.Primes) (m : ℕ) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusMultiplicativePowerSource rho s m) =
      (((-2 * deningerBigWittPrimeSeamFiniteCalkinEnergy rho s : ℝ) : ℂ) ^ m) := by
  rw [deningerBigWittFrobeniusMultiplicativePowerSource, map_pow, map_pow]
  simp only [deningerBigWittFrobeniusTwoRingHom_apply]
  rw [
    deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_eq_calkin]

/-- Real physical first-ghost ground of the multiplicative power source. -/
def deningerBigWittFrobeniusMultiplicativeGround
    (rho : ℂ) (s : Finset Nat.Primes) (m : ℕ) : ℝ :=
  Complex.re (deningerBigWittGhostComponent 1 Nat.zero_lt_one
    (deningerBigWittFrobeniusMultiplicativePowerSource rho s m))

/-- Exact finite multiplicative ground formula. -/
theorem deningerBigWittFrobeniusMultiplicativeGround_eq
    (rho : ℂ) (s : Finset Nat.Primes) (m : ℕ) :
    deningerBigWittFrobeniusMultiplicativeGround rho s m =
      (-2 * deningerBigWittPrimeSeamFiniteCalkinEnergy rho s) ^ m := by
  rw [deningerBigWittFrobeniusMultiplicativeGround,
    deningerBigWittFrobeniusMultiplicativePowerSource_ghost_one]
  norm_cast

/-- Every multiplicative level has a rigid cofinal residue: the `m`th power
of the original one-particle obstruction. -/
theorem tendsto_deningerBigWittFrobeniusMultiplicativeGround_div_mass_pow
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (m : ℕ) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        deningerBigWittFrobeniusMultiplicativeGround rho s m /
          primeReciprocalMass s ^ m)
      atTop
      (nhds ((-4 * orbitwisePrimeSeamWeightedNormSq rho) ^ m)) := by
  have henergy :=
    tendsto_deningerBigWittPrimeSeamFiniteCalkinEnergy_div_mass hstrip
  have hscaled : Tendsto
      (fun s : Finset Nat.Primes =>
        -2 * (deningerBigWittPrimeSeamFiniteCalkinEnergy rho s /
          primeReciprocalMass s))
      atTop
      (nhds (-4 * orbitwisePrimeSeamWeightedNormSq rho)) := by
    convert tendsto_const_nhds.mul henergy using 1
    ring
  have hp := hscaled.pow m
  convert hp using 1
  funext s
  rw [deningerBigWittFrobeniusMultiplicativeGround_eq, ← div_pow]
  congr 1
  ring

/-- Sharp no-go: no finite multiplicative level is submass at an off-critical
open-strip point. -/
theorem deningerBigWittFrobeniusMultiplicativeGround_not_submass_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) (m : ℕ) :
    ¬ Tendsto
      (fun s : Finset Nat.Primes =>
        deningerBigWittFrobeniusMultiplicativeGround rho s m /
          primeReciprocalMass s ^ m)
      atTop (nhds 0) := by
  intro hzero
  have hpos := orbitwisePrimeSeamWeightedNormSq_pos_of_re_ne_half hstrip hoff
  have hlim := tendsto_deningerBigWittFrobeniusMultiplicativeGround_div_mass_pow hstrip m
  have heq : (0 : ℝ) = (-4 * orbitwisePrimeSeamWeightedNormSq rho) ^ m :=
    tendsto_nhds_unique hzero hlim
  have hne : (-4 * orbitwisePrimeSeamWeightedNormSq rho) ^ m ≠ 0 :=
    pow_ne_zero m (mul_ne_zero (by norm_num) hpos.ne')
  exact hne heq.symm

end

end RHTower
