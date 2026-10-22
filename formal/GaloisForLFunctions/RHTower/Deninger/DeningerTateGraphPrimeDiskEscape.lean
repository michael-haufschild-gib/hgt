import GaloisForLFunctions.RHTower.Deninger.DeningerTateGraphGreenPrimeSector
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Unit-Green packets escape every fixed Tate graph disk

Normalizing a positive Tate mode to have unsmoothed Green energy one forces scalar mass
`lam⁻¹`.  Its Tate graph cost is at least the square of the prime period.  Since prime logarithms
escape to infinity, every family of unit-Green packets has graph cost tending to infinity along
the cofinite prime filter, independently of its positive frequency choices.

This is the quantitative bridge between local prime energy and the global Banach-disk obstruction:
the graph completion is not ruled out, but no fixed graph disk contains unit-Green packets at
arbitrarily large primes.
-/

namespace RHTower

open Filter Topology

/-- Scalar mass which normalizes a positive Tate mode to unit unsmoothed Green energy. -/
noncomputable def deningerTateUnitGreenModeMass (lam : ℝ) : ℝ :=
  lam⁻¹

/-- The unit-Green mass has unsmoothed energy exactly one. -/
theorem deningerTateUnitGreenMode_energy_eq_one {lam : ℝ} (hlam : 0 < lam) :
    lam * deningerTateUnitGreenModeMass lam = 1 := by
  exact mul_inv_cancel₀ hlam.ne'

/-- A unit-Green mode costs at least the square of its period in the Tate graph scale. -/
theorem deningerTateUnitGreenMode_graphCost_ge_period_sq
    {L lam : ℝ} (hlam : 0 < lam) :
    L ^ (2 : ℕ) ≤ deningerTateGraphWeight L lam * deningerTateUnitGreenModeMass lam := by
  rw [deningerTateUnitGreenModeMass, deningerTateGraphWeight]
  have hL : 0 ≤ L ^ (2 : ℕ) := sq_nonneg L
  have hinv : 0 < lam⁻¹ := inv_pos.mpr hlam
  calc
    L ^ (2 : ℕ) = L ^ (2 : ℕ) * lam * lam⁻¹ := by field_simp
    _ ≤ L ^ (2 : ℕ) * (1 + lam) * lam⁻¹ := by
      gcongr
      linarith

/-- Along the primes, graph costs of arbitrary positive-frequency unit-Green packets diverge. -/
theorem deningerTateUnitGreenPrime_graphCost_tendsto_atTop
    (lam : Nat.Primes → ℝ) (hlam : ∀ p, 0 < lam p) :
    Tendsto (fun p : Nat.Primes =>
      deningerTateGraphWeight (Real.log (p : ℝ)) (lam p) *
        deningerTateUnitGreenModeMass (lam p)) cofinite atTop := by
  have hlog : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ)) cofinite atTop :=
    Real.tendsto_log_atTop.comp tendsto_prime_coe_real_cofinite_atTop
  have hsq : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ) ^ (2 : ℕ)) cofinite atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  exact tendsto_atTop_mono' cofinite
    (Eventually.of_forall fun p =>
      deningerTateUnitGreenMode_graphCost_ge_period_sq (hlam p)) hsq

end RHTower
