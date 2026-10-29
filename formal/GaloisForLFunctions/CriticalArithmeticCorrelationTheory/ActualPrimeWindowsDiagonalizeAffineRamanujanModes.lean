import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueWindowsConvergeToTheirUnitMean
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnitAveragesDiagonalizeSuccessorCorrections

/-!
# Actual prime windows diagonalize affine Ramanujan modes

The residue-class Mertens limits realize the finite unit-average law on the
literal von Mangoldt source. Both affine parameters and every prime power
are retained. Conductor and window endpoints are fixed in these limits.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

private theorem lagCoefficient_eq_of_modEq {q a b : ℕ} (hab : Nat.ModEq q a b) :
    ramanujanLagCoefficient q a = ramanujanLagCoefficient q b := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  rw [hab.dvd_iff (Nat.dvd_of_mem_divisors hd)]

/-- The affine Ramanujan pattern as a function of the multiplier residue. -/
def affineRamanujanResidue (q n h : ℕ) (r : ZMod q) : ℝ :=
  ramanujanLagCoefficient q (r.val * n + h)

private theorem affineRamanujanResidue_natCast {q : ℕ} [NeZero q] (n h k : ℕ) :
    affineRamanujanResidue q n h (k : ZMod q) = ramanujanLagCoefficient q (k * n + h) := by
  rw [affineRamanujanResidue, ZMod.val_natCast]
  have hk : Nat.ModEq q (k % q) k := by
    change (k % q) % q = k % q
    exact Nat.mod_mod k q
  exact lagCoefficient_eq_of_modEq ((hk.mul_right n).add_right h)

private theorem sum_zmod_real_eq_range {q : ℕ} [NeZero q] (F : ZMod q → ℝ) :
    (∑ r : ZMod q, F r) = ∑ k ∈ range q, F (k : ZMod q) := by
  refine sum_nbij' (fun r : ZMod q => r.val) (fun k : ℕ => (k : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro r _
    exact mem_range.mpr (ZMod.val_lt r)
  · intro k _
    exact mem_univ _
  · intro r _
    exact ZMod.natCast_zmod_val r
  · intro k hk
    exact ZMod.val_natCast_of_lt (mem_range.mp hk)
  · intro r _
    rw [ZMod.natCast_zmod_val]

/-- The mean of the actual affine residue pattern is its exact successor
eigenvalue times the original Ramanujan coefficient. -/
theorem primeClassKappa_affineRamanujanResidue {q : ℕ} [NeZero q] (n h : ℕ) :
    primeClassKappa q (affineRamanujanResidue q n h) =
      ramanujanLagCoefficient q n * ramanujanLagCoefficient q h / (q.totient : ℝ) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsplit : (∑ r : ZMod q, if IsUnit r then affineRamanujanResidue q n h r else 0) =
      ∑ u : (ZMod q)ˣ, affineRamanujanResidue q n h u := by
    rw [sum_zmod_eq_units_add]
    have hnon : (∑ r ∈ univ.filter (fun r : ZMod q => ¬ IsUnit r),
        if IsUnit r then affineRamanujanResidue q n h r else 0) = 0 := by
      exact sum_eq_zero fun r hr => if_neg (mem_filter.mp hr).2
    rw [hnon, add_zero]
    exact sum_congr rfl fun u _ => if_pos u.isUnit
  unfold primeClassKappa
  rw [← hsplit, sum_zmod_real_eq_range]
  simp_rw [ZMod.isUnit_iff_coprime, affineRamanujanResidue_natCast]
  rw [← sum_filter, sum_coprime_ramanujanLagCoefficient_affine hq]

/-- The literal affine reading on a growing multiplicative prime window. -/
def affineRamanujanPrimeWindow (q n h A B N : ℕ) : ℝ :=
  ∑ k ∈ Ioc (A * N) (B * N),
    (ArithmeticFunction.vonMangoldt k : ℝ) / k * ramanujanLagCoefficient q (k * n + h)

private theorem affineRamanujanPrimeWindow_eq_residue {q : ℕ} [NeZero q]
    (n h A B N : ℕ) :
    affineRamanujanPrimeWindow q n h A B N =
      residuePrimeWindow q (affineRamanujanResidue q n h) A B N := by
  unfold affineRamanujanPrimeWindow residuePrimeWindow
  refine sum_congr rfl fun k _ => ?_
  rw [affineRamanujanResidue_natCast]
  ring

/-- Actual affine prime averages converge to the unit-average eigenvalue.
This is a source theorem, with no prime-correlation model as a premise. -/
theorem tendsto_affineRamanujanPrimeWindow {q : ℕ} (hq : 0 < q) (n h : ℕ)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Tendsto (affineRamanujanPrimeWindow q n h A B) atTop
      (𝓝 ((Real.log B - Real.log A) * ramanujanLagCoefficient q n *
        ramanujanLagCoefficient q h / (q.totient : ℝ))) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hlim := tendsto_residuePrimeWindow (affineRamanujanResidue q n h) hA hAB
  rw [primeClassKappa_affineRamanujanResidue] at hlim
  convert hlim using 1
  · funext N
    exact affineRamanujanPrimeWindow_eq_residue n h A B N
  · congr 1
    ring

/-- The normalized actual arithmetic modes have the same successor
eigenvalue on multiplicative prime windows. -/
theorem tendsto_normalizedRamanujanMode_prime_window {q : ℕ} (hq : 0 < q) (n h : ℕ)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Tendsto (fun N : ℕ => ∑ k ∈ Ioc (A * N) (B * N),
      (ArithmeticFunction.vonMangoldt k : ℝ) / k * normalizedRamanujanMode q (k * n + h))
      atTop (𝓝 ((Real.log B - Real.log A) *
        (ramanujanLagCoefficient q h / (q.totient : ℝ)) * normalizedRamanujanMode q n)) := by
  have hlim := (tendsto_affineRamanujanPrimeWindow hq n h hA hAB).div_const
    (Real.sqrt (q.totient : ℝ))
  convert hlim using 1
  · funext N
    simp only [affineRamanujanPrimeWindow, normalizedRamanujanMode_eq_coefficient hq, sum_div]
    exact sum_congr rfl fun k _ => by ring
  · rw [normalizedRamanujanMode_eq_coefficient hq]
    congr 1
    ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primeClassKappa_affineRamanujanResidue
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_affineRamanujanPrimeWindow
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_normalizedRamanujanMode_prime_window
