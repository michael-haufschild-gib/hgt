import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Square-one bounds in cyclotomic images

The p-primary Birch--Tate denominator is finite once the square of the cyclotomic character is
nontrivial. Degree growth supplies that nontriviality after bounding square-one units modulo prime
powers. This module proves the sharp uniform bounds: two for odd primes and four for `2`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- At most two units modulo an odd prime power square to one. -/
theorem card_squareOneUnits_oddPrimePow_le_two
    (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (powMonoidHom 2 : (ZMod (p ^ n))ˣ →* (ZMod (p ^ n))ˣ).ker ≤ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  rw [IsCyclic.card_powMonoidHom_ker]
  exact Nat.gcd_le_right _ (by decide : 0 < 2)

/-- At most four units modulo a power of two square to one. -/
theorem card_squareOneUnits_twoPow_le_four (n : ℕ) :
    Nat.card (powMonoidHom 2 : (ZMod (2 ^ (n + 3)))ˣ →* (ZMod (2 ^ (n + 3)))ˣ).ker ≤ 4 := by
  let G := (ZMod (2 ^ (n + 3)))ˣ
  let sq : G →* G := powMonoidHom 2
  let five : G := ZMod.unitOfCoprime 5 ((by norm_num : Nat.Coprime 5 2).pow_right _)
  have hfive : orderOf five = 2 ^ (n + 1) := by
    rw [← orderOf_units]
    exact ZMod.orderOf_five (n + 1)
  have htwo : 2 ∣ orderOf five := by
    rw [hfive]
    exact dvd_pow_self 2 (by omega)
  have hfiveSq : orderOf (five ^ 2) = 2 ^ n := by
    rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) htwo, hfive]
    simp [pow_succ]
  let y : sq.range := ⟨five ^ 2, ⟨five, rfl⟩⟩
  have hy : orderOf y = 2 ^ n := by
    rw [← Subgroup.orderOf_coe]
    exact hfiveSq
  have hrange : 2 ^ n ≤ Nat.card sq.range := by
    rw [← hy]
    exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard y)
  have hcard : Nat.card G = 2 ^ (n + 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hprod : Nat.card sq.ker * Nat.card sq.range = 2 ^ (n + 2) := by
    rw [← hcard, ← Subgroup.index_ker]
    exact sq.ker.card_mul_index
  apply Nat.le_of_mul_le_mul_right (c := 2 ^ n) _ (pow_pos (by decide) n)
  calc
    Nat.card sq.ker * 2 ^ n ≤ Nat.card sq.ker * Nat.card sq.range :=
      Nat.mul_le_mul_left _ hrange
    _ = 2 ^ (n + 2) := hprod
    _ = 4 * 2 ^ n := by ring

end GaloisForLFunctions.HTGeometry
