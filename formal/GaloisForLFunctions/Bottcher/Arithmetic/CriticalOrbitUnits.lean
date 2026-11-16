import GaloisForLFunctions.Bottcher.Arithmetic.CriticalParameterIntegrality
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Divisibility and units in unicritical critical orbits

Critical iterates at multiple indices are divisible by the earlier iterate.
On a periodic tail, the secants between two distinct shifted orbits multiply
to one. Their common critical divisor must consequently be a unit.
-/

noncomputable section
open Finset
namespace Bottcher.Arithmetic
variable {R : Type*} [CommRing R]

/-- Unicritical iteration over a ring, with an arbitrary initial point. -/
def unicriticalRingIterate (d : ℕ) (c : R) : ℕ → R → R
  | 0, x => x
  | n + 1, x => unicriticalRingIterate d c n x ^ (d + 2) + c

/-- Critical orbit in the parameter ring, before passage to its fraction field. -/
def ringCriticalOrbit (d : ℕ) (c : R) (n : ℕ) : R := unicriticalRingIterate d c n 0

private theorem ringIterate_add (d : ℕ) (c x : R) (n k : ℕ) :
    unicriticalRingIterate d c (n + k) x =
      unicriticalRingIterate d c n (unicriticalRingIterate d c k x) := by
  induction n with
  | zero => simp only [Nat.zero_add, unicriticalRingIterate]
  | succ n ih => simp only [Nat.succ_add, unicriticalRingIterate, ih]

/-- Ring iteration agrees with the existing field-valued critical orbit. -/
theorem ringCriticalOrbit_eq_criticalOrbit {K : Type*} [Field K] (d : ℕ) (c : K) (n : ℕ) :
    ringCriticalOrbit d c n = criticalOrbit d c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ringCriticalOrbit d c n ^ (d + 2) + c = _
    rw [ih, criticalOrbit_succ]

/-- Polynomial iteration preserves divisibility of differences. -/
theorem sub_dvd_unicriticalRingIterate_sub (d n : ℕ) (c x y : R) :
    x - y ∣ unicriticalRingIterate d c n x - unicriticalRingIterate d c n y := by
  induction n with
  | zero => exact dvd_refl _
  | succ n ih =>
    simp only [unicriticalRingIterate, add_sub_add_right_eq_sub]
    exact ih.trans (sub_dvd_pow_sub_pow _ _ _)

/-- Every critical iterate divides all critical iterates at multiple indices. -/
theorem ringCriticalOrbit_dvd_multiple (d r k : ℕ) (c : R) :
    ringCriticalOrbit d c r ∣ ringCriticalOrbit d c (r * k) := by
  induction k with
  | zero => simp only [mul_zero, ringCriticalOrbit, unicriticalRingIterate, dvd_zero]
  | succ k ih =>
    have hh := sub_dvd_unicriticalRingIterate_sub d r c (ringCriticalOrbit d c (r * k)) 0
    rw [sub_zero] at hh
    have he : ringCriticalOrbit d c (r * (k + 1)) =
        unicriticalRingIterate d c r (ringCriticalOrbit d c (r * k)) := by
      rw [mul_add, mul_one, add_comm, ringCriticalOrbit, ringIterate_add]
      rfl
    rw [he]
    have h := (ih.trans hh).add (dvd_refl (ringCriticalOrbit d c r))
    simpa only [ringCriticalOrbit, sub_add_cancel] using h

/-- The divided difference of the unicritical polynomial. -/
def unicriticalSecant (d : ℕ) (x y : R) : R :=
  ∑ i ∈ range (d + 2), x ^ i * y ^ (d + 2 - 1 - i)

private theorem unicriticalSecant_mul (d : ℕ) (x y : R) :
    unicriticalSecant d x y * (x - y) = x ^ (d + 2) - y ^ (d + 2) :=
  geom_sum₂_mul x y (d + 2)

private theorem dvd_unicriticalSecant (d : ℕ) (a x y : R) (hx : a ∣ x) (hy : a ∣ y) :
    a ∣ unicriticalSecant d x y := by
  apply Finset.dvd_sum
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp only [pow_zero, one_mul, Nat.sub_zero]
    exact hy.trans (dvd_pow_self y (by omega : d + 2 - 1 ≠ 0))
  · exact dvd_mul_of_dvd_left (hx.trans (dvd_pow_self x hi0)) _

private theorem secant_product_transport (d n : ℕ) (c x y : R) :
    (∏ j ∈ range n, unicriticalSecant d (unicriticalRingIterate d c j x)
      (unicriticalRingIterate d c j y)) * (x - y) =
      unicriticalRingIterate d c n x - unicriticalRingIterate d c n y := by
  induction n with
  | zero => simp only [prod_range_zero, one_mul, unicriticalRingIterate]
  | succ n ih =>
    rw [prod_range_succ]
    rw [mul_right_comm, ih, mul_comm, unicriticalSecant_mul]
    simp only [unicriticalRingIterate, add_sub_add_right_eq_sub]

private theorem common_divisor_periodic_points_unit [IsDomain R]
    (d n : ℕ) (c a x y : R) (hx : a ∣ x) (hy : a ∣ y) (hxy : x ≠ y)
    (hxp : unicriticalRingIterate d c (n + 1) x = x)
    (hyp : unicriticalRingIterate d c (n + 1) y = y) : IsUnit a := by
  have hp := secant_product_transport d (n + 1) c x y
  rw [hxp, hyp] at hp
  have hprod : (∏ j ∈ range (n + 1), unicriticalSecant d
      (unicriticalRingIterate d c j x) (unicriticalRingIterate d c j y)) = 1 := by
    exact mul_right_cancel₀ (sub_ne_zero.mpr hxy) (hp.trans (one_mul _).symm)
  apply isUnit_iff_dvd_one.mpr
  rw [← hprod]
  apply (dvd_unicriticalSecant d a x y hx hy).trans
  exact Finset.dvd_prod_of_mem _ (mem_range.mpr (by omega : 0 < n + 1))

private theorem unicriticalSecant_split (d : ℕ) (x y : R) :
    unicriticalSecant d x y =
      x * (∑ i ∈ range (d + 1), x ^ i * y ^ (d - i)) + y * y ^ d := by
  rw [unicriticalSecant, show d + 2 = (d + 1) + 1 by omega, sum_range_succ']
  simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero, mul_sum]
  rw [show y ^ (d + 1) = y * y ^ d by rw [pow_succ]; ring]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [show d + 1 - (i + 1) = d - i by omega, pow_succ]
  ring

/-- Distinct periodic points of a unicritical polynomial generate the unit ideal. -/
theorem unicritical_periodic_points_coprime [IsDomain R]
    (d n : ℕ) (c x y : R) :
    unicriticalRingIterate d c (n + 1) x ≠ x ∨
      unicriticalRingIterate d c (n + 1) y ≠ y ∨ x = y ∨ IsCoprime x y := by
  by_cases hx : unicriticalRingIterate d c (n + 1) x = x
  · right
    by_cases hy : unicriticalRingIterate d c (n + 1) y = y
    · right
      by_cases hxy : x = y
      · exact Or.inl hxy
      · right
        have hp := secant_product_transport d (n + 1) c x y
        rw [hx, hy] at hp
        have hprod : (∏ j ∈ range (n + 1), unicriticalSecant d
            (unicriticalRingIterate d c j x) (unicriticalRingIterate d c j y)) = 1 :=
          mul_right_cancel₀ (sub_ne_zero.mpr hxy) (hp.trans (one_mul _).symm)
        rw [prod_range_succ', unicriticalRingIterate, unicriticalSecant_split] at hprod
        simp only [show unicriticalRingIterate d c 0 y = y from rfl] at hprod
        let B := ∏ j ∈ range n, unicriticalSecant d
          (unicriticalRingIterate d c (j + 1) x) (unicriticalRingIterate d c (j + 1) y)
        refine ⟨B * (∑ i ∈ range (d + 1), x ^ i * y ^ (d - i)), B * y ^ d, ?_⟩
        change _ = 1
        dsimp only [B]
        linear_combination hprod
    · exact Or.inl hy
  · exact Or.inl hx

/-- A periodic critical tail either identifies the shifted points or forces their critical divisor
  to be a unit. No number-field or integrality assumption is required. -/
theorem criticalOrbit_collision_or_unit [IsDomain R] (d m n r : ℕ) (c : R) :
    let ℓ := (r + 1) * (m + 1)
    ringCriticalOrbit d c (ℓ + (n + 1)) ≠ ringCriticalOrbit d c ℓ ∨
      ringCriticalOrbit d c (ℓ + (r + 1)) = ringCriticalOrbit d c ℓ ∨
      IsUnit (ringCriticalOrbit d c (r + 1)) := by
  dsimp only
  let ℓ := (r + 1) * (m + 1)
  change ringCriticalOrbit d c (ℓ + (n + 1)) ≠ ringCriticalOrbit d c ℓ ∨
    ringCriticalOrbit d c (ℓ + (r + 1)) = ringCriticalOrbit d c ℓ ∨ _
  by_cases hp : ringCriticalOrbit d c (ℓ + (n + 1)) = ringCriticalOrbit d c ℓ
  · right
    by_cases hs : ringCriticalOrbit d c (ℓ + (r + 1)) = ringCriticalOrbit d c ℓ
    · exact Or.inl hs
    · right
      have hx : ringCriticalOrbit d c (r + 1) ∣ ringCriticalOrbit d c (ℓ + (r + 1)) := by
        rw [show ℓ + (r + 1) = (r + 1) * (m + 2) by dsimp only [ℓ]; ring]
        exact ringCriticalOrbit_dvd_multiple d (r + 1) (m + 2) c
      have hy := ringCriticalOrbit_dvd_multiple d (r + 1) (m + 1) c
      have hyp : unicriticalRingIterate d c (n + 1) (ringCriticalOrbit d c ℓ) =
          ringCriticalOrbit d c ℓ := by
        rw [ringCriticalOrbit, ← ringIterate_add, add_comm (n + 1)]
        exact hp
      have hxp : unicriticalRingIterate d c (n + 1)
          (ringCriticalOrbit d c (ℓ + (r + 1))) = ringCriticalOrbit d c (ℓ + (r + 1)) := by
        have he : ringCriticalOrbit d c (ℓ + (r + 1)) =
            unicriticalRingIterate d c (r + 1) (ringCriticalOrbit d c ℓ) := by
          simpa only [ringCriticalOrbit, Nat.add_comm] using ringIterate_add d c 0 (r + 1) ℓ
        rw [he, ← ringIterate_add, add_comm (n + 1), ringIterate_add, hyp]
      exact common_divisor_periodic_points_unit d n c _ _ _ hx hy hs hxp hyp
  · exact Or.inl hp

end Bottcher.Arithmetic

#print axioms Bottcher.Arithmetic.ringCriticalOrbit_dvd_multiple
#print axioms Bottcher.Arithmetic.criticalOrbit_collision_or_unit

#print axioms Bottcher.Arithmetic.unicritical_periodic_points_coprime
