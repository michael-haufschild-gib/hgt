import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-!
# Divisible edges at the cubic roughness boundary

A product of two nonunits below its least-factor cube has prime factors.
Consequently a nontrivial dilation edge on this support is exactly a prime
multiple of a twin-prime pair. These classifications assert no edge supply.
-/

namespace TwinPrime

set_option autoImplicit false

/-- Two nonunit factors whose product lies on cubic rough support. -/
def cubicFactorPairs (z : ℕ) : Set (ℕ × ℕ) :=
  {ab | 2 ≤ ab.1 ∧ 2 ≤ ab.2 ∧ z ≤ (ab.1 * ab.2).minFac ∧ ab.1 * ab.2 < z ^ 3}

/-- Cubic rough factor pairs are exactly the corresponding prime products. -/
theorem cubicFactorPairs_eq_prime_products (z : ℕ) :
    cubicFactorPairs z =
      {ab | ab.1.Prime ∧ ab.2.Prime ∧ z ≤ ab.1 ∧ z ≤ ab.2 ∧ ab.1 * ab.2 < z ^ 3} := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (2 ≤ a ∧ 2 ≤ b ∧ z ≤ (a * b).minFac ∧ a * b < z ^ 3) ↔
    (a.Prime ∧ b.Prime ∧ z ≤ a ∧ z ≤ b ∧ a * b < z ^ 3)
  constructor
  · rintro ⟨ha, hb, hz, hlt⟩
    have prime_factor : ∀ x y : ℕ, x * y = a * b → 2 ≤ x → 2 ≤ y → x.Prime := by
      intro x y hxy hx hy
      by_contra hnp
      have hpx := Nat.minFac_prime (by omega : x ≠ 1)
      have hzx : z ≤ x.minFac := hz.trans (Nat.minFac_le_of_dvd hpx.two_le
        (hxy ▸ dvd_mul_of_dvd_left (Nat.minFac_dvd x) y))
      have hzy : z ≤ y := hz.trans
        (Nat.minFac_le_of_dvd hy (hxy ▸ dvd_mul_left y x))
      have hzsq : z ^ 2 ≤ x := (Nat.pow_le_pow_left hzx 2).trans
        (Nat.minFac_sq_le_self (by omega) hnp)
      have hcube : z ^ 3 ≤ a * b := calc
        z ^ 3 = z ^ 2 * z := pow_succ z 2
        _ ≤ x * y := Nat.mul_le_mul hzsq hzy
        _ = a * b := hxy
      exact (not_le_of_gt hlt) hcube
    refine ⟨prime_factor a b rfl ha hb,
      prime_factor b a (Nat.mul_comm b a) hb ha, ?_, ?_, hlt⟩
    · exact hz.trans (Nat.minFac_le_of_dvd ha (dvd_mul_right a b))
    · exact hz.trans (Nat.minFac_le_of_dvd hb (dvd_mul_left b a))
  · rintro ⟨ha, hb, hza, hzb, hlt⟩
    refine ⟨ha.two_le, hb.two_le, ?_, hlt⟩
    have hab1 : a * b ≠ 1 := by
      have hab := Nat.mul_le_mul ha.two_le hb.two_le
      omega
    have hp := Nat.minFac_prime hab1
    rcases hp.dvd_mul.mp (Nat.minFac_dvd (a * b)) with hpa | hpb
    · exact hza.trans_eq ((Nat.dvd_prime_two_le ha hp.two_le).mp hpa).symm
    · exact hzb.trans_eq ((Nat.dvd_prime_two_le hb hp.two_le).mp hpb).symm

/-- The edge `d*a → d*(a+2)`, with nonunit label and cofactors. -/
def cubicDilationPairs (z : ℕ) : Set (ℕ × ℕ) :=
  {da | da ∈ cubicFactorPairs z ∧ (da.1, da.2 + 2) ∈ cubicFactorPairs z}

/-- Every surviving nontrivial edge has a prime label and twin-prime cofactors. -/
theorem cubicDilationPairs_eq_prime_twin_parameters (z : ℕ) :
    cubicDilationPairs z =
      {da | da.1.Prime ∧ da.2.Prime ∧ (da.2 + 2).Prime ∧
        z ≤ da.1 ∧ z ≤ da.2 ∧ da.1 * (da.2 + 2) < z ^ 3} := by
  ext da
  rcases da with ⟨d, a⟩
  change ((d, a) ∈ cubicFactorPairs z ∧ (d, a + 2) ∈ cubicFactorPairs z) ↔ _
  rw [cubicFactorPairs_eq_prime_products]
  change ((d.Prime ∧ a.Prime ∧ z ≤ d ∧ z ≤ a ∧ d * a < z ^ 3) ∧
    (d.Prime ∧ (a + 2).Prime ∧ z ≤ d ∧ z ≤ a + 2 ∧ d * (a + 2) < z ^ 3)) ↔ _
  constructor
  · rintro ⟨⟨hd, ha, hzd, hza, _⟩, ⟨_, hap, _, _, hbound⟩⟩
    exact ⟨hd, ha, hap, hzd, hza, hbound⟩
  · rintro ⟨hd, ha, hap, hzd, hza, hbound⟩
    have haa : a ≤ a + 2 := Nat.le_add_right a 2
    exact ⟨⟨hd, ha, hzd, hza, (Nat.mul_le_mul_left d haa).trans_lt hbound⟩,
      ⟨hd, hap, hzd, hza.trans haa, hbound⟩⟩

end TwinPrime

#print axioms TwinPrime.cubicFactorPairs_eq_prime_products
#print axioms TwinPrime.cubicDilationPairs_eq_prime_twin_parameters
