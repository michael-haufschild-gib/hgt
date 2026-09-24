import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Triple-incidence sparsity at the square-root cofactor boundary

Three distinct prime divisors `p,q,r` of `n` with `n/p,n/q,n/r ≤ R`
force `n² ≤ R³`. This is an exact finite restriction on repeated incidence
in the source-faithful Haar–Ramaré expansion. At `R=floor(sqrt Y)`, every
triple-incidence source atom lies below `Y^(3/4)`; hence these atoms cannot
contribute to a `Y/log² Y` main term even with logarithmic multiplicity.
-/

namespace RHTower

private theorem triple_small_cofactors_sq_le_cube
    {n R p q r : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hprod : p * q * r ∣ n)
    (hpm : n / p ≤ R) (hqm : n / q ≤ R) (hrm : n / r ≤ R) :
    n * n ≤ R * R * R := by
  obtain ⟨a, ha⟩ := hprod
  have hpquot : n / p = q * r * a := by
    rw [ha]
    calc
      (p * q * r * a) / p = (p * (q * r * a)) / p := by congr 1; ring
      _ = q * r * a := Nat.mul_div_cancel_left (q * r * a) hp.pos
  have hqquot : n / q = p * r * a := by
    rw [ha]
    calc
      (p * q * r * a) / q = (q * (p * r * a)) / q := by congr 1; ring
      _ = p * r * a := Nat.mul_div_cancel_left (p * r * a) hq.pos
  have hrquot : n / r = p * q * a := by
    rw [ha]
    calc
      (p * q * r * a) / r = (r * (p * q * a)) / r := by congr 1; ring
      _ = p * q * a := Nat.mul_div_cancel_left (p * q * a) hr.pos
  have hpa : q * r * a ≤ R := hpquot ▸ hpm
  have hqa : p * r * a ≤ R := hqquot ▸ hqm
  have hra : p * q * a ≤ R := hrquot ▸ hrm
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hpa hqa) hra
  have hid : (q * r * a) * (p * r * a) * (p * q * a) = n * n * a := by
    rw [ha]
    ring
  have ha1 : 1 ≤ a := by
    have : a ≠ 0 := by
      intro hz
      have : n = 0 := by simp [ha, hz]
      omega
    omega
  have hle : n * n ≤ n * n * a := by
    simpa using Nat.mul_le_mul_left (n * n) ha1
  omega

theorem triple_small_cofactors_sq_le_cube_of_distinct_primes
    {n R p q r : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpm : n / p ≤ R) (hqm : n / q ≤ R) (hrm : n / r ≤ R) :
    n * n ≤ R * R * R := by
  have hpqcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hprcop : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 hpr
  have hqrcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have hpqdiv : p * q ∣ n := hpqcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpqrcop : Nat.Coprime (p * q) r := Nat.coprime_mul_iff_left.mpr ⟨hprcop, hqrcop⟩
  have hpqrdiv : p * q * r ∣ n := hpqrcop.mul_dvd_of_dvd_of_dvd hpqdiv hrn
  exact triple_small_cofactors_sq_le_cube hn hp hq hr hpqrdiv hpm hqm hrm

end RHTower
