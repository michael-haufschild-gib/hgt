import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Double-incidence rigidity in the upper Haar half

Let `R² ≤ Y`. If `Y/2 < n ≤ Y` and two distinct primes `p,q` dividing
`n` both have cofactors at most `R`, then `n=pq`. Indeed writing `n=pqa`
gives `(n/p)(n/q)=na≤R²≤Y<2n`, so `a=1`.

For odd source terms this rigidity extends to the top third: `Y/3<n≤Y`
implies `a<3`, and the odd factor `a` must again be `1`. Thus higher-prime-degree
odd source terms have at most one small-cofactor incidence above `Y/3`.
This is an exact structural restriction, independent of any cancellation estimate.
-/

namespace RHTower

/-- Two selected prime cofactors in the upper Haar half force a semiprime. -/
theorem two_small_cofactors_top_window_semiprime
    {Y R n p q : ℕ}
    (hR : R * R ≤ Y) (hn : Y < 2 * n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n)
    (hpm : n / p ≤ R) (hqm : n / q ≤ R) :
    n = p * q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  obtain ⟨a, ha⟩ := hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpquot : n / p = q * a := by
    rw [ha]
    simpa only [mul_assoc] using (Nat.mul_div_cancel_left (q * a) hp.pos)
  have hqquot : n / q = p * a := by
    calc
      n / q = (q * (p * a)) / q := by rw [ha]; congr 1; ring
      _ = p * a := Nat.mul_div_cancel_left (p * a) hq.pos
  have hqa : q * a ≤ R := hpquot ▸ hpm
  have hpa : p * a ≤ R := hqquot ▸ hqm
  have hbound : n * a ≤ Y := by
    have hmul := Nat.mul_le_mul hpa hqa
    have hid : (p * a) * (q * a) = n * a := by rw [ha]; ring
    omega
  have ha1 : a = 1 := by
    have ha0 : a ≠ 0 := by
      intro hz
      have : n = 0 := by simp [ha, hz]
      omega
    by_contra hnot
    have ha2 : 2 ≤ a := by omega
    have h2n : 2 * n ≤ n * a := by
      simpa [mul_comm] using Nat.mul_le_mul_left n ha2
    omega
  rw [ha, ha1]
  simp

/-- On odd source terms, double small-cofactor incidence is semiprime already above `Y/3`. -/
theorem two_small_cofactors_top_third_semiprime
    {Y R n p q : ℕ}
    (hR : R * R ≤ Y) (hn : Y < 3 * n) (hodd : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpn : p ∣ n) (hqn : q ∣ n)
    (hpm : n / p ≤ R) (hqm : n / q ≤ R) :
    n = p * q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  obtain ⟨a, ha⟩ := hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpquot : n / p = q * a := by
    rw [ha]
    simpa only [mul_assoc] using (Nat.mul_div_cancel_left (q * a) hp.pos)
  have hqquot : n / q = p * a := by
    calc
      n / q = (q * (p * a)) / q := by rw [ha]; congr 1; ring
      _ = p * a := Nat.mul_div_cancel_left (p * a) hq.pos
  have hqa : q * a ≤ R := hpquot ▸ hpm
  have hpa : p * a ≤ R := hqquot ▸ hqm
  have hbound : n * a ≤ Y := by
    have hmul := Nat.mul_le_mul hpa hqa
    have hid : (p * a) * (q * a) = n * a := by rw [ha]; ring
    omega
  have haodd : Odd a := by
    have hodd' : Odd (p * (q * a)) := by simpa only [ha, mul_assoc] using hodd
    exact Nat.Odd.of_mul_right (Nat.Odd.of_mul_right hodd')
  have ha1 : a = 1 := by
    have ha_lt : a < 3 := by
      by_contra hnot
      have ha3 : 3 ≤ a := by omega
      have h3n : 3 * n ≤ n * a := by
        simpa [mul_comm] using Nat.mul_le_mul_left n ha3
      omega
    obtain ⟨k, hk⟩ := haodd
    omega
  rw [ha, ha1]
  simp

end RHTower
