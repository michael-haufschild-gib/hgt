import GaloisForLFunctions.ArithmeticDegenerationTheory.TheDilationsLowerTheConductor
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor

/-!
# The monodromy is eventually idempotent

The dilation `D_p : F ↦ F(p·)` lowers the `p`-valuation of the conductor of a Ramanujan sum
(`TheDilationsLowerTheConductor`). Iterating, the `p`-string of a conductor `m = m' p^v`
(`p ∤ m'`) is exhausted after exactly `v` steps:

* **Exhausting a string** (`ramanujanLagCoefficient_prime_pow_mul`): for `k ≥ v = v_p(m)`,
  `c_m(p^k n) = φ(p^v) c_{m/p^v}(n)`. The weights along the string multiply to
  `p^{v−1}(p − 1) = φ(p^v)`.
* **Eventual idempotence** (`dilation_eventually_idempotent`): `D_p^{v+1} c_m = D_p^v c_m`. On the
  span of a `p`-string of length `v` the monodromy satisfies `D_p^v (D_p − 1) = 0`: its spectrum is
  `{0, 1}`, the eigenvalue `1` carried by the `p`-free conductor and `0` by a nilpotent string of
  length `v`.
* **The full cone** (`ramanujanLagCoefficient_mul_of_dvd`): if `m ∣ d` then `c_m(dn) = φ(m)`: the
  dilations by a multiple of the conductor send every Ramanujan sum to a multiple of the pole mode.

Hodge-theoretic monodromy is quasi-unipotent (eigenvalues roots of unity); the arithmetic monodromy
is eventually idempotent (eigenvalues `0` and `1`), and the length of the nilpotent string is the
valuation. The weight of the conductor `m` along the prime `p` is `v_p(m)`.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open BezoutValuationIncidence

/-- **Exhausting a `p`-string.** If `p^v ∣ m` with `p ∤ m/p^v`, then
`c_m(p^v n) = φ(p^v) c_{m/p^v}(n)`. -/
theorem ramanujanLagCoefficient_prime_pow_mul_self {p : ℕ} (hp : p.Prime) :
    ∀ (v m : ℕ), 0 < m → p ^ v ∣ m → ¬p ∣ m / p ^ v → ∀ n : ℕ,
      ramanujanLagCoefficient m (p ^ v * n) =
        ((p ^ v).totient : ℝ) * ramanujanLagCoefficient (m / p ^ v) n := by
  intro v
  induction v with
  | zero => intro m _ _ _ n; simp
  | succ v ih =>
      intro m hm hdvd hfree n
      have hpm : p ∣ m := (dvd_pow_self p (Nat.succ_ne_zero v)).trans hdvd
      have hm' : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
      have hdvd' : p ^ v ∣ m / p := by
        rw [pow_succ] at hdvd
        exact Nat.dvd_div_of_mul_dvd (by rwa [mul_comm] at hdvd)
      have hquot : m / p / p ^ v = m / p ^ (v + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      have hfree' : ¬p ∣ m / p / p ^ v := by rwa [hquot]
      have hsplit : p ^ (v + 1) * n = p * (p ^ v * n) := by ring
      rw [hsplit, ramanujanLagCoefficient_prime_mul_of_dvd hp hm hpm,
        ih (m / p) hm' hdvd' hfree' n, hquot]
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · have : ¬p ∣ m / p := by simpa using hfree'
        simp only [zero_add, pow_zero, pow_one, Nat.totient_one, Nat.totient_prime hp, if_neg this,
          Nat.cast_one, one_mul]
        push_cast [Nat.cast_sub hp.one_le]
        ring
      · have : p ∣ m / p := (dvd_pow_self p hv.ne').trans hdvd'
        rw [if_pos this, Nat.totient_prime_pow hp (Nat.succ_pos v), Nat.totient_prime_pow hp hv]
        push_cast [Nat.cast_sub hp.one_le]
        have e : (p : ℝ) ^ v = p * p ^ (v - 1) := by rw [← pow_succ', Nat.sub_add_cancel hv]
        rw [e]
        ring

/-- A Ramanujan sum with conductor prime to `p` is fixed by every dilation by a power of `p`. -/
theorem ramanujanLagCoefficient_prime_pow_mul_of_not_dvd {p m : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m)
    (k n : ℕ) : ramanujanLagCoefficient m (p ^ k * n) = ramanujanLagCoefficient m n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, ramanujanLagCoefficient_prime_mul_of_not_dvd hp hpm, ih]

/-- **Exhausting a string, all later powers.** For `k ≥ v_p(m)`,
`c_m(p^k n) = φ(p^v) c_{m/p^v}(n)` with `v = v_p(m)`. -/
theorem ramanujanLagCoefficient_prime_pow_mul {p m : ℕ} (hp : p.Prime) (hm : 0 < m) {k : ℕ}
    (hk : m.factorization p ≤ k) (n : ℕ) :
    ramanujanLagCoefficient m (p ^ k * n) =
      ((p ^ m.factorization p).totient : ℝ) *
        ramanujanLagCoefficient (m / p ^ m.factorization p) n := by
  set v := m.factorization p
  have hdvd : p ^ v ∣ m := Nat.ordProj_dvd m p
  have hfree : ¬p ∣ m / p ^ v := Nat.not_dvd_ordCompl hp hm.ne'
  have hsplit : p ^ k * n = p ^ v * (p ^ (k - v) * n) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit, ramanujanLagCoefficient_prime_pow_mul_self hp v m hm hdvd hfree,
    ramanujanLagCoefficient_prime_pow_mul_of_not_dvd hp hfree]

/-- **Eventual idempotence of the monodromy.** `D_p^{v+1} c_m = D_p^v c_m` for `v = v_p(m)`, and
`D_p^{k} c_m = D_p^{v} c_m` for every `k ≥ v`. -/
theorem dilation_eventually_idempotent {p m : ℕ} (hp : p.Prime) (hm : 0 < m) {k : ℕ}
    (hk : m.factorization p ≤ k) (n : ℕ) :
    ramanujanLagCoefficient m (p ^ k * n) =
      ramanujanLagCoefficient m (p ^ m.factorization p * n) := by
  rw [ramanujanLagCoefficient_prime_pow_mul hp hm hk, ramanujanLagCoefficient_prime_pow_mul hp hm le_rfl]

/-- A nonzero dilation of a positive conductor that the conductor divides sends the Ramanujan sum
to its totient: `c_m(dn) = φ(m)` for `m ∣ d`. -/
theorem ramanujanLagCoefficient_mul_of_dvd {m d : ℕ} (hm : 0 < m) (hmd : m ∣ d) (n : ℕ) :
    ramanujanLagCoefficient m (d * n) = m.totient := by
  have hdn : m ∣ d * n := hmd.mul_right n
  rw [ramanujanLagCoefficient_eq_gcd_divisor_sum, Nat.gcd_eq_left hdn]
  have h := RenormalizedArithmeticPotentialTheory.CompletedShell.sum_divisors_moebius_div_mul m
  rw [← h]
  refine sum_congr rfl fun e _ => ?_
  rw [mul_comm]
  rfl

end GaloisForLFunctions.ArithmeticDegenerationTheory
