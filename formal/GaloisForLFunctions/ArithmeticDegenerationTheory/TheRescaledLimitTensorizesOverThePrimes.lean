import GaloisForLFunctions.ArithmeticDegenerationTheory.TheWeightStringsOfTheRescaledLimit

/-!
# The rescaled limit tensorizes over the primes

The conductor space of the degenerating family is spanned by the Ramanujan packets `r_m`, and the
monodromy acts on the `p`-valuation of `m` one prime at a time (`TheDilationsLowerTheConductor`).
In Hodge theory of several commuting nilpotents the limiting structure of a product of
degenerations is the tensor product of the limiting structures. This file proves the arithmetic
counterpart for the rescaled limit of the complete Weil family.

* **Multiplicativity** (`jordanTotient_mul_of_coprime`): `J_k = μ ∗ id^k` is multiplicative.
* **Tensor law** (`jordanCoefficient_mul_of_coprime`): for coprime `a, b`,
  `J(1) J(ab) = J(a) J(b)`: the limiting polarization of the conductor `ab` is the product of the
  polarizations of `a` and `b`, normalized at the pole conductor.
* **Prime powers** (`jordanTotient_prime_pow`, `jordanCoefficient_prime_pow`):
  `J_k(p^a) = p^{k(a−1)}(p^k − 1)` and `J(p^a) = J(1) [8]_p p^{7(a−1)}` for `a ≥ 1`.

So the limiting polarization is the tensor product over the primes of one weight string per prime:
the string of `p` starts with the `p`-integer `[8]_p` and climbs by `p⁷` per step. The prime cone has
independent weight filtrations, and the archimedean place enters only through the common scalar
`J(1) = 2A_φ ζ(8)/M`, the polarization of the pole conductor.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

/-- Jordan's totient `μ ∗ id^k` as an arithmetic function. -/
def jordanAF (k : ℕ) : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ) * ((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

theorem isMultiplicative_jordanAF (k : ℕ) : (jordanAF k).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul isMultiplicative_pow.natCast

theorem jordanAF_apply {k m : ℕ} (hk : 0 < k) : jordanAF k m = jordanTotient k m := by
  rw [jordanAF, mul_apply, jordanTotient, Nat.sum_divisorsAntidiagonal' (fun x y =>
    ((μ : ArithmeticFunction ℝ) x) * (((pow k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) y))]
  refine sum_congr rfl fun d hd => ?_
  rw [natCoe_apply, pow_apply, if_neg (by omega), intCoe_apply]
  push_cast
  rw [Real.rpow_natCast]

/-- **Jordan's totient is multiplicative.** -/
theorem jordanTotient_mul_of_coprime {k a b : ℕ} (hk : 0 < k) (hab : Nat.Coprime a b) :
    jordanTotient k (a * b) = jordanTotient k a * jordanTotient k b := by
  rw [← jordanAF_apply hk, ← jordanAF_apply hk, ← jordanAF_apply hk,
    (isMultiplicative_jordanAF k).map_mul_of_coprime hab]

theorem jordanTotient_one (k : ℝ) : jordanTotient k 1 = 1 := by
  simp [jordanTotient]

/-- `J_k(p^a) = p^{k(a−1)} (p^k − 1)` for `a ≥ 1`. -/
theorem jordanTotient_prime_pow {p : ℕ} (hp : p.Prime) (k : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    jordanTotient k (p ^ a) = (p : ℝ) ^ (k * (a - 1 : ℕ)) * ((p : ℝ) ^ k - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  induction a, ha using Nat.le_induction with
  | base =>
      rw [pow_one, jordanTotient_prime_mul_of_dvd hp hp.pos dvd_rfl, Nat.div_self hp.pos,
        if_neg (by simpa using hp.one_lt.ne'), jordanTotient_one]
      simp
  | succ a ha ih =>
      have hpa : p ∣ p ^ (a + 1) := dvd_pow_self p (by omega)
      have hdiv : p ^ (a + 1) / p = p ^ a := by
        rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
      rw [jordanTotient_prime_mul_of_dvd hp (pow_pos hp.pos _) hpa, hdiv,
        if_pos (dvd_pow_self p (by omega)), ih, ← mul_assoc, ← Real.rpow_add hp0]
      congr 2
      have : (a + 1 - 1 : ℕ) = (a - 1 : ℕ) + 1 := by omega
      rw [this]
      push_cast
      ring

theorem jordanCoefficient_one :
    jordanCoefficient 1 = 2 / (∫ u, SpacingScaleHarmonicAnalysis.tiltedUnitSpline u ^ 2) *
      tiltedTailConstant * zetaSum 8 := by
  simp [jordanCoefficient, jordanTotient_one]

/-- **The tensor law.** For coprime `a, b ≥ 1`, `J(1) J(ab) = J(a) J(b)`. -/
theorem jordanCoefficient_mul_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    jordanCoefficient 1 * jordanCoefficient (a * b) = jordanCoefficient a * jordanCoefficient b := by
  have hJ := jordanTotient_mul_of_coprime (k := 8) (by norm_num) hab
  have ht : ((a * b).totient : ℝ) = a.totient * b.totient := by
    exact_mod_cast Nat.totient_mul hab
  have hta : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have htb : (0 : ℝ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
  simp only [jordanCoefficient, Nat.totient_one, Nat.cast_one, jordanTotient_one, div_one, mul_one]
  push_cast at hJ ⊢
  rw [hJ, ht]
  field_simp

/-- **The prime-power coefficients.** `J(p^a) = J(1) [8]_p p^{7(a−1)}` for `a ≥ 1`. -/
theorem jordanCoefficient_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    jordanCoefficient (p ^ a) = jordanCoefficient 1 * pInteger p * (p : ℝ) ^ (7 * (a - 1 : ℕ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have ht : ((p ^ a).totient : ℝ) = (p : ℝ) ^ (a - 1) * ((p : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hJ := jordanTotient_prime_pow hp 8 ha
  simp only [jordanCoefficient, Nat.totient_one, Nat.cast_one, jordanTotient_one, div_one, mul_one]
  rw [hJ, ht, pInteger]
  have e : (p : ℝ) ^ ((8 : ℝ) * (a - 1 : ℕ)) = (p : ℝ) ^ (7 * (a - 1)) * (p : ℝ) ^ (a - 1) := by
    rw [← pow_add, show 7 * (a - 1) + (a - 1) = 8 * (a - 1) by ring, ← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [e]
  have : (0 : ℝ) < (p : ℝ) ^ (a - 1) := pow_pos hp0 _
  field_simp

end GaloisForLFunctions.ArithmeticDegenerationTheory
