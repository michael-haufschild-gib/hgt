import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Moduli with independent residue classes

The elementary input of the crossing of a cyclic extension with a cyclotomic extension.

* **A prime with a large order** (`exists_prime_dvd_orderOf_natCast`): for `a ≥ 2`, `n ≥ 1` and
  `t ≥ 1` there is a prime `p ∤ t a` such that `n` divides the order of `a` modulo `p`. With
  `N = 6 n`, which is not a prime power, and `k` a multiple of `q − 1` for the primes `q | t N`,
  the value `Φ_N(a^k)` is `≡ 1` modulo every prime `q | t N` (it is `Φ_N(0)` or `Φ_N(1)`) and
  exceeds `1`. A prime factor `p` of it does not divide `N`, so `a^k` has order `N` modulo `p`.
* **The modulus** (`exists_modulus_unit_forall_zpow_mul_zpow`): for `n ≥ 1`, a finite set `A` of
  integers `≥ 2` and `t ≥ 1` there are `m ≥ 1` prime to `t` and a unit `b` modulo `m` such that,
  for every `a ∈ A`, `a^x b^y ≡ 1 (mod m)` forces `n | x` and `n | y`. Take a prime `P₀` with
  `n | ord_{P₀}(2)`, primes `P_a ≠ P₀` with `n (P₀ − 1) | ord_{P_a}(a)`, `m = P₀ Π_a P_a` and
  `b ≡ 2 (P₀)`, `b ≡ 1 (P_a)`. Modulo `P_a` the relation gives `n (P₀ − 1) | x`; then
  `a^x ≡ 1 (P₀)`, and `2^y ≡ 1 (P₀)` gives `n | y`.
-/

open Polynomial

namespace GaloisForLFunctions

/-- The value of a cyclotomic polynomial at a natural number, modulo `q`. -/
theorem eval_natCast_cyclotomic_zmod (N c q : ℕ) :
    (cyclotomic N (ZMod q)).eval (c : ZMod q) =
      (((cyclotomic N ℤ).eval (c : ℤ) : ℤ) : ZMod q) := by
  rw [← map_cyclotomic_int N (ZMod q), eval_natCast_map, eq_intCast]

/-- **A prime with a large order.** For `a ≥ 2`, `n ≥ 1` and `t ≥ 1` there is a prime `p` that
divides neither `t` nor `a`, such that `n` divides the order of `a` modulo `p`. -/
theorem exists_prime_dvd_orderOf_natCast {a : ℕ} (ha : 2 ≤ a) {n : ℕ} (hn : n ≠ 0) {t : ℕ}
    (ht : t ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ t ∧ ¬ p ∣ a ∧ n ∣ orderOf (a : ZMod p) := by
  have hN1 : 1 < 6 * n := by omega
  -- `6 n` is not a prime power
  have hNpp : ∀ {q : ℕ}, q.Prime → ∀ j : ℕ, q ^ j ≠ 6 * n := by
    intro q hq j hqj
    have h2 : 2 ∣ q ^ j := by rw [hqj]; exact ⟨3 * n, by ring⟩
    have h3 : 3 ∣ q ^ j := by rw [hqj]; exact ⟨2 * n, by ring⟩
    have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hs0 : t * (6 * n) ≠ 0 := Nat.mul_ne_zero ht (by omega)
  -- an exponent divisible by `q − 1` for the primes `q | t N`
  obtain ⟨k, hk0, hkdvd⟩ : ∃ k : ℕ, k ≠ 0 ∧ ∀ q ∈ (t * (6 * n)).primeFactors, q - 1 ∣ k :=
    ⟨∏ q ∈ (t * (6 * n)).primeFactors, (q - 1),
      Finset.prod_ne_zero_iff.mpr fun q hq =>
        (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hq).one_lt).ne',
      fun q hq => Finset.dvd_prod_of_mem _ hq⟩
  have hak : 2 ≤ a ^ k := ha.trans (Nat.le_self_pow hk0 a)
  -- `Φ_N(a^k) ≡ 1` modulo every prime factor of `t N`
  have hres : ∀ q : ℕ, q.Prime → q ∣ t * (6 * n) →
      (cyclotomic (6 * n) (ZMod q)).eval ((a ^ k : ℕ) : ZMod q) = 1 := by
    intro q hq hqs
    haveI := Fact.mk hq
    rw [Nat.cast_pow]
    by_cases hqa : (a : ZMod q) = 0
    · rw [hqa, zero_pow hk0, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hN1]
    · obtain ⟨j, hj⟩ := hkdvd q (Nat.mem_primeFactors.mpr ⟨hq, hqs, hs0⟩)
      rw [hj, pow_mul, ZMod.pow_card_sub_one_eq_one hqa, one_pow,
        eval_one_cyclotomic_not_prime_pow hNpp]
  -- a prime factor of `Φ_N(a^k) > 1`
  have hgt : 1 < ((cyclotomic (6 * n) ℤ).eval ((a ^ k : ℕ) : ℤ)).natAbs :=
    lt_of_le_of_lt (Nat.le_sub_one_of_lt hak)
      (sub_one_lt_natAbs_cyclotomic_eval hN1 (Nat.ne_of_gt hak))
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgt.ne'
  haveI := Fact.mk hp
  have hroot : IsRoot (cyclotomic (6 * n) (ZMod p)) ((a ^ k : ℕ) : ZMod p) := by
    rw [IsRoot.def, eval_natCast_cyclotomic_zmod, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpdvd
  have hps : ¬ p ∣ t * (6 * n) := fun h =>
    one_ne_zero ((hres p hp h).symm.trans (IsRoot.def.mp hroot))
  -- `a^k` has order `N` modulo `p`
  haveI : NeZero ((6 * n : ℕ) : ZMod p) :=
    ⟨fun h => hps (Dvd.dvd.mul_left ((ZMod.natCast_eq_zero_iff _ _).mp h) t)⟩
  have hprim : IsPrimitiveRoot ((a : ZMod p) ^ k) (6 * n) := by
    rw [← Nat.cast_pow]
    exact isRoot_cyclotomic_iff.mp hroot
  have hap : (a : ZMod p) ≠ 0 := fun h => by
    have h1 := hprim.pow_eq_one
    rw [h, zero_pow hk0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  refine ⟨p, hp, fun h => hps (Dvd.dvd.mul_right h _),
    fun h => hap ((ZMod.natCast_eq_zero_iff a p).mpr h), ?_⟩
  have h6 : 6 * n ∣ orderOf (a : ZMod p) := by
    rw [hprim.eq_orderOf]
    exact orderOf_pow_dvd k
  exact (dvd_mul_left n 6).trans h6

/-- The reduction modulo a divisor `p` of `m` of a unit modulo `m` with residue `k`. -/
theorem coe_unitsMap_eq_natCast {m p : ℕ} (h : p ∣ m) {u : (ZMod m)ˣ} {k : ℕ}
    (hu : (u : ZMod m) = (k : ZMod m)) :
    ((ZMod.unitsMap h u : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, hu]
  exact map_natCast (ZMod.castHom h (ZMod p)) k

/-- **A modulus with independent residue classes.** For `n ≥ 1`, a finite set `A` of integers
`≥ 2` and `t ≥ 1` there are `m ≥ 1` prime to `t` and a unit `b` modulo `m` such that for every
`a ∈ A`: if `a^x b^y ≡ 1 (mod m)` then `n` divides `x` and `y`. -/
theorem exists_modulus_unit_forall_zpow_mul_zpow {n : ℕ} (hn : n ≠ 0) (A : Finset ℕ)
    (hA : ∀ a ∈ A, 2 ≤ a) {t : ℕ} (ht : t ≠ 0) :
    ∃ (m : ℕ) (b : (ZMod m)ˣ), m ≠ 0 ∧ m.Coprime t ∧
      ∀ a ∈ A, ∀ u : (ZMod m)ˣ, (u : ZMod m) = (a : ZMod m) → ∀ x y : ℤ,
        u ^ x * b ^ y = 1 → (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y := by
  -- a prime `P₀` modulo which `2` has order divisible by `n`
  obtain ⟨P₀, hP₀, hP₀t, hP₀2, hord₀⟩ := exists_prime_dvd_orderOf_natCast (le_refl 2) hn ht
  haveI := Fact.mk hP₀
  have hn' : n * (P₀ - 1) ≠ 0 := Nat.mul_ne_zero hn (Nat.sub_pos_of_lt hP₀.one_lt).ne'
  have ht' : t * P₀ ≠ 0 := Nat.mul_ne_zero ht hP₀.ne_zero
  -- primes `P a ≠ P₀` modulo which `a` has order divisible by `n (P₀ − 1)`
  have hex : ∀ a ∈ A, ∃ p : ℕ, p.Prime ∧ ¬ p ∣ t * P₀ ∧
      n * (P₀ - 1) ∣ orderOf (a : ZMod p) := fun a ha =>
    let ⟨p, hp, hpt, _, hord⟩ := exists_prime_dvd_orderOf_natCast (hA a ha) hn' ht'
    ⟨p, hp, hpt, hord⟩
  choose! P hP hPt hPord using hex
  have hcop₀ : P₀.Coprime (∏ a ∈ A, P a) := Nat.Coprime.prod_right fun a ha =>
    (Nat.coprime_primes hP₀ (hP a ha)).mpr fun h =>
      hPt a ha (Dvd.dvd.mul_left (dvd_of_eq h.symm) t)
  -- `b ≡ 2` modulo `P₀` and `b ≡ 1` modulo the other primes
  obtain ⟨b₀, hb₀2, hb₀1⟩ := Nat.chineseRemainder hcop₀ 2 1
  have h2P₀ : Nat.Coprime 2 P₀ :=
    (Nat.coprime_primes Nat.prime_two hP₀).mpr fun h => hP₀2 (dvd_of_eq h.symm)
  have hb₀ : b₀.Coprime (P₀ * ∏ a ∈ A, P a) :=
    Nat.Coprime.mul_right (hb₀2.gcd_eq.trans h2P₀) (hb₀1.gcd_eq.trans (Nat.gcd_one_left _))
  have hm0 : P₀ * ∏ a ∈ A, P a ≠ 0 :=
    Nat.mul_ne_zero hP₀.ne_zero (Finset.prod_ne_zero_iff.mpr fun a ha => (hP a ha).ne_zero)
  have hP₀m : P₀ ∣ P₀ * ∏ a ∈ A, P a := dvd_mul_right _ _
  have hPm : ∀ a ∈ A, P a ∣ P₀ * ∏ a ∈ A, P a := fun a ha =>
    (Finset.dvd_prod_of_mem P ha).mul_left _
  refine ⟨P₀ * ∏ a ∈ A, P a, ZMod.unitOfCoprime b₀ hb₀, hm0,
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hP₀).mpr hP₀t)
      (Nat.Coprime.prod_left fun a ha =>
        (Nat.Prime.coprime_iff_not_dvd (hP a ha)).mpr fun h => hPt a ha (h.mul_right _)), ?_⟩
  intro a ha u hu x y hxy
  -- modulo `P a`: `b ≡ 1`, so `a^x ≡ 1` and `n (P₀ − 1) | x`
  have hb1 : ZMod.unitsMap (hPm a ha) (ZMod.unitOfCoprime b₀ hb₀) = 1 := by
    refine Units.ext ?_
    rw [coe_unitsMap_eq_natCast (hPm a ha) (ZMod.coe_unitOfCoprime b₀ hb₀), Units.val_one]
    exact ((ZMod.natCast_eq_natCast_iff b₀ 1 (P a)).mpr
      (hb₀1.of_dvd (Finset.dvd_prod_of_mem P ha))).trans Nat.cast_one
  have hp := congrArg (ZMod.unitsMap (hPm a ha)) hxy
  rw [map_mul, map_zpow, map_zpow, map_one, hb1, one_zpow, mul_one] at hp
  have hordu : orderOf (ZMod.unitsMap (hPm a ha) u) = orderOf (a : ZMod (P a)) := by
    rw [← orderOf_units, coe_unitsMap_eq_natCast (hPm a ha) hu]
  have hx : ((n * (P₀ - 1) : ℕ) : ℤ) ∣ x := by
    refine (Int.natCast_dvd_natCast.mpr ?_).trans (orderOf_dvd_iff_zpow_eq_one.mpr hp)
    rw [hordu]
    exact hPord a ha
  have hxn : (n : ℤ) ∣ x := (Int.natCast_dvd_natCast.mpr (dvd_mul_right n (P₀ - 1))).trans hx
  obtain ⟨j, hj⟩ : ((P₀ - 1 : ℕ) : ℤ) ∣ x :=
    (Int.natCast_dvd_natCast.mpr (dvd_mul_left (P₀ - 1) n)).trans hx
  -- modulo `P₀`: `a^x ≡ 1`, so `2^y ≡ 1` and `n | y`
  have hp₀ := congrArg (ZMod.unitsMap hP₀m) hxy
  rw [map_mul, map_zpow, map_zpow, map_one, hj, zpow_mul, zpow_natCast,
    ZMod.units_pow_card_sub_one_eq_one, one_zpow, one_mul] at hp₀
  have hordb : orderOf (ZMod.unitsMap hP₀m (ZMod.unitOfCoprime b₀ hb₀)) =
      orderOf ((2 : ℕ) : ZMod P₀) := by
    rw [← orderOf_units, coe_unitsMap_eq_natCast hP₀m (ZMod.coe_unitOfCoprime b₀ hb₀),
      (ZMod.natCast_eq_natCast_iff b₀ 2 P₀).mpr hb₀2]
  refine ⟨hxn, (Int.natCast_dvd_natCast.mpr ?_).trans (orderOf_dvd_iff_zpow_eq_one.mpr hp₀)⟩
  rw [hordb]
  exact hord₀

end GaloisForLFunctions
