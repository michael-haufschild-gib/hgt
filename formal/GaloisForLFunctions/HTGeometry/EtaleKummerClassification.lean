import Mathlib

/-!
# The étale/Kummer classification of the critical horizon chart

Step 4 of the full-symmetric-monodromy card argues that a hidden block system for the critical
horizon monodromy would produce a nontrivial finite étale cover of the parameter chart
`(𝔾ₘ)² × 𝔸^{L-2}`; over an algebraically closed field of characteristic zero such a cover is a torus
Kummer cover, so it has a cyclic quotient

```text
z ^ r = p ^ a q ^ b ,    (a, b) not both zero mod r .            (15)
```

The two coordinate divisors of the *source* chart then kill it: in the source function field the
prime divisor `x_m = 0` sees `p` once and `q` not at all, and symmetrically for `y_n = 0`, so

```text
v_m(z ^ r) = a ,  v_n(z ^ r) = b   ⟹   r ∣ a  and  r ∣ b .      (16)–(17)
```

This file proves `(16)–(17)` unconditionally and in the generality the argument needs — the `r`-th
root is allowed to be **any** element of the fraction field, not a unit of the chart, which is what
makes the statement about the block cover rather than about the unit group.

```text
dvd_of_pow_eq_pow_mul_pow_mul            the multiplicity identity in a UFD
dvd_of_pow_eq_algebraMap                 an r-th root in the fraction field forces r ∣ k
dvd_of_pow_eq_zpow_mul                   the Laurent (integer-exponent) form
dvd_exponents_of_pow_eq_unit_mul_zpow_mul_zpow
    ** a unit times a Laurent monomial in two non-associate primes has an r-th root in the
       fraction field only when r divides both exponents **
not_exists_kummer_root_of_not_dvd_exponents      the sharp contrapositive
dvd_exponents_of_kummer_root_mvPolynomial        the coordinate-chart specialisation
```

The companion file `LocalizationTwoPrimeUnits.lean` settles the same divisibility when the root is a
*unit of the chart*; the theorems here remove that restriction, so together they classify every
everywhere-unramified cyclic cover of the chart that is dominated by the rational source.
-/

namespace GaloisForLFunctions.HTGeometry

theorem dvd_of_pow_eq_pow_mul_pow_mul
    {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    {p b s t : A} {k r : ℕ} (hp : Prime p) (hb : ¬ p ∣ b)
    (ht : t ≠ 0) (h : s ^ r = t ^ r * (p ^ k * b)) :
    r ∣ k := by
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero p)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [pow_zero, one_mul] at h
    have hunit : IsUnit (p ^ k) := isUnit_of_mul_isUnit_left (h ▸ isUnit_one)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact dvd_rfl
    · exact absurd (isUnit_of_dvd_unit (dvd_pow_self p hk.ne') hunit) hp.not_unit
  · have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow hr.ne'] at h
      exact (mul_ne_zero (pow_ne_zero r ht)
        (mul_ne_zero (pow_ne_zero k hp.ne_zero) hb0)) h.symm
    have hfs := FiniteMultiplicity.of_prime_left hp hs0
    have hft := FiniteMultiplicity.of_prime_left hp ht
    have key : emultiplicity p (s ^ r) = emultiplicity p (t ^ r * (p ^ k * b)) := by rw [h]
    rw [emultiplicity_pow hp, emultiplicity_mul hp, emultiplicity_pow hp,
        emultiplicity_mul hp, emultiplicity_pow_self hp.ne_zero hp.not_unit,
        emultiplicity_eq_zero.mpr hb, hfs.emultiplicity_eq_multiplicity,
        hft.emultiplicity_eq_multiplicity] at key
    have keyN : r * multiplicity p s = r * multiplicity p t + k := by
      have : ((r * multiplicity p s : ℕ) : ℕ∞) = ((r * multiplicity p t + k : ℕ) : ℕ∞) := by
        push_cast
        simpa [add_zero] using key
      exact_mod_cast this
    have hle : multiplicity p t ≤ multiplicity p s :=
      Nat.le_of_mul_le_mul_left (by omega) hr
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨d, ?_⟩
    rw [hd, Nat.mul_add] at keyN
    omega

/-- **The unramified radical criterion in the fraction field.**  An `r`-th root, *anywhere in the
fraction field of the unique factorisation domain*, of `p ^ k * b` with `p` a prime not dividing the
cofactor `b`, forces `r ∣ k`.  This is exactly `(16)--(17)`: the divisorial valuation at `p` of the
root is `k / r`, so the radical cover is unramified along `p = 0` only when `r` divides `k`. -/
theorem dvd_of_pow_eq_algebraMap
    {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
    {p b : A} {k r : ℕ} {z : F} (hp : Prime p) (hb : ¬ p ∣ b)
    (hz : z ^ r = algebraMap A F (p ^ k * b)) :
    r ∣ k := by
  obtain ⟨s, t, ht, hst⟩ := IsFractionRing.div_surjective (A := A) (K := F) z
  have ht0 : t ≠ 0 := fun h => by
    simp only [h] at ht
    exact zero_notMem_nonZeroDivisors ht
  have htF : algebraMap A F t ≠ 0 := fun h => ht0 (IsFractionRing.injective A F (by simpa using h))
  have hmain : (algebraMap A F s) ^ r = (algebraMap A F t) ^ r * algebraMap A F (p ^ k * b) := by
    rw [← hz, ← hst, div_pow, mul_div_cancel₀ _ (pow_ne_zero r htF)]
  refine dvd_of_pow_eq_pow_mul_pow_mul (p := p) (b := b) (s := s) (t := t) hp hb ht0 ?_
  refine IsFractionRing.injective A F ?_
  simpa [map_mul, map_pow] using hmain


section TwoPrimes

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]

/-- A prime does not divide a unit times a power of a non-associate prime. -/
theorem not_dvd_unit_mul_pow {p q c : A} (hp : Prime p) (hq : Prime q)
    (hpq : ¬ Associated p q) (hc : IsUnit c) (J : ℕ) :
    ¬ p ∣ c * q ^ J := by
  intro hdvd
  rcases hp.dvd_mul.mp hdvd with hcd | hqd
  · exact hp.not_unit (isUnit_of_dvd_unit hcd hc)
  · exact hpq ((hp.associated_of_dvd hq (hp.dvd_of_dvd_pow hqd)))

/-- **The Laurent form of the unramified radical criterion.**  An `r`-th root in the fraction field
of `p ^ k · b`, with an *integer* exponent `k`, forces `r ∣ k`. -/
theorem dvd_of_pow_eq_zpow_mul {p b : A} {k : ℤ} {r : ℕ} {z : F}
    (hp : Prime p) (hb : ¬ p ∣ b) (hr : 0 < r)
    (hz : z ^ r = (algebraMap A F p) ^ k * algebraMap A F b) :
    (r : ℤ) ∣ k := by
  have hpF : algebraMap A F p ≠ 0 := fun h =>
    hp.ne_zero (IsFractionRing.injective A F (by simpa using h))
  set N : ℕ := k.natAbs with hN
  have hnonneg : 0 ≤ k + (r : ℤ) * (N : ℤ) := by
    have h1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    have h2 : (N : ℤ) = |k| := by simp [hN]
    nlinarith [abs_nonneg k, neg_abs_le k, le_abs_self k]
  set K : ℕ := (k + (r : ℤ) * (N : ℤ)).toNat with hK
  have hKcast : (K : ℤ) = k + (r : ℤ) * (N : ℤ) := Int.toNat_of_nonneg hnonneg
  have hw : (z * (algebraMap A F p) ^ N) ^ r = algebraMap A F (p ^ K * b) := by
    rw [mul_pow, hz, map_mul, map_pow]
    rw [← zpow_natCast (algebraMap A F p) N, ← zpow_natCast (algebraMap A F p) K,
      ← zpow_natCast ((algebraMap A F p) ^ (N : ℤ)) r, ← zpow_mul, hKcast]
    rw [mul_comm ((algebraMap A F p) ^ k) (algebraMap A F b), mul_assoc,
      ← zpow_add₀ hpF, mul_comm]
    ring_nf
  have := dvd_of_pow_eq_algebraMap (A := A) (F := F) hp hb hw
  obtain ⟨d, hd⟩ := this
  refine ⟨d - (N : ℤ), ?_⟩
  have : (K : ℤ) = (r : ℤ) * (d : ℤ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hd
  rw [hKcast] at this
  linarith [this]

/-- **The étale/Kummer classification for a two-divisor chart, radical form.**  If a unit times a
Laurent monomial in two non-associate primes has an `r`-th root anywhere in the fraction field, then
`r` divides both exponents.

This is `(15)--(17)` of the full-symmetric-monodromy card in the form the block argument consumes:
the cyclic quotient of a hidden block cover would be a torus Kummer cover `z ^ r = p ^ a q ^ b`, and
its two divisorial valuations force `r ∣ a` and `r ∣ b`, so the cover is trivial. -/
theorem dvd_exponents_of_pow_eq_unit_mul_zpow_mul_zpow {p q c : A} {i j : ℤ} {r : ℕ} {z : F}
    (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q) (hc : IsUnit c) (hr : 0 < r)
    (hz : z ^ r = algebraMap A F c * (algebraMap A F p) ^ i * (algebraMap A F q) ^ j) :
    (r : ℤ) ∣ i ∧ (r : ℤ) ∣ j := by
  have hpF : algebraMap A F p ≠ 0 := fun h =>
    hp.ne_zero (IsFractionRing.injective A F (by simpa using h))
  have hqF : algebraMap A F q ≠ 0 := fun h =>
    hq.ne_zero (IsFractionRing.injective A F (by simpa using h))
  have hqpa : ¬ Associated q p := fun h => hpq h.symm
  set N : ℕ := i.natAbs with hNdef
  set M : ℕ := j.natAbs with hMdef
  have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hInn : 0 ≤ i + (r : ℤ) * (N : ℤ) := by
    have h2 : (N : ℤ) = |i| := by simp [hNdef]
    nlinarith [abs_nonneg i, neg_abs_le i, le_abs_self i]
  have hJnn : 0 ≤ j + (r : ℤ) * (M : ℤ) := by
    have h2 : (M : ℤ) = |j| := by simp [hMdef]
    nlinarith [abs_nonneg j, neg_abs_le j, le_abs_self j]
  set I : ℕ := (i + (r : ℤ) * (N : ℤ)).toNat with hIdef
  set J : ℕ := (j + (r : ℤ) * (M : ℤ)).toNat with hJdef
  have hI : (I : ℤ) = i + (r : ℤ) * (N : ℤ) := Int.toNat_of_nonneg hInn
  have hJ : (J : ℤ) = j + (r : ℤ) * (M : ℤ) := Int.toNat_of_nonneg hJnn
  have hpow_p : (algebraMap A F p) ^ i * (algebraMap A F p) ^ (N * r : ℕ)
      = (algebraMap A F p) ^ (I : ℕ) := by
    rw [← zpow_natCast (algebraMap A F p) (N * r), ← zpow_add₀ hpF,
      ← zpow_natCast (algebraMap A F p) I, hI]
    congr 1
    push_cast
    ring
  have hpow_q : (algebraMap A F q) ^ j * (algebraMap A F q) ^ (M * r : ℕ)
      = (algebraMap A F q) ^ (J : ℕ) := by
    rw [← zpow_natCast (algebraMap A F q) (M * r), ← zpow_add₀ hqF,
      ← zpow_natCast (algebraMap A F q) J, hJ]
    congr 1
    push_cast
    ring
  obtain ⟨P, hP⟩ : ∃ P : F, (algebraMap A F p) ^ i = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : F, (algebraMap A F q) ^ j = Q := ⟨_, rfl⟩
  rw [hP, hQ] at hz
  rw [hP] at hpow_p
  rw [hQ] at hpow_q
  have hw : (z * (algebraMap A F p) ^ N * (algebraMap A F q) ^ M) ^ r
      = algebraMap A F (c * p ^ I * q ^ J) := by
    rw [mul_pow, mul_pow, hz, ← pow_mul, ← pow_mul, map_mul, map_mul, map_pow, map_pow]
    calc algebraMap A F c * P * Q * (algebraMap A F p) ^ (N * r)
            * (algebraMap A F q) ^ (M * r)
        = algebraMap A F c * (P * (algebraMap A F p) ^ (N * r))
            * (Q * (algebraMap A F q) ^ (M * r)) := by ring
      _ = algebraMap A F c * (algebraMap A F p) ^ I * (algebraMap A F q) ^ J := by
            rw [hpow_p, hpow_q]
  have hdI : r ∣ I := by
    refine dvd_of_pow_eq_algebraMap (A := A) (F := F) (p := p) (b := c * q ^ J)
      (z := z * (algebraMap A F p) ^ N * (algebraMap A F q) ^ M) hp
      (not_dvd_unit_mul_pow hp hq hpq hc _) ?_
    rw [hw]
    congr 1
    ring
  have hdJ : r ∣ J := by
    refine dvd_of_pow_eq_algebraMap (A := A) (F := F) (p := q) (b := c * p ^ I)
      (z := z * (algebraMap A F p) ^ N * (algebraMap A F q) ^ M) hq
      (not_dvd_unit_mul_pow hq hp hqpa hc _) ?_
    rw [hw]
    congr 1
    ring
  obtain ⟨dI, hdI'⟩ := hdI
  obtain ⟨dJ, hdJ'⟩ := hdJ
  have hIz : (I : ℤ) = (r : ℤ) * (dI : ℤ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdI'
  have hJz : (J : ℤ) = (r : ℤ) * (dJ : ℤ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdJ'
  rw [hI] at hIz
  rw [hJ] at hJz
  exact ⟨⟨(dI : ℤ) - (N : ℤ), by linarith⟩, ⟨(dJ : ℤ) - (M : ℤ), by linarith⟩⟩

/-- **The sharp form.**  If the exponent pair of the Kummer radicand is not both divisible by `r`,
then no `r`-th root exists anywhere in the fraction field: the hypothetical block cover of the
critical horizon has no function-field realisation. -/
theorem not_exists_kummer_root_of_not_dvd_exponents {p q c : A} {i j : ℤ} {r : ℕ}
    (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q) (hc : IsUnit c) (hr : 0 < r)
    (hnd : ¬ ((r : ℤ) ∣ i ∧ (r : ℤ) ∣ j)) :
    ¬ ∃ z : F, z ^ r
      = algebraMap A F c * (algebraMap A F p) ^ i * (algebraMap A F q) ^ j := by
  rintro ⟨z, hz⟩
  exact hnd (dvd_exponents_of_pow_eq_unit_mul_zpow_mul_zpow hp hq hpq hc hr hz)

end TwoPrimes

section MvPolynomialChart

open MvPolynomial

variable {σ : Type*} {K : Type*} [Field K]

/-- **Two distinct coordinates are never associate.** -/
theorem not_associated_X_of_ne [DecidableEq σ] {a b : σ} (hab : a ≠ b) :
    ¬ Associated (X a : MvPolynomial σ K) (X b) := by
  rintro ⟨u, hu⟩
  obtain ⟨r, -, hcr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [hcr] at hu
  have hzero : MvPolynomial.degreeOf b (X a * C r : MvPolynomial σ K) = 0 := by
    refine Nat.le_zero.1 (le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_)
    rw [MvPolynomial.degreeOf_X_of_ne (Ne.symm hab), MvPolynomial.degreeOf_C]
  rw [hu, MvPolynomial.degreeOf_X] at hzero
  exact absurd hzero (by simp)

/-- **The étale/Kummer classification on a coordinate chart.**  Over the rational function field of
a polynomial ring, a nonzero constant times a Laurent monomial in two distinct coordinates has an
`r`-th root only when `r` divides both exponents.  Equivalently: the torus chart obtained by
inverting two coordinates has no nontrivial cyclic cover realised inside the ambient rational
source field. -/
theorem dvd_exponents_of_kummer_root_mvPolynomial [DecidableEq σ]
    {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    {a b : σ} (hab : a ≠ b) {c : K} (hc : c ≠ 0) {i j : ℤ} {r : ℕ} (hr : 0 < r)
    {z : F} (hz : z ^ r = algebraMap (MvPolynomial σ K) F (C c)
      * (algebraMap (MvPolynomial σ K) F (X a)) ^ i
      * (algebraMap (MvPolynomial σ K) F (X b)) ^ j) :
    (r : ℤ) ∣ i ∧ (r : ℤ) ∣ j :=
  dvd_exponents_of_pow_eq_unit_mul_zpow_mul_zpow MvPolynomial.X_prime MvPolynomial.X_prime
    (not_associated_X_of_ne hab) ((MvPolynomial.C (σ := σ) (R := K)).isUnit_map hc.isUnit) hr hz

end MvPolynomialChart


end GaloisForLFunctions.HTGeometry
