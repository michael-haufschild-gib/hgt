import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Units of a localization away from two primes

Inverting a product of two primes of a unique factorization domain produces a ring whose units are
exactly the constants times integer powers of the two primes: a unit of the localization, cleared of
its denominator, divides a power of the inverted element, and a divisor of a product of powers of two
primes is a unit times powers of those two primes.

This is the coordinate ring of a two-dimensional torus times an affine space, presented as a
localization, and the statement is the description of its unit group that the classification of its
cyclic covers rests on.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-! ## Divisors of a product of prime powers -/

/-- **A divisor of a product of powers of two primes is a unit times powers of those primes.** -/
theorem exists_unit_mul_pow_mul_pow_of_dvd {p q a : A} (hp : Prime p) (hq : Prime q) {m k : ℕ}
    (h : a ∣ p ^ m * q ^ k) :
    ∃ (c : Aˣ) (s t : ℕ), a = c * p ^ s * q ^ t := by
  obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  obtain ⟨s, -, u₁, hu₁⟩ := (dvd_prime_pow hp m).1 hb₁
  obtain ⟨t, -, u₂, hu₂⟩ := (dvd_prime_pow hq k).1 hb₂
  refine ⟨(u₁ * u₂)⁻¹, s, t, ?_⟩
  have key : (p : A) ^ s * q ^ t = ((u₁ * u₂ : Aˣ) : A) * (b₁ * b₂) := by
    rw [Units.val_mul, ← hu₁, ← hu₂]
    ring
  rw [mul_assoc, key, Units.inv_mul_cancel_left]

/-! ## Units of the localization -/

variable (R : Type*) [CommRing R] [Algebra A R]

omit [UniqueFactorizationMonoid A] in
/-- **An element of the base whose image in the localization is a unit divides a power of the
inverted element.** -/
theorem dvd_pow_of_isUnit_algebraMap {f a : A} (hf : f ≠ 0) [IsLocalization.Away f R]
    (h : IsUnit (algebraMap A R a)) :
    ∃ k : ℕ, a ∣ f ^ k := by
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R
      (Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hf))
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨k, b', hb'⟩ := IsLocalization.Away.surj (S := R) f b
  refine ⟨k, b', hinj ?_⟩
  rw [map_mul, ← hb', ← mul_assoc, hb, one_mul, map_pow]

/-- **Every unit of the localization away from a product of two primes is a constant times a Laurent
monomial in the two primes.**  Cleared of its denominator, a unit is the image of an element of the
base dividing a power of the inverted product, and such an element is a unit times powers of the two
primes. -/
theorem exists_monomial_of_isUnit_away {p q : A} (hp : Prime p) (hq : Prime q)
    [IsLocalization.Away (p * q) R] (u : Rˣ) :
    ∃ (c : Aˣ) (s t n : ℕ),
      (u : R) * algebraMap A R (p * q) ^ n = algebraMap A R ((c : A) * p ^ s * q ^ t) := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := R) (p * q) (u : R)
  have hunit : IsUnit (algebraMap A R a) := by
    rw [← ha]
    exact u.isUnit.mul ((IsLocalization.map_units R
      (⟨p * q, Submonoid.mem_powers _⟩ : Submonoid.powers (p * q))).pow n)
  obtain ⟨k, hk⟩ := dvd_pow_of_isUnit_algebraMap R hpq hunit
  rw [mul_pow] at hk
  obtain ⟨c, s, t, hc⟩ := exists_unit_mul_pow_mul_pow_of_dvd hp hq hk
  exact ⟨c, s, t, n, by rw [ha, hc]⟩

/-! ## Uniqueness of the exponents -/

variable {R}

omit [UniqueFactorizationMonoid A] in
/-- **Distinct primes stay distinct in a product of powers.**  If a unit times a product of powers of
two non-associate primes equals another such product, the exponents of the first prime agree. -/
theorem exponent_eq_of_unit_mul_pow_mul_pow {p q : A} (hp : Prime p) (hq : Prime q)
    (hpq : ¬ Associated p q) {c c' : Aˣ} {a b a' b' : ℕ}
    (h : (c : A) * p ^ a * q ^ b = (c' : A) * p ^ a' * q ^ b') :
    a = a' := by
  have hpdvd : ¬ (p ∣ q) := fun hd => hpq (hp.associated_of_dvd hq hd)
  have hnc : ∀ (d : Aˣ) (m : ℕ), ¬ (p ∣ (d : A) * q ^ m) := by
    intro d m hd
    rcases hp.dvd_mul.1 hd with h1 | h2
    · exact hp.not_unit (isUnit_of_dvd_unit h1 d.isUnit)
    · exact hpdvd (hp.dvd_of_dvd_pow h2)
  have key : ∀ {d e : Aˣ} {i j i' j' : ℕ},
      (d : A) * p ^ i * q ^ j = (e : A) * p ^ i' * q ^ j' → i < i' → False := by
    intro d e i j i' j' heq hlt
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    subst hk
    have hp0 : (p : A) ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hcancel : (d : A) * q ^ j = (e : A) * p ^ (k + 1) * q ^ j' := by
      refine mul_left_cancel₀ hp0 ?_
      calc (p : A) ^ i * ((d : A) * q ^ j) = (d : A) * p ^ i * q ^ j := by ring
        _ = (e : A) * p ^ (i + k + 1) * q ^ j' := heq
        _ = (p : A) ^ i * ((e : A) * p ^ (k + 1) * q ^ j') := by ring
    refine hnc d j ⟨(e : A) * p ^ k * q ^ j', ?_⟩
    rw [hcancel]
    ring
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd hlt (fun hl => absurd (key h hl) (fun x => x))
  · exact heq
  · exact absurd (key h.symm hgt) (fun x => x)

omit [UniqueFactorizationMonoid A] in
/-- **A unit times a product of powers of two non-associate primes determines both exponents and the
unit.** -/
theorem eq_of_unit_mul_pow_mul_pow {p q : A} (hp : Prime p) (hq : Prime q)
    (hpq : ¬ Associated p q) {c c' : Aˣ} {a b a' b' : ℕ}
    (h : (c : A) * p ^ a * q ^ b = (c' : A) * p ^ a' * q ^ b') :
    a = a' ∧ b = b' ∧ c = c' := by
  have ha : a = a' := exponent_eq_of_unit_mul_pow_mul_pow hp hq hpq h
  have hswap : (c : A) * q ^ b * p ^ a = (c' : A) * q ^ b' * p ^ a' := by
    rw [show (c : A) * q ^ b * p ^ a = (c : A) * p ^ a * q ^ b from by ring, h]
    ring
  have hb : b = b' :=
    exponent_eq_of_unit_mul_pow_mul_pow hq hp (fun hcon => hpq hcon.symm) hswap
  subst ha
  subst hb
  refine ⟨rfl, rfl, ?_⟩
  have hx : (q : A) ^ b ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hy : (p : A) ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  exact Units.ext (mul_right_cancel₀ hy (mul_right_cancel₀ hx h))

/-! ## The exponents of a unit of the localization -/

omit [UniqueFactorizationMonoid A] in
/-- **The exponents of a unit of the localization are well defined.**  Two presentations of the same
unit as a constant times a Laurent monomial in the two primes have the same exponent differences and
the same constant. -/
theorem exponents_unique_away {p q : A} (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q)
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.Away (p * q) R] {u : Rˣ}
    {c c' : Aˣ} {s t n s' t' n' : ℕ}
    (h : (u : R) * algebraMap A R (p * q) ^ n = algebraMap A R ((c : A) * p ^ s * q ^ t))
    (h' : (u : R) * algebraMap A R (p * q) ^ n' = algebraMap A R ((c' : A) * p ^ s' * q ^ t')) :
    s + n' = s' + n ∧ t + n' = t' + n ∧ c = c' := by
  have hpq0 : (p * q : A) ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R (Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hpq0))
  have hbig : algebraMap A R ((c : A) * p ^ s * q ^ t) * algebraMap A R (p * q) ^ n'
      = algebraMap A R ((c' : A) * p ^ s' * q ^ t') * algebraMap A R (p * q) ^ n := by
    rw [← h, ← h']
    ring
  have hA : (c : A) * p ^ (s + n') * q ^ (t + n') = (c' : A) * p ^ (s' + n) * q ^ (t' + n) := by
    refine hinj ?_
    simp only [map_mul, map_pow, mul_pow] at hbig ⊢
    linear_combination hbig
  obtain ⟨h1, h2, h3⟩ := eq_of_unit_mul_pow_mul_pow hp hq hpq hA
  exact ⟨h1, h2, h3⟩

/-! ## Powers and the exponents -/

variable (R : Type*) [CommRing R] [Algebra A R]

omit [IsDomain A] [UniqueFactorizationMonoid A] in
/-- **The first prime becomes a unit in the localization.** -/
theorem isUnit_algebraMap_left (p q : A) [IsLocalization.Away (p * q) R] :
    IsUnit (algebraMap A R p) := by
  have h : IsUnit (algebraMap A R (p * q)) :=
    IsLocalization.map_units R (⟨p * q, Submonoid.mem_powers _⟩ : Submonoid.powers (p * q))
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

omit [IsDomain A] [UniqueFactorizationMonoid A] in
/-- **And so does the second.** -/
theorem isUnit_algebraMap_right (p q : A) [IsLocalization.Away (p * q) R] :
    IsUnit (algebraMap A R q) := by
  have h : IsUnit (algebraMap A R (p * q)) :=
    IsLocalization.map_units R (⟨p * q, Submonoid.mem_powers _⟩ : Submonoid.powers (p * q))
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

variable {R}

omit [UniqueFactorizationMonoid A] in
/-- **An `r`-th power has both exponents divisible by `r`.**  Raising a presentation of the root to
the `r`-th power presents the element itself, and the presentation data is unique, so the two exponent
differences of the element are `r` times those of the root.

This is the obstruction `(15)--(17)` in the form the classification needs: a cyclic radical extension
of degree `r` generated by a unit whose exponent pair is nontrivial modulo `r` does not exist. -/
theorem dvd_exponents_of_eq_pow {p q : A} (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q)
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.Away (p * q) R]
    {u w : Rˣ} {r : ℕ} (hw : u = w ^ r)
    {c c' : Aˣ} {s t n s' t' n' : ℕ}
    (h : (u : R) * algebraMap A R (p * q) ^ n = algebraMap A R ((c : A) * p ^ s * q ^ t))
    (h' : (w : R) * algebraMap A R (p * q) ^ n' = algebraMap A R ((c' : A) * p ^ s' * q ^ t')) :
    (r : ℤ) ∣ ((s : ℤ) - (n : ℤ)) ∧ (r : ℤ) ∣ ((t : ℤ) - (n : ℤ)) := by
  have hupow : (u : R) = (w : R) ^ r := by
    rw [hw, Units.val_pow_eq_pow_val]
  have hpow : (u : R) * algebraMap A R (p * q) ^ (r * n')
      = algebraMap A R (((c' ^ r : Aˣ) : A) * p ^ (r * s') * q ^ (r * t')) := by
    have hr := congrArg (fun x : R => x ^ r) h'
    simp only [mul_pow, ← pow_mul] at hr
    rw [hupow, mul_comm n' r] at *
    rw [hr, ← map_pow]
    congr 1
    rw [Units.val_pow_eq_pow_val]
    ring
  obtain ⟨h1, h2, -⟩ := exponents_unique_away hp hq hpq R h hpow
  refine ⟨⟨(s' : ℤ) - (n' : ℤ), ?_⟩, ⟨(t' : ℤ) - (n' : ℤ), ?_⟩⟩
  · have hcast : (s : ℤ) + (r : ℤ) * (n' : ℤ) = (r : ℤ) * (s' : ℤ) + (n : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h1
    linear_combination hcast
  · have hcast : (t : ℤ) + (r : ℤ) * (n' : ℤ) = (r : ℤ) * (t' : ℤ) + (n : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h2
    linear_combination hcast

/-! ## The chart of a two-dimensional torus times an affine space -/

open MvPolynomial

/-- The coordinate ring of `(𝔾ₘ)² × 𝔸ᴸ`: the polynomial ring in `L + 2` variables with the first two
coordinates inverted. -/
abbrev TorusChart (K : Type*) [Field K] (L : ℕ) : Type _ :=
  Localization.Away ((X 0 * X 1 : MvPolynomial (Fin (L + 2)) K))

/-- **Every unit of the chart is a nonzero constant times a Laurent monomial in the two invertible
coordinates.**  This is the unit group of `(𝔾ₘ)² × 𝔸ᴸ`. -/
theorem exists_monomial_of_isUnit_torusChart {K : Type*} [Field K] {L : ℕ}
    (u : (TorusChart K L)ˣ) :
    ∃ (c : K) (s t n : ℕ), IsUnit c ∧
      (u : TorusChart K L) *
          algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L) (X 0 * X 1) ^ n
        = algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L)
            (C c * X 0 ^ s * X 1 ^ t) := by
  obtain ⟨c, s, t, n, h⟩ :=
    exists_monomial_of_isUnit_away (A := MvPolynomial (Fin (L + 2)) K) (R := TorusChart K L)
      (p := X 0) (q := X 1) MvPolynomial.X_prime MvPolynomial.X_prime u
  obtain ⟨r, hr, hcr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 c.isUnit
  exact ⟨r, s, t, n, hr, by rw [h, hcr]⟩

/-- **The two inverted coordinates are not associate.** -/
theorem not_associated_X_zero_X_one {K : Type*} [Field K] {L : ℕ} :
    ¬ Associated (X (0 : Fin (L + 2)) : MvPolynomial (Fin (L + 2)) K) (X 1) := by
  rintro ⟨u, hu⟩
  obtain ⟨r, -, hcr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [hcr] at hu
  have hne : (1 : Fin (L + 2)) ≠ 0 := by simp
  have hzero : MvPolynomial.degreeOf (1 : Fin (L + 2))
      (X (0 : Fin (L + 2)) * C r : MvPolynomial (Fin (L + 2)) K) = 0 := by
    refine Nat.le_zero.1 (le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_)
    rw [MvPolynomial.degreeOf_X_of_ne hne, MvPolynomial.degreeOf_C]
  rw [hu, MvPolynomial.degreeOf_X] at hzero
  exact one_ne_zero hzero

/-- **The exponents of an `r`-th power in the chart are divisible by `r`.**  This is `(15)--(17)` for
`(𝔾ₘ)² × 𝔸ᴸ`: a unit that is an `r`-th power has both monomial exponents divisible by `r`, so a
cyclic cover whose exponent pair is nontrivial modulo `r` does not exist. -/
theorem dvd_exponents_of_eq_pow_torusChart {K : Type*} [Field K] {L : ℕ}
    {u w : (TorusChart K L)ˣ} {r : ℕ} (hw : u = w ^ r)
    {c c' : (MvPolynomial (Fin (L + 2)) K)ˣ} {s t n s' t' n' : ℕ}
    (h : (u : TorusChart K L) *
        algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L) (X 0 * X 1) ^ n
      = algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L)
          ((c : MvPolynomial (Fin (L + 2)) K) * X 0 ^ s * X 1 ^ t))
    (h' : (w : TorusChart K L) *
        algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L) (X 0 * X 1) ^ n'
      = algebraMap (MvPolynomial (Fin (L + 2)) K) (TorusChart K L)
          ((c' : MvPolynomial (Fin (L + 2)) K) * X 0 ^ s' * X 1 ^ t')) :
    (r : ℤ) ∣ ((s : ℤ) - (n : ℤ)) ∧ (r : ℤ) ∣ ((t : ℤ) - (n : ℤ)) :=
  dvd_exponents_of_eq_pow MvPolynomial.X_prime MvPolynomial.X_prime not_associated_X_zero_X_one
    (TorusChart K L) hw h h'

end GaloisForLFunctions.HTGeometry
