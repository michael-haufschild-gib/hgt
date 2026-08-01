import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Prod

/-!
# Kummer exponents against two independent valuations

A cyclic Kummer relation `z ^ r = c * p ^ a * q ^ b` is tested by any homomorphism from the ambient
group to the integers.  If one such homomorphism sees `p` with value one and `q` with value zero, and
a second sees them the other way round, while both vanish on `c`, then reading the relation through
the two homomorphisms gives `r ∣ a` and `r ∣ b`.  So a relation whose exponent pair is not divisible
by the degree cannot exist.

The situation this describes is a two-dimensional torus times an affine space: the coordinate ring's
units are a constant times two monomial exponents, and the two homomorphisms are the two exponents.
Over an algebraically closed field the constant is never an obstruction, so in that group the `r`-th
powers are **exactly** the elements whose two exponents are divisible by `r`.  Both directions are
proved, so the obstruction is sharp and the hypotheses are inhabited.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Two independent valuations -/

variable {G : Type*} [CommGroup G]

/-- **One valuation divides one exponent.**  Reading a Kummer relation through a homomorphism that
sees the first base element once, the second not at all, and the constant not at all, gives the
exponent of the first base element as a multiple of the degree. -/
theorem dvd_of_kummer_relation_left (v : G →* Multiplicative ℤ) {z c p q : G} {r : ℕ} {a b : ℤ}
    (hz : z ^ r = c * p ^ a * q ^ b) (hcv : v c = 1)
    (hpv : v p = Multiplicative.ofAdd (1 : ℤ)) (hqv : v q = 1) :
    (r : ℤ) ∣ a := by
  have h := congrArg (fun x : G => (v x).toAdd) hz
  simp only [map_mul, map_pow, map_zpow, hcv, hpv, hqv, one_zpow, one_mul, mul_one,
    toAdd_pow, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_one] at h
  exact ⟨(v z).toAdd, h.symm⟩

/-- **Two independent valuations divide both exponents.** -/
theorem dvd_of_kummer_relation (v w : G →* Multiplicative ℤ) {z c p q : G} {r : ℕ} {a b : ℤ}
    (hz : z ^ r = c * p ^ a * q ^ b)
    (hcv : v c = 1) (hpv : v p = Multiplicative.ofAdd (1 : ℤ)) (hqv : v q = 1)
    (hcw : w c = 1) (hpw : w p = 1) (hqw : w q = Multiplicative.ofAdd (1 : ℤ)) :
    (r : ℤ) ∣ a ∧ (r : ℤ) ∣ b := by
  refine ⟨dvd_of_kummer_relation_left v hz hcv hpv hqv, ?_⟩
  refine dvd_of_kummer_relation_left w (z := z) (c := c) (p := q) (q := p) (a := b) (b := a)
    ?_ hcw hqw hpw
  rw [hz, mul_right_comm]

/-- **A Kummer relation with an exponent pair not divisible by the degree does not exist.**  This is
the obstruction in the form the monodromy argument uses: two divisors seeing the two base elements
separately force both exponents to be divisible, so a cover whose exponent pair is nontrivial modulo
the degree cannot occur. -/
theorem not_exists_kummer_relation (v w : G →* Multiplicative ℤ) {p q : G} {r : ℕ} {a b : ℤ}
    (hpv : v p = Multiplicative.ofAdd (1 : ℤ)) (hqv : v q = 1)
    (hpw : w p = 1) (hqw : w q = Multiplicative.ofAdd (1 : ℤ))
    (hab : ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b)) :
    ¬ ∃ z c : G, v c = 1 ∧ w c = 1 ∧ z ^ r = c * p ^ a * q ^ b := by
  rintro ⟨z, c, hcv, hcw, hz⟩
  exact hab (dvd_of_kummer_relation v w hz hcv hpv hqv hcw hpw hqw)

/-! ## Powers of the generator -/

theorem ofAdd_one_zpow (n : ℤ) : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
  rw [← ofAdd_zsmul, smul_eq_mul, mul_one]

theorem ofAdd_pow_nat (a : ℤ) (r : ℕ) :
    (Multiplicative.ofAdd a) ^ r = Multiplicative.ofAdd ((r : ℤ) * a) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul]

/-! ## The unit group of a two-dimensional torus times an affine space -/

/-- The units of the coordinate ring of `(𝔾ₘ)² × 𝔸ᵏ`: a constant together with the two monomial
exponents. -/
abbrev TorusUnitGroup (K : Type*) [Field K] : Type _ :=
  Kˣ × Multiplicative ℤ × Multiplicative ℤ

/-- The exponent of the first torus coordinate. -/
def torusVal₁ (K : Type*) [Field K] : TorusUnitGroup K →* Multiplicative ℤ where
  toFun u := u.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The exponent of the second torus coordinate. -/
def torusVal₂ (K : Type*) [Field K] : TorusUnitGroup K →* Multiplicative ℤ where
  toFun u := u.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The first torus coordinate as a unit. -/
def torusGen₁ (K : Type*) [Field K] : TorusUnitGroup K :=
  (1, Multiplicative.ofAdd (1 : ℤ), 1)

/-- The second torus coordinate as a unit. -/
def torusGen₂ (K : Type*) [Field K] : TorusUnitGroup K :=
  (1, 1, Multiplicative.ofAdd (1 : ℤ))

theorem torusVal₁_gen₁ (K : Type*) [Field K] :
    torusVal₁ K (torusGen₁ K) = Multiplicative.ofAdd (1 : ℤ) := rfl

theorem torusVal₁_gen₂ (K : Type*) [Field K] : torusVal₁ K (torusGen₂ K) = 1 := rfl

theorem torusVal₂_gen₁ (K : Type*) [Field K] : torusVal₂ K (torusGen₁ K) = 1 := rfl

theorem torusVal₂_gen₂ (K : Type*) [Field K] :
    torusVal₂ K (torusGen₂ K) = Multiplicative.ofAdd (1 : ℤ) := rfl

/-- **Every unit is a constant times the two coordinates raised to its exponents.** -/
theorem torusUnit_eq (K : Type*) [Field K] (u : TorusUnitGroup K) :
    u = ((u.1, 1, 1) : TorusUnitGroup K) *
      torusGen₁ K ^ (u.2.1).toAdd * torusGen₂ K ^ (u.2.2).toAdd := by
  simp [torusGen₁, torusGen₂, ofAdd_one_zpow]

/-- **The `r`-th powers are exactly the units whose two exponents are divisible by `r`.**  The
constant never obstructs, because an algebraically closed field has all roots. -/
theorem exists_pow_eq_torusUnit_iff {K : Type*} [Field K] [IsAlgClosed K] {r : ℕ} (hr : 0 < r)
    (u : TorusUnitGroup K) :
    (∃ z : TorusUnitGroup K, z ^ r = u) ↔
      ((r : ℤ) ∣ (torusVal₁ K u).toAdd ∧ (r : ℤ) ∣ (torusVal₂ K u).toAdd) := by
  constructor
  · rintro ⟨z, hz⟩
    refine dvd_of_kummer_relation (torusVal₁ K) (torusVal₂ K)
      (z := z) (c := (u.1, 1, 1)) (p := torusGen₁ K) (q := torusGen₂ K) ?_ rfl rfl rfl rfl rfl rfl
    rw [hz]
    exact torusUnit_eq K u
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq ((u.1 : K)) hr
    have hκ0 : κ ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega)] at hκ
      exact u.1.ne_zero hκ.symm
    refine ⟨(Units.mk0 κ hκ0, Multiplicative.ofAdd a, Multiplicative.ofAdd b), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (Units.mk0 κ hκ0) ^ r = u.1
      refine Units.ext ?_
      simpa using hκ
    · show (Multiplicative.ofAdd a) ^ r = u.2.1
      rw [ofAdd_pow_nat]
      have hval : ((r : ℤ) * a) = (u.2.1).toAdd := ha.symm
      rw [hval, ofAdd_toAdd]
    · show (Multiplicative.ofAdd b) ^ r = u.2.2
      rw [ofAdd_pow_nat]
      have hval : ((r : ℤ) * b) = (u.2.2).toAdd := hb.symm
      rw [hval, ofAdd_toAdd]

/-- **No nontrivial cyclic cover of the torus.**  A Kummer relation with an exponent pair that is
nontrivial modulo the degree has no solution in the unit group, at any constant. -/
theorem not_exists_pow_eq_torusUnit {K : Type*} [Field K] [IsAlgClosed K] {r : ℕ} (hr : 0 < r)
    {a b : ℤ} (hab : ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b)) (c : Kˣ) :
    ¬ ∃ z : TorusUnitGroup K,
      z ^ r = ((c, Multiplicative.ofAdd a, Multiplicative.ofAdd b) : TorusUnitGroup K) := by
  intro h
  exact hab ((exists_pow_eq_torusUnit_iff hr _).1 h)

end GaloisForLFunctions.HTGeometry
