import GaloisForLFunctions.HTGeometry.RationalNormalCone
import GaloisForLFunctions.HTGeometry.MonomialValuation

/-!
# The cone over the rational normal curve is normal

The exponent semigroup `coneExp d = {(a,b) : b ≤ d a}` is exactly the non-negative part of the
integer weight `w = (d, -1)`:

```text
weight w (a, b) = d a - b ≥ 0   ⟺   b ≤ d a .
```

So `rationalNormalCone K d = weightNonneg K (coneWeight d)`, and the lowest-weight argument of
`MonomialValuation.lean` applies verbatim: an element satisfying a monic equation over the cone ring
has non-negative minimal weight, hence lies in the cone ring.

```text
rationalNormalCone_eq_weightNonneg                    the identification
mem_rationalNormalCone_of_isIntegral                  integrally closed inside K[U,T]
mem_rationalNormalCone_of_monic_relation              the explicit form
exists_mem_rationalNormalCone_of_relation_fractionRing
    ** normal: an element of the fraction field integral over the cone ring is already in it **
```

The fraction-field statement uses that `K[U,T]` is a unique factorisation domain, hence integrally
closed, to place the element in `K[U,T]` first; the weight argument then finishes.

Together with `isCohenMacaulayRing_rationalNormalCone` this proves the card's clause "normal and
Cohen–Macaulay" for the last Hankel stratum `C_{m-1}`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {K : Type u} [Field K]

/-- The weight that cuts out the cone over the rational normal curve of degree `d`. -/
def coneWeight (d : ℕ) : Fin 2 → ℤ := ![(d : ℤ), -1]

theorem weight_coneWeight (d : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (coneWeight d) e = (d : ℤ) * (e 0 : ℤ) - (e 1 : ℤ) := by
  conv_lhs => rw [finsupp_fin2_eq e]
  rw [map_add, Finsupp.weight_single, Finsupp.weight_single]
  simp only [coneWeight, Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul]
  ring

/-- **The cone ring is the non-negative part of the weight `(d, -1)`.** -/
theorem rationalNormalCone_eq_weightNonneg (K : Type u) [Field K] (d : ℕ) :
    rationalNormalCone K d = weightNonneg K (coneWeight d) := by
  ext p
  rw [show (p ∈ rationalNormalCone K d) ↔ (↑p.support : Set (Fin 2 →₀ ℕ)) ⊆ coneExp d from
    mem_rationalNormalCone_iff, mem_weightNonneg_iff]
  constructor
  · intro h e he
    have hmem : e ∈ coneExp d := h (by simpa using he)
    have hnat : e 1 ≤ d * e 0 := hmem
    have hcast : ((e 1 : ℕ) : ℤ) ≤ ((d * e 0 : ℕ) : ℤ) := Nat.cast_le.mpr hnat
    push_cast at hcast
    rw [weight_coneWeight]
    linarith
  · intro h e he
    have hw := h e (by simpa using he)
    rw [weight_coneWeight] at hw
    show e 1 ≤ d * e 0
    have hcast : ((e 1 : ℕ) : ℤ) ≤ ((d * e 0 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hcast

/-- **The cone over the rational normal curve is normal**: it is integrally closed inside `K[U,T]`.
-/
theorem mem_rationalNormalCone_of_isIntegral {d : ℕ} {z : MvPolynomial (Fin 2) K}
    (hz : IsIntegral (rationalNormalCone K d) z) : z ∈ rationalNormalCone K d := by
  rw [rationalNormalCone_eq_weightNonneg K d] at hz ⊢
  exact mem_weightNonneg_of_isIntegral hz

/-- The same in explicit monic-relation form. -/
theorem mem_rationalNormalCone_of_monic_relation {d : ℕ} {z : MvPolynomial (Fin 2) K} {n : ℕ}
    (hn : 0 < n) (a : ℕ → MvPolynomial (Fin 2) K) (ha : ∀ j, a j ∈ rationalNormalCone K d)
    (heq : z ^ n + ∑ j ∈ Finset.range n, a j * z ^ j = 0) :
    z ∈ rationalNormalCone K d := by
  rw [rationalNormalCone_eq_weightNonneg K d] at ha ⊢
  exact mem_weightNonneg_of_monic_relation hn a ha heq

/-- The monic polynomial attached to an explicit integral relation. -/
noncomputable def relationPoly {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) : Polynomial R :=
  Polynomial.X ^ n + ∑ j ∈ Finset.range n, Polynomial.C (a j) * Polynomial.X ^ j

theorem relationPoly_monic {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) :
    (relationPoly a n).Monic := by
  refine Polynomial.monic_X_pow_add ?_
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro j hj
  have h1 : (Polynomial.C (a j) * Polynomial.X ^ j).degree ≤ (j : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_mul_le _ _) ?_
    calc (Polynomial.C (a j)).degree + (Polynomial.X ^ j : Polynomial R).degree
        ≤ 0 + (j : WithBot ℕ) :=
          add_le_add Polynomial.degree_C_le (Polynomial.degree_X_pow_le j)
      _ = (j : WithBot ℕ) := zero_add _
  refine lt_of_le_of_lt h1 ?_
  exact_mod_cast Finset.mem_range.mp hj

theorem eval₂_relationPoly {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : S)
    (a : ℕ → R) (n : ℕ) :
    Polynomial.eval₂ f z (relationPoly a n)
      = z ^ n + ∑ j ∈ Finset.range n, f (a j) * z ^ j := by
  simp [relationPoly, Polynomial.eval₂_finsetSum]

/-- **Normality of the cone in its fraction field.**  An element of the fraction field of `K[U,T]`
satisfying a monic equation with coefficients in the cone ring is the image of an element of the
cone ring.  The polynomial ring is a unique factorisation domain, hence integrally closed, so the
element is a polynomial; the weight argument then puts it in the cone. -/
theorem exists_mem_rationalNormalCone_of_relation_fractionRing {d : ℕ}
    {F : Type u} [Field F] [Algebra (MvPolynomial (Fin 2) K) F]
    [IsFractionRing (MvPolynomial (Fin 2) K) F]
    {z : F} {n : ℕ} (hn : 0 < n)
    (a : ℕ → MvPolynomial (Fin 2) K) (ha : ∀ j, a j ∈ rationalNormalCone K d)
    (heq : z ^ n + ∑ j ∈ Finset.range n,
      algebraMap (MvPolynomial (Fin 2) K) F (a j) * z ^ j = 0) :
    ∃ y ∈ rationalNormalCone K d, algebraMap (MvPolynomial (Fin 2) K) F y = z := by
  have hint : IsIntegral (MvPolynomial (Fin 2) K) z := by
    refine ⟨relationPoly a n, relationPoly_monic a n, ?_⟩
    rw [eval₂_relationPoly]
    exact heq
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_, hy⟩
  refine mem_rationalNormalCone_of_monic_relation hn a ha ?_
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) K) F) :=
    IsFractionRing.injective _ _
  refine hinj ?_
  rw [map_add, map_pow, map_zero, map_sum, hy]
  rw [← heq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, hy]


end GaloisForLFunctions.HTGeometry
