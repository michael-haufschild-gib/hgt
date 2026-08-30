import Mathlib

/-!
# The monomial valuation of an integer weight, and normality of its non-negative part

Fix integer weights `w : σ → ℤ` on the variables.  For a nonzero polynomial let

```text
minWeight w p = min { weight w e : e ∈ supp p } .
```

The content of this file is that `minWeight` is **additive**:

```text
minWeight w (p * q) = minWeight w p + minWeight w q ,
```

which is the statement that the lowest-weight forms multiply without cancellation.  The proof is at
the level of coefficients: if `weight e = minWeight p + minWeight q` then every antidiagonal pair
contributing to `coeff e (p q)` has both entries of minimal weight, so `coeff e (p q)` equals
`coeff e (lowestForm p · lowestForm q)`, and the latter product is nonzero because the polynomial
ring over a field is a domain.

The consequence is the normality of the monomial algebra `weightNonneg K w` cut out by the single
inequality `weight ≥ 0`: if `z` satisfies a monic equation over that algebra and `minWeight z < 0`,
then the lowest form of `z ^ n` has weight `n · minWeight z`, while every other term of the equation
has weight at least `(n-1) · minWeight z`, which is strictly larger.  So

```text
mem_weightNonneg_of_isIntegral
    ** the weight-non-negative subalgebra is integrally closed in the polynomial ring **
```

Neither the valuation nor its additivity is in mathlib.  Applied to `w = (d, -1)` on two variables,
`weightNonneg` is the coordinate ring of the cone over the rational normal curve of degree `d`, so
this file supplies its normality.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The minimal weight attained on the support of a polynomial (zero for the zero polynomial). -/
noncomputable def minWeight (w : σ → ℤ) (p : MvPolynomial σ K) : ℤ :=
  if h : p.support.Nonempty then p.support.inf' h (fun e => Finsupp.weight w e) else 0

theorem minWeight_le {w : σ → ℤ} {p : MvPolynomial σ K} {e : σ →₀ ℕ} (he : e ∈ p.support) :
    minWeight w p ≤ Finsupp.weight w e := by
  have hne : p.support.Nonempty := ⟨e, he⟩
  rw [minWeight, dif_pos hne]
  exact Finset.inf'_le _ he

theorem exists_mem_support_weight_eq_minWeight {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ e ∈ p.support, Finsupp.weight w e = minWeight w p := by
  have hne : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨e, he, hval⟩ := Finset.exists_mem_eq_inf' hne (fun e => Finsupp.weight w e)
  refine ⟨e, he, ?_⟩
  rw [minWeight, dif_pos hne, ← hval]

theorem le_minWeight {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) {a : ℤ}
    (h : ∀ e ∈ p.support, a ≤ Finsupp.weight w e) : a ≤ minWeight w p := by
  obtain ⟨e, he, hval⟩ := exists_mem_support_weight_eq_minWeight (w := w) hp
  rw [← hval]
  exact h e he

/-- The lowest-weight form of a polynomial. -/
noncomputable def lowestForm (w : σ → ℤ) (p : MvPolynomial σ K) : MvPolynomial σ K :=
  weightedHomogeneousComponent w (minWeight w p) p

theorem lowestForm_ne_zero {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    lowestForm w p ≠ 0 := by
  classical
  obtain ⟨e, he, hval⟩ := exists_mem_support_weight_eq_minWeight (w := w) hp
  intro hcon
  have hc : MvPolynomial.coeff e (lowestForm w p) = MvPolynomial.coeff e p := by
    rw [lowestForm, coeff_weightedHomogeneousComponent, if_pos hval]
  rw [hcon] at hc
  simp only [MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp he) hc.symm

theorem coeff_lowestForm_of_weight_eq {w : σ → ℤ} {p : MvPolynomial σ K} {e : σ →₀ ℕ}
    (he : Finsupp.weight w e = minWeight w p) :
    MvPolynomial.coeff e (lowestForm w p) = MvPolynomial.coeff e p := by
  classical
  rw [lowestForm, coeff_weightedHomogeneousComponent, if_pos he]

theorem coeff_lowestForm_of_weight_ne {w : σ → ℤ} {p : MvPolynomial σ K} {e : σ →₀ ℕ}
    (he : Finsupp.weight w e ≠ minWeight w p) :
    MvPolynomial.coeff e (lowestForm w p) = 0 := by
  classical
  rw [lowestForm, coeff_weightedHomogeneousComponent, if_neg he]

theorem weight_eq_of_coeff_mul_ne_zero {w : σ → ℤ} {p q : MvPolynomial σ K}
    {e f g : σ →₀ ℕ} (hsum : f + g = e)
    (he : Finsupp.weight w e = minWeight w p + minWeight w q)
    (hne : MvPolynomial.coeff f p * MvPolynomial.coeff g q ≠ 0) :
    Finsupp.weight w f = minWeight w p ∧ Finsupp.weight w g = minWeight w q := by
  have hf : f ∈ p.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
  have hg : g ∈ q.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
  have hfw := minWeight_le (w := w) hf
  have hgw := minWeight_le (w := w) hg
  have hadd : Finsupp.weight w f + Finsupp.weight w g
      = minWeight w p + minWeight w q := by
    rw [← map_add, hsum, he]
  omega

theorem coeff_mul_eq_of_weight_eq {w : σ → ℤ} {p q : MvPolynomial σ K}
    {e : σ →₀ ℕ} (he : Finsupp.weight w e = minWeight w p + minWeight w q) :
    MvPolynomial.coeff e (p * q)
      = MvPolynomial.coeff e (lowestForm w p * lowestForm w q) := by
  classical
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨f, g⟩ hfg
  have hsum : f + g = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hfg
  by_cases hne : MvPolynomial.coeff f p * MvPolynomial.coeff g q = 0
  · rw [hne]
    by_cases hf : Finsupp.weight w f = minWeight w p
    · by_cases hg : Finsupp.weight w g = minWeight w q
      · rw [coeff_lowestForm_of_weight_eq hf, coeff_lowestForm_of_weight_eq hg, hne]
      · rw [coeff_lowestForm_of_weight_ne hg, mul_zero]
    · rw [coeff_lowestForm_of_weight_ne hf, zero_mul]
  · obtain ⟨hf, hg⟩ := weight_eq_of_coeff_mul_ne_zero hsum he hne
    rw [coeff_lowestForm_of_weight_eq hf, coeff_lowestForm_of_weight_eq hg]

/-- **The minimal weight is additive**: the lowest-weight forms multiply without cancellation. -/
theorem minWeight_mul {w : σ → ℤ} {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    minWeight w (p * q) = minWeight w p + minWeight w q := by
  classical
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  refine le_antisymm ?_ ?_
  · obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr
      (mul_ne_zero (lowestForm_ne_zero (w := w) hp) (lowestForm_ne_zero (w := w) hq))
    have hhom := MvPolynomial.IsWeightedHomogeneous.mul
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := w) (minWeight w p) p)
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := w) (minWeight w q) q)
    have hw : Finsupp.weight w e = minWeight w p + minWeight w q :=
      hhom (MvPolynomial.mem_support_iff.mp he)
    have hne : MvPolynomial.coeff e (p * q) ≠ 0 := by
      rw [coeff_mul_eq_of_weight_eq hw]
      exact MvPolynomial.mem_support_iff.mp he
    calc minWeight w (p * q) ≤ Finsupp.weight w e :=
          minWeight_le (MvPolynomial.mem_support_iff.mpr hne)
      _ = minWeight w p + minWeight w q := hw
  · refine le_minWeight hpq ?_
    intro e he
    have hmem := MvPolynomial.support_mul p q he
    rw [Finset.mem_add] at hmem
    obtain ⟨f, hf, g, hg, rfl⟩ := hmem
    rw [map_add]
    exact add_le_add (minWeight_le hf) (minWeight_le hg)

theorem minWeight_one {w : σ → ℤ} : minWeight w (1 : MvPolynomial σ K) = 0 := by
  have h1 : (1 : MvPolynomial σ K) ≠ 0 := one_ne_zero
  refine le_antisymm ?_ (le_minWeight h1 ?_)
  · have h0 : (0 : σ →₀ ℕ) ∈ (1 : MvPolynomial σ K).support := by
      rw [MvPolynomial.support_one]
      simp
    simpa using minWeight_le (w := w) h0
  · intro e he
    rw [MvPolynomial.support_one] at he
    have : e = 0 := by simpa using he
    simp [this]

theorem minWeight_pow {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) (n : ℕ) :
    minWeight w (p ^ n) = n * minWeight w p := by
  induction n with
  | zero => simpa using minWeight_one (w := w) (K := K)
  | succ n ih =>
    rw [pow_succ, minWeight_mul (pow_ne_zero n hp) hp, ih]
    push_cast
    ring


/-! ## The subalgebra of non-negative weight -/

/-- The exponent semigroup of non-negative weight. -/
def weightNonnegExp (w : σ → ℤ) : Set (σ →₀ ℕ) := {e | 0 ≤ Finsupp.weight w e}

/-- Polynomials all of whose monomials have non-negative weight. -/
noncomputable def weightNonneg (K : Type u) [Field K] (w : σ → ℤ) :
    Subalgebra K (MvPolynomial σ K) where
  carrier := {p : MvPolynomial σ K | ∀ e ∈ p.support, 0 ≤ Finsupp.weight w e}
  mul_mem' := by
    classical
    intro p q hp hq e he
    have hmem := MvPolynomial.support_mul p q he
    rw [Finset.mem_add] at hmem
    obtain ⟨f, hf, g, hg, rfl⟩ := hmem
    rw [map_add]
    exact add_nonneg (hp f hf) (hq g hg)
  one_mem' := by
    intro e he
    rw [MvPolynomial.support_one] at he
    have : e = 0 := by simpa using he
    simp [this]
  add_mem' := by
    classical
    intro p q hp hq e he
    have hmem := MvPolynomial.support_add (p := p) (q := q) (by simpa using he)
    rcases Finset.mem_union.mp hmem with h | h
    · exact hp e h
    · exact hq e h
  zero_mem' := by simp
  algebraMap_mem' := by
    classical
    intro r e he
    rw [MvPolynomial.algebraMap_eq] at he
    have hne := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_C] at hne
    have he0 : e = 0 := by
      by_contra h
      rw [if_neg (Ne.symm h)] at hne
      exact hne rfl
    simp [he0]

theorem mem_weightNonneg_iff {w : σ → ℤ} {p : MvPolynomial σ K} :
    p ∈ weightNonneg K w ↔ ∀ e ∈ p.support, 0 ≤ Finsupp.weight w e := Iff.rfl

theorem mem_weightNonneg_iff_minWeight {w : σ → ℤ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
    p ∈ weightNonneg K w ↔ 0 ≤ minWeight w p := by
  constructor
  · intro h
    exact le_minWeight hp (fun e he => h e he)
  · intro h e he
    exact le_trans h (minWeight_le he)

/-- **The lowest-weight argument.**  A monic relation with coefficients of non-negative weight
forces the root to have non-negative weight: the lowest form of `z ^ n` has weight `n · μ`, while
every term `a_j z ^ j` has weight at least `j · μ ≥ (n-1) · μ`, and `n μ ≥ (n-1) μ` fails for
`μ < 0`. -/
theorem mem_weightNonneg_of_monic_relation {w : σ → ℤ} {z : MvPolynomial σ K} {n : ℕ} (_hn : 0 < n)
    (a : ℕ → MvPolynomial σ K) (ha : ∀ j, a j ∈ weightNonneg K w)
    (heq : z ^ n + ∑ j ∈ Finset.range n, a j * z ^ j = 0) :
    z ∈ weightNonneg K w := by
  classical
  by_cases hz : z = 0
  · rw [hz]; exact Subalgebra.zero_mem _
  by_contra hcon
  have hmw : minWeight w z < 0 := by
    by_contra h
    rw [not_lt] at h
    exact hcon ((mem_weightNonneg_iff_minWeight hz).mpr h)
  have hzn : z ^ n ≠ 0 := pow_ne_zero n hz
  obtain ⟨e, he, hew⟩ := exists_mem_support_weight_eq_minWeight (w := w) hzn
  rw [minWeight_pow hz n] at hew
  have hsum : z ^ n = - ∑ j ∈ Finset.range n, a j * z ^ j := by
    rw [eq_neg_iff_add_eq_zero]; exact heq
  have hce : MvPolynomial.coeff e (z ^ n) ≠ 0 := MvPolynomial.mem_support_iff.mp he
  rw [hsum, MvPolynomial.coeff_neg, neg_ne_zero, MvPolynomial.coeff_sum] at hce
  obtain ⟨j, hj, hcj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hce
  have hjn : j < n := Finset.mem_range.mp hj
  have hprod : a j * z ^ j ≠ 0 := fun h => hcj (by rw [h, MvPolynomial.coeff_zero])
  have haj : a j ≠ 0 := left_ne_zero_of_mul hprod
  have hzj : z ^ j ≠ 0 := pow_ne_zero j hz
  have hlow : minWeight w (a j * z ^ j) ≤ Finsupp.weight w e :=
    minWeight_le (MvPolynomial.mem_support_iff.mpr hcj)
  rw [minWeight_mul haj hzj, minWeight_pow hz j] at hlow
  have haj0 : 0 ≤ minWeight w (a j) := (mem_weightNonneg_iff_minWeight haj).mp (ha j)
  rw [hew] at hlow
  have hkey : ((n : ℤ) - (j : ℤ)) * minWeight w z ≥ 0 := by
    have : (j : ℤ) * minWeight w z ≤ (n : ℤ) * minWeight w z := by linarith
    linarith [this]
  have hge1 : (1 : ℤ) ≤ (n : ℤ) - (j : ℤ) := by
    have : (j : ℤ) < (n : ℤ) := by exact_mod_cast hjn
    linarith
  nlinarith [hkey, hge1, hmw]


/-- **The weight-non-negative subalgebra is integrally closed inside the polynomial ring.**  This is
the normality of a monomial algebra cut out by a single weight inequality: a saturated exponent
semigroup has no new integral elements. -/
theorem mem_weightNonneg_of_isIntegral {w : σ → ℤ} {z : MvPolynomial σ K}
    (hz : IsIntegral (weightNonneg K w) z) : z ∈ weightNonneg K w := by
  obtain ⟨P, hmonic, hroot⟩ := hz
  by_cases hn : P.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic hn, Polynomial.eval₂_one] at hroot
    exact absurd hroot one_ne_zero
  · rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree,
      map_one, one_mul] at hroot
    refine mem_weightNonneg_of_monic_relation (n := P.natDegree) (Nat.pos_of_ne_zero hn)
      (fun j => (algebraMap (weightNonneg K w) (MvPolynomial σ K)) (P.coeff j))
      (fun j => (P.coeff j).2) ?_
    rw [add_comm]
    exact hroot


end GaloisForLFunctions.HTGeometry
