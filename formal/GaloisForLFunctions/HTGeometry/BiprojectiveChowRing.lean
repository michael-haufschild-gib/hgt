import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity

/-!
# The Chow ring of a product of two projective spaces

The Chow ring of `P^m × P^n` is the bigraded truncation

```text
ℤ[H₁, H₂] / (H₁^(m+1), H₂^(n+1)),
```

with `H₁, H₂` the two hyperplane classes.  A divisor of bidegree `(1,1)` has class `H₁ + H₂`, so a
complete intersection of `m + n` of them has class `(H₁ + H₂)^(m+n)`, and its degree is by definition
the coefficient of the top box monomial `H₁^m H₂^n`.

Here that degree is computed: every mixed term of the binomial expansion is killed by one of the two
truncations, and the surviving term is the one with `H₁`-exponent exactly `m`, so

```text
(H₁ + H₂)^(m+n) = choose (m+n) m · H₁^m H₂^n.
```

The coefficient is not merely *a* representation: the box monomials are torsion free, so the integer
`choose (m+n) m` is uniquely determined by the class.  Torsion freeness is proved by descending the
coefficient functional at a box exponent through the truncation ideal — a coefficient inside the box
cannot be produced by a multiple of `H₁^(m+1)` or of `H₂^(n+1)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-! ## A coefficient beyond the degree of a monomial factor -/

/-- **A monomial factor exceeding the exponent kills the coefficient.**  If a product carries a
factor `X i ^ k` with `k` larger than the `i`-th exponent of `d`, then the `d`-coefficient of the
product vanishes: every splitting of `d` in the convolution has to give `X i ^ k` its whole
exponent. -/
theorem coeff_mul_X_pow_eq_zero {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (d : σ →₀ ℕ) (i : σ) (k : ℕ) (hk : d i < k) (q : MvPolynomial σ R) :
    coeff d (q * X i ^ k) = 0 := by
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [MvPolynomial.coeff_X_pow]
  by_cases h : (Finsupp.single i k) = x.2
  · exfalso
    have hz : x.1 i + x.2 i = d i := by
      rw [← hx]
      simp [Finsupp.add_apply]
    have hx2 : x.2 i = k := by
      rw [← h]
      exact Finsupp.single_eq_same
    omega
  · rw [if_neg h, mul_zero]

/-! ## The truncation ideal -/

/-- The truncation ideal `(H₁^(m+1), H₂^(n+1))` of `P^m × P^n`. -/
noncomputable def chowIdeal (m n : ℕ) : Ideal (MvPolynomial (Fin 2) ℤ) :=
  Ideal.span {X 0 ^ (m + 1), X 1 ^ (n + 1)}

/-- The Chow ring of `P^m × P^n`. -/
abbrev ChowProd (m n : ℕ) := MvPolynomial (Fin 2) ℤ ⧸ chowIdeal m n

/-- The hyperplane class of the first factor. -/
noncomputable def chowH₁ (m n : ℕ) : ChowProd m n := Ideal.Quotient.mk (chowIdeal m n) (X 0)

/-- The hyperplane class of the second factor. -/
noncomputable def chowH₂ (m n : ℕ) : ChowProd m n := Ideal.Quotient.mk (chowIdeal m n) (X 1)

/-- The top box class `H₁^m H₂^n`, the fundamental class of a point. -/
noncomputable def chowTop (m n : ℕ) : ChowProd m n := chowH₁ m n ^ m * chowH₂ m n ^ n

/-- **The first truncation relation.** -/
theorem chowH₁_pow_eq_zero {m n k : ℕ} (hk : m < k) : chowH₁ m n ^ k = 0 := by
  have hmem : (X 0 : MvPolynomial (Fin 2) ℤ) ^ k ∈ chowIdeal m n := by
    obtain ⟨c, hc⟩ : (X 0 : MvPolynomial (Fin 2) ℤ) ^ (m + 1) ∣ X 0 ^ k :=
      pow_dvd_pow _ (by omega)
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  rw [chowH₁, ← map_pow]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem

/-- **The second truncation relation.** -/
theorem chowH₂_pow_eq_zero {m n k : ℕ} (hk : n < k) : chowH₂ m n ^ k = 0 := by
  have hmem : (X 1 : MvPolynomial (Fin 2) ℤ) ^ k ∈ chowIdeal m n := by
    obtain ⟨c, hc⟩ : (X 1 : MvPolynomial (Fin 2) ℤ) ^ (n + 1) ∣ X 1 ^ k :=
      pow_dvd_pow _ (by omega)
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [chowH₂, ← map_pow]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem

/-! ## Box coefficients -/

/-- The exponent of the box monomial `H₁^i H₂^j`. -/
noncomputable def chowBoxExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

theorem chowBoxExponent_apply_zero (i j : ℕ) : chowBoxExponent i j 0 = i := by
  rw [chowBoxExponent, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide), add_zero]

theorem chowBoxExponent_apply_one (i j : ℕ) : chowBoxExponent i j 1 = j := by
  rw [chowBoxExponent, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide), zero_add]

/-- **A box coefficient annihilates the truncation ideal.**  A coefficient whose two exponents both
stay inside the box cannot be produced by a multiple of either truncation generator. -/
theorem coeff_chowBoxExponent_eq_zero_of_mem {m n i j : ℕ} (hi : i ≤ m) (hj : j ≤ n)
    {p : MvPolynomial (Fin 2) ℤ} (hp : p ∈ chowIdeal m n) :
    coeff (chowBoxExponent i j) p = 0 := by
  simp only [chowIdeal] at hp
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hp
  rw [← hab, MvPolynomial.coeff_add,
    coeff_mul_X_pow_eq_zero _ _ _ (by rw [chowBoxExponent_apply_zero]; omega) a,
    coeff_mul_X_pow_eq_zero _ _ _ (by rw [chowBoxExponent_apply_one]; omega) b, add_zero]

/-- The box monomial has box coefficient one. -/
theorem coeff_chowBoxExponent_monomial (i j : ℕ) :
    coeff (chowBoxExponent i j) (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) ℤ) = 1 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial, chowBoxExponent,
    if_pos rfl]

/-- The box class as the image of the box monomial. -/
theorem chowH₁_pow_mul_chowH₂_pow (m n i j : ℕ) :
    chowH₁ m n ^ i * chowH₂ m n ^ j
      = Ideal.Quotient.mk (chowIdeal m n) (X 0 ^ i * X 1 ^ j) := by
  rw [chowH₁, chowH₂, ← map_pow, ← map_pow, ← map_mul]

/-- **The box classes are torsion free.**  No nonzero integer multiple of a box class vanishes, so
an integer read off from a class in the box is uniquely determined by that class. -/
theorem intCast_mul_chow_box_eq_zero_iff {m n i j : ℕ} (hi : i ≤ m) (hj : j ≤ n) (c : ℤ) :
    (c : ChowProd m n) * (chowH₁ m n ^ i * chowH₂ m n ^ j) = 0 ↔ c = 0 := by
  constructor
  · intro h
    rw [chowH₁_pow_mul_chowH₂_pow, ← map_intCast (Ideal.Quotient.mk (chowIdeal m n)) c,
      ← map_mul] at h
    have hmem := (Ideal.Quotient.eq_zero_iff_mem).1 h
    have hco := coeff_chowBoxExponent_eq_zero_of_mem (i := i) (j := j) hi hj hmem
    rw [← zsmul_eq_mul, MvPolynomial.coeff_smul, coeff_chowBoxExponent_monomial,
      smul_eq_mul, mul_one] at hco
    exact hco
  · rintro rfl
    rw [Int.cast_zero, zero_mul]

/-- **The top class is nonzero.** -/
theorem chowTop_ne_zero (m n : ℕ) : chowTop m n ≠ 0 := by
  intro h
  have := (intCast_mul_chow_box_eq_zero_iff (m := m) (n := n) le_rfl le_rfl 1).1 (by
    rw [Int.cast_one, one_mul]
    exact h)
  exact one_ne_zero this

/-! ## Freeness on the box -/

/-- Distinct box exponents are distinct. -/
theorem chowBoxExponent_inj {i j a b : ℕ} (h : chowBoxExponent i j = chowBoxExponent a b) :
    i = a ∧ j = b := by
  refine ⟨?_, ?_⟩
  · have h0 := congrArg (fun f => f (0 : Fin 2)) h
    simpa [chowBoxExponent_apply_zero] using h0
  · have h1 := congrArg (fun f => f (1 : Fin 2)) h
    simpa [chowBoxExponent_apply_one] using h1

/-- The box coefficients of a box monomial. -/
theorem coeff_chowBoxExponent_box (i j a b : ℕ) :
    coeff (chowBoxExponent a b) (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) ℤ)
      = if i = a ∧ j = b then 1 else 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
  by_cases h : i = a ∧ j = b
  · rw [if_pos h, if_pos]
    rw [h.1, h.2]
    rfl
  · rw [if_neg h, if_neg]
    intro hcon
    exact h (chowBoxExponent_inj (by rw [chowBoxExponent]; exact hcon))

/-- **The box classes are linearly independent over the integers.**  Hence the Chow ring is a free
abelian group on the box monomials, and an integer coefficient read off a class is unambiguous. -/
theorem chow_box_independent {m n : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : ∀ p ∈ s, p.1 ≤ m ∧ p.2 ≤ n) (c : ℕ × ℕ → ℤ)
    (h : ∑ p ∈ s, c p • (chowH₁ m n ^ p.1 * chowH₂ m n ^ p.2) = 0) :
    ∀ p ∈ s, c p = 0 := by
  intro q hq
  have hlift : (∑ p ∈ s, c p • ((X 0 : MvPolynomial (Fin 2) ℤ) ^ p.1 * X 1 ^ p.2))
      ∈ chowIdeal m n := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_zsmul, chowH₁_pow_mul_chowH₂_pow]
  have hco := coeff_chowBoxExponent_eq_zero_of_mem (i := q.1) (j := q.2)
    (hs q hq).1 (hs q hq).2 hlift
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single_of_mem q hq] at hco
  · rwa [MvPolynomial.coeff_smul, coeff_chowBoxExponent_box, if_pos ⟨rfl, rfl⟩,
      smul_eq_mul, mul_one] at hco
  · intro p _ hpq
    rw [MvPolynomial.coeff_smul, coeff_chowBoxExponent_box, if_neg, smul_zero]
    intro hcon
    exact hpq (Prod.ext hcon.1 hcon.2)

/-! ## The intersection degree -/

/-- **The class of a complete intersection of `m + n` divisors of bidegree `(1,1)`.**  Every mixed
term of the binomial expansion is killed by one of the two truncations, leaving exactly the top box
class with the binomial coefficient. -/
theorem chow_hyperplane_sum_pow (m n : ℕ) :
    (chowH₁ m n + chowH₂ m n) ^ (m + n)
      = ((criticalHorizonMultiplicity m n : ℤ) : ChowProd m n) * chowTop m n := by
  rw [add_pow, Finset.sum_eq_single m]
  · rw [Nat.add_sub_cancel_left, chowTop, criticalHorizonMultiplicity]
    push_cast
    ring
  · intro k hk hkm
    rcases lt_or_gt_of_ne hkm with h | h
    · rw [Finset.mem_range] at hk
      rw [chowH₂_pow_eq_zero (m := m) (n := n) (k := m + n - k) (by omega), mul_zero, zero_mul]
    · rw [chowH₁_pow_eq_zero (m := m) (n := n) (k := k) h, zero_mul, zero_mul]
  · intro hm
    exact absurd (Finset.mem_range.2 (by omega)) hm

/-- **The intersection degree is the critical horizon multiplicity, and nothing else.**  Any integer
expressing the complete intersection class as a multiple of the point class is the binomial
coefficient. -/
theorem chow_degree_unique {m n : ℕ} {c : ℤ}
    (h : (chowH₁ m n + chowH₂ m n) ^ (m + n) = (c : ChowProd m n) * chowTop m n) :
    c = criticalHorizonMultiplicity m n := by
  have h2 := chow_hyperplane_sum_pow m n
  rw [h] at h2
  have hsub : ((c - (criticalHorizonMultiplicity m n : ℤ) : ℤ) : ChowProd m n) * chowTop m n = 0 := by
    rw [Int.cast_sub, sub_mul, ← h2, sub_self]
  rw [chowTop] at hsub
  have := (intCast_mul_chow_box_eq_zero_iff (m := m) (n := n) le_rfl le_rfl _).1 hsub
  omega

end GaloisForLFunctions.HTGeometry
