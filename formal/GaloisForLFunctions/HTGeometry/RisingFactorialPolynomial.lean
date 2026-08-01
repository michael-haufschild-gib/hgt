import GaloisForLFunctions.HTGeometry.RationalOrderBound

/-!
# The rising factorial as a polynomial

The expansion of a polygamma jet to a given depth is an algebraic induction: at each step the
remainder is a rational function whose numerator is a polynomial and whose denominator is a power of
the argument times rising factorials.  Carrying the numerator as a `Polynomial ℂ` makes the degree
bookkeeping — which is what controls the decay order — exact.

Here the rising factorial is realized as a monic polynomial of its length, evaluating to the
analytic rising factorial.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The rising factorial as a polynomial. -/
noncomputable def risingPoly (m : ℕ) : Polynomial ℂ :=
  ∏ j ∈ Finset.range m, (Polynomial.X + Polynomial.C (j : ℂ))

@[simp] theorem risingPoly_eval (x : ℂ) (m : ℕ) : (risingPoly m).eval x = risingProd x m := by
  rw [risingPoly, risingProd, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

theorem risingPoly_monic (m : ℕ) : (risingPoly m).Monic := by
  rw [risingPoly]
  refine Polynomial.monic_prod_of_monic _ _ fun j _ => ?_
  exact Polynomial.monic_X_add_C _

@[simp] theorem risingPoly_natDegree (m : ℕ) : (risingPoly m).natDegree = m := by
  have h := Polynomial.natDegree_prod_of_monic (R := ℂ) (Finset.range m)
    (fun j : ℕ => Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
    (fun j _ => Polynomial.monic_X_add_C _)
  rw [risingPoly, h]
  have hcongr : ∀ j ∈ Finset.range m,
      (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ)).natDegree = 1 := by
    intro j _
    exact Polynomial.natDegree_X_add_C _
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem risingPoly_ne_zero (m : ℕ) : risingPoly m ≠ 0 := (risingPoly_monic m).ne_zero

/-- The monomial-times-rising-factorial polynomials are monic of the total degree. -/
theorem monic_X_pow_mul_risingPoly (a b : ℕ) :
    (Polynomial.X ^ a * risingPoly b).Monic :=
  (Polynomial.monic_X_pow a).mul (risingPoly_monic b)

@[simp] theorem natDegree_X_pow_mul_risingPoly (a b : ℕ) :
    (Polynomial.X ^ a * risingPoly b).natDegree = a + b := by
  rw [Polynomial.natDegree_mul (Polynomial.monic_X_pow a).ne_zero (risingPoly_ne_zero b),
    Polynomial.natDegree_X_pow, risingPoly_natDegree]

/-- **The expansion step.**  Subtracting the leading reciprocal rising factorial lowers the numerator
degree by one, hence raises the decay order by one.  The new numerator is explicit. -/
theorem expansion_step (P : Polynomial ℂ) (d a b p : ℕ) (hp : 1 ≤ p) (hab : a + b = d + p)
    (hdeg : P.natDegree ≤ d) :
    ∃ Q : Polynomial ℂ, Q.natDegree + 1 ≤ a + b ∧
      ∀ x : ℂ, 0 < x.re →
        P.eval x / (x ^ a * risingProd x b) - P.coeff d * (risingProd x p)⁻¹
          = Q.eval x / (x ^ a * risingProd x b * risingProd x p) := by
  classical
  set c : ℂ := P.coeff d with hc
  set Q : Polynomial ℂ :=
    P * risingPoly p - Polynomial.C c * (Polynomial.X ^ a * risingPoly b) with hQ
  have habpos : 1 ≤ a + b := by omega
  -- the first summand of the decomposition has small degree
  have hlow : (P - Polynomial.C c * Polynomial.X ^ d).degree < ((d : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    rcases eq_or_lt_of_le hn with hEq | hLt
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos hEq.symm,
        mul_one, ← hEq, hc]
      ring
    · have h1 : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : (Polynomial.C c * Polynomial.X ^ d).coeff n = 0 := by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      rw [Polynomial.coeff_sub, h1, h2, sub_zero]
  have hfirst : ((P - Polynomial.C c * Polynomial.X ^ d) * risingPoly p).degree
      < ((a + b : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree (risingPoly_ne_zero p),
      risingPoly_natDegree]
    have : ((d : ℕ) : WithBot ℕ) + (p : ℕ) = ((a + b : ℕ) : WithBot ℕ) := by
      rw [hab]
      push_cast
      ring
    rw [← this]
    exact WithBot.add_lt_add_right (by simp) hlow
  -- the second summand is a difference of two monic polynomials of the same degree
  have hmon1 : (Polynomial.X ^ d * risingPoly p).Monic := monic_X_pow_mul_risingPoly d p
  have hmon2 : (Polynomial.X ^ a * risingPoly b).Monic := monic_X_pow_mul_risingPoly a b
  have hdeg1 : (Polynomial.X ^ d * risingPoly p).natDegree = a + b := by
    rw [natDegree_X_pow_mul_risingPoly, hab]
  have hdeg2 : (Polynomial.X ^ a * risingPoly b).natDegree = a + b :=
    natDegree_X_pow_mul_risingPoly a b
  have hsecond : (Polynomial.X ^ d * risingPoly p
      - Polynomial.X ^ a * risingPoly b).degree < ((a + b : ℕ) : WithBot ℕ) := by
    have hdegeq : (Polynomial.X ^ d * risingPoly p).degree
        = (Polynomial.X ^ a * risingPoly b).degree := by
      rw [Polynomial.degree_eq_natDegree hmon1.ne_zero,
        Polynomial.degree_eq_natDegree hmon2.ne_zero, hdeg1, hdeg2]
    have hlt := Polynomial.degree_sub_lt hdegeq hmon1.ne_zero (by rw [hmon1.leadingCoeff,
      hmon2.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hmon1.ne_zero, hdeg1] at hlt
  have hsplit : Q = (P - Polynomial.C c * Polynomial.X ^ d) * risingPoly p
      + Polynomial.C c * (Polynomial.X ^ d * risingPoly p - Polynomial.X ^ a * risingPoly b) := by
    rw [hQ]
    ring
  have hQdeg : Q.degree < ((a + b : ℕ) : WithBot ℕ) := by
    rw [hsplit]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hfirst ?_)
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hC : (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    calc (Polynomial.C c).degree
          + (Polynomial.X ^ d * risingPoly p - Polynomial.X ^ a * risingPoly b).degree
        ≤ 0 + (Polynomial.X ^ d * risingPoly p
            - Polynomial.X ^ a * risingPoly b).degree := by
          exact add_le_add hC (le_refl _)
      _ = (Polynomial.X ^ d * risingPoly p - Polynomial.X ^ a * risingPoly b).degree := by
          rw [zero_add]
      _ < ((a + b : ℕ) : WithBot ℕ) := hsecond
  refine ⟨Q, ?_, fun x hx => ?_⟩
  · by_cases hQ0 : Q = 0
    · rw [hQ0]
      simpa using habpos
    · have := (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQdeg
      omega
  · have hxne : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
    have hRb : risingProd x b ≠ 0 := risingProd_ne_zero hx b
    have hRp : risingProd x p ≠ 0 := risingProd_ne_zero hx p
    have hxa : x ^ a ≠ 0 := pow_ne_zero _ hxne
    have hQeval : Q.eval x = P.eval x * risingProd x p - c * (x ^ a * risingProd x b) := by
      rw [hQ]
      simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rw [hQeval]
    field_simp

end GaloisForLFunctions
