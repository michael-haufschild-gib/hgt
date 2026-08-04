import GaloisForLFunctions.HTGeometry.PrefixStateIndependence
import GaloisForLFunctions.HTGeometry.MonomialIndependence

/-!
# From independence over the constants to the corpus's monomial independence

`PolyIndependent` asks that no combination of monomials in the states with polynomial coefficients
vanish.  Absorbing the coefficient variable as one more state — the coordinate, which is the zeroth
cascade state — turns such a combination into a single polynomial over the constants, so the
constant-coefficient independence already proved implies it.

The only work is the coefficient identification: distinct summands carry distinct monomials, because
the exponent map is injective and the coordinate exponent is read off separately.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The exponent vector with a prescribed coordinate exponent and state exponents. -/
noncomputable def coordExp {n : ℕ} (k : ℕ) (E : Fin n → ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons k E)

@[simp] theorem coordExp_zero {n : ℕ} (k : ℕ) (E : Fin n → ℕ) :
    coordExp k E 0 = k := by
  simp [coordExp]

@[simp] theorem coordExp_succ {n : ℕ} (k : ℕ) (E : Fin n → ℕ) (i : Fin n) :
    coordExp k E i.succ = E i := by
  simp [coordExp]

theorem coordExp_injective {n : ℕ} {k k' : ℕ} {E E' : Fin n → ℕ}
    (h : coordExp k E = coordExp k' E') : k = k' ∧ E = E' := by
  constructor
  · have := congrArg (fun m : Fin (n + 1) →₀ ℕ => m 0) h
    simpa using this
  · funext i
    have := congrArg (fun m : Fin (n + 1) →₀ ℕ => m i.succ) h
    simpa using this

/-- The evaluation of a coordinate-extended monomial. -/
theorem eval_monomial_coordExp {n : ℕ} (k : ℕ) (E : Fin n → ℕ) (a : ℂ)
    (x : Fin (n + 1) → ℂ) :
    MvPolynomial.eval x (MvPolynomial.monomial (coordExp k E) a)
      = a * x 0 ^ k * ∏ i : Fin n, x i.succ ^ E i := by
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_succ]
  simp only [coordExp_zero, coordExp_succ]
  ring

/-! ## Absorbing the coefficient variable -/

open scoped Classical in
/-- A monomial combination with polynomial coefficients, as a single polynomial in the coordinate and
the states. -/
noncomputable def coordPoly {n : ℕ} {ι : Type} (T : Finset ι) (E : ι → Fin n → ℕ)
    (A : ι → Polynomial ℂ) : MvPolynomial (Fin (n + 1)) ℂ :=
  ∑ e ∈ T, ∑ k ∈ Finset.range ((A e).natDegree + 1),
    MvPolynomial.monomial (coordExp k (E e)) ((A e).coeff k)

open scoped Classical in
theorem eval_coordPoly {n : ℕ} {ι : Type} (T : Finset ι) (E : ι → Fin n → ℕ)
    (A : ι → Polynomial ℂ) (x : Fin (n + 1) → ℂ) :
    MvPolynomial.eval x (coordPoly T E A)
      = ∑ e ∈ T, (A e).eval (x 0) * ∏ i : Fin n, x i.succ ^ (E e i) := by
  rw [coordPoly, map_sum]
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range ((A e).natDegree + 1),
      MvPolynomial.eval x (MvPolynomial.monomial (coordExp k (E e)) ((A e).coeff k))
        = ((A e).coeff k * x 0 ^ k) * ∏ i : Fin n, x i.succ ^ (E e i) := by
    intro k _
    rw [eval_monomial_coordExp]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Polynomial.eval_eq_sum_range]

open scoped Classical in
theorem coeff_coordPoly {n : ℕ} {ι : Type} (T : Finset ι) (E : ι → Fin n → ℕ)
    (A : ι → Polynomial ℂ) (hinj : Set.InjOn E T) {e₀ : ι} (he₀ : e₀ ∈ T) (k₀ : ℕ) :
    MvPolynomial.coeff (coordExp k₀ (E e₀)) (coordPoly T E A) = (A e₀).coeff k₀ := by
  classical
  rw [coordPoly, MvPolynomial.coeff_sum]
  have hinner : ∀ e ∈ T,
      MvPolynomial.coeff (coordExp k₀ (E e₀))
          (∑ k ∈ Finset.range ((A e).natDegree + 1),
            MvPolynomial.monomial (coordExp k (E e)) ((A e).coeff k))
        = ∑ k ∈ Finset.range ((A e).natDegree + 1),
            (if coordExp k (E e) = coordExp k₀ (E e₀) then (A e).coeff k else 0) := by
    intro e _
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_congr rfl hinner]
  refine Eq.trans (Finset.sum_eq_single e₀ ?_ ?_) ?_
  · intro e he hne
    refine Finset.sum_eq_zero ?_
    intro k _
    refine if_neg ?_
    intro hc
    exact hne (hinj he he₀ (coordExp_injective hc).2)
  · intro hc
    exact absurd he₀ hc
  · have hcond : ∀ k ∈ Finset.range ((A e₀).natDegree + 1),
        (if coordExp k (E e₀) = coordExp k₀ (E e₀) then (A e₀).coeff k else 0)
          = (if k = k₀ then (A e₀).coeff k else 0) := by
      intro k _
      by_cases hk : k = k₀
      · rw [if_pos hk, if_pos (by rw [hk])]
      · rw [if_neg hk, if_neg (fun hc => hk (coordExp_injective hc).1)]
    rw [Finset.sum_congr rfl hcond, Finset.sum_ite_eq' (Finset.range ((A e₀).natDegree + 1)) k₀
      (fun k => (A e₀).coeff k)]
    by_cases hk₀ : k₀ ∈ Finset.range ((A e₀).natDegree + 1)
    · rw [if_pos hk₀]
    · rw [if_neg hk₀]
      refine (Polynomial.coeff_eq_zero_of_natDegree_lt ?_).symm
      have := Finset.mem_range.not.mp hk₀
      omega

/-- **The corpus's monomial independence, from independence over the constants.**  The coefficient
variable is absorbed as the zeroth state, which for a cascade is the coordinate. -/
theorem polyIndependent_of_noRelation {n : ℕ} {Y : ℕ → ℂ → ℂ} (hY0 : ∀ z : ℂ, Y 0 z = z)
    (hno : ∀ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j : Fin (n + 1) => Y (j : ℕ) z) P = 0)) :
    PolyIndependent (fun i : Fin n => Y (i.1 + 1)) := by
  classical
  intro ι T E A hinj hsum e₀ he₀
  by_contra hA
  refine hno (coordPoly T E A) ?_ ?_
  · intro hzero
    have hk₀ : (A e₀).coeff ((A e₀).natDegree) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA
    have hcc := coeff_coordPoly T E A hinj he₀ ((A e₀).natDegree)
    rw [hzero, MvPolynomial.coeff_zero] at hcc
    exact hk₀ hcc.symm
  · intro z
    rw [eval_coordPoly]
    have hterm : ∀ e ∈ T,
        (A e).eval ((fun j : Fin (n + 1) => Y (j : ℕ) z) 0)
            * ∏ i : Fin n, (fun j : Fin (n + 1) => Y (j : ℕ) z) i.succ ^ (E e i)
          = (A e).eval z * ∏ i : Fin n, (Y (i.1 + 1) z) ^ (E e i) := by
      intro e _
      rw [show ((fun j : Fin (n + 1) => Y (j : ℕ) z) 0) = z from hY0 z]
      congr 1
    rw [Finset.sum_congr rfl hterm]
    exact hsum z

end GaloisForLFunctions.HTGeometry
