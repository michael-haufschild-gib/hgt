import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

/-!
# The algebraic core of the rank-defect codimension bound

The codimension estimate for the rank-defect locus rests on two elementary facts about a projective
coefficient vector — a nonzero tuple of polynomials `c β` of bounded degree.

First, the evaluation indices at which *every* `c β` vanishes are few: one of them is a nonzero
polynomial, and a nonzero polynomial has finitely many roots.  Second, at any remaining index the
combination `∑ β c β (z) M β` is a nonzero polynomial in the jet variables, because the `M β` are
distinct monomials and therefore linearly independent.

Together these say the projective incidence condition is nondegenerate at all but boundedly many
indices, which is exactly what drives the codimension count.  The stratification and transversality
layers built on top of this count are not formalized here.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **Few common roots.**  If one member of a polynomial tuple is nonzero, the points where every
member vanishes form a finite set. -/
theorem finite_common_roots_of_exists_ne_zero
    {κ : Type*} (c : κ → Polynomial ℂ) {β₀ : κ} (hβ₀ : c β₀ ≠ 0) :
    {z : ℂ | ∀ β, (c β).eval z = 0}.Finite := by
  apply Set.Finite.subset (Polynomial.finite_setOf_isRoot hβ₀)
  intro z hz
  exact hz β₀

/-- The common-root set is contained in the roots of any nonzero member, so its cardinality is
bounded by that member's degree. -/
theorem common_roots_subset_roots
    {κ : Type*} (c : κ → Polynomial ℂ) (β₀ : κ) :
    {z : ℂ | ∀ β, (c β).eval z = 0} ⊆ {z : ℂ | (c β₀).IsRoot z} := by
  intro z hz
  exact hz β₀

/-- **Distinct monomials detect a nonzero coefficient.**  A finite combination of monomials with
pairwise distinct exponents is nonzero as soon as one coefficient is nonzero. -/
theorem sum_monomial_ne_zero
    {σ κ : Type*} [Fintype κ] [DecidableEq κ]
    (exponent : κ → (σ →₀ ℕ)) (hexp : Function.Injective exponent)
    (a : κ → ℂ) {β₀ : κ} (ha : a β₀ ≠ 0) :
    (∑ β, MvPolynomial.monomial (exponent β) (a β)) ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (exponent β₀)) hzero
  rw [MvPolynomial.coeff_zero] at hcoeff
  have hsum : MvPolynomial.coeff (exponent β₀)
      (∑ β, MvPolynomial.monomial (exponent β) (a β)) = a β₀ := by
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single β₀]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      exact hβ (hexp heq)
    · intro hcontra
      exact absurd (Finset.mem_univ β₀) hcontra
  exact ha (hsum ▸ hcoeff)

/-- **Nondegeneracy at a non-root index.**  At an evaluation point where some coefficient
polynomial does not vanish, the monomial combination is a nonzero polynomial. -/
theorem sum_eval_monomial_ne_zero
    {σ κ : Type*} [Fintype κ] [DecidableEq κ]
    (exponent : κ → (σ →₀ ℕ)) (hexp : Function.Injective exponent)
    (c : κ → Polynomial ℂ) (z : ℂ) {β₀ : κ} (hz : (c β₀).eval z ≠ 0) :
    (∑ β, MvPolynomial.monomial (exponent β) ((c β).eval z)) ≠ 0 :=
  sum_monomial_ne_zero exponent hexp (fun β => (c β).eval z) hz

/-- The polynomial coefficient attached to one monomial by an expanded coefficient vector. -/
def rowCoefficientPolynomial {κ : Type*} (q : ℕ)
    (coeff : κ × Fin (q + 1) → ℂ) (β : κ) (z : ℂ) : ℂ :=
  ∑ d : Fin (q + 1), coeff (β, d) * z ^ (d : ℕ)

/-- **The expanded relation is a monomial combination with polynomial coefficients.**  Reading one
row of the expanded evaluation matrix against a coefficient vector gives exactly the evaluation of
`∑ β cβ(z b) Mβ`, where each `cβ` is a polynomial of degree at most `q` in the row node.  This is
the projective coefficient vector of the codimension argument. -/
theorem sum_coeff_mul_expandedDifferentialEvaluationMatrix
    {row κ : Type*} [Fintype κ] (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (y : row × Fin n → ℂ)
    (coeff : κ × Fin (q + 1) → ℂ) (b : row) :
    (∑ col : κ × Fin (q + 1),
        coeff col * expandedDifferentialEvaluationMatrix q n z exponent y b col) =
      MvPolynomial.eval (fun k => y (b, k))
        (∑ β : κ, MvPolynomial.monomial (exponent β)
          (rowCoefficientPolynomial q coeff β (z b))) := by
  classical
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro β _
  rw [MvPolynomial.eval_monomial, rowCoefficientPolynomial, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [expandedDifferentialEvaluationMatrix, MvPolynomial.eval_monomial, one_mul]
  ring

/-- **Nondegeneracy of a surviving row.**  If some coefficient polynomial does not vanish at the row
node, the row relation is the vanishing of a nonzero polynomial in the jet variables. -/
theorem expandedRelation_nonzero_polynomial
    {row κ : Type*} [Fintype κ] [DecidableEq κ] (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (coeff : κ × Fin (q + 1) → ℂ) (b : row) {β₀ : κ}
    (hβ₀ : rowCoefficientPolynomial q coeff β₀ (z b) ≠ 0) :
    (∑ β : κ, MvPolynomial.monomial (exponent β)
      (rowCoefficientPolynomial q coeff β (z b))) ≠ 0 :=
  sum_monomial_ne_zero exponent hexp _ hβ₀

/-- The coefficient polynomial of one monomial, as an honest polynomial of degree at most `q`. -/
def rowCoefficientPoly {κ : Type*} (q : ℕ)
    (coeff : κ × Fin (q + 1) → ℂ) (β : κ) : Polynomial ℂ :=
  ∑ d : Fin (q + 1), Polynomial.C (coeff (β, d)) * Polynomial.X ^ (d : ℕ)

theorem eval_rowCoefficientPoly {κ : Type*} (q : ℕ)
    (coeff : κ × Fin (q + 1) → ℂ) (β : κ) (z : ℂ) :
    (rowCoefficientPoly q coeff β).eval z =
      rowCoefficientPolynomial q coeff β z := by
  rw [rowCoefficientPoly, rowCoefficientPolynomial, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro d _
  simp

/-- A nonzero entry of the coefficient vector makes the corresponding coefficient polynomial
nonzero. -/
theorem rowCoefficientPoly_ne_zero {κ : Type*} (q : ℕ)
    (coeff : κ × Fin (q + 1) → ℂ) (β₀ : κ) {d₀ : Fin (q + 1)}
    (h : coeff (β₀, d₀) ≠ 0) :
    rowCoefficientPoly q coeff β₀ ≠ 0 := by
  intro hzero
  apply h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (d₀ : ℕ)) hzero
  simp only [Polynomial.coeff_zero, rowCoefficientPoly,
    Polynomial.finsetSum_coeff] at hc
  rw [Finset.sum_eq_single d₀] at hc
  · simpa using hc
  · intro d _ hd
    have hne : (d₀ : ℕ) ≠ (d : ℕ) := fun heq => hd (Fin.ext heq.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro hcontra
    exact absurd (Finset.mem_univ d₀) hcontra

/-- **Few degenerate row nodes.**  If the coefficient vector is nonzero, the row nodes at which
*every* coefficient polynomial vanishes form a finite set.  At every other node the row relation is
the vanishing of a nonzero polynomial in the jet variables. -/
theorem finite_degenerate_rowNodes {κ : Type*} (q : ℕ)
    (coeff : κ × Fin (q + 1) → ℂ) (β₀ : κ) {d₀ : Fin (q + 1)}
    (h : coeff (β₀, d₀) ≠ 0) :
    {z : ℂ | ∀ β, rowCoefficientPolynomial q coeff β z = 0}.Finite := by
  have hsub : {z : ℂ | ∀ β, rowCoefficientPolynomial q coeff β z = 0} ⊆
      {z : ℂ | ∀ β, (rowCoefficientPoly q coeff β).eval z = 0} := by
    intro z hz β
    rw [eval_rowCoefficientPoly]
    exact hz β
  exact Set.Finite.subset
    (finite_common_roots_of_exists_ne_zero (rowCoefficientPoly q coeff)
      (rowCoefficientPoly_ne_zero q coeff β₀ h)) hsub

/-- **The expanded relation confines the jets to a proper zero set.**  At a row whose coefficient
polynomial survives, an expanded pattern relation says exactly that the row's jet vector lies in the
zero set of a *nonzero* multivariate polynomial.  This is the hypothesis that generic jets refute:
the relation cannot hold unless the coefficient vector degenerates. -/
theorem expandedRelation_forces_jet_in_zeroSet
    {row κ : Type*} [Fintype κ] [DecidableEq κ] (q n : ℕ) (z : row → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (y : row × Fin n → ℂ) (coeff : κ × Fin (q + 1) → ℂ) (b : row)
    (hrel : (∑ col : κ × Fin (q + 1),
      coeff col * expandedDifferentialEvaluationMatrix q n z exponent y b col) = 0)
    {β₀ : κ} (hβ₀ : rowCoefficientPolynomial q coeff β₀ (z b) ≠ 0) :
    (∑ β : κ, MvPolynomial.monomial (exponent β)
        (rowCoefficientPolynomial q coeff β (z b))) ≠ 0 ∧
      MvPolynomial.eval (fun k => y (b, k))
        (∑ β : κ, MvPolynomial.monomial (exponent β)
          (rowCoefficientPolynomial q coeff β (z b))) = 0 := by
  refine ⟨expandedRelation_nonzero_polynomial q n z exponent hexp coeff b hβ₀, ?_⟩
  rw [← sum_coeff_mul_expandedDifferentialEvaluationMatrix q n z exponent y coeff b]
  exact hrel

/-- **Row survival away from a finite bad set.**  For a nonzero coefficient vector the row nodes at
which the previous theorem does not apply are finite, so all but finitely many rows confine the jets
to a proper zero set. -/
theorem finite_rows_without_surviving_coefficient
    {κ : Type*} (q : ℕ) (coeff : κ × Fin (q + 1) → ℂ)
    (β₀ : κ) {d₀ : Fin (q + 1)} (h : coeff (β₀, d₀) ≠ 0) :
    {z : ℂ | ¬ ∃ β, rowCoefficientPolynomial q coeff β z ≠ 0}.Finite := by
  have hset : {z : ℂ | ¬ ∃ β, rowCoefficientPolynomial q coeff β z ≠ 0} =
      {z : ℂ | ∀ β, rowCoefficientPolynomial q coeff β z = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, not_exists, not_not]
  rw [hset]
  exact finite_degenerate_rowNodes q coeff β₀ h

end

end GaloisForLFunctions.HTGeometry
