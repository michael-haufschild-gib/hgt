import GaloisForLFunctions.HTGeometry.ExpandedMonomialEvaluation

/-!
# Root-counting core of evaluation codimension

For coefficient polynomials of degree at most `q` evaluated at distinct row parameters, a nonzero
coefficient tensor can make every coefficient polynomial vanish on at most `q` rows.  This is the
exact algebraic root-counting input in the manuscript's incidence-dimension argument.  It does not
formalize algebraic codimension, stratification, or parametric transversality.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- The polynomial with coefficient vector indexed by degrees `0, ..., q`. -/
noncomputable def boundedCoefficientPolynomial (q : ℕ)
    (c : Fin (q + 1) → ℂ) : Polynomial ℂ :=
  ∑ d : Fin (q + 1), Polynomial.monomial (d : ℕ) (c d)

/-- Coefficients are recovered exactly from the bounded coefficient polynomial. -/
@[simp] theorem boundedCoefficientPolynomial_coeff
    (q : ℕ) (c : Fin (q + 1) → ℂ) (d : Fin (q + 1)) :
    (boundedCoefficientPolynomial q c).coeff d = c d := by
  classical
  simp only [boundedCoefficientPolynomial, ← Polynomial.lcoeff_apply]
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  calc
    (∑ e : Fin (q + 1), if (e : ℕ) = (d : ℕ) then c e else 0) =
        (if (d : ℕ) = (d : ℕ) then c d else 0) := by
      apply Fintype.sum_eq_single d
      intro e hed
      simp [show (e : ℕ) ≠ (d : ℕ) by
        exact fun h => hed (Fin.ext h)]
    _ = c d := by simp

/-- Its natural degree is at most the prescribed degree bound. -/
theorem boundedCoefficientPolynomial_natDegree_le
    (q : ℕ) (c : Fin (q + 1) → ℂ) :
    (boundedCoefficientPolynomial q c).natDegree ≤ q := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  classical
  simp only [boundedCoefficientPolynomial, ← Polynomial.lcoeff_apply]
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  apply Finset.sum_eq_zero
  intro d hd
  simp [Polynomial.coeff_monomial, show (d : ℕ) ≠ N by omega]

/-- Evaluation is the expected bounded power sum. -/
@[simp] theorem boundedCoefficientPolynomial_eval
    (q : ℕ) (c : Fin (q + 1) → ℂ) (z : ℂ) :
    (boundedCoefficientPolynomial q c).eval z = ∑ d, c d * z ^ (d : ℕ) := by
  classical
  simp only [boundedCoefficientPolynomial]
  change (Polynomial.evalRingHom z)
    (∑ d : Fin (q + 1), Polynomial.monomial (d : ℕ) (c d)) = _
  rw [map_sum]
  simp [Polynomial.eval_monomial]

/-- A nonzero coefficient makes the bounded coefficient polynomial nonzero. -/
theorem boundedCoefficientPolynomial_ne_zero_of_apply_ne_zero
    (q : ℕ) (c : Fin (q + 1) → ℂ) {d : Fin (q + 1)} (hd : c d ≠ 0) :
    boundedCoefficientPolynomial q c ≠ 0 := by
  intro h
  have := congrArg (fun P : Polynomial ℂ => P.coeff d) h
  change (boundedCoefficientPolynomial q c).coeff d =
    (0 : Polynomial ℂ).coeff d at this
  rw [boundedCoefficientPolynomial_coeff] at this
  simp only [Polynomial.coeff_zero] at this
  exact hd this

/-- For a nonzero coefficient tensor and injective row parameters, all coefficient polynomials
vanish simultaneously on at most `q` rows. -/
theorem card_rows_all_boundedCoefficientPolynomials_zero_le
    {row κ : Type*} [Fintype row] [DecidableEq row]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (c : κ × Fin (q + 1) → ℂ) (hc : c ≠ 0) :
    Set.ncard {b | ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0} ≤ q := by
  classical
  have hex : ∃ a d, c (a, d) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext x
    exact h x.1 x.2
  obtain ⟨a, d, had⟩ := hex
  let P : Polynomial ℂ := boundedCoefficientPolynomial q (fun e => c (a, e))
  have hP : P ≠ 0 := boundedCoefficientPolynomial_ne_zero_of_apply_ne_zero q _ had
  let bad : Finset row := Finset.univ.filter fun b =>
    ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0
  have hbadCard :
      Set.ncard {b | ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0} = bad.card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext b
    simp [bad]
  have himage : Finset.image z bad ⊆ P.roots.toFinset := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    rw [Polynomial.IsRoot.def, boundedCoefficientPolynomial_eval]
    exact (Finset.mem_filter.mp hb).2 a
  have hcard : bad.card = (Finset.image z bad).card := by
    symm
    exact Finset.card_image_iff.mpr hz.injOn
  rw [hbadCard]
  calc
    bad.card = (Finset.image z bad).card := hcard
    _ ≤ P.roots.toFinset.card := Finset.card_le_card himage
    _ ≤ P.roots.card := Multiset.toFinset_card_le P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ q := boundedCoefficientPolynomial_natDegree_le q _

/-- Consequently at least `card row - q` rows carry a nonzero coefficient polynomial, expressed
without truncated subtraction as `card row ≤ q + goodRows`. -/
theorem card_rows_some_boundedCoefficientPolynomial_nonzero
    {row κ : Type*} [Fintype row] [DecidableEq row]
    (q : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (c : κ × Fin (q + 1) → ℂ) (hc : c ≠ 0) :
    Fintype.card row ≤ q +
      Set.ncard {b | ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0} := by
  classical
  let bad : Finset row := Finset.univ.filter fun b =>
    ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0
  let good : Finset row := Finset.univ.filter fun b =>
    ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0
  have hbadCard :
      Set.ncard {b | ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0} = bad.card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext b
    simp [bad]
  have hgoodCard :
      Set.ncard {b | ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0} = good.card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext b
    simp [good]
  have hbad : bad.card ≤ q := by
    rw [← hbadCard]
    exact card_rows_all_boundedCoefficientPolynomials_zero_le q z hz c hc
  have hpartition : bad.card + good.card = Fintype.card row := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset row))
      (fun b => ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0)
    change bad.card + good.card = Fintype.card row
    simpa [bad, good] using h
  rw [hgoodCard, ← hpartition]
  exact Nat.add_le_add_right hbad good.card

end
end GaloisForLFunctions.HTGeometry
