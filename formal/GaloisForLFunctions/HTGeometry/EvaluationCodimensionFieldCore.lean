import GaloisForLFunctions.HTGeometry.EvaluationCodimensionCore

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

def boundedCoefficientPolynomialOver
    {K : Type*} [Field K] (q : ℕ) (c : Fin (q + 1) → K) : Polynomial K :=
  ∑ d : Fin (q + 1), Polynomial.monomial (d : ℕ) (c d)

@[simp] theorem boundedCoefficientPolynomialOver_coeff
    {K : Type*} [Field K] (q : ℕ) (c : Fin (q + 1) → K) (d : Fin (q + 1)) :
    (boundedCoefficientPolynomialOver q c).coeff d = c d := by
  classical
  simp only [boundedCoefficientPolynomialOver, ← Polynomial.lcoeff_apply]
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  calc
    (∑ e : Fin (q + 1), if (e : ℕ) = (d : ℕ) then c e else 0) =
        (if (d : ℕ) = (d : ℕ) then c d else 0) := by
      apply Fintype.sum_eq_single d
      intro e hed
      simp [show (e : ℕ) ≠ (d : ℕ) by exact fun h => hed (Fin.ext h)]
    _ = c d := by simp

theorem boundedCoefficientPolynomialOver_natDegree_le
    {K : Type*} [Field K] (q : ℕ) (c : Fin (q + 1) → K) :
    (boundedCoefficientPolynomialOver q c).natDegree ≤ q := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  classical
  simp only [boundedCoefficientPolynomialOver, ← Polynomial.lcoeff_apply]
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  apply Finset.sum_eq_zero
  intro d hd
  simp [Polynomial.coeff_monomial, show (d : ℕ) ≠ N by omega]

@[simp] theorem boundedCoefficientPolynomialOver_eval
    {K : Type*} [Field K] (q : ℕ) (c : Fin (q + 1) → K) (z : K) :
    (boundedCoefficientPolynomialOver q c).eval z = ∑ d, c d * z ^ (d : ℕ) := by
  classical
  simp only [boundedCoefficientPolynomialOver]
  change (Polynomial.evalRingHom z)
    (∑ d : Fin (q + 1), Polynomial.monomial (d : ℕ) (c d)) = _
  rw [map_sum]
  simp [Polynomial.eval_monomial]

theorem boundedCoefficientPolynomialOver_ne_zero_of_apply_ne_zero
    {K : Type*} [Field K] (q : ℕ) (c : Fin (q + 1) → K)
    {d : Fin (q + 1)} (hd : c d ≠ 0) :
    boundedCoefficientPolynomialOver q c ≠ 0 := by
  intro h
  have hc : (boundedCoefficientPolynomialOver q c).coeff d = 0 := by
    rw [h]
    simp
  rw [boundedCoefficientPolynomialOver_coeff] at hc
  exact hd hc

/-- Field-valued root count for coefficient tensors. -/
theorem card_rows_all_boundedCoefficientPolynomialsOver_zero_le
    {K row κ : Type*} [Field K] [DecidableEq K]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → K) (hz : Function.Injective z)
    (c : κ × Fin (q + 1) → K) (hc : c ≠ 0) :
    (Finset.univ.filter fun b =>
      ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0).card ≤ q := by
  classical
  have hex : ∃ a d, c (a, d) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext x
    exact h x.1 x.2
  obtain ⟨a, d, had⟩ := hex
  let P : Polynomial K := boundedCoefficientPolynomialOver q (fun e => c (a, e))
  have hP : P ≠ 0 := boundedCoefficientPolynomialOver_ne_zero_of_apply_ne_zero q _ had
  let bad : Finset row := Finset.univ.filter fun b =>
    ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0
  have himage : Finset.image z bad ⊆ P.roots.toFinset := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    rw [Polynomial.IsRoot.def, boundedCoefficientPolynomialOver_eval]
    exact (Finset.mem_filter.mp hb).2 a
  have hcard : bad.card = (Finset.image z bad).card := by
    symm
    exact Finset.card_image_iff.mpr hz.injOn
  calc
    bad.card = (Finset.image z bad).card := hcard
    _ ≤ P.roots.toFinset.card := Finset.card_le_card himage
    _ ≤ P.roots.card := Multiset.toFinset_card_le P.roots
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ q := boundedCoefficientPolynomialOver_natDegree_le q _

/-- At least `card row - q` rows are active over an arbitrary coefficient field. -/
theorem card_rows_some_boundedCoefficientPolynomialOver_nonzero
    {K row κ : Type*} [Field K] [DecidableEq K]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → K) (hz : Function.Injective z)
    (c : κ × Fin (q + 1) → K) (hc : c ≠ 0) :
    Fintype.card row ≤ q +
      (Finset.univ.filter fun b =>
        ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0).card := by
  classical
  let bad : Finset row := Finset.univ.filter fun b =>
    ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0
  let good : Finset row := Finset.univ.filter fun b =>
    ∃ a, ∑ d, c (a, d) * z b ^ (d : ℕ) ≠ 0
  have hbad : bad.card ≤ q :=
    card_rows_all_boundedCoefficientPolynomialsOver_zero_le q z hz c hc
  have hpartition : bad.card + good.card = Fintype.card row := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset row))
      (fun b => ∀ a, ∑ d, c (a, d) * z b ^ (d : ℕ) = 0)
    change bad.card + good.card = Fintype.card row
    simpa [bad, good] using h
  rw [← hpartition]
  exact Nat.add_le_add_right hbad good.card

end
end GaloisForLFunctions.HTGeometry
