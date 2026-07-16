import GaloisForLFunctions.HTGeometry.GeneralKaehlerPrincipalSymbol
import Mathlib.Data.Sigma.Order
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.RingTheory.Ideal.Operations

/-!
# Block Kähler principal symbols

Every maximal minor of a coefficient matrix lies in the product of ideals controlling its rows.
For a disjoint block matrix this bound is exact: choosing one column from each block produces a
diagonal maximal minor, so the maximal-minor ideal is precisely the product of the row ideals.

Combining this with the general Kähler principal-symbol theorem identifies the intrinsic Kähler
coefficient ideal of a disjoint linear-jet packet with the base change of that product.  This is
the algebraic mechanism behind the universal pretemporal factor in free horizon realizations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators Pointwise

universe u v w

variable {R : Type u} {G : Type v} [CommRing R] [LinearOrder G]

/-- If row `i` of a coefficient matrix lies in `I i`, every maximal minor lies in the product of
the row ideals. -/
theorem universalLinearJetMinor_mem_prod_rowIdeals
    {n : ℕ} (M : Fin n → G → R) (I : Fin n → Ideal R)
    (hM : ∀ i g, M i g ∈ I i) (s : Set.powersetCard G n) :
    universalLinearJetMinor M s ∈ ∏ i, I i := by
  rw [universalLinearJetMinor, Matrix.det_apply']
  apply Ideal.sum_mem
  intro σ hσ
  apply Ideal.mul_mem_left
  have hprod :
      (∏ j, M (σ j) (Set.powersetCard.ofFinEmbEquiv.symm s j)) ∈
        ∏ j, I (σ j) := by
    apply Ideal.prod_mem_prod
    intro j hj
    exact hM (σ j) _
  have hperm : (∏ j, I (σ j)) = ∏ j, I j :=
    Equiv.prod_comp (σ : Fin n ≃ Fin n) I
  rwa [hperm] at hprod

/-- The maximal-minor ideal is bounded by any product of row ideals containing the matrix
coefficients row by row. -/
theorem universalLinearJetMinorIdeal_le_prod_rowIdeals
    {n : ℕ} (M : Fin n → G → R) (I : Fin n → Ideal R)
    (hM : ∀ i g, M i g ∈ I i) :
    universalLinearJetMinorIdeal M ≤ ∏ i, I i := by
  rw [universalLinearJetMinorIdeal]
  apply Ideal.span_le.2
  rintro p ⟨s, rfl⟩
  exact universalLinearJetMinor_mem_prod_rowIdeals M I hM s

/-- Lexicographically ordered columns, split into one block per row. -/
abbrev LinearJetBlockColumn (n : ℕ) (H : Type w) := Lex (Σ _ : Fin n, H)

/-- Selecting one payload in every row block gives an order embedding, hence a canonical maximal
minor coordinate. -/
def blockChoiceOrderEmbedding {n : ℕ} {H : Type w} [LinearOrder H]
    (h : Fin n → H) : Fin n ↪o LinearJetBlockColumn n H where
  toFun i := toLex ⟨i, h i⟩
  inj' := by
    intro i j hij
    exact congrArg (fun g : LinearJetBlockColumn n H => (ofLex g).1) hij
  map_rel_iff' := by
    intro i j
    rw [Sigma.Lex.le_def]
    constructor
    · rintro (hij | ⟨hij, hh⟩)
      · exact le_of_lt hij
      · exact le_of_eq hij
    · intro hij
      obtain hij | rfl := hij.lt_or_eq
      · exact Or.inl hij
      · exact Or.inr ⟨rfl, le_rfl⟩

/-- A coefficient matrix with one disjoint column block per row. -/
def blockDiagonalLinearJetCoefficient {n : ℕ} {H : Type w}
    (a : Fin n → H → R) (i : Fin n) (g : LinearJetBlockColumn n H) : R :=
  if i = (ofLex g).1 then a i (ofLex g).2 else 0

/-- A canonical block choice produces the product of the selected row coefficients as a maximal
minor. -/
theorem blockDiagonalLinearJetMinor_choice
    {n : ℕ} {H : Type w} [Fintype H] [LinearOrder H]
    (a : Fin n → H → R) (h : Fin n → H) :
    universalLinearJetMinor (blockDiagonalLinearJetCoefficient a)
        (Set.powersetCard.ofFinEmbEquiv (blockChoiceOrderEmbedding h)) =
      ∏ i, a i (h i) := by
  rw [universalLinearJetMinor]
  have henum :
      Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofFinEmbEquiv (blockChoiceOrderEmbedding h)) =
        blockChoiceOrderEmbedding h :=
    Equiv.symm_apply_apply Set.powersetCard.ofFinEmbEquiv _
  rw [henum]
  have hmatrix :
      Matrix.of (fun i j =>
        blockDiagonalLinearJetCoefficient a i (blockChoiceOrderEmbedding h j)) =
        Matrix.diagonal (fun i => a i (h i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [blockDiagonalLinearJetCoefficient, blockChoiceOrderEmbedding]
    · simp [blockDiagonalLinearJetCoefficient, blockChoiceOrderEmbedding, hij]
  rw [hmatrix, Matrix.det_diagonal]

/-- **Exact block principal-symbol theorem.**  The maximal-minor ideal of a disjoint block
coefficient matrix is exactly the product of its row coefficient ideals. -/
theorem blockDiagonalLinearJetMinorIdeal_eq_prod_rowIdeals
    {n : ℕ} {H : Type w} [Fintype H] [LinearOrder H]
    (a : Fin n → H → R) :
    universalLinearJetMinorIdeal (blockDiagonalLinearJetCoefficient a) =
      ∏ i, Ideal.span (Set.range (a i)) := by
  apply le_antisymm
  · apply universalLinearJetMinorIdeal_le_prod_rowIdeals
    intro i g
    by_cases hi : i = (ofLex g).1
    · simp only [blockDiagonalLinearJetCoefficient, if_pos hi]
      exact Ideal.subset_span ⟨(ofLex g).2, rfl⟩
    · simp [blockDiagonalLinearJetCoefficient, hi]
  · rw [Ideal.prod_span]
    apply Ideal.span_le.2
    intro p hp
    rw [Set.mem_fintype_prod] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    choose h hh using hg
    have hgprod : (∏ i, g i) = ∏ i, a i (h i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hh i).symm
    rw [hgprod, ← blockDiagonalLinearJetMinor_choice a h]
    exact Ideal.subset_span ⟨
      Set.powersetCard.ofFinEmbEquiv (blockChoiceOrderEmbedding h), rfl⟩

/-- **Exact block Kähler principal-symbol theorem.**  The intrinsic Kähler coefficient ideal of
a disjoint universal linear-jet packet is the base change of the product of its row coefficient
ideals. -/
theorem blockDiagonalLinearJetKaehlerCoefficientIdeal_eq_map_prod_rowIdeals
    {n : ℕ} {H : Type w} [Fintype H] [LinearOrder H]
    (a : Fin n → H → R) :
    universalLinearJetKaehlerCoefficientIdeal (blockDiagonalLinearJetCoefficient a) =
      Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (LinearJetBlockColumn n H) R)
        (∏ i, Ideal.span (Set.range (a i))) := by
  rw [universalLinearJetKaehlerCoefficientIdeal_eq_map_minorIdeal,
    blockDiagonalLinearJetMinorIdeal_eq_prod_rowIdeals]

end

end GaloisForLFunctions.HTGeometry
