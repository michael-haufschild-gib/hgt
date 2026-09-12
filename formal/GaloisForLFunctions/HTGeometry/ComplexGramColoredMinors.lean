import GaloisForLFunctions.HTGeometry.ComplexGramPlucker

/-!
# Colored lower bounds for complex Gram determinants

Strictly separated finite coordinate blocks make every colored transversal a canonical maximal
minor. Distinct transversals give distinct Pluecker coordinates, so their common determinant floor
is multiplied by the product of block cardinalities.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Set

noncomputable section

variable {κ : Type*} [Fintype κ] [LinearOrder κ]

/-- One choice from each strictly ordered color block is itself an order embedding. -/
def coloredChoiceOrderEmbedding {J : ℕ} (S : Fin J → Finset κ)
    (hsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y)
    (q : ∀ j, ↥(S j)) : Fin J ↪o κ :=
  OrderEmbedding.ofStrictMono (fun j => (q j).1) (by
    intro i j hij
    exact hsep i j hij _ (q i).2 _ (q j).2)

/-- Canonical maximal-minor coordinate selected by one element of every color block. -/
def coloredChoiceMinorIndex {J : ℕ} (S : Fin J → Finset κ)
    (hsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y)
    (q : ∀ j, ↥(S j)) : Set.powersetCard κ J :=
  Set.powersetCard.ofFinEmbEquiv (coloredChoiceOrderEmbedding S hsep q)

omit [Fintype κ] in
/-- Distinct ordered colored choices select distinct maximal-minor coordinates. -/
theorem coloredChoiceMinorIndex_injective {J : ℕ} (S : Fin J → Finset κ)
    (hsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y) :
    Function.Injective (coloredChoiceMinorIndex S hsep) := by
  intro q r hqr
  have he : coloredChoiceOrderEmbedding S hsep q =
      coloredChoiceOrderEmbedding S hsep r :=
    Set.powersetCard.ofFinEmbEquiv.injective hqr
  funext j
  apply Subtype.ext
  exact congrArg (fun e : Fin J ↪o κ => e j) he

omit [Fintype κ] in
/-- A colored-choice minor is the matrix with chosen columns in color order. -/
theorem hermFeatureMinor_coloredChoiceMinorIndex {J : ℕ}
    (v : Fin J → κ → ℂ) (S : Fin J → Finset κ)
    (hsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y)
    (q : ∀ j, ↥(S j)) :
    hermFeatureMinor v (coloredChoiceMinorIndex S hsep q) =
      (Matrix.of fun i j => v i (q j).1).det := by
  unfold hermFeatureMinor coloredChoiceMinorIndex
  rw [Equiv.symm_apply_apply]
  rfl

/-- **Colored many-minor lower bound.** A common determinant-norm floor on all transversals is
multiplied by the product of color-block cardinalities inside the full Pluecker norm. -/
theorem prod_card_mul_sq_le_hermPluckerNormSq_of_coloredChoices {J : ℕ}
    (v : Fin J → κ → ℂ) (S : Fin J → Finset κ)
    (hsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y)
    {c : ℝ} (hc : 0 ≤ c)
    (hminor : ∀ q : ∀ j, ↥(S j),
      c ≤ ‖(Matrix.of fun i j => v i (q j).1).det‖) :
    ((∏ j, (S j).card : ℕ) : ℝ) * c ^ 2 ≤ hermPluckerNormSq v := by
  let f : (∀ j, ↥(S j)) → Set.powersetCard κ J := coloredChoiceMinorIndex S hsep
  have hf : Function.Injective f := coloredChoiceMinorIndex_injective S hsep
  let T : Finset (Set.powersetCard κ J) := Finset.univ.map ⟨f, hf⟩
  calc
    ((∏ j, (S j).card : ℕ) : ℝ) * c ^ 2 =
        ∑ q : ∀ j, ↥(S j), c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [Fintype.card_pi, Fintype.card_coe]
    _ ≤ ∑ q : ∀ j, ↥(S j), ‖hermFeatureMinor v (f q)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          rw [show f q = coloredChoiceMinorIndex S hsep q from rfl,
            hermFeatureMinor_coloredChoiceMinorIndex]
          exact pow_le_pow_left₀ hc (hminor q) 2
    _ = ∑ s ∈ T, ‖hermFeatureMinor v s‖ ^ 2 := by
          unfold T
          rw [Finset.sum_map]
          rfl
    _ ≤ hermPluckerNormSq v := by
          unfold hermPluckerNormSq
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun s hs hnot => sq_nonneg _)

end

end GaloisForLFunctions.HTGeometry
