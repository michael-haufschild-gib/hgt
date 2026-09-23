import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceTypes
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerPaperCount

/-!
# Proposition 2.2 scale classification

The final proof paragraph has one dichotomy.  A small product of iterated prime blocks is absorbed
into the long coefficient, producing Type I for the pair term and Type I/II for the triple term.
A large product supplies a nonempty selected block subset in the Type-II range.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Pair term: exact Type-I/Type-II scale dichotomy. -/
theorem matomakiTeravainen_pairTerm_typeI_or_typeII
    {Q : ℕ → ℝ} {S : Finset ℕ}
    {X ε E Q₁ Q₂ : ℝ}
    (hX : 1 < X) (hε0 : 0 < ε) (hε : ε ≤ 2 / 11)
    (hE0 : 0 ≤ E) (hQ₁0 : 0 ≤ Q₁) (hQ₂0 : 0 ≤ Q₂)
    (hE : E ≤ X ^ (ε / 4))
    (hQ₁ : Q₁ ≤ X ^ (1 / 4 - 2 * ε))
    (hQ₂ : Q₂ ≤ X ^ (1 / 4 - 2 * ε))
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    E * Q₁ * Q₂ * (∏ i ∈ S, Q i) ≤ X ^ (1 / 2 + ε) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (ε / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  rcases matomakiTeravainen_primeBlockProduct_dichotomy
      hX hε0 hε hQone hQcap with hsmall | htypeII
  · left
    exact matomakiTeravainen_small_product_typeI_scale hX.le hε0.le
      hE0 hQ₁0 hQ₂0
      (Finset.prod_nonneg fun i hi => zero_le_one.trans (hQone i hi))
      hE hQ₁ hQ₂ hsmall.le
  · exact Or.inr htypeII

/-- Triple term: exact Type-I/II/Type-II scale dichotomy with source grouping
`M₁=E Q₂ Q₃`, `M₂=Q₁∏Qᵢ'`. -/
theorem matomakiTeravainen_tripleTerm_typeI_II_or_typeII
    {Q : ℕ → ℝ} {S : Finset ℕ}
    {X ε E Q₁ Q₂ Q₃ : ℝ}
    (hX : 1 < X) (hε0 : 0 < ε) (hε : ε ≤ 2 / 11)
    (hE0 : 0 ≤ E) (hQ₁0 : 0 ≤ Q₁) (hQ₂0 : 0 ≤ Q₂) (hQ₃0 : 0 ≤ Q₃)
    (hE : E ≤ X ^ (ε / 4))
    (hQ₁ : Q₁ ≤ X ^ (1 / 4 - 2 * ε))
    (hQ₃Q₂ : Q₃ ≤ Q₂)
    (hgeometry : Q₁ * Q₂ ^ (4 : ℕ) ≤ X ^ (1 - 2 * ε))
    (hQone : ∀ i ∈ S, 1 ≤ Q i)
    (hQcap : ∀ i ∈ S, Q i ≤ X ^ (2 / 11 : ℝ)) :
    ((E * Q₂ * Q₃) ^ (2 : ℕ) * (Q₁ * ∏ i ∈ S, Q i) ≤ X ^ (1 - ε) ∧
        Q₁ * (∏ i ∈ S, Q i) ≤ X ^ (1 / 4 - ε)) ∨
      ∃ I ⊆ S, I.Nonempty ∧
        X ^ (ε / 2) ≤ ∏ i ∈ I, Q i ∧
          ∏ i ∈ I, Q i ≤ X ^ (2 / 11 : ℝ) := by
  rcases matomakiTeravainen_primeBlockProduct_dichotomy
      hX hε0 hε hQone hQcap with hsmall | htypeII
  · left
    exact matomakiTeravainen_small_product_typeI_II_scales hX.le hε0.le
      hE0 hQ₁0 hQ₂0 hQ₃0
      (Finset.prod_nonneg fun i hi => zero_le_one.trans (hQone i hi))
      hE hQ₁ hQ₃Q₂ hgeometry hsmall.le
  · exact Or.inr htypeII

end

end RHTower.Sieve
