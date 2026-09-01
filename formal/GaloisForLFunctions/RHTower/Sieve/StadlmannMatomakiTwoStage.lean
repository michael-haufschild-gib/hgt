import GaloisForLFunctions.RHTower.Sieve.StadlmannShiftedGreedy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor

/-!
# Stadlmann two-stage allocation for Matomäki--Teräväinen block families

The two sequential smooth-factor selections in Stadlmann Lemma 12 become two disjoint selected
recursive-block families.  Their complement is the exact third convolution factor.
-/

namespace RHTower

open Finset

noncomputable section

/-- Two selected Matomäki block families and the unselected remainder factor the full family. -/
theorem StadlmannTwoStageProductData.exists_matomakiThreeFactorSplit
    {t : ℕ} {Q : Fin t → ℝ} {S : Finset (Fin t)}
    (d : StadlmannTwoStageProductData Q S)
    (block : Fin t → Finset ℕ) :
    ∃ J₁ J₂ : Finset (Fin t),
      J₁ ⊆ S ∧ J₂ ⊆ S ∧ Disjoint J₁ J₂ ∧
        Real.exp d.fill.lowerOne ≤
          Real.exp d.fill.baseOne * ∏ i ∈ J₁, Q i ∧
        Real.exp d.fill.baseOne * ∏ i ∈ J₁, Q i ≤
          Real.exp d.fill.upperOne ∧
        Real.exp d.fill.lowerTwo ≤
          Real.exp d.fill.baseTwo * ∏ i ∈ J₂, Q i ∧
        Real.exp d.fill.baseTwo * ∏ i ∈ J₂, Q i ≤
          Real.exp d.fill.upperTwo ∧
        RHTower.Sieve.mtPrimeBlockFamilyAF block S =
          (RHTower.Sieve.mtPrimeBlockFamilyAF block J₁ *
            RHTower.Sieve.mtPrimeBlockFamilyAF block J₂) *
          RHTower.Sieve.mtPrimeBlockFamilyAF block (S \ (J₁ ∪ J₂)) := by
  obtain ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi⟩ :=
    d.exists_disjoint_subproducts_in_intervals
  have hUnion : J₁ ∪ J₂ ⊆ S := Finset.union_subset hJ₁S hJ₂S
  have hsplit := RHTower.Sieve.mtPrimeBlockFamilyAF_split block hUnion
  have hselected :
      RHTower.Sieve.mtPrimeBlockFamilyAF block (J₁ ∪ J₂) =
        RHTower.Sieve.mtPrimeBlockFamilyAF block J₁ *
          RHTower.Sieve.mtPrimeBlockFamilyAF block J₂ := by
    unfold RHTower.Sieve.mtPrimeBlockFamilyAF
    exact Finset.prod_union hdisj
  refine ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj,
    hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi, ?_⟩
  rw [hsplit, hselected]

/-- Nested selected Matomäki block family splits from its complementary selected blocks. -/
theorem StadlmannNestedProductData.exists_matomakiNestedFactorSplit
    {t : ℕ} {Q : Fin t → ℝ} {S : Finset (Fin t)}
    (d : StadlmannNestedProductData Q S)
    (block : Fin t → Finset ℕ) :
    ∀ c : {c : ℝ // d.refinement.outerLower ≤ c ∧
        c ≤ d.refinement.outerUpper},
      ∃ J ⊆ S,
        Real.exp (2 * c.1 + d.refinement.innerLower) ≤
          Real.exp d.refinement.base * ∏ i ∈ J, Q i ∧
        Real.exp d.refinement.base * ∏ i ∈ J, Q i ≤
          Real.exp (2 * c.1 + d.refinement.innerUpper) ∧
        RHTower.Sieve.mtPrimeBlockFamilyAF block S =
          RHTower.Sieve.mtPrimeBlockFamilyAF block J *
            RHTower.Sieve.mtPrimeBlockFamilyAF block (S \ J) := by
  intro c
  obtain ⟨J, hJS, hlo, hhi⟩ := d.exists_subproduct_at_every_outer_scale c
  exact ⟨J, hJS, hlo, hhi,
    RHTower.Sieve.mtPrimeBlockFamilyAF_split block hJS⟩

end

end RHTower
