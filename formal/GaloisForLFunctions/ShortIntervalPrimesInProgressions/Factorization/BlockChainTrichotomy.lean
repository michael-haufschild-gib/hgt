import GaloisForLFunctions.ShortIntervalPrimesInProgressions.Factorization.WeightTrichotomy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor

/-!
# Balanced factorization of the prime-block convolution

The factor-length trichotomy chooses the subsets needed by the exact
Matomäki–Teräväinen block-product identities. Every prime-block family has a
large factor, a balanced two-factor convolution, or a three-factor convolution
with one prime block, unless its total length is below the threshold.
The conclusion constructs the factors; it assumes no Type-II estimate.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions
open RHTower.Sieve

/-- The length trichotomy supplies exact factorizations of the actual
prime-block arithmetic functions, with no coefficient estimates required. -/
theorem mtPrimeBlockFamilyAF_trichotomy {n : ℕ}
    (block : Fin n → Finset ℕ) (w : Fin n → ℝ) (t : ℝ) (s : Finset (Fin n)) :
    factorMass w s ≤ 2 * |t| ∨
    (∃ i ∈ s, |t| < |w i| ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockAF (block i) * mtPrimeBlockFamilyAF block (s.erase i)) ∨
    (∃ u ⊆ s, |t| ≤ factorMass w u ∧ |t| ≤ factorMass w (s \ u) ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockFamilyAF block u * mtPrimeBlockFamilyAF block (s \ u)) ∨
    ∃ i u v, Disjoint u v ∧ i ∉ u ∧ i ∉ v ∧ insert i (u ∪ v) = s ∧
      |w i| ∈ Set.Ioc (factorMass w s - 2 * |t|) |t| ∧
      factorMass w u ∈ Set.Ioo (factorMass w s - 2 * |t|) |t| ∧
      factorMass w v ∈ Set.Ioo (factorMass w s - 2 * |t|) |t| ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockAF (block i) * mtPrimeBlockFamilyAF block u *
          mtPrimeBlockFamilyAF block v := by
  rcases factorMass_trichotomy w t s with hsmall | hlarge | hbalanced | hexceptional
  · exact Or.inl hsmall
  · obtain ⟨i, hi, hwi⟩ := hlarge
    refine Or.inr (Or.inl ⟨i, hi, hwi, ?_⟩)
    unfold mtPrimeBlockFamilyAF
    exact (Finset.prod_erase_mul s (fun j => mtPrimeBlockAF (block j)) hi).symm.trans
      (mul_comm _ _)
  · obtain ⟨u, hus, hu, hcomp⟩ := hbalanced
    exact Or.inr (Or.inr (Or.inl ⟨u, hus, hu, hcomp,
      mtPrimeBlockFamilyAF_split block hus⟩))
  · obtain ⟨i, u, v, hdis, hiu, hiv, hcover, hi, hu, hv⟩ := hexceptional
    refine Or.inr (Or.inr (Or.inr ⟨i, u, v, hdis, hiu, hiv, hcover, hi, hu, hv, ?_⟩))
    have hin : i ∉ u ∪ v := by
      simpa only [Finset.mem_union, not_or] using And.intro hiu hiv
    rw [← hcover]
    unfold mtPrimeBlockFamilyAF
    rw [Finset.prod_insert hin, Finset.prod_union hdis, mul_assoc]

#print axioms mtPrimeBlockFamilyAF_trichotomy

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
