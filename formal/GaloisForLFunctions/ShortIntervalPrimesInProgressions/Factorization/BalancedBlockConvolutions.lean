import GaloisForLFunctions.ShortIntervalPrimesInProgressions.Factorization.BalancedThreeFactorPartition
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor

/-!
# Three balanced convolution factors in the prime-block family

The two-fifths trichotomy supplies large-block, large-pair, or balanced
trilinear factorizations of the existing prime-block arithmetic functions.
In the last case the first group also gives a balanced bilinear split.
Only the grouping is asserted; analytic estimates of the factors remain separate.
-/

noncomputable section
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions
open RHTower.Sieve

/-- Every prime-block family factors around a large block, a large pair,
or three groups in the admissible trilinear length range. -/
theorem mtPrimeBlockFamilyAF_balanced_three {n : ℕ}
    (block : Fin n → Finset ℕ) (w : Fin n → ℝ) (s : Finset (Fin n)) :
    (∃ i ∈ s, 2 * factorMass w s / 5 ≤ |w i| ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockAF (block i) * mtPrimeBlockFamilyAF block (s.erase i)) ∨
    (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ 3 * factorMass w s / 5 ≤ |w i| + |w j| ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockAF (block i) * mtPrimeBlockAF (block j) *
          mtPrimeBlockFamilyAF block (s \ {i, j})) ∨
    ∃ u ⊆ s, ∃ v ⊆ s \ u,
      factorMass w u ∈ Set.Icc (2 * factorMass w s / 5) (factorMass w s / 2) ∧
      factorMass w v ∈ Set.Icc (factorMass w s / 10) (factorMass w s / 2) ∧
      factorMass w ((s \ u) \ v) ∈ Set.Icc (factorMass w s / 10) (factorMass w s / 2) ∧
      mtPrimeBlockFamilyAF block s =
        mtPrimeBlockFamilyAF block u * mtPrimeBlockFamilyAF block v *
          mtPrimeBlockFamilyAF block ((s \ u) \ v) := by
  rcases factorMass_balanced_three_partition w s with hsingle | hpair | hthree
  · obtain ⟨i, hi, hwi⟩ := hsingle
    refine Or.inl ⟨i, hi, hwi, ?_⟩
    unfold mtPrimeBlockFamilyAF
    exact (Finset.prod_erase_mul s (fun j => mtPrimeBlockAF (block j)) hi).symm.trans
      (mul_comm _ _)
  · obtain ⟨i, hi, j, hj, hij, hmass⟩ := hpair
    refine Or.inr (Or.inl ⟨i, hi, j, hj, hij, hmass, ?_⟩)
    have hsub : ({i, j} : Finset (Fin n)) ⊆ s :=
      Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
    have hproduct : mtPrimeBlockFamilyAF block {i, j} =
        mtPrimeBlockAF (block i) * mtPrimeBlockAF (block j) := by
      simp [mtPrimeBlockFamilyAF, hij]
    rw [mtPrimeBlockFamilyAF_split block hsub, hproduct]
  · obtain ⟨u, hus, v, hvr, hu, hv, hz⟩ := hthree
    refine Or.inr (Or.inr ⟨u, hus, v, hvr, hu, hv, hz, ?_⟩)
    calc
      mtPrimeBlockFamilyAF block s =
          mtPrimeBlockFamilyAF block u * mtPrimeBlockFamilyAF block (s \ u) :=
        mtPrimeBlockFamilyAF_split block hus
      _ = mtPrimeBlockFamilyAF block u *
          (mtPrimeBlockFamilyAF block v * mtPrimeBlockFamilyAF block ((s \ u) \ v)) := by
        rw [mtPrimeBlockFamilyAF_split block hvr]
      _ = _ := (mul_assoc _ _ _).symm

#print axioms mtPrimeBlockFamilyAF_balanced_three

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
