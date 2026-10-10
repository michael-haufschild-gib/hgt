import GaloisForLFunctions.RHTower.WeilLogShiftMomentFiber

/-! Actual Gram tests see the complete canonical moment fiber through one coordinate. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMixture_pairing (r k : ℕ) (a b : ℝ)
    (y : Fin (r + 2) → ℝ) :
    (∑ i, finiteWeilCanonicalMixture r k a i * y i) -
      (∑ i, finiteWeilCanonicalMixture r k b i * y i) =
        (a - b) * ((∑ i, finiteWeilCanonicalPositiveProfile r k i * y i) -
          ∑ i, finiteWeilCanonicalNegativeProfile r k i * y i) := by
  simp only [finiteWeilCanonicalMixture, add_mul, mul_assoc, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- One actual test reads the exact mixture coordinate on the entire affine line. -/
theorem exists_finiteWeilGram_reads_mixture_coordinate (r : ℕ) (s : Finset ℕ) (k : ℕ)
    (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s) :
    ∃ w : FiniteWeilGramTest, ∀ a : ℝ,
      (∑ i, finiteWeilCanonicalMixture r k a i *
        finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a := by
  obtain ⟨w, hp, hq⟩ := exists_finiteWeilGram_separates_canonical_profiles r s k hmem
  refine ⟨w, fun a => ?_⟩
  simp only [finiteWeilCanonicalMixture, add_mul, mul_assoc, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp, hq, mul_one, mul_zero, add_zero]

/-- Native-cost sensitivity scales with the exact distance between any two members
of the canonical moment fiber; all constants come from the proved endpoint law. -/
theorem exists_finiteWeilGram_moment_fiber_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      ∀ v z : Fin (r + 2) → ℝ,
        finiteWeilCanonicalMomentFiber r k v → finiteWeilCanonicalMomentFiber r k z →
        ∀ w : FiniteWeilGramTest,
          |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
            (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
              (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤
                ((∑ i, |v i - z i|) / 2) * B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_probability_profile_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth v z hv hz w => ?_⟩
  obtain ⟨a, ha, _⟩ := (finiteWeilCanonicalMomentFiber_iff r k v).mp hv
  obtain ⟨b, hb, _⟩ := (finiteWeilCanonicalMomentFiber_iff r k z).mp hz
  rw [ha.2.2, hb.2.2, finiteWeilCanonicalMixture_pairing, abs_mul,
    finiteWeilCanonicalMixture_abs_distance]
  have hc := (hbound r s k hmem hwidth).2 w
  calc
    _ = |a - b| * (|(∑ i, finiteWeilCanonicalPositiveProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
        (∑ i, finiteWeilCanonicalNegativeProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
            (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r)) := by ring
    _ ≤ |a - b| * (B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = _ := by ring

end RHTower
