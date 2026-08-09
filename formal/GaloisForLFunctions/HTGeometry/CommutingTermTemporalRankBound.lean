import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw

/-!
# Additive spectra have at most the summed anchored temporal rank

If a finite spectrum is a sum of finitely many level functions, every anchored gap is a sum of
component gaps, so the anchored gap module lies in the span of the finitely many nonzero component
gaps.  A component whose level function takes at most `v` values contributes at most `v - 1` of
them, giving anchored temporal rank at most `m (v - 1)`.

Simultaneously diagonalisable commuting terms produce exactly such an additive spectrum, so a
Hamiltonian written as `m` commuting terms with at most four levels each — two-qubit terms — has
anchored temporal rank at most `3 m`, linear rather than exponential in the number of sites.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] {m : ℕ}

/-- The finite set of nonzero component gaps of an additive spectrum. -/
def componentGapSet (f : Fin m → I → ℝ) (reference : I) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun k : Fin m =>
    (Finset.univ.image fun i : I => f k i - f k reference).erase 0

theorem anchoredGapSubspace_le_span_componentGapSet
    (f : Fin m → I → ℝ) (reference : I) :
    anchoredGapSubspace (fun i => ∑ k, f k i) reference ≤
      Submodule.span ℚ (componentGapSet f reference : Set ℝ) := by
  classical
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  have hsum : (∑ k, f k i) - ∑ k, f k reference = ∑ k, (f k i - f k reference) := by
    rw [← Finset.sum_sub_distrib]
  show ((∑ k, f k i) - ∑ k, f k reference) ∈
    Submodule.span ℚ (componentGapSet f reference : Set ℝ)
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hzero : f k i - f k reference = 0
  · rw [hzero]; exact Submodule.zero_mem _
  · refine Submodule.subset_span ?_
    refine Finset.mem_coe.mpr ?_
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩
    exact Finset.mem_erase.mpr ⟨hzero, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

theorem card_componentGapSet_le
    (f : Fin m → I → ℝ) (reference : I) {v : ℕ}
    (hcard : ∀ k, (Finset.univ.image fun i : I => f k i).card ≤ v) :
    (componentGapSet f reference).card ≤ m * (v - 1) := by
  classical
  have hstep : ∀ k : Fin m,
      ((Finset.univ.image fun i : I => f k i - f k reference).erase 0).card ≤ v - 1 := by
    intro k
    have hmem : (0 : ℝ) ∈ Finset.univ.image fun i : I => f k i - f k reference :=
      Finset.mem_image.mpr ⟨reference, Finset.mem_univ _, by ring⟩
    have hshift : (Finset.univ.image fun i : I => f k i - f k reference).card =
        (Finset.univ.image fun i : I => f k i).card := by
      refine Finset.card_bij (fun a _ => a + f k reference) ?_ ?_ ?_
      · intro a ha
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by ring⟩
      · intro a ha b hb hab
        linarith
      · intro b hb
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
        exact ⟨f k i - f k reference, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, by ring⟩
    have herase : ((Finset.univ.image fun i : I => f k i - f k reference).erase 0).card + 1 =
        (Finset.univ.image fun i : I => f k i - f k reference).card :=
      Finset.card_erase_add_one hmem
    have := hcard k
    omega
  calc (componentGapSet f reference).card
      ≤ ∑ k : Fin m,
          ((Finset.univ.image fun i : I => f k i - f k reference).erase 0).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k : Fin m, (v - 1) := Finset.sum_le_sum fun k _ => hstep k
    _ = m * (v - 1) := by simp [Finset.sum_const]

/-- **Additive-spectrum temporal-rank bound.**  A spectrum that is a sum of `m` level functions
each taking at most `v` values has anchored temporal rank at most `m (v - 1)`. -/
theorem anchoredTemporalRank_sum_le
    (f : Fin m → I → ℝ) (reference : I) {v : ℕ}
    (hcard : ∀ k, (Finset.univ.image fun i : I => f k i).card ≤ v) :
    anchoredTemporalRank (fun i => ∑ k, f k i) reference ≤ m * (v - 1) := by
  classical
  have hspan := anchoredGapSubspace_le_span_componentGapSet f reference
  have hfinite : Module.Finite ℚ
      (Submodule.span ℚ (componentGapSet f reference : Set ℝ)) :=
    Module.Finite.span_of_finite ℚ (componentGapSet f reference).finite_toSet
  have hmono : Module.finrank ℚ (anchoredGapSubspace (fun i => ∑ k, f k i) reference) ≤
      Module.finrank ℚ (Submodule.span ℚ (componentGapSet f reference : Set ℝ)) :=
    Submodule.finrank_mono hspan
  have hcardle : Module.finrank ℚ
      (Submodule.span ℚ (componentGapSet f reference : Set ℝ)) ≤
      (componentGapSet f reference).card := by
    simpa [Set.finrank] using
      finrank_span_finset_le_card (R := ℚ) (componentGapSet f reference)
  exact le_trans (le_trans hmono hcardle) (card_componentGapSet_le f reference hcard)

/-- **Commuting two-level-pair bound.**  `m` commuting two-qubit terms give anchored temporal rank
at most `3 m`. -/
theorem anchoredTemporalRank_sum_le_three_mul
    (f : Fin m → I → ℝ) (reference : I)
    (hcard : ∀ k, (Finset.univ.image fun i : I => f k i).card ≤ 4) :
    anchoredTemporalRank (fun i => ∑ k, f k i) reference ≤ 3 * m := by
  have := anchoredTemporalRank_sum_le f reference (v := 4) hcard
  simpa [mul_comm] using this

end

end GaloisForLFunctions.HTGeometry
