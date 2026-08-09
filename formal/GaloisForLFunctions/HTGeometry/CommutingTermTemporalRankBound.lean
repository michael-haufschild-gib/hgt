import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw

/-!
# Additive spectra have at most the summed anchored temporal rank

If a finite spectrum is a sum of finitely many level functions, its anchored gap module is
contained in the join of the component gap modules, so its anchored temporal rank is at most the
sum of the component ranks.  Each component whose range has at most `v` values contributes at
most `v - 1`.

Simultaneously diagonalisable commuting terms produce exactly such an additive spectrum, so a
Hamiltonian written as `m` commuting terms each with at most `v` distinct levels has anchored
temporal rank at most `m (v - 1)`.  For two-qubit terms this is the linear bound `3 m`.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] {m : ℕ}

/-- The anchored gap module of a sum of level functions lies in the join of the component gap
modules. -/
theorem anchoredGapSubspace_sum_le
    (f : Fin m → I → ℝ) (reference : I) :
    anchoredGapSubspace (fun i => ∑ k, f k i) reference ≤
      ⨆ k : Fin m, anchoredGapSubspace (f k) reference := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  have hsum : (∑ k, f k i) - ∑ k, f k reference = ∑ k, (f k i - f k reference) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine (le_iSup (fun k : Fin m => anchoredGapSubspace (f k) reference) k) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The anchored gap module of a level function with few values has small rational dimension. -/
theorem finrank_anchoredGapSubspace_le_ncard_sub_one
    (g : I → ℝ) (reference : I) {v : ℕ}
    (hv : (Set.range g).Finite) (hcard : hv.toFinset.card ≤ v) (hvpos : 1 ≤ v) :
    Module.finrank ℚ (anchoredGapSubspace g reference) ≤ v - 1 := by
  classical
  have hrange : Set.range (fun i => g i - g reference) ⊆
      (fun r => r - g reference) '' Set.range g := by
    rintro _ ⟨i, rfl⟩
    exact ⟨g i, ⟨i, rfl⟩, rfl⟩
  have hfin : ((fun r => r - g reference) '' Set.range g).Finite := hv.image _
  have hspanle : anchoredGapSubspace g reference ≤
      Submodule.span ℚ ((fun r => r - g reference) '' Set.range g) :=
    Submodule.span_mono hrange
  have hzero : (0 : ℝ) ∈ (fun r => r - g reference) '' Set.range g :=
    ⟨g reference, ⟨reference, rfl⟩, by ring⟩
  have hspan_eq : Submodule.span ℚ ((fun r => r - g reference) '' Set.range g) =
      Submodule.span ℚ (((fun r => r - g reference) '' Set.range g) \ {0}) := by
    rw [Submodule.span_diff_singleton_eq_span_of_mem_zero]
    simp
  have hle1 : Module.finrank ℚ (anchoredGapSubspace g reference) ≤
      Module.finrank ℚ (Submodule.span ℚ
        (((fun r => r - g reference) '' Set.range g) \ {0})) := by
    rw [← hspan_eq]
    exact Submodule.finrank_mono hspanle
  have hfin' : (((fun r => r - g reference) '' Set.range g) \ {0}).Finite :=
    hfin.diff
  have hle2 : Module.finrank ℚ (Submodule.span ℚ
      (((fun r => r - g reference) '' Set.range g) \ {0})) ≤ hfin'.toFinset.card := by
    have := finrank_span_le_card (K := ℚ)
      (((fun r => r - g reference) '' Set.range g) \ {0}) (n := hfin'.toFinset.card)
      (by simp [Set.ncard_eq_toFinset_card' , hfin'])
    exact this
  have hcard' : hfin'.toFinset.card ≤ v - 1 := by
    have hsub : hfin'.toFinset ⊂ hfin.toFinset := by
      constructor
      · intro x hx
        exact hfin.mem_toFinset.mpr (hfin'.mem_toFinset.mp hx).1
      · intro hsupset
        have := hsupset (hfin.mem_toFinset.mpr hzero)
        exact ((hfin'.mem_toFinset.mp this).2 rfl)
    have hlt : hfin'.toFinset.card < hfin.toFinset.card := Finset.card_lt_card hsub
    have himg : hfin.toFinset.card ≤ hv.toFinset.card := by
      have : hfin.toFinset ⊆ hv.toFinset.image (fun r => r - g reference) := by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := hfin.mem_toFinset.mp hx
        exact Finset.mem_image.mpr ⟨r, hv.mem_toFinset.mpr hr, rfl⟩
      exact le_trans (Finset.card_le_card this) Finset.card_image_le
    omega
  omega

/-- **Commuting-term temporal-rank bound.**  A spectrum that is a sum of `m` level functions each
taking at most `v` values has anchored temporal rank at most `m (v - 1)`. -/
theorem anchoredTemporalRank_sum_le
    (f : Fin m → I → ℝ) (reference : I) {v : ℕ} (hvpos : 1 ≤ v)
    (hv : ∀ k, (Set.range (f k)).Finite)
    (hcard : ∀ k, (hv k).toFinset.card ≤ v) :
    anchoredTemporalRank (fun i => ∑ k, f k i) reference ≤ m * (v - 1) := by
  classical
  have hle := anchoredGapSubspace_sum_le f reference
  have hsup : Module.finrank ℚ (⨆ k : Fin m, anchoredGapSubspace (f k) reference) ≤
      ∑ k : Fin m, Module.finrank ℚ (anchoredGapSubspace (f k) reference) :=
    Submodule.finrank_iSup_le_sum_finrank _
  have hterm : ∀ k : Fin m,
      Module.finrank ℚ (anchoredGapSubspace (f k) reference) ≤ v - 1 := fun k =>
    finrank_anchoredGapSubspace_le_ncard_sub_one (f k) reference (hv k) (hcard k) hvpos
  have hbound : ∑ k : Fin m, Module.finrank ℚ (anchoredGapSubspace (f k) reference) ≤
      m * (v - 1) := by
    calc ∑ k : Fin m, Module.finrank ℚ (anchoredGapSubspace (f k) reference)
        ≤ ∑ _k : Fin m, (v - 1) := Finset.sum_le_sum fun k _ => hterm k
      _ = m * (v - 1) := by simp [Finset.sum_const, mul_comm]
  exact le_trans (le_trans (Submodule.finrank_mono hle) hsup) hbound

/-- Two-level factors: `m` commuting two-qubit terms give anchored temporal rank at most `3 m`. -/
theorem anchoredTemporalRank_sum_le_three_mul
    (f : Fin m → I → ℝ) (reference : I)
    (hv : ∀ k, (Set.range (f k)).Finite)
    (hcard : ∀ k, (hv k).toFinset.card ≤ 4) :
    anchoredTemporalRank (fun i => ∑ k, f k i) reference ≤ 3 * m := by
  have := anchoredTemporalRank_sum_le f reference (v := 4) (by norm_num) hv hcard
  simpa [mul_comm] using this

end

end GaloisForLFunctions.HTGeometry
