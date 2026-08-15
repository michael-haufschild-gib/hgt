import Mathlib

/-!
# Sample points with prescribed differences

Evaluation points whose pairwise differences avoid a countable set are produced by one scale: the
arithmetic progression `t n = n · s` has differences `(m - n) · s`, so it suffices that no nonzero
integer multiple of `s` lies in the countable set, and the scales failing that form a countable
union of countable sets.

This is what node distinctness asks of the sample points: two members of one source share a node
exactly when the difference of the sample points lies in a fixed countable set determined by the
frequency and the two translation classes.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A scale whose nonzero integer multiples avoid a countable set.** -/
theorem exists_scale_zsmul_notMem {D : Set ℂ} (hD : D.Countable) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ k : ℤ, k ≠ 0 → (k : ℂ) * s ∉ D := by
  classical
  set bad : Set ℂ := {0} ∪ ⋃ k : ℤ, (fun d : ℂ => d / (k : ℂ)) '' D with hbad
  have hcount : bad.Countable := by
    refine Set.Countable.union (Set.countable_singleton 0) ?_
    exact Set.countable_iUnion fun k => hD.image _
  have hne : ∃ s : ℂ, s ∉ bad := by
    by_contra hcon
    push Not at hcon
    exact (Cardinal.not_countable_real (by
      have huniv : (Set.univ : Set ℂ) ⊆ bad := fun s _ => hcon s
      have hc : (Set.univ : Set ℂ).Countable := hcount.mono huniv
      have hcc : Countable ℂ := by
        rw [← Set.countable_univ_iff]
        exact hc
      have : Countable ℝ := by
        refine Function.Injective.countable (f := fun x : ℝ => (x : ℂ)) ?_
        exact Complex.ofReal_injective
      rw [← Set.countable_univ_iff] at this
      exact this))
  obtain ⟨s, hs⟩ := hne
  have hs0 : s ≠ 0 := fun h => hs (Or.inl (by rw [h]; rfl))
  refine ⟨s, hs0, fun k hk hmem => hs (Or.inr ?_)⟩
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  refine ⟨(k : ℂ) * s, hmem, ?_⟩
  have hkc : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  field_simp

/-- The arithmetic progression of sample points attached to a scale. -/
def sampleProgression (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) * s

theorem sampleProgression_sub (s : ℂ) (m n : ℕ) :
    sampleProgression s m - sampleProgression s n = ((m : ℤ) - (n : ℤ) : ℤ) * s := by
  rw [sampleProgression, sampleProgression]
  push_cast
  ring

/-- **Sample points whose pairwise differences avoid a countable set.** -/
theorem exists_sample_diff_notMem {D : Set ℂ} (hD : D.Countable) :
    ∃ t : ℕ → ℂ, Function.Injective t ∧ ∀ m n : ℕ, m ≠ n → t m - t n ∉ D := by
  classical
  obtain ⟨s, hs0, hs⟩ := exists_scale_zsmul_notMem (D := D ∪ {0}) (hD.union (countable_singleton 0))
  refine ⟨sampleProgression s, ?_, ?_⟩
  · intro m n hmn
    by_contra hne
    have hzero : sampleProgression s m - sampleProgression s n = 0 := by rw [hmn, sub_self]
    rw [sampleProgression_sub] at hzero
    exact hs ((m : ℤ) - (n : ℤ)) (by
      intro h
      exact hne (by exact_mod_cast (by omega : (m : ℤ) = (n : ℤ)))) (by
        rw [hzero]
        exact Or.inr rfl)
  · intro m n hmn hmem
    rw [sampleProgression_sub] at hmem
    exact hs ((m : ℤ) - (n : ℤ)) (by
      intro h
      exact hmn (by exact_mod_cast (by omega : (m : ℤ) = (n : ℤ)))) (Or.inl hmem)

end

end GaloisForLFunctions.HTGeometry
