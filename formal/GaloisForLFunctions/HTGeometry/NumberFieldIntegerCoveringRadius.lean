import GaloisForLFunctions.HTGeometry.LatticeCoveringRadius

/-!
# Covering radius of a number field's integer lattice

The general basis-rounding theorem is specialized to the actual image of the ring of integers in
the mixed embedding space.  Mathlib's `mixedEmbedding.latticeBasis` is simultaneously a real basis
of the mixed space and an integral basis of that image, so the span witness produced by rounding is
an embedded algebraic integer.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

/-- **The embedded ring of integers has finite covering radius.**  Every point of the mixed
embedding space is uniformly close to one actual algebraic integer; no abstract lattice or span
hypothesis remains. -/
theorem exists_numberFieldInteger_coveringRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : mixedEmbedding.mixedSpace K,
      ∃ a : 𝓞 K, ‖x - mixedEmbedding K (a : K)‖ ≤ R := by
  obtain ⟨R, hR, hcover⟩ :=
    exists_coveringRadius (mixedEmbedding.latticeBasis K)
  refine ⟨R, hR, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hcover x
  rw [mixedEmbedding.span_latticeBasis] at hy
  obtain ⟨a, rfl⟩ := hy
  exact ⟨a, hxy⟩

/-- **Coordinate form of the covering radius.**  One algebraic integer simultaneously approximates
every real and complex embedding coordinate with the same bound. -/
theorem exists_numberFieldInteger_coordinateCoveringRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : mixedEmbedding.mixedSpace K,
      ∃ a : 𝓞 K,
        (∀ w : {w : InfinitePlace K // IsReal w},
          |x.1 w - embedding_of_isReal w.prop (a : K)| ≤ R) ∧
        (∀ w : {w : InfinitePlace K // IsComplex w},
          ‖x.2 w - w.val.embedding (a : K)‖ ≤ R) := by
  obtain ⟨R, hR, hcover⟩ := exists_numberFieldInteger_coveringRadius K
  refine ⟨R, hR, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcover x
  refine ⟨a, fun w => ?_, fun w => ?_⟩
  · have hcoord := le_trans
      (norm_le_pi_norm (x - mixedEmbedding K (a : K)).1 w)
      (norm_fst_le (x - mixedEmbedding K (a : K)))
    simpa [Real.norm_eq_abs] using hcoord.trans ha
  · have hcoord := le_trans
      (norm_le_pi_norm (x - mixedEmbedding K (a : K)).2 w)
      (norm_snd_le (x - mixedEmbedding K (a : K)))
    simpa using hcoord.trans ha

end


end GaloisForLFunctions.HTGeometry
