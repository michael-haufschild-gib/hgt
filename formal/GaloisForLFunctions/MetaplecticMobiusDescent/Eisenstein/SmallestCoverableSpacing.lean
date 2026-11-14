import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.MinimalDiskObstructions
import GaloisForLFunctions.HTGeometry.LeeYangForcingThreshold

/-!
# Attainment of the first positive coverable spacing

The coverability locus is closed, contains every spacing at least two,
and has a positive gap immediately above the collapsed lattice. Thus its
positive part has an attained minimum. This applies the corpus's closed
threshold lemma without assuming that the coverability locus is monotone.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

open Set

/-- A strictly positive smallest coverable spacing exists. -/
theorem exists_smallest_positive_coverable_spacing :
    ∃ d : ℝ, 0 < d ∧ CoverableSpacing d ∧
      ∀ d' : ℝ, 0 < d' → CoverableSpacing d' → d ≤ d' := by
  obtain ⟨ε, hε, hgap⟩ := exists_initial_noncoverable_interval
  have htwo : CoverableSpacing 2 := coverableSpacing_of_two_le le_rfl
  have hεtwo : ε ≤ 2 := by
    by_contra h
    exact hgap 2 (by positivity) (lt_of_not_ge h) htwo
  let S : Set ℝ := {d | CoverableSpacing d} ∩ Ici ε
  have hS : IsClosed S := isClosed_coverableSpacing.inter isClosed_Ici
  have hne : S.Nonempty := ⟨2, htwo, hεtwo⟩
  have hbelow : BddBelow S := ⟨ε, fun _ h => h.2⟩
  have hmin : sInf S ∈ S := csInf_mem_of_isClosed hS hne hbelow
  refine ⟨sInf S, hε.trans_le hmin.2, hmin.1, fun d hd hcover => ?_⟩
  have hεd : ε ≤ d := by
    by_contra h
    exact hgap d hd (lt_of_not_ge h) hcover
  exact csInf_le hbelow ⟨hcover, hεd⟩

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.DiskCovering.exists_smallest_positive_coverable_spacing
