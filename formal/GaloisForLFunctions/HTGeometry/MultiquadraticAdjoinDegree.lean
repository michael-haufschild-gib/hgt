import GaloisForLFunctions.HTGeometry.QuadraticAdjoinSquareKernel

/-!
# Exact degree of a finite independent family of quadratic radicals

The proof maintains the degree and finite-support square-class kernel together.
Independence forces each inserted root to generate a quadratic step, and the
one-step square-class criterion propagates the kernel statement through the tower.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped IntermediateField
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- Degree and square-class kernel are controlled together by finite-support independence. -/
theorem multiquadratic_degree_and_twists {ι : Type*} (d : ι → F) (r : ι → L)
    (h2 : (2 : L) ≠ 0) (hsq : ∀ i, r i * r i = algebraMap F L (d i))
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, d i))
    (S : Finset ι) :
    Module.finrank F ↥(IntermediateField.adjoin F (r '' (S : Set ι))) = 2 ^ S.card ∧
      ∀ a : F, IsSquare (algebraMap F ↥(IntermediateField.adjoin F (r '' (S : Set ι))) a) →
        ∃ T : Finset ι, T ⊆ S ∧ IsSquare (a * ∏ i ∈ T, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hempty : r '' ((∅ : Finset ι) : Set ι) = (∅ : Set L) := by simp
    rw [hempty, IntermediateField.adjoin_empty]
    simp only [Finset.card_empty, pow_zero, IntermediateField.finrank_bot, true_and]
    intro a ha
    obtain ⟨u, hu⟩ := ha
    have h : IsSqIn (algebraMap F L).fieldRange (algebraMap F L a) :=
      ⟨(u : L), u.property, congrArg (fun w : (⊥ : IntermediateField F L) => (w : L)) hu⟩
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simpa using (isSqIn_fieldRange_iff_isSquare a).mp h
  | @insert i S hi ih =>
    let E := IntermediateField.adjoin F (r '' (S : Set ι))
    have hEi : ¬ IsSquare (algebraMap F E (d i)) := by
      intro h
      obtain ⟨T, hT, hs⟩ := ih.2 (d i) h
      have hiT : i ∉ T := fun hit => hi (hT hit)
      apply hind (insert i T) (Finset.insert_nonempty _ _)
      rw [Finset.prod_insert hiT]
      exact hs
    have hsqE : r i * r i = algebraMap E L (algebraMap F E (d i)) := by
      change r i * r i = algebraMap F L (d i)
      exact hsq i
    have hlast : Module.finrank E E⟮r i⟯ = 2 :=
      finrank_adjoin_eq_two hsqE (root_not_mem_bot_of_not_isSquare hsqE hEi)
    have hstep : (E⟮r i⟯).restrictScalars F =
        IntermediateField.adjoin F (r '' ((insert i S : Finset ι) : Set ι)) := by
      dsimp [E]
      rw [IntermediateField.adjoin_adjoin_left]
      congr 1
      rw [Finset.coe_insert, Set.image_insert_eq, Set.union_singleton]
    constructor
    · rw [← hstep]
      change Module.finrank F E⟮r i⟯ = 2 ^ (insert i S).card
      rw [← Module.finrank_mul_finrank F E E⟮r i⟯, hlast, ih.1,
        Finset.card_insert_of_notMem hi, pow_succ]
    · intro a ha
      rw [← hstep] at ha
      change IsSquare (algebraMap E E⟮r i⟯ (algebraMap F E a)) at ha
      rcases (isSquare_adjoin_root_iff h2 hsqE hEi).mp ha with h | h
      · obtain ⟨T, hT, hs⟩ := ih.2 a h
        exact ⟨T, fun j hj => Finset.mem_insert_of_mem (hT hj), hs⟩
      · rw [← map_mul] at h
        obtain ⟨T, hT, hs⟩ := ih.2 (d i * a) h
        have hiT : i ∉ T := fun hit => hi (hT hit)
        refine ⟨insert i T, Finset.insert_subset_insert i hT, ?_⟩
        rw [Finset.prod_insert hiT]
        convert hs using 1
        ring

end GaloisForLFunctions.HTGeometry
