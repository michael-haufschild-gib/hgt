import GaloisForLFunctions.HTGeometry.RegularLevelSetStratification

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/--
A well-founded algebraic category in which every nonempty object has a regular
open piece admits a finite regular stratification.  The statement is phrased
for an arbitrary predicate on subsets so that the well-founded algebraic
topology and the ambient analytic topology need not be placed on the same
type-class instance.
-/
theorem finiteRegularStratification_of_wellFounded_peel
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {c : ℕ} (Algebraic : Set Y → Prop)
    (hwf : WellFounded (fun T S : {Z : Set Y // Algebraic Z} => T.1 ⊂ S.1))
    (peel : ∀ S, Algebraic S → S.Nonempty →
      ∃ R : Set Y, R.Nonempty ∧ R ⊆ S ∧
        IsLocalRegularLevelSetOfCodimAtLeast R c ∧ Algebraic (S \ R)) :
    ∀ S, Algebraic S → Nonempty (FiniteRegularStratification S c) := by
  intro S hS
  let Z : {Z : Set Y // Algebraic Z} := ⟨S, hS⟩
  change Nonempty (FiniteRegularStratification Z.1 c)
  induction Z using hwf.induction with
  | h Z ih =>
      by_cases hZ : Z.1.Nonempty
      · obtain ⟨R, hRne, hRZ, hRreg, hrem⟩ := peel Z.1 Z.2 hZ
        let T : {Z : Set Y // Algebraic Z} := ⟨Z.1 \ R, hrem⟩
        have hTZ : T.1 ⊂ Z.1 := by
          refine Set.ssubset_iff_exists.mpr ⟨diff_subset, ?_⟩
          obtain ⟨r, hrR⟩ := hRne
          exact ⟨r, hRZ hrR, fun hrT => hrT.2 hrR⟩
        obtain ⟨tail⟩ := ih T hTZ
        have hdisj : Disjoint R T.1 := by
          rw [Set.disjoint_left]
          intro x hxR hxT
          exact hxT.2 hxR
        have hcover : Z.1 = R ∪ T.1 := by
          ext x
          constructor
          · intro hx
            by_cases hxR : x ∈ R
            · exact Or.inl hxR
            · exact Or.inr ⟨hx, hxR⟩
          · rintro (hxR | hxT)
            · exact hRZ hxR
            · exact hxT.1
        exact ⟨tail.cons hRreg hdisj hcover⟩
      · have hZempty : Z.1 = ∅ := not_nonempty_iff_eq_empty.mp hZ
        refine ⟨?_⟩
        exact {
          numberOfStrata := 0
          stratum := fun i => i.elim0
          pairwise_disjoint := by
            intro i
            exact i.elim0
          cover := by simp [hZempty]
          regular := by intro i; exact i.elim0
        }

end

end GaloisForLFunctions.HTGeometry
