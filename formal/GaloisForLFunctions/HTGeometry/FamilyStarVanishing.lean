import GaloisForLFunctions.HTGeometry.FamilyPosetNerve
import GaloisForLFunctions.HTGeometry.LocallyConicalPoset
import GaloisForLFunctions.HTGeometry.NerveVertexRemoval

/-!
# The disjoint union of the stars of a family of elements has no homology in positive degrees

Each star folds onto its own centre, so the disjoint union of a family of stars folds onto the
discrete set of centres.  That is exactly the locally conical situation: the fold dominates the
identity and dominates the map sending everything to the centre of its own part, and the latter is
constant on comparable pairs, since comparable elements of a disjoint union lie in the same part.

This is the middle term of the Mayer--Vietoris sequence of a cover by stars.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

variable {P : Type u} [PartialOrder P] {ι : Type u}

open scoped Classical in
/-- Folding a disjoint union of stars onto the centres, part by part. -/
noncomputable def famStarCone (V : ι → P) :
    famPoset (fun a => generalStar (V a)) →o famPoset (fun a => generalStar (V a)) where
  toFun q :=
    ⟨((Subtype.val q).1,
        if (Subtype.val q).2 ≤ V (Subtype.val q).1 then V (Subtype.val q).1 else (Subtype.val q).2),
      by
        split_ifs with h
        · exact Or.inl le_rfl
        · exact q.2⟩
  monotone' q q' h := by
    obtain ⟨hidx, hle⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    simp only [hidx]
    by_cases hq : (Subtype.val q).2 ≤ V (Subtype.val q').1
    · by_cases hq' : (Subtype.val q').2 ≤ V (Subtype.val q').1
      · rw [if_pos hq, if_pos hq']
      · rw [if_pos hq, if_neg hq']
        exact (q'.2).resolve_left hq'
    · have hq' : ¬ (Subtype.val q').2 ≤ V (Subtype.val q').1 :=
        fun hcon => hq (le_trans hle hcon)
      rw [if_neg hq, if_neg hq']
      exact hle

/-- Sending every element of a disjoint union of stars to the centre of its own part. -/
def famStarCentre (V : ι → P) :
    famPoset (fun a => generalStar (V a)) →o famPoset (fun a => generalStar (V a)) where
  toFun q := ⟨((Subtype.val q).1, V (Subtype.val q).1), Or.inl le_rfl⟩
  monotone' q q' h := by
    obtain ⟨hidx, -⟩ := famPoset_le_iff.1 h
    refine ⟨hidx, ?_⟩
    show V (Subtype.val q).1 ≤ V (Subtype.val q').1
    exact le_of_eq (congrArg V hidx)

/-- **The disjoint union of a family of stars has no homology in positive degrees.** -/
theorem isZero_homology_nerve_famPoset_generalStar (V : ι → P) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero ((nerve (famPoset (fun a => generalStar (V a)))).homology R n) := by
  classical
  refine isZero_homology_of_locally_conical (famStarCone V) (famStarCentre V)
    (fun q => ?_) (fun q => ?_) (fun q q' h => ?_) R n hn
  · refine famPoset_le_iff.2 ⟨rfl, ?_⟩
    show (Subtype.val q).2 ≤ if (Subtype.val q).2 ≤ V (Subtype.val q).1 then _ else _
    split_ifs with hq
    · exact hq
    · exact le_rfl
  · refine famPoset_le_iff.2 ⟨rfl, ?_⟩
    show V (Subtype.val q).1 ≤ if (Subtype.val q).2 ≤ V (Subtype.val q).1 then _ else _
    split_ifs with hq
    · exact le_rfl
    · exact (q.2).resolve_left hq
  · exact Subtype.ext (Prod.ext (famPoset_le_iff.1 h).1 (congrArg V (famPoset_le_iff.1 h).1))

/-- **And therefore so does the disjoint union of the full subcomplexes they span.** -/
theorem isZero_homology_famSSet_generalStar (V : ι → P) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero
      ((famSSet (fun a => nerveSubcomplex (generalStar (V a)))).homology R n) :=
  Limits.IsZero.of_iso (isZero_homology_nerve_famPoset_generalStar V R n hn)
    (famPosetHomologyIso (fun a => generalStar (V a)) R n)

end GaloisForLFunctions.HTGeometry
