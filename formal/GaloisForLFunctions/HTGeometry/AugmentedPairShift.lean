import GaloisForLFunctions.HTGeometry.AugmentedShift
import GaloisForLFunctions.HTGeometry.ExcisionPair

/-!
# The augmented relative complex of a pair is the ordinary one, shifted

The relative complex of a pair of subspaces, formed inside the augmented complex, agrees with the
ordinary relative complex one degree lower.  This is what transfers excision into the reduced world.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

theorem augSub_carrier_mono {S T : Set X} (h : S ⊆ T) :
    ∀ k, (augSub R X S).carrier k ≤ (augSub R X T).carrier k := by
  intro k
  cases k with
  | zero => exact le_refl _
  | succ n => exact subChains_mono R h n

/-- The chains supported in `S`, inside the augmented chains supported in `T`. -/
noncomputable def augPairSub {S T : Set X} (h : S ⊆ T) :
    ModuleSubcomplex R ((augSub R X T).complex) :=
  ModuleSubcomplex.restrictTo (augSub R X T) (augSub R X S) (augSub_carrier_mono R h)

theorem augPair_d_eq {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (augPairSub R h).quotComplex.d (n + 2) (n + 1)
      = (pairSub R h).quotComplex.d (n + 1) n := by
  rw [ModuleSubcomplex.quotComplex_d, ModuleSubcomplex.quotComplex_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective ((augPairSub R h).carrier (n + 2)) x
  show Submodule.Quotient.mk (((augSub R X T).complex.d (n + 2) (n + 1)) c)
    = (Submodule.Quotient.mk (((subcomplexOfSubset R T).complex.d (n + 1) n) c) :
        _ ⧸ (pairSub R h).carrier n)
  rw [augSub_d_eq]
  rfl

/-- Above degree one the augmented relative complex agrees with the ordinary one, shifted. -/
noncomputable def augPairQuotShiftSc {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (augPairSub R h).quotComplex.sc' (n + 3) (n + 2) (n + 1)
      ≅ (pairSub R h).quotComplex.sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      show 𝟙 _ ≫ (pairSub R h).quotComplex.d (n + 2) (n + 1)
        = (augPairSub R h).quotComplex.d (n + 3) (n + 2) ≫ 𝟙 _
      rw [augPair_d_eq R h (n + 1)]
      simp)
    (by
      show 𝟙 _ ≫ (pairSub R h).quotComplex.d (n + 1) n
        = (augPairSub R h).quotComplex.d (n + 2) (n + 1) ≫ 𝟙 _
      rw [augPair_d_eq R h n]
      simp)

noncomputable def augPairQuotHomologyShiftSucc {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (augPairSub R h).quotComplex.homology (n + 2)
      ≅ (pairSub R h).quotComplex.homology (n + 1) :=
  ShortComplex.homologyMapIso ((augPairSub R h).quotComplex.isoSc' (n + 3) (n + 2) (n + 1)
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _)) ≪≫
    ShortComplex.homologyMapIso (augPairQuotShiftSc R h n) ≪≫
    (ShortComplex.homologyMapIso ((pairSub R h).quotComplex.isoSc'
      (n + 2) (n + 1) n (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _))).symm

end GaloisForLFunctions.HTGeometry
