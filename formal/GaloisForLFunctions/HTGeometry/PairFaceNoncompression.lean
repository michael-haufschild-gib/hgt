import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTransverseDADepth
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDifference
import GaloisForLFunctions.HTGeometry.BottomFaceStarIndependence

/-!
# The canonical pair carrier and boundary noncompression

Fix a finite upper-half-plane period family.  For a two-element face `e` the **canonical carrier**
is the composite of the structural transverse differences in every direction outside `e`, applied
to the genuine multiple elliptic gamma logarithmic derivative.  By the coface equation it is the
face coordinate whose surviving parameters are exactly `e`.

Its pair-face signatures are computed without any realization theorem: on `e` itself the carrier is
hypertranscendental as soon as the two periods of `e` are rationally independent together with `1`,
while pushing it toward any other pair deletes one of its two surviving directions and lands in the
differentially algebraic locus.

Consequently no proper subcollection of the pair faces classifies differential algebraicity: for any
omitted pair its own carrier is invisible on every retained face.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Iterated differences of a face -/

/-- **Relative coface equation.**  The composite of the structural transverse differences along a
duplicate-free list of directions, none of them already deleted, deletes exactly those parameters
from a face coordinate. -/
theorem iteratedTransverseDifferenceMero_face
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    ∀ l : List ι, l.Nodup → (∀ q ∈ l, q ∉ J) →
      iteratedTransverseDifferenceMero τ l
          (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        multipleEllipticGammaLogDerivFaceMero τ hτ (J ∪ l.toFinset) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons j l ih =>
      intro hnodup hmem
      have hjl : j ∉ l := (List.nodup_cons.mp hnodup).1
      have hnodupl : l.Nodup := (List.nodup_cons.mp hnodup).2
      have hmeml : ∀ q ∈ l, q ∉ J := fun q hq => hmem q (List.mem_cons_of_mem j hq)
      have hjJ : j ∉ J := hmem j (List.mem_cons_self)
      have hjnew : j ∉ J ∪ l.toFinset := by
        simp only [Finset.mem_union, List.mem_toFinset, not_or]
        exact ⟨hjJ, hjl⟩
      rw [iteratedTransverseDifferenceMero_cons, ih hnodupl hmeml, transverseDifferenceMero,
        multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ _ j hjnew]
      congr 1
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_cons]
      tauto

/-! ### The canonical pair carrier -/

/-- **The canonical carrier of a face.**  The face coordinate whose surviving parameters are exactly
`e`: the composite of the structural transverse differences in every direction outside `e`. -/
def pairFaceCarrier (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (e : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaLogDerivFaceMero τ hτ eᶜ

/-- The carrier is the announced composite of transverse differences. -/
theorem pairFaceCarrier_eq_iteratedTransverseDifference
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (e : Finset ι) :
    pairFaceCarrier τ hτ e =
      iteratedTransverseDifferenceMero τ eᶜ.toList
        (multipleEllipticGammaLogDerivMero τ hτ) := by
  rw [iteratedTransverseDifferenceMero_eq_face τ hτ _ eᶜ.nodup_toList, Finset.toList_toFinset]
  rfl

/-- **The signature of a carrier on another face.**  Delete the surviving directions that the target
face does not see; what is left is the face of the intersection. -/
def pairFaceSignature (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (e f : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaLogDerivFaceMero τ hτ (e ∩ f)ᶜ

@[simp] theorem pairFaceSignature_self (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (e : Finset ι) :
    pairFaceSignature τ hτ e e = pairFaceCarrier τ hτ e := by
  rw [pairFaceSignature, pairFaceCarrier, Finset.inter_self]

/-- The signature is obtained from the carrier by the transverse differences the target face
deletes. -/
theorem pairFaceSignature_eq_iteratedTransverseDifference
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (e f : Finset ι) :
    pairFaceSignature τ hτ e f =
      iteratedTransverseDifferenceMero τ (e \ f).toList (pairFaceCarrier τ hτ e) := by
  rw [pairFaceCarrier, iteratedTransverseDifferenceMero_face τ hτ eᶜ _ (e \ f).nodup_toList
    (by
      intro q hq
      have hqe : q ∈ e \ f := (Finset.mem_toList).mp hq
      simp only [Finset.mem_compl, not_not]
      exact (Finset.mem_sdiff.mp hqe).1),
    Finset.toList_toFinset, pairFaceSignature]
  congr 1
  ext x
  simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, not_and_or]
  tauto

/-! ### The private signature of a pair -/

/-- **The canonical carrier is hypertranscendental on its own face.**  Two surviving directions
whose periods are rationally independent together with `1` keep the carrier outside the
differentially algebraic locus. -/
theorem not_differentialAlgebraicOver_pairFaceCarrier
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {e : Finset ι} {q r : ι}
    (hq : q ∈ e) (hr : r ∈ e) (hqr : q ≠ r)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ) (pairFaceCarrier τ hτ e) :=
  not_differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_independentPair
    τ hτ eᶜ (by simpa using hq) (by simpa using hr) hqr hind

/-- **Off-target signatures vanish.**  If two faces meet in at most one direction, the signature of
the first carrier on the second is differentially algebraic: the push deletes one of the two
surviving directions and leaves a face with at most one survivor. -/
theorem differentialAlgebraicOver_pairFaceSignature_of_inter_subsingleton
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {e f : Finset ι}
    (hmeet : ∀ i j : ι, i ∈ e ∩ f → j ∈ e ∩ f → i = j) :
    DifferentialAlgebraicOver (RatFunc ℂ) (pairFaceSignature τ hτ e f) := by
  refine differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_subsingleton
    τ hτ (e ∩ f)ᶜ ?_
  intro i j hi hj
  refine hmeet i j ?_ ?_
  · simpa using hi
  · simpa using hj

omit [Fintype ι] in
/-- Two distinct two-element faces meet in at most one direction. -/
theorem inter_subsingleton_of_card_two
    {e f : Finset ι} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    ∀ i j : ι, i ∈ e ∩ f → j ∈ e ∩ f → i = j := by
  classical
  intro i j hi hj
  by_contra hij
  have hsub : e ∩ f ⊆ e := Finset.inter_subset_left
  have htwo : 2 ≤ (e ∩ f).card := by
    have hpair : ({i, j} : Finset ι) ⊆ e ∩ f := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hi
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hj
    have hcard : ({i, j} : Finset ι).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
    exact hcard ▸ Finset.card_le_card hpair
  have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hef' : e ⊆ f := by
    intro x hx
    rw [← heq] at hx
    exact (Finset.mem_inter.mp hx).2
  exact hef (Finset.eq_of_subset_of_card_le hef' (by omega))

/-! ### Boundary noncompression -/

/-- **The private pair signature.**  For a pair whose two periods are rationally independent
together with `1`, the canonical carrier is hypertranscendental, while its signature on every other
two-element face is differentially algebraic. -/
theorem pairFaceCarrier_private
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {e : Finset ι} {q r : ι}
    (he : e.card = 2) (hq : q ∈ e) (hr : r ∈ e) (hqr : q ≠ r)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ) (pairFaceCarrier τ hτ e) ∧
      ∀ f : Finset ι, f.card = 2 → f ≠ e →
        DifferentialAlgebraicOver (RatFunc ℂ) (pairFaceSignature τ hτ e f) := by
  refine ⟨not_differentialAlgebraicOver_pairFaceCarrier τ hτ hq hr hqr hind, ?_⟩
  intro f hf hfe
  exact differentialAlgebraicOver_pairFaceSignature_of_inter_subsingleton τ hτ
    (inter_subsingleton_of_card_two he hf (Ne.symm hfe))

/-- **Boundary noncompression.**  Deleting any pair face from the signature atlas loses information:
the omitted pair carries a hypertranscendental element all of whose retained signatures are
differentially algebraic.  No proper subcollection of the two-element faces classifies differential
algebraicity. -/
theorem exists_private_carrier_of_omitted_pair
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {e : Finset ι} {q r : ι}
    (he : e.card = 2) (hq : q ∈ e) (hr : r ∈ e) (hqr : q ≠ r)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r)))
    (E : Set (Finset ι)) (hE : ∀ f ∈ E, f.card = 2 ∧ f ≠ e) :
    ∃ x : meroField (Set.univ : Set ℂ),
      ¬ DifferentialAlgebraicOver (RatFunc ℂ) x ∧
        ∀ f ∈ E, DifferentialAlgebraicOver (RatFunc ℂ) (pairFaceSignature τ hτ e f) ∧
          x = pairFaceCarrier τ hτ e := by
  obtain ⟨hht, hoff⟩ := pairFaceCarrier_private τ hτ he hq hr hqr hind
  refine ⟨pairFaceCarrier τ hτ e, hht, ?_⟩
  intro f hf
  obtain ⟨hcard, hne⟩ := hE f hf
  exact ⟨hoff f hcard hne, rfl⟩

/-! ### The direct sum of the pair sectors -/

/-- The faces obtained by deleting every direction outside a pair. -/
def pairFaceFamily (ι : Type) [Fintype ι] [DecidableEq ι] : Finset (Finset ι) :=
  (Finset.univ.powersetCard 2).image (fun e => eᶜ)

theorem mem_pairFaceFamily_iff {J : Finset ι} :
    J ∈ pairFaceFamily ι ↔ ∃ e : Finset ι, e.card = 2 ∧ eᶜ = J := by
  simp only [pairFaceFamily, Finset.mem_image, Finset.mem_powersetCard_univ]

/-- There are exactly `binom(d, 2)` pair faces. -/
theorem card_pairFaceFamily : (pairFaceFamily ι).card = Nat.choose (Fintype.card ι) 2 := by
  classical
  rw [pairFaceFamily, Finset.card_image_of_injective _ (fun a b hab => by
    simpa using congrArg (fun s : Finset ι => sᶜ) hab), Finset.card_powersetCard,
    Finset.card_univ]

/-- Every pair face deletes the same number of directions. -/
theorem pairFaceFamily_uniform {J : Finset ι} (hJ : J ∈ pairFaceFamily ι) :
    J.card = Fintype.card ι - 2 := by
  obtain ⟨e, hcard, rfl⟩ := mem_pairFaceFamily_iff.mp hJ
  rw [Finset.card_compl, hcard]

/-- Every pair face keeps exactly two directions alive. -/
theorem pairFaceFamily_bottom {J : Finset ι} (hJ : J ∈ pairFaceFamily ι) :
    ∃ a b : ι, a ∉ J ∧ b ∉ J ∧ a ≠ b ∧ ∀ i, i ∉ J → i = a ∨ i = b := by
  classical
  obtain ⟨e, hcard, rfl⟩ := mem_pairFaceFamily_iff.mp hJ
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  refine ⟨a, b, by simp, by simp, hab, ?_⟩
  intro i hi
  have hmem : i ∈ ({a, b} : Finset ι) := by
    by_contra hcon
    exact hi (Finset.mem_compl.mpr hcon)
  rcases Finset.mem_insert.mp hmem with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.mp h)

/-- **The pair sectors are independently addressable.**  For an integrally independent period family
the packets of all `binom(d, 2)` pair faces are jointly differentially independent over the
constants: no pair-private mode is a differential function of the others. -/
theorem pairFaceStar_diffIndepOn (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) :
    DiffIndepOn ℂ (faceStar (pairFaceFamily ι) (multipleEllipticGammaFacePacket τ hτ) ∅) :=
  multipleEllipticGammaFaceStar_diffIndepOn_bottom τ hτ hQ (pairFaceFamily ι)
    (Fintype.card ι - 2) (fun _ hJ => pairFaceFamily_uniform hJ)
    (fun _ hJ => pairFaceFamily_bottom hJ)

/-- The same statement over any differentially algebraic extension of the constants. -/
theorem pairFaceStar_diffIndepOn_daExtension (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ)
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G)
      (faceStar (pairFaceFamily ι) (multipleEllipticGammaFacePacket τ hτ) ∅) :=
  multipleEllipticGammaFaceStar_diffIndepOn_bottom_daExtension τ hτ hQ (pairFaceFamily ι)
    (Fintype.card ι - 2) (fun _ hJ => pairFaceFamily_uniform hJ)
    (fun _ hJ => pairFaceFamily_bottom hJ) hG

end

end GaloisForLFunctions
