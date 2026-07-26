import GaloisForLFunctions.HTGeometry.FieldOneAffineGeometry
import GaloisForLFunctions.HTGeometry.FieldOneCyclotomicExtensions
import GaloisForLFunctions.HTGeometry.FieldOneMultiplicativeCore
import GaloisForLFunctions.HTGeometry.FieldOneSignedAxis

/-!
# Loss-aware doctrine atlas for the field with one element

No literal carrier represents every construction called `F₁`. This file
formalizes the conservative replacement used by the project: a finite doctrine
index, explicit enhancement axes and point functors, and comparison edges whose
non-equivalences must carry a nonempty loss ledger.

This is an organizational construction. A doctrine index is not a formalization
of that doctrine's published scheme theory; exact algebraic certificates remain
in the imported field-one modules.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

universe u v

/-- Major doctrine families represented in the method-neutral field-one atlas. -/
inductive FieldOneDoctrine where
  | pointedMonoids
  | relativeMonoidSchemes
  | souleGadgets
  | blueprints
  | orderedBlueprints
  | bands
  | hyperringsPastures
  | idempotentSemirings
  | characteristicTwo
  | lambdaGeometry
  | durovGeneralizedRings
  | haranNonadditiveGeometry
  | sphereSpectra
  | gammaAlgebras
  | congruenceSpaces
  | arithmeticScalingSites
  deriving DecidableEq, Fintype, Repr

/-- Independent kinds of structure that a doctrine may add to the multiplicative core. -/
inductive EnhancementAxis where
  | multiplicative
  | totalAdditive
  | relationalAdditive
  | ordered
  | descent
  | generalizedOperations
  | homotopical
  | topological
  | analytic
  deriving DecidableEq, Fintype, Repr

/-- Point functors that must remain named rather than conflated. -/
inductive FieldOnePointFunctor where
  | moduleTits
  | monoidPrimeSpectrum
  | monoidProj
  | schemeMorphisms
  | blueSpectrum
  | bandSpectrum
  | hyperringSpectrum
  | congruence
  | tropical
  | geometric
  deriving DecidableEq, Fintype, Repr

/-- Projective point functors whose exact carriers and counts are certified in this project. -/
inductive CertifiedProjectivePointFunctor where
  | moduleTits
  | monoidProj
  deriving DecidableEq, Fintype, Repr

/-- Embed a certified projective point functor into the full point-functor index. -/
def CertifiedProjectivePointFunctor.toPointFunctor :
    CertifiedProjectivePointFunctor → FieldOnePointFunctor
  | .moduleTits => .moduleTits
  | .monoidProj => .monoidProj

/-- Exact point carrier selected by a certified projective point functor. -/
def certifiedProjectivePointCarrier :
    CertifiedProjectivePointFunctor → ℕ → Type
  | .moduleTits, n => {x : FreeFieldOneModule (Fin n) // x ≠ 0}
  | .monoidProj, n => ProjectiveMonoidPoint (Fin n)

/-- Formula paired with each certified projective point functor. -/
def certifiedProjectivePointCount :
    CertifiedProjectivePointFunctor → ℕ → ℕ
  | .moduleTits, n => n
  | .monoidProj, n => 2 ^ n - 1

/-- The named projective point carrier has its paired, previously proved count. -/
theorem certifiedProjectivePointCount_correct
    (p : CertifiedProjectivePointFunctor) (n : ℕ) :
    Nat.card (certifiedProjectivePointCarrier p n) =
      certifiedProjectivePointCount p n := by
  cases p
  · exact card_projectiveModulePoints n
  · exact card_projectiveMonoidSpectrum n

/-- Profile attached to an atlas node. Nonemptiness prevents content-free nodes. -/
structure DoctrineProfile where
  axes : Finset EnhancementAxis
  axes_nonempty : axes.Nonempty
  pointFunctors : Finset FieldOnePointFunctor

/-- Principal axis used to verify that every doctrine family has explicit content. -/
def primaryAxis : FieldOneDoctrine → EnhancementAxis
  | .pointedMonoids => .multiplicative
  | .relativeMonoidSchemes => .multiplicative
  | .souleGadgets => .multiplicative
  | .blueprints => .relationalAdditive
  | .orderedBlueprints => .ordered
  | .bands => .relationalAdditive
  | .hyperringsPastures => .relationalAdditive
  | .idempotentSemirings => .totalAdditive
  | .characteristicTwo => .totalAdditive
  | .lambdaGeometry => .descent
  | .durovGeneralizedRings => .generalizedOperations
  | .haranNonadditiveGeometry => .generalizedOperations
  | .sphereSpectra => .homotopical
  | .gammaAlgebras => .generalizedOperations
  | .congruenceSpaces => .topological
  | .arithmeticScalingSites => .analytic

/-- Explicit doctrine profiles. No profile is declared the universal winner. -/
def doctrineProfile : FieldOneDoctrine → DoctrineProfile
  | .pointedMonoids =>
      ⟨{.multiplicative, .topological}, by simp,
        {.moduleTits, .monoidPrimeSpectrum, .monoidProj}⟩
  | .relativeMonoidSchemes =>
      ⟨{.multiplicative, .topological}, by simp, {.schemeMorphisms}⟩
  | .souleGadgets =>
      ⟨{.multiplicative, .topological}, by simp, {.geometric}⟩
  | .blueprints =>
      ⟨{.multiplicative, .relationalAdditive, .topological}, by simp,
        {.blueSpectrum, .schemeMorphisms}⟩
  | .orderedBlueprints =>
      ⟨{.multiplicative, .relationalAdditive, .ordered, .topological}, by simp,
        {.blueSpectrum, .tropical}⟩
  | .bands =>
      ⟨{.multiplicative, .relationalAdditive, .topological}, by simp,
        {.bandSpectrum, .schemeMorphisms}⟩
  | .hyperringsPastures =>
      ⟨{.multiplicative, .relationalAdditive, .topological}, by simp,
        {.hyperringSpectrum}⟩
  | .idempotentSemirings =>
      ⟨{.multiplicative, .totalAdditive, .ordered, .topological}, by simp,
        {.tropical, .schemeMorphisms}⟩
  | .characteristicTwo =>
      ⟨{.multiplicative, .totalAdditive}, by simp, {.schemeMorphisms}⟩
  | .lambdaGeometry =>
      ⟨{.totalAdditive, .descent, .topological}, by simp, {.schemeMorphisms}⟩
  | .durovGeneralizedRings =>
      ⟨{.generalizedOperations, .topological}, by simp, {.schemeMorphisms}⟩
  | .haranNonadditiveGeometry =>
      ⟨{.generalizedOperations, .topological}, by simp, {.schemeMorphisms}⟩
  | .sphereSpectra =>
      ⟨{.homotopical, .topological}, by simp, {.geometric}⟩
  | .gammaAlgebras =>
      ⟨{.generalizedOperations, .homotopical, .topological}, by simp,
        {.geometric, .monoidPrimeSpectrum}⟩
  | .congruenceSpaces =>
      ⟨{.multiplicative, .topological}, by simp, {.congruence}⟩
  | .arithmeticScalingSites =>
      ⟨{.ordered, .descent, .topological, .analytic}, by simp,
        {.tropical, .geometric}⟩

/-- The declared principal axis occurs in every doctrine profile. -/
theorem primaryAxis_mem_doctrineProfile (d : FieldOneDoctrine) :
    primaryAxis d ∈ (doctrineProfile d).axes := by
  cases d <;> simp [primaryAxis, doctrineProfile]

/-- Every doctrine node has a nonempty enhancement profile. -/
theorem doctrineProfile_nonempty (d : FieldOneDoctrine) :
    (doctrineProfile d).axes.Nonempty :=
  (doctrineProfile d).axes_nonempty

/-- Kinds of morphisms and comparisons admitted as atlas edges. -/
inductive AtlasEdgeKind where
  | equivalence
  | forgetful
  | quotient
  | baseExtension
  | realization
  | comparison
  deriving DecidableEq, Fintype, Repr

/-- Information that may be changed or lost along a non-equivalence edge. -/
inductive AtlasLoss where
  | carrierIdentification
  | additiveRelations
  | nullRelations
  | scalarExtension
  | moduleCategory
  | spectrum
  | pointFunctor
  | exactness
  | homotopyData
  deriving DecidableEq, Fintype, Repr

/-- Provenance status prevents a literature registration from masquerading as a Lean proof. -/
inductive AtlasEvidence where
  | formalized
  | literature
  | mixed
  deriving DecidableEq, Fintype, Repr

/--
A comparison edge is well formed only when every non-equivalence names at
least one loss. An equivalence may have an empty ledger.
-/
structure LossAwareAtlasEdge where
  source : FieldOneDoctrine
  target : FieldOneDoctrine
  kind : AtlasEdgeKind
  evidence : AtlasEvidence
  losses : Finset AtlasLoss
  loss_nonempty : kind ≠ .equivalence → losses.Nonempty

/-- The type-level edge invariant exposes the mandatory loss ledger. -/
theorem nonEquivalence_has_named_loss (e : LossAwareAtlasEdge)
    (h : e.kind ≠ .equivalence) : e.losses.Nonempty :=
  e.loss_nonempty h

/-- Forgetting the signed band's null sums changes relational and scalar-extension data. -/
def signedForgetfulEdge : LossAwareAtlasEdge where
  source := .bands
  target := .pointedMonoids
  kind := .forgetful
  evidence := .formalized
  losses := {.nullRelations, .scalarExtension}
  loss_nonempty := by simp

/-- Collapsing the two signs to the Krasner carrier identifies elements and changes null data. -/
def signCollapseEdge : LossAwareAtlasEdge where
  source := .bands
  target := .hyperringsPastures
  kind := .quotient
  evidence := .mixed
  losses := {.carrierIdentification, .nullRelations}
  loss_nonempty := by simp

/-- Deitmar and relative monoid schemes are registered by a literature equivalence edge. -/
def monoidRelativeEquivalenceEdge : LossAwareAtlasEdge where
  source := .pointedMonoids
  target := .relativeMonoidSchemes
  kind := .equivalence
  evidence := .literature
  losses := ∅
  loss_nonempty := by simp

/-- Coherence facets that any future certified doctrine comparison must address. -/
inductive ComparisonFacet where
  | baseObject
  | freeAlgebra
  | scalarExtension
  | localization
  | spectrum
  | modules
  | pointFunctors
  deriving DecidableEq, Fintype, Repr

/-- Requiring all facets means taking the full finite checklist. -/
def requiredComparisonFacets : Finset ComparisonFacet := Finset.univ

theorem every_comparisonFacet_required (f : ComparisonFacet) :
    f ∈ requiredComparisonFacets :=
  Finset.mem_univ f

/-- Finite, method-neutral organizational atlas for the construction. -/
structure FieldOneDoctrineAtlas where
  profile : FieldOneDoctrine → DoctrineProfile
  edges : List LossAwareAtlasEdge
  multiplicativeCore : FieldOneDoctrine
  core_is_pointedMonoids : multiplicativeCore = .pointedMonoids

/-- The constructed atlas: doctrine profiles plus evidence-labelled comparison edges. -/
def fieldOneDoctrineAtlas : FieldOneDoctrineAtlas where
  profile := doctrineProfile
  edges := [monoidRelativeEquivalenceEdge, signedForgetfulEdge, signCollapseEdge]
  multiplicativeCore := .pointedMonoids
  core_is_pointedMonoids := rfl

/--
No literal carrier can realize both distinguished algebraic bases. This is
the decisive reason that the completed construction is an atlas.
-/
theorem doctrineAtlas_no_literal_common_carrier :
    ∀ (A : Type u), (A ≃ WithZero PUnit.{v + 1}) →
      (A ≃ SignedFieldOne) → False :=
  no_literal_common_carrier

/-- The two certified projective point functors are definitionally distinct. -/
theorem moduleTits_ne_monoidProj :
    FieldOnePointFunctor.moduleTits ≠ .monoidProj := by
  decide

/-- The two total-addition atlas nodes are definitionally distinct. -/
theorem characteristicTwo_ne_idempotent :
    FieldOneDoctrine.characteristicTwo ≠ .idempotentSemirings := by
  decide

end GaloisForLFunctions.HTGeometry.FieldOneCore
