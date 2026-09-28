import GaloisForLFunctions.HTGeometry.AlgebraicGroupPositionVelocity
import GaloisForLFunctions.HTGeometry.DifferentialTranscendenceDegree
import GaloisForLFunctions.HTGeometry.FiniteHolonomyTail
import GaloisForLFunctions.HTGeometry.HypertranscendentalPow
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Corollaries of the isogeny-tail theorems

**Differential transcendence degree.**  A differentially independent family over which every
element is differentially algebraic is a differential transcendence basis.  The jet field
`K = C(J^∞ G)` has differential transcendence degree `dim G` over `C` (basis: a transcendence basis
`t` of `C(G)`), and so does the velocity field `C⟨ℓ⟩`.

**Corollary C (zeroth-to-first-jet transmutation).**  If the iterated kernels of `α` are Zariski
dense, the tail is `C⟨ℓ⟩`, it meets `C(G)` only in `C`, and it has differential transcendence
degree `dim G`.

**Corollary D (finite-holonomy quotients).**  For automorphisms `φ` of `G` commuting with `α`, the
tail of `α*` on the `φ`-invariant part of `K` is the `φ`-invariant part of `K^(H(C))`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-! ### Differential transcendence bases without generation -/

/-- **A differentially independent family over which everything is differentially algebraic
realizes the differential transcendence degree.** -/
theorem differentialTranscendenceDegree_eq_of_differentialAlgebraicOver
    {F E κ : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : κ → E) (hx : DifferentialIndependent F x)
    (halg : ∀ y : E, DifferentialAlgebraicOver (differentialAdjoin F (Set.range x)) y) :
    differentialTranscendenceDegree F E = Cardinal.mk κ := by
  let M := differentialMatroid F E
  have hind : M.Indep (Set.range x) := by
    rw [differentialMatroid_indep_iff]
    exact diffIndepOn_range_of_differentialIndependent hx
  have hclosure : M.closure (Set.range x) = M.E := by
    rw [differentialMatroid_ground]
    apply Set.eq_univ_of_forall
    intro y
    rw [differentialMatroid_mem_closure_iff_of_indep
      (diffIndepOn_range_of_differentialIndependent hx)]
    exact halg y
  have hbase : M.IsBase (Set.range x) := M.isBase_iff_indep_closure_eq.mpr ⟨hind, hclosure⟩
  change M.cRank = Cardinal.mk κ
  exact hbase.cardinalMk_eq_cRank.symm.trans (Cardinal.mk_range_eq x hx.injective)

variable {C : Type u} [Field C] (G : Over (Spec (.of C))) [IsIntegral G.left]
  [LocallyOfFiniteType G.hom] [CharZero C]

/-- The constants carry the zero derivation. -/
@[implicit_reducible]
def trivialDifferential (C : Type u) [Field C] : Differential C := ⟨0⟩

instance groupJetField_charZero : CharZero (GroupJetField G) :=
  charZero_of_injective_algebraMap (algebraMap C (GroupJetField G)).injective

attribute [local instance] trivialDifferential

instance groupJetDifferentialAlgebra : DifferentialAlgebra C (GroupJetField G) :=
  ⟨fun c => by
    change groupJetDerivation G (algebraMap C _ c) = algebraMap C _ ((0 : Derivation ℤ C C) c)
    rw [Derivation.map_algebraMap, Derivation.zero_apply, map_zero]⟩

theorem differentialJet_algebraMap_basis (i : Fin (groupDim G)) (n : ℕ) :
    differentialJet (n + 1) (algebraMap _ (GroupJetField G) (groupBasis G i)) =
      functionJet (i, n) := by
  rw [groupJetDifferentialJet_eq_iterate]
  induction n with
  | zero => rw [Function.iterate_one, jetFieldDerivation_basis]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, jetFieldDerivation_functionJet]

/-- **`dtrdeg_C K = dim G`**: the transcendence basis `t` is a differential transcendence basis of
the jet field. -/
theorem differentialTranscendenceDegree_groupJetField :
    differentialTranscendenceDegree C (GroupJetField G) = groupDim G := by
  classical
  let t := groupBasis G
  have ht : IsTranscendenceBasis C t := groupBasis_isTranscendenceBasis G
  let x : Fin (groupDim G) → GroupJetField G := fun i => algebraMap _ (GroupJetField G) (t i)
  -- the jets of `t` are `t` itself and the free jet coordinates
  have hy : AlgebraicIndependent G.left.functionField
      (functionJet : Fin (groupDim G) × ℕ → GroupJetField G) :=
    (MvPolynomial.algebraicIndependent_X (Fin (groupDim G) × ℕ) G.left.functionField).map'
      (f := IsScalarTower.toAlgHom G.left.functionField (FunctionJetPoly G.left.functionField
        (groupDim G)) (GroupJetField G)) (IsFractionRing.injective _ _)
  have hsum := ht.1.sumElim_comp hy
  let e : Fin (groupDim G) × ℕ ≃ (Fin (groupDim G) × ℕ) ⊕ Fin (groupDim G) :=
    { toFun := fun
        | (i, 0) => Sum.inr i
        | (i, n + 1) => Sum.inl (i, n)
      invFun := fun
        | Sum.inl q => (q.1, q.2 + 1)
        | Sum.inr i => (i, 0)
      left_inv := fun
        | (i, 0) => rfl
        | (i, n + 1) => rfl
      right_inv := fun
        | Sum.inl q => rfl
        | Sum.inr i => rfl }
  have he0 : ∀ i, e (i, 0) = Sum.inr i := fun _ => rfl
  have he1 : ∀ i n, e (i, n + 1) = Sum.inl (i, n) := fun _ _ => rfl
  have hfam : (fun p : Fin (groupDim G) × ℕ => differentialJet p.2 (x p.1)) =
      (Sum.elim functionJet (algebraMap _ (GroupJetField G) ∘ t)) ∘ e := by
    funext p
    obtain ⟨i, n⟩ := p
    cases n with
    | zero =>
        rw [Function.comp_apply, he0, Sum.elim_inr, differentialJet_zero]
        rfl
    | succ n =>
        rw [Function.comp_apply, he1, Sum.elim_inl]
        exact differentialJet_algebraMap_basis G i n
  have hind : DifferentialIndependent C x := by
    unfold DifferentialIndependent
    rw [hfam]
    exact hsum.comp e e.injective
  -- reindex by a type in the universe of `K`
  let x' : ULift.{u} (Fin (groupDim G)) → GroupJetField G := fun i => x i.down
  have hind' : DifferentialIndependent C x' := by
    unfold DifferentialIndependent at hind ⊢
    have hfun : (fun p : ULift.{u} (Fin (groupDim G)) × ℕ => differentialJet p.2 (x' p.1)) =
        (fun p : Fin (groupDim G) × ℕ => differentialJet p.2 (x p.1)) ∘
          (fun p : ULift.{u} (Fin (groupDim G)) × ℕ => (p.1.down, p.2)) := by
      funext p
      rfl
    rw [hfun]
    exact hind.comp _ fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (ULift.ext _ _ h.1) h.2
  have hrange : Set.range x' = Set.range x :=
    Set.ext fun v => ⟨fun ⟨i, hi⟩ => ⟨i.down, hi⟩, fun ⟨i, hi⟩ => ⟨⟨i⟩, hi⟩⟩
  have hdim : Cardinal.mk (ULift.{u} (Fin (groupDim G))) = groupDim G := by simp
  rw [differentialTranscendenceDegree_eq_of_differentialAlgebraicOver x' hind', hdim]
  -- every element of `K` is algebraic over `C⟨t⟩`
  intro u
  rw [hrange]
  let B := differentialAdjoin C (Set.range x)
  refine differentialAlgebraicOver_of_isAlgebraic (A := B) ?_
  have hxB : ∀ i, x i ∈ B := fun i => subset_differentialAdjoin C _ ⟨i, rfl⟩
  have hjetB : ∀ p, (functionJet p : GroupJetField G) ∈ B := by
    rintro ⟨i, n⟩
    rw [← differentialJet_algebraMap_basis G i n]
    exact IntermediateField.subset_adjoin C _ ⟨x i, ⟨i, rfl⟩, n + 1, rfl⟩
  have hFalg : ∀ a : G.left.functionField,
      algebraMap _ (GroupJetField G) a ∈ algebraicClosure B (GroupJetField G) := by
    intro a
    let L' : IntermediateField C G.left.functionField :=
      IntermediateField.comap (IsScalarTower.toAlgHom C G.left.functionField (GroupJetField G)) B
    have hle : IntermediateField.adjoin C (Set.range t) ≤ L' := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact hxB i
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range t)) G.left.functionField :=
      ht.isAlgebraic_field
    have ha : IsAlgebraic L' a := by
      letI : Algebra (IntermediateField.adjoin C (Set.range t)) L' :=
        (IntermediateField.inclusion hle).toAlgebra
      haveI : IsScalarTower (IntermediateField.adjoin C (Set.range t)) L' G.left.functionField :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact (Algebra.IsAlgebraic.isAlgebraic a).extendScalars
        (IntermediateField.inclusion_injective hle)
    let φ : L' →+* B :=
      { toFun := fun z => ⟨algebraMap _ (GroupJetField G) z, z.2⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun a b => Subtype.ext (map_add _ _ _) }
    rw [mem_algebraicClosure_iff']
    exact IsIntegral.map_of_comp_eq φ (algebraMap G.left.functionField (GroupJetField G))
      (RingHom.ext fun _ => rfl) ha.isIntegral
  let A : IntermediateField G.left.functionField (GroupJetField G) :=
    (algebraicClosure B (GroupJetField G)).toSubfield.toIntermediateField hFalg
  have hA : IntermediateField.adjoin G.left.functionField
      (Set.range (functionJet : Fin (groupDim G) × ℕ → GroupJetField G)) ≤ A := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact (mem_algebraicClosure_iff' (F := B)).mpr
      (isIntegral_algebraMap (x := (⟨functionJet p, hjetB p⟩ : B)))
  rw [adjoin_functionJet_eq_top, top_le_iff] at hA
  have hu : u ∈ A := by rw [hA]; exact IntermediateField.mem_top
  exact isAlgebraic_iff_isIntegral.mpr hu

/-! ### The velocity field -/

theorem differentialJet_algebraMap_const (c : C) (n : ℕ) :
    differentialJet (n + 1) (algebraMap C (GroupJetField G) c) = 0 := by
  rw [groupJetDifferentialJet_eq_iterate, Function.iterate_succ_apply]
  rw [show groupJetDerivation G (algebraMap C (GroupJetField G) c) = 0 from
    Derivation.map_algebraMap _ c]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- Adjoining constants does not change a differential adjoin. -/
theorem differentialAdjoin_union_constants (s : Set (GroupJetField G)) :
    differentialAdjoin C (Set.range (algebraMap C (GroupJetField G)) ∪ s) =
      differentialAdjoin C s := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, hy | hy, n, rfl⟩
    · obtain ⟨c, rfl⟩ := hy
      cases n with
      | zero => rw [differentialJet_zero]; exact IntermediateField.algebraMap_mem _ c
      | succ n => rw [differentialJet_algebraMap_const]; exact IntermediateField.zero_mem _
    · exact IntermediateField.subset_adjoin C _ ⟨y, hy, n, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨y, hy, n, rfl⟩
    exact IntermediateField.subset_adjoin C _ ⟨y, Or.inr hy, n, rfl⟩

variable [GrpObj G] [IsCommMonObj G]

/-- **The Maurer–Cartan velocity is differentially independent over `C`.** -/
theorem mcVelocity_differentialIndependent : DifferentialIndependent C (mcVelocity G) := by
  have h := (algebraicIndependent_maurerCartanJet (groupBasis_isTranscendenceBasis G)
    (mcDerivation_det_ne_zero G)).restrictScalars (R := C)
    (algebraMap C G.left.functionField).injective
  unfold DifferentialIndependent
  have hfun : (fun p : Fin (groupDim G) × ℕ => differentialJet p.2 (mcVelocity G p.1)) =
      maurerCartanJet (D := mcDerivation G) (groupBasis_isTranscendenceBasis G) ∘
        (fun p => (p.2, p.1)) := by
    funext p
    rfl
  rw [hfun]
  exact h.comp _ fun p q h' => by
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext h'.2 h'.1

/-- The velocity field `C⟨ℓ⟩`. -/
abbrev maurerCartanVelocityField : IntermediateField C (GroupJetField G) :=
  differentialAdjoin C (Set.range (mcVelocity G))

theorem maurerCartanVelocityField_derivationClosed :
    DerivationClosed (maurerCartanVelocityField G) :=
  derivationClosed_differentialAdjoin C _

/-- The velocity field as a differential field. -/
@[implicit_reducible]
def maurerCartanVelocityFieldDifferential : Differential (maurerCartanVelocityField G) :=
  derivationClosedDifferential _ (maurerCartanVelocityField_derivationClosed G)

attribute [local instance] maurerCartanVelocityFieldDifferential

instance maurerCartanVelocityField_differentialAlgebra :
    DifferentialAlgebra C (maurerCartanVelocityField G) :=
  ⟨fun c => Subtype.ext (by
    change groupJetDerivation G (algebraMap C (GroupJetField G) c) =
      algebraMap C (GroupJetField G) ((0 : Derivation ℤ C C) c)
    rw [Derivation.map_algebraMap, Derivation.zero_apply, map_zero])⟩

instance maurerCartanVelocityField_charZero : CharZero (maurerCartanVelocityField G) :=
  charZero_of_injective_algebraMap (algebraMap C (maurerCartanVelocityField G)).injective

theorem val_differentialJet_velocityField (n : ℕ) (y : maurerCartanVelocityField G) :
    ((differentialJet n y : maurerCartanVelocityField G) : GroupJetField G) =
      differentialJet n (y : GroupJetField G) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, ← ih y]
      rfl

/-- **`dtrdeg_C C⟨ℓ⟩ = dim G`.** -/
theorem differentialTranscendenceDegree_velocityField :
    differentialTranscendenceDegree C (maurerCartanVelocityField G) = groupDim G := by
  let xL : ULift.{u} (Fin (groupDim G)) → maurerCartanVelocityField G := fun i =>
    ⟨mcVelocity G i.down, subset_differentialAdjoin C _ ⟨i.down, rfl⟩⟩
  have hind : DifferentialIndependent C xL := by
    unfold DifferentialIndependent
    refine AlgebraicIndependent.of_comp (maurerCartanVelocityField G).val ?_
    have hK := mcVelocity_differentialIndependent G
    unfold DifferentialIndependent at hK
    have hfun : (maurerCartanVelocityField G).val ∘ (fun p : ULift.{u} (Fin (groupDim G)) × ℕ =>
        differentialJet p.2 (xL p.1)) =
        (fun p : Fin (groupDim G) × ℕ => differentialJet p.2 (mcVelocity G p.1)) ∘
          (fun p => (p.1.down, p.2)) := by
      funext p
      exact val_differentialJet_velocityField G p.2 (xL p.1)
    rw [hfun]
    exact hK.comp _ fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (ULift.ext _ _ h.1) h.2
  have hgen : differentialAdjoin C (Set.range xL) = ⊤ := by
    apply IntermediateField.lift_injective (maurerCartanVelocityField G)
    rw [IntermediateField.lift_top, differentialAdjoin, IntermediateField.lift_adjoin]
    congr 1
    ext v
    constructor
    · rintro ⟨w, ⟨y, ⟨i, rfl⟩, n, rfl⟩, rfl⟩
      exact ⟨mcVelocity G i.down, ⟨i.down, rfl⟩, n,
        (val_differentialJet_velocityField G n (xL i)).symm⟩
    · rintro ⟨y, ⟨i, rfl⟩, n, rfl⟩
      exact ⟨differentialJet n (xL ⟨i⟩), ⟨xL ⟨i⟩, ⟨⟨i⟩, rfl⟩, n, rfl⟩,
        val_differentialJet_velocityField G n (xL ⟨i⟩)⟩
  rw [differentialTranscendenceDegree_eq_cardinalMk_of_differentialIndependent_of_adjoin_eq_top
    xL hind hgen]
  simp

/-! ### Corollary C: the purely expanding case -/

variable [IsAlgClosed C] (α : G ⟶ G) [IsIsogeny G α]

omit [IsIntegral G.left] [LocallyOfFiniteType G.hom] [CharZero C] [IsCommMonObj G] [IsAlgClosed C]
  [IsIsogeny G α] in
theorem deckClosurePoints_eq_univ_of_dense
    (hdense : Dense (⋃ n, (fun c => rationalPointHom G c default) '' isogenyKernelPoints G α n)) :
    deckClosurePoints G α = Set.univ :=
  Set.eq_univ_of_forall fun x => by
    change rationalPointHom G x default ∈ closure _
    rw [hdense.closure_eq]
    trivial

omit [CharZero C] [IsIsogeny G α] in
theorem deckClosurePositions_eq_of_dense
    (hdense : Dense (⋃ n, (fun c => rationalPointHom G c default) '' isogenyKernelPoints G α n)) :
    deckClosurePositions G α = Set.range (algebraMap C G.left.functionField) := by
  ext a
  constructor
  · intro ha
    exact mem_range_algebraMap_of_translation_fixed G a fun x =>
      ha x (by rw [deckClosurePoints_eq_univ_of_dense G α hdense]; trivial)
  · rintro ⟨c, rfl⟩ x _
    exact AlgEquiv.commutes _ c

/-- **Corollary C, (5)**: if the iterated kernels are Zariski dense, the tail is the velocity
field, `Tail(α) = C⟨ℓ⟩`. -/
theorem mem_isogenyTail_iff_mem_velocityField
    (hdense : Dense (⋃ n, (fun c => rationalPointHom G c default) '' isogenyKernelPoints G α n))
    (u : GroupJetField G) :
    (∀ n, u ∈ Set.range ((⇑(jetIsogenyPullback G α))^[n])) ↔ u ∈ maurerCartanVelocityField G := by
  have hcomp : ⇑(algebraMap G.left.functionField (GroupJetField G)) ∘
      ⇑(algebraMap C G.left.functionField) = ⇑(algebraMap C (GroupJetField G)) := by
    funext c
    exact (IsScalarTower.algebraMap_apply C G.left.functionField (GroupJetField G) c).symm
  rw [mem_isogenyTail_iff_deckClosure_fixed, deckClosure_fixed_iff_mem_differentialAdjoin,
    deckClosurePositions_eq_of_dense G α hdense, ← Set.range_comp, hcomp,
    differentialAdjoin_union_constants]

/-- **Corollary C, (6)**: the tail meets the rational functions of `G` only in the constants. -/
theorem algebraMap_mem_isogenyTail_iff
    (hdense : Dense (⋃ n, (fun c => rationalPointHom G c default) '' isogenyKernelPoints G α n))
    (f : G.left.functionField) :
    (∀ n, algebraMap _ (GroupJetField G) f ∈ Set.range ((⇑(jetIsogenyPullback G α))^[n])) ↔
      f ∈ Set.range (algebraMap C G.left.functionField) := by
  rw [mem_isogenyTail_iff_deckClosure_fixed, deckClosurePoints_eq_univ_of_dense G α hdense]
  constructor
  · intro h
    refine mem_range_algebraMap_of_translation_fixed G f fun x => ?_
    have hx := h x trivial
    rw [jetTranslation, jetFieldExtension_algebraMap] at hx
    exact (algebraMap _ (GroupJetField G)).injective hx
  · rintro ⟨c, rfl⟩ x _
    rw [jetTranslation, jetFieldExtension_algebraMap]
    exact congrArg _ (AlgEquiv.commutes _ c)

/-! ### Corollary D: finite-holonomy quotients -/

/-- The pullback of an automorphism of `G` to the jet field. -/
def jetAutomorphismPullback (φ : G ≅ G) : GroupJetField G →+* GroupJetField G :=
  jetFieldExtension (groupBasis_isTranscendenceBasis G) (overFunctionFieldPullback G φ.hom)

/-- The holonomy maps on the jet field. -/
def holonomyMaps (Φ : Set (G ≅ G)) : Set (GroupJetField G → GroupJetField G) :=
  (fun φ => ⇑(jetAutomorphismPullback G φ)) '' Φ

omit [IsAlgClosed C] [IsCommMonObj G] in
/-- An automorphism commuting with `α` commutes with `α*` on the jet field. -/
theorem jetIsogenyPullback_jetAutomorphismPullback (φ : G ≅ G) (hφ : φ.hom ≫ α = α ≫ φ.hom)
    (u : GroupJetField G) :
    jetIsogenyPullback G α (jetAutomorphismPullback G φ u) =
      jetAutomorphismPullback G φ (jetIsogenyPullback G α u) := by
  have hc : (overFunctionFieldPullback G α).comp (overFunctionFieldPullback G φ.hom) =
      (overFunctionFieldPullback G φ.hom).comp (overFunctionFieldPullback G α) := by
    ext a
    simp only [AlgHom.comp_apply, overFunctionFieldPullback_apply]
    have h := Scheme.Hom.functionFieldPullback_congr (α.left ≫ φ.hom.left) (φ.hom.left ≫ α.left)
      (congrArg CommaMorphism.left hφ).symm
    rw [Scheme.Hom.functionFieldPullback_comp, Scheme.Hom.functionFieldPullback_comp] at h
    exact congrArg (fun q : G.left.functionField ⟶ G.left.functionField => q a) h
  have := congrArg (fun f : GroupJetField G →+* GroupJetField G => f u)
    (congrArg (jetFieldExtension (groupBasis_isTranscendenceBasis G)) hc)
  simp only [jetFieldExtension_comp, RingHom.comp_apply] at this
  exact this

/-- **Corollary D (finite holonomy).**  For automorphisms of `G` commuting with the isogeny, the
tail of `α*` on the holonomy-invariant part of the jet field is the holonomy-invariant part of
`K^(H(C))`: `⋂_n α^(n*) (K^Φ) = (K^(H(C)))^Φ`. -/
theorem finiteHolonomyTail (Φ : Set (G ≅ G)) (hΦ : ∀ φ ∈ Φ, φ.hom ≫ α = α ≫ φ.hom) :
    (⋂ n, (⇑(jetIsogenyPullback G α))^[n] '' fixedSubset (holonomyMaps G Φ) Set.univ) =
      fixedSubset (holonomyMaps G Φ)
        {u | ∀ x ∈ deckClosurePoints G α, jetTranslation G x u = u} := by
  have hinj : ∀ n, Function.Injective ((⇑(jetIsogenyPullback G α))^[n]) := fun n =>
    (jetIsogenyPullback G α).injective.iterate n
  have hcomm : ∀ n, ∀ f ∈ holonomyMaps G Φ, ∀ x,
      (⇑(jetIsogenyPullback G α))^[n] (f x) = f ((⇑(jetIsogenyPullback G α))^[n] x) := by
    rintro n _ ⟨φ, hφΦ, rfl⟩ x
    have hc : Function.Commute (jetIsogenyPullback G α) (jetAutomorphismPullback G φ) :=
      fun u => jetIsogenyPullback_jetAutomorphismPullback G α φ (hΦ φ hφΦ) u
    exact (hc.iterate_left n) x
  rw [iInter_image_fixedSubset (holonomyMaps G Φ) (fun n => (⇑(jetIsogenyPullback G α))^[n])
    hinj hcomm Set.univ]
  congr 1
  ext u
  simp only [Set.image_univ, Set.mem_iInter, Set.mem_setOf_eq]
  exact mem_isogenyTail_iff_deckClosure_fixed G α u

/-- **Corollary D, (9)**: in the purely expanding case the holonomy tail is the
holonomy-invariant part of the velocity field. -/
theorem finiteHolonomyTail_of_dense (Φ : Set (G ≅ G)) (hΦ : ∀ φ ∈ Φ, φ.hom ≫ α = α ≫ φ.hom)
    (hdense : Dense (⋃ n, (fun c => rationalPointHom G c default) '' isogenyKernelPoints G α n)) :
    (⋂ n, (⇑(jetIsogenyPullback G α))^[n] '' fixedSubset (holonomyMaps G Φ) Set.univ) =
      fixedSubset (holonomyMaps G Φ) (maurerCartanVelocityField G : Set (GroupJetField G)) := by
  rw [finiteHolonomyTail G α Φ hΦ]
  congr 1
  ext u
  change (∀ x ∈ deckClosurePoints G α, jetTranslation G x u = u) ↔ u ∈ maurerCartanVelocityField G
  rw [← mem_isogenyTail_iff_deckClosure_fixed, mem_isogenyTail_iff_mem_velocityField G α hdense]

end

end GaloisForLFunctions.HTGeometry
