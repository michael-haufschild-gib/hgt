import GaloisForLFunctions.HTGeometry.SquareZeroPointLifts
import GaloisForLFunctions.HTGeometry.FractionRingDerivation

/-!
# Derivations of the function field of an algebraic group and tangent vectors at the identity

Let `G` be an integral group scheme over `C` with function field `F` and generic point `g`.

* **Derivations are lifts of the generic point.**  A `C`-derivation `D` of `F` gives the
  `F[ε]`-point `g_D = g ∘ Spec(a ↦ a + εDa)`, and every `F[ε]`-point reducing to `g` is some `g_D`,
  for a unique `D`.
* **Tangent vectors.**  `u_D = g_D · g_0⁻¹` reduces to the identity; it is a stalk point at the
  identity `e`, given by a lift `χ_D : O_(G,e) → F[ε]` of the evaluation `O_(G,e) → C → F`.
* **Linearity.**  `u_(D₁+D₂) = u_(D₁) u_(D₂)` and `χ_(D₁+D₂) = χ_(D₁) ⊞ χ_(D₂)` (the group law on
  lifts is addition), and `χ_(aD)` is `χ_D` with the `ε`-part scaled by `a`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C : Type u} [Field C] (G : Over (Spec (.of C)))

/-! ### Derivations of the function field as lifts of the generic point -/

section Generic

variable [IsIntegral G.left]

theorem stalkConstants_genericPoint :
    stalkConstants G (genericPoint G.left) =
      CommRingCat.ofHom (algebraMap C G.left.functionField) :=
  Spec.map_injective ((fromSpecStalk_comp_hom G _).symm.trans
    (fromSpecStalk_genericPoint_comp_hom G))

/-- The identity of the function field, as the stalk homomorphism of the generic point. -/
abbrev genericStalkId : G.left.presheaf.stalk (genericPoint G.left) ⟶
    CommRingCat.of G.left.functionField :=
  CommRingCat.ofHom (RingHom.id G.left.functionField)

theorem stalkConstants_genericPoint_comp_id :
    stalkConstants G (genericPoint G.left) ≫ genericStalkId G =
      CommRingCat.ofHom (algebraMap C G.left.functionField) := by
  rw [stalkConstants_genericPoint]
  rfl

theorem genericPointHom_eq_stalkPoint :
    genericPointHom G = stalkPoint G (genericPoint G.left) (genericStalkId G)
      (stalkConstants_genericPoint_comp_id G) := by
  apply Over.OverMorphism.ext
  change G.left.fromSpecStalk (genericPoint G.left) =
    Spec.map (𝟙 _) ≫ G.left.fromSpecStalk (genericPoint G.left)
  rw [Spec.map_id, Category.id_comp]

variable (L : Type u) [Field L] [Algebra C L] [Algebra G.left.functionField L]
  [IsScalarTower C G.left.functionField L]

/-- The graph `a ↦ a + ε D a` of a derivation `D : F → L`. -/
abbrev dualGraph (D : Derivation C G.left.functionField L) :
    G.left.functionField →ₐ[C] DualL L :=
  derivationGraphAlgHom D

@[simp]
theorem dualGraph_fst (D : Derivation C G.left.functionField L) (a : G.left.functionField) :
    (dualGraph G L D a).fst = algebraMap _ L a := rfl

@[simp]
theorem dualGraph_snd (D : Derivation C G.left.functionField L) (a : G.left.functionField) :
    (dualGraph G L D a).snd = D a := rfl

/-- The generic point with values in an extension `L` of the function field. -/
abbrev genericPointAt : algebraicPointSource (K := C) (R := L) ⟶ G :=
  pointSourceMap (IsScalarTower.toAlgHom C G.left.functionField L) ≫ genericPointHom G

/-- The stalk homomorphism of the generic point with values in `L`. -/
abbrev genericStalkAt : G.left.presheaf.stalk (genericPoint G.left) ⟶ CommRingCat.of L :=
  CommRingCat.ofHom (algebraMap G.left.functionField L)

theorem genericStalkAt_const :
    stalkConstants G (genericPoint G.left) ≫ genericStalkAt G L =
      CommRingCat.ofHom (algebraMap C L) := by
  rw [stalkConstants_genericPoint]
  exact CommRingCat.hom_ext (RingHom.ext fun c =>
    (IsScalarTower.algebraMap_apply C G.left.functionField L c).symm)

instance isLocalHom_genericStalkAt : IsLocalHom (genericStalkAt G L).hom :=
  inferInstanceAs (IsLocalHom (algebraMap G.left.functionField L))

theorem genericPointAt_eq_stalkPoint :
    genericPointAt G L = stalkPoint G (genericPoint G.left) (genericStalkAt G L)
      (genericStalkAt_const G L) := by
  rw [genericPointAt, genericPointHom_eq_stalkPoint, pointSourceMap_comp_stalkPoint]
  exact stalkPoint_congr G _ rfl _ _

/-- The lift `g_D` of the generic point along `L[ε] → L`. -/
def genericLift (D : Derivation C G.left.functionField L) :
    algebraicPointSource (K := C) (R := DualL L) ⟶ G :=
  pointSourceMap (dualGraph G L D) ≫ genericPointHom G

theorem dualGraph_const (D : Derivation C G.left.functionField L) :
    stalkConstants G (genericPoint G.left) ≫ CommRingCat.ofHom (dualGraph G L D).toRingHom =
      CommRingCat.ofHom (algebraMap C (DualL L)) := by
  rw [stalkConstants_genericPoint]
  exact CommRingCat.hom_ext (RingHom.ext fun c => (dualGraph G L D).commutes c)

theorem genericLift_eq_stalkPoint (D : Derivation C G.left.functionField L) :
    genericLift G L D = stalkPoint G (genericPoint G.left)
      (CommRingCat.ofHom (dualGraph G L D).toRingHom) (dualGraph_const G L D) := by
  rw [genericLift, genericPointHom_eq_stalkPoint, pointSourceMap_comp_stalkPoint]
  exact stalkPoint_congr G _ rfl _ _

theorem dualGraph_comp_sqzFst (D : Derivation C G.left.functionField L) :
    CommRingCat.ofHom (dualGraph G L D).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = genericStalkAt G L :=
  rfl

instance isLocalHom_dualGraph (D : Derivation C G.left.functionField L) :
    IsLocalHom (CommRingCat.ofHom (dualGraph G L D).toRingHom).hom :=
  isLocalHom_of_fst_comp _ (algebraMap G.left.functionField L) fun _ => rfl

/-- **The lift determines the derivation.** -/
theorem genericLift_injective {D₁ D₂ : Derivation C G.left.functionField L}
    (h : genericLift G L D₁ = genericLift G L D₂) : D₁ = D₂ := by
  rw [genericLift_eq_stalkPoint, genericLift_eq_stalkPoint] at h
  have h' := stalkPoint_injective G h
  ext a
  exact congrArg (fun q : G.left.functionField ⟶ CommRingCat.of (DualL L) => (q a).snd) h'

/-- The reduction of a lift of the generic point. -/
theorem sqzFst_genericLift (D : Derivation C G.left.functionField L) :
    pointSourceMap (sqzFst (C := C) (L := L) (M := L)) ≫ genericLift G L D =
      genericPointAt G L := by
  rw [genericLift, ← Category.assoc, ← pointSourceMap_comp]
  have h : (sqzFst (C := C) (L := L) (M := L)).comp (dualGraph G L D) =
      IsScalarTower.toAlgHom C G.left.functionField L := AlgHom.ext fun _ => rfl
  rw [h]

/-- **Every lift of the generic point along `L[ε] → L` comes from a derivation.** -/
theorem exists_genericLift_eq (w : algebraicPointSource (K := C) (R := DualL L) ⟶ G)
    (hw : pointSourceMap (sqzFst (C := C) (L := L) (M := L)) ≫ w = genericPointAt G L) :
    ∃ D : Derivation C G.left.functionField L, w = genericLift G L D := by
  rw [genericPointAt_eq_stalkPoint] at hw
  obtain ⟨ψ, hψ, hψφ, rfl⟩ := exists_stalkPoint_of_lift G _ (genericStalkAt G L) _ w hw
  have hfst : ∀ a, (ψ a).fst = algebraMap G.left.functionField L a := fun a =>
    congrArg (fun q : G.left.presheaf.stalk (genericPoint G.left) ⟶ _ => q a) hψφ
  have hconst : ∀ c : C, ψ (algebraMap C G.left.functionField c) =
      algebraMap C (DualL L) c := by
    intro c
    rw [stalkConstants_genericPoint] at hψ
    exact congrArg (fun q : CommRingCat.of C ⟶ _ => q c) hψ
  let D : Derivation C G.left.functionField L :=
    Derivation.mk'
      { toFun := fun a => (ψ a).snd
        map_add' := fun a b => by rw [map_add, TrivSqZeroExt.snd_add]
        map_smul' := fun c a => by
          have hc : algebraMap C (DualL L) c = TrivSqZeroExt.inl (algebraMap C L c) := rfl
          rw [RingHom.id_apply, Algebra.smul_def, map_mul, hconst, TrivSqZeroExt.snd_mul, hc,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul,
            Algebra.smul_def] }
      (fun a b => by
        change (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, Algebra.smul_def a, Algebra.smul_def b,
          smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring)
  refine ⟨D, ?_⟩
  rw [genericLift_eq_stalkPoint]
  apply stalkPoint_congr
  exact CommRingCat.hom_ext (RingHom.ext fun a => TrivSqZeroExt.ext (hfst a) rfl)

end Generic

/-! ### The identity point and its tangent vectors -/

section Identity

variable [GrpObj G]

/-- The identity element as a `C`-valued point. -/
def identityPointC : algebraicPointSource (K := C) (R := C) ⟶ G := toUnit _ ≫ η[G]

theorem exists_identityPointC_eq_stalkPoint :
    ∃ (x : G.left) (ψ : G.left.presheaf.stalk x ⟶ CommRingCat.of C)
      (hψ : stalkConstants G x ≫ ψ = CommRingCat.ofHom (algebraMap C C)),
      IsLocalHom ψ.hom ∧ identityPointC G = stalkPoint G x ψ hψ :=
  exists_eq_stalkPoint G _

/-- The point `e ∈ G` underlying the identity. -/
def identityCenter : G.left := (exists_identityPointC_eq_stalkPoint G).choose

/-- Evaluation at the identity, `O_(G,e) → C`. -/
def identityEval : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of C :=
  (exists_identityPointC_eq_stalkPoint G).choose_spec.choose

theorem identityEval_const :
    stalkConstants G (identityCenter G) ≫ identityEval G = CommRingCat.ofHom (algebraMap C C) :=
  (exists_identityPointC_eq_stalkPoint G).choose_spec.choose_spec.choose

instance isLocalHom_identityEval : IsLocalHom (identityEval G).hom :=
  (exists_identityPointC_eq_stalkPoint G).choose_spec.choose_spec.choose_spec.1

theorem identityPointC_eq : identityPointC G =
    stalkPoint G (identityCenter G) (identityEval G) (identityEval_const G) :=
  (exists_identityPointC_eq_stalkPoint G).choose_spec.choose_spec.choose_spec.2

theorem identityEval_stalkConstants (c : C) :
    identityEval G (stalkConstants G (identityCenter G) c) = c :=
  congrArg (fun q : CommRingCat.of C ⟶ CommRingCat.of C => q c) (identityEval_const G)

variable (L : Type u) [Field L] [Algebra C L]

/-- Evaluation at the identity with values in `L`. -/
def identityEvalAt : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of L :=
  identityEval G ≫ CommRingCat.ofHom (algebraMap C L)

theorem identityEvalAt_const :
    stalkConstants G (identityCenter G) ≫ identityEvalAt G L =
      CommRingCat.ofHom (algebraMap C L) := by
  rw [identityEvalAt, ← Category.assoc, identityEval_const]
  rfl

instance isLocalHom_identityEvalAt : IsLocalHom (identityEvalAt G L).hom :=
  ⟨fun a ha => (isLocalHom_identityEval G).map_nonunit a (by
    have : IsUnit (identityEval G a) := by
      have h := ha
      change IsUnit (algebraMap C L (identityEval G a)) at h
      rw [isUnit_iff_ne_zero] at h ⊢
      intro h0
      exact h (by rw [h0, map_zero])
    exact this)⟩

/-- **The identity with values in `L` is the stalk point `(e, ev_e)`.** -/
theorem one_eq_stalkPoint :
    (1 : algebraicPointSource (K := C) (R := L) ⟶ G) =
      stalkPoint G (identityCenter G) (identityEvalAt G L) (identityEvalAt_const G L) := by
  have h1 : (1 : algebraicPointSource (K := C) (R := L) ⟶ G) =
      pointSourceMap (Algebra.ofId C L) ≫ identityPointC G := by
    rw [identityPointC, ← Category.assoc, Hom.one_def,
      show pointSourceMap (Algebra.ofId C L) ≫ toUnit _ = toUnit _ from toUnit_unique _ _]
  rw [h1, identityPointC_eq, pointSourceMap_comp_stalkPoint]
  rfl

theorem identityEval_eq_zero_of_mem {a : G.left.presheaf.stalk (identityCenter G)}
    (ha : a ∈ IsLocalRing.maximalIdeal _) : identityEval G a = 0 := by
  by_contra h
  exact ha ((isLocalHom_identityEval G).map_nonunit a (isUnit_iff_ne_zero.mpr h))

theorem sub_mem_maximalIdeal (a : G.left.presheaf.stalk (identityCenter G)) :
    a - stalkConstants G (identityCenter G) (identityEval G a) ∈ IsLocalRing.maximalIdeal _ := by
  intro hunit
  have := hunit.map (identityEval G).hom
  rw [map_sub, identityEval_stalkConstants, sub_self] at this
  exact not_isUnit_zero this

variable [LocallyOfFiniteType G.hom]

theorem maximalIdeal_identity_fg : (IsLocalRing.maximalIdeal
    (G.left.presheaf.stalk (identityCenter G))).FG := by
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact IsNoetherian.noetherian _

/-- The number of generators of the maximal ideal at the identity. -/
def tangentRank : ℕ :=
  (Submodule.fg_iff_exists_fin_generating_family.mp (maximalIdeal_identity_fg G)).choose

/-- Generators of the maximal ideal at the identity. -/
def tangentGenerators : Fin (tangentRank G) → G.left.presheaf.stalk (identityCenter G) :=
  (Submodule.fg_iff_exists_fin_generating_family.mp (maximalIdeal_identity_fg G)).choose_spec.choose

theorem span_tangentGenerators : Submodule.span _ (Set.range (tangentGenerators G)) =
    IsLocalRing.maximalIdeal (G.left.presheaf.stalk (identityCenter G)) :=
  (Submodule.fg_iff_exists_fin_generating_family.mp
    (maximalIdeal_identity_fg G)).choose_spec.choose_spec

/-- **A lift of the identity is determined by its values on the generators.**  A point derivation
at `e` kills the constants and the square of the maximal ideal. -/
theorem lift_ext_of_generators
    {χ₁ χ₂ : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L)}
    (hχ₁ : stalkConstants G (identityCenter G) ≫ χ₁ = CommRingCat.ofHom (algebraMap C (DualL L)))
    (hχ₂ : stalkConstants G (identityCenter G) ≫ χ₂ = CommRingCat.ofHom (algebraMap C (DualL L)))
    (hφ₁ : χ₁ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom =
      identityEvalAt G L)
    (hφ₂ : χ₂ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom =
      identityEvalAt G L)
    (hgen : ∀ i, (χ₁ (tangentGenerators G i)).snd = (χ₂ (tangentGenerators G i)).snd) :
    χ₁ = χ₂ := by
  have hfst : ∀ (χ : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L)),
      χ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = identityEvalAt G L →
      ∀ a, (χ a).fst = algebraMap C L (identityEval G a) := fun χ h a =>
    congrArg (fun q : _ ⟶ CommRingCat.of L => q a) h
  have hconst : ∀ (χ : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L)),
      stalkConstants G (identityCenter G) ≫ χ = CommRingCat.ofHom (algebraMap C (DualL L)) →
      ∀ c, (χ (stalkConstants G (identityCenter G) c)).snd = 0 := fun χ h c => by
    have := congrArg (fun q : CommRingCat.of C ⟶ CommRingCat.of (DualL L) => (q c).snd) h
    exact this
  have hsnd : ∀ (χ : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L)),
      stalkConstants G (identityCenter G) ≫ χ = CommRingCat.ofHom (algebraMap C (DualL L)) →
      χ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = identityEvalAt G L →
      ∀ a, ∃ b : Fin (tangentRank G) → G.left.presheaf.stalk (identityCenter G),
        (∀ χ' : G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L),
          stalkConstants G (identityCenter G) ≫ χ' = CommRingCat.ofHom (algebraMap C (DualL L)) →
          χ' ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom =
            identityEvalAt G L →
          (χ' a).snd = ∑ i, algebraMap C L (identityEval G (b i)) *
            (χ' (tangentGenerators G i)).snd) := by
    intro _ _ _ a
    have hm := sub_mem_maximalIdeal G a
    rw [← span_tangentGenerators, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, fun χ' hc' hf' => ?_⟩
    have hb' : ∑ i, b i * tangentGenerators G i =
        a - stalkConstants G (identityCenter G) (identityEval G a) := by
      rw [← hb]
      simp only [smul_eq_mul]
    have ha : a = stalkConstants G (identityCenter G) (identityEval G a) +
        ∑ i, b i * tangentGenerators G i := by
      rw [hb']
      ring
    rw [ha, map_add, TrivSqZeroExt.snd_add, hconst χ' hc', zero_add, map_sum,
      TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst χ' hf', hfst χ' hf',
      identityEval_eq_zero_of_mem G (a := tangentGenerators G i) (by
        rw [← span_tangentGenerators]
        exact Submodule.subset_span ⟨i, rfl⟩), map_zero]
    simp [smul_eq_mul]
  refine CommRingCat.hom_ext (RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_)
  · change (χ₁ a).fst = (χ₂ a).fst
    rw [hfst χ₁ hφ₁, hfst χ₂ hφ₂]
  · change (χ₁ a).snd = (χ₂ a).snd
    obtain ⟨b, hb⟩ := hsnd χ₁ hχ₁ hφ₁ a
    rw [hb χ₁ hχ₁ hφ₁, hb χ₂ hχ₂ hφ₂]
    exact Finset.sum_congr rfl fun i _ => by rw [hgen i]

end Identity

end

end GaloisForLFunctions.HTGeometry
