import GaloisForLFunctions.HTGeometry.AbelianVariety
import GaloisForLFunctions.HTGeometry.AlgebraicGroupJet

/-!
# The generic point of an integral scheme over a field, and translations

For an integral scheme `X` over `Spec C` the function field `F = C(X)` is a `C`-algebra, and the
canonical morphism `g : Spec F → X` is an `F`-valued point of `X` over `C`: the generic point.

* Pullback along a dominant `C`-morphism `f` is the `C`-algebra map `f*` of function fields, and
  `f ∘ g = g ∘ Spec(f*)`.
* A field-valued point factoring through the generic point determines its field map: if
  `g ∘ Spec a = g ∘ Spec b` then `a = b`.
* For a group scheme `G` over `C`, translation by a rational point `x` gives a `C`-automorphism
  `σ_x = τ_x*` of `C(G)`, the map `x ↦ σ_x` is a homomorphism, and `g ∘ Spec(σ_x) = g · x`.
-/

open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Pullback along a dominant morphism of integral schemes intertwines the generic points. -/
theorem Scheme.Hom.specMap_functionFieldPullback_fromSpecStalk
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) [IsDominant f] :
    Spec.map f.functionFieldPullback ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [Scheme.Hom.functionFieldPullback, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- **Field-valued points through the generic point are determined by their field maps.** -/
theorem Scheme.specMap_fromSpecStalk_genericPoint_injective {X : Scheme.{u}}
    [IsIntegral X] {N : Type u} [Field N] {a b : X.functionField ⟶ CommRingCat.of N}
    (h : Spec.map a ≫ X.fromSpecStalk (genericPoint X) =
      Spec.map b ≫ X.fromSpecStalk (genericPoint X)) : a = b := by
  have h' := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of N))
    (show (SpecToEquivOfLocalRing X (CommRingCat.of N)).symm
        ⟨genericPoint X, ⟨a, inferInstance⟩⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of N)).symm
        ⟨genericPoint X, ⟨b, inferInstance⟩⟩ from h)
  simp only [Equiv.apply_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and] at h'
  exact congrArg Subtype.val h'

variable {C : Type u} [Field C]

section Integral

variable (X : Over (Spec (.of C))) [IsIntegral X.left]

/-- The function field of an integral scheme over `C` is a `C`-algebra. -/
instance overFunctionFieldAlgebra : Algebra C X.left.functionField :=
  RingHom.toAlgebra
    (X.hom.functionFieldPullback.hom.comp (Scheme.specFunctionFieldAlgEquiv C).toRingHom)

theorem overFunctionField_algebraMap_eq :
    algebraMap C X.left.functionField =
      X.hom.functionFieldPullback.hom.comp (Scheme.specFunctionFieldAlgEquiv C).toRingHom := rfl

theorem specFunctionFieldAlgEquiv_eq_toStalk (c : C) :
    Scheme.specFunctionFieldAlgEquiv C c =
      (StructureSheaf.toStalk C (genericPoint (Spec (.of C)))).hom c := by
  letI := Scheme.specFunctionFieldAlgebra C
  exact (Scheme.specFunctionFieldAlgEquiv C).commutes c

/-- **The generic point is a point over `C`.** -/
theorem fromSpecStalk_genericPoint_comp_hom :
    X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap C X.left.functionField)) := by
  rw [← Scheme.Hom.specMap_functionFieldPullback_fromSpecStalk, Spec.fromSpecStalk_eq,
    ← Spec.map_comp]
  congr 1

/-- The generic point of `X`, as an `F`-valued point over `C`. -/
def genericPointHom :
    algebraicPointSource (K := C) (R := X.left.functionField) ⟶ X :=
  Over.homMk (X.left.fromSpecStalk (genericPoint X.left)) (fromSpecStalk_genericPoint_comp_hom X)

@[simp]
theorem genericPointHom_left :
    (genericPointHom X).left = X.left.fromSpecStalk (genericPoint X.left) := rfl

/-- The source morphism induced by a map of `C`-algebras. -/
def pointSourceMap {R S : Type u} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S]
    (f : R →ₐ[C] S) :
    algebraicPointSource (K := C) (R := S) ⟶ algebraicPointSource (K := C) (R := R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap C R)) =
      Spec.map (CommRingCat.ofHom (algebraMap C S))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext f.commutes))

@[simp]
theorem pointSourceMap_left {R S : Type u} [CommRing R] [CommRing S] [Algebra C R]
    [Algebra C S] (f : R →ₐ[C] S) :
    (pointSourceMap f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

theorem pointSourceMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra C R] [Algebra C S] [Algebra C T] (f : R →ₐ[C] S) (g : S →ₐ[C] T) :
    pointSourceMap (g.comp f) = pointSourceMap g ≫ pointSourceMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Pullback of rational functions along a dominant `C`-morphism, as a `C`-algebra map. -/
def overFunctionFieldPullback {Y : Over (Spec (.of C))} [IsIntegral Y.left] (f : X ⟶ Y)
    [IsDominant f.left] : Y.left.functionField →ₐ[C] X.left.functionField where
  toRingHom := f.left.functionFieldPullback.hom
  commutes' c := by
    change f.left.functionFieldPullback (Y.hom.functionFieldPullback
        (Scheme.specFunctionFieldAlgEquiv C c)) =
      X.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv C c)
    have h := f.left.functionFieldPullback_comp Y.hom
    have hw := Scheme.Hom.functionFieldPullback_congr (f.left ≫ Y.hom) X.hom (Over.w f)
    exact congrArg (fun q : (Spec (.of C)).functionField ⟶ X.left.functionField =>
      q (Scheme.specFunctionFieldAlgEquiv C c)) (h.symm.trans hw)

theorem overFunctionFieldPullback_apply {Y : Over (Spec (.of C))} [IsIntegral Y.left]
    (f : X ⟶ Y) [IsDominant f.left] (a : Y.left.functionField) :
    overFunctionFieldPullback X f a = f.left.functionFieldPullback a := rfl

/-- **A dominant morphism carries the generic point to the generic point.** -/
theorem genericPointHom_comp {Y : Over (Spec (.of C))} [IsIntegral Y.left] (f : X ⟶ Y)
    [IsDominant f.left] :
    genericPointHom X ≫ f = pointSourceMap (overFunctionFieldPullback X f) ≫ genericPointHom Y := by
  apply Over.OverMorphism.ext
  change X.left.fromSpecStalk (genericPoint X.left) ≫ f.left =
    Spec.map f.left.functionFieldPullback ≫ Y.left.fromSpecStalk (genericPoint Y.left)
  rw [Scheme.Hom.specMap_functionFieldPullback_fromSpecStalk]

/-- **Field-valued points through the generic point are determined by their field maps.** -/
theorem pointSourceMap_genericPointHom_injective {N : Type u} [Field N] [Algebra C N]
    {a b : X.left.functionField →ₐ[C] N}
    (h : pointSourceMap a ≫ genericPointHom X = pointSourceMap b ≫ genericPointHom X) :
    a = b := by
  have h' := congrArg CommaMorphism.left h
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.left.fromSpecStalk (genericPoint X.left) =
    Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.left.fromSpecStalk (genericPoint X.left) at h'
  have := Scheme.specMap_fromSpecStalk_genericPoint_injective h'
  ext z
  exact congrArg (fun q : X.left.functionField ⟶ CommRingCat.of N => q z) this

end Integral

/-! ### Translations of a group scheme -/

section Group

variable (G : Over (Spec (.of C))) [GrpObj G] [IsIntegral G.left]

/-- Right translation by a rational point, as an automorphism of the underlying scheme. -/
def translationSchemeIso (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) : G.left ≅ G.left :=
  (Over.forget (Spec (.of C))).mapIso (GrpObj.mulRight x)

/-- **Translation by a rational point acts on the function field.**  `σ_x = τ_x*`. -/
def translationAlgEquiv (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    G.left.functionField ≃ₐ[C] G.left.functionField :=
  AlgEquiv.ofRingEquiv (f := Scheme.Iso.functionFieldPullbackRingEquiv (translationSchemeIso G x))
    (fun c => (overFunctionFieldPullback G (GrpObj.mulRight x).hom).commutes c)

theorem translationAlgEquiv_apply (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) (a : G.left.functionField) :
    translationAlgEquiv G x a = overFunctionFieldPullback G (GrpObj.mulRight x).hom a := rfl

theorem translationAlgEquiv_toAlgHom (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    (translationAlgEquiv G x).toAlgHom = overFunctionFieldPullback G (GrpObj.mulRight x).hom :=
  rfl

theorem translationAlgEquiv_mul (x y : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    translationAlgEquiv G (x * y) = translationAlgEquiv G x * translationAlgEquiv G y := by
  ext a
  rw [AlgEquiv.mul_apply, translationAlgEquiv_apply, translationAlgEquiv_apply,
    translationAlgEquiv_apply, overFunctionFieldPullback_apply, overFunctionFieldPullback_apply,
    overFunctionFieldPullback_apply]
  have hs := congrArg (fun e : G ≅ G => e.hom.left) (GrpObj.mulRight_trans x y)
  change (GrpObj.mulRight x).hom.left ≫ (GrpObj.mulRight y).hom.left =
    (GrpObj.mulRight (x * y)).hom.left at hs
  rw [← Scheme.Hom.functionFieldPullback_congr _ _ hs, Scheme.Hom.functionFieldPullback_comp]
  rfl

theorem translationAlgEquiv_one : translationAlgEquiv G 1 = 1 := by
  ext a
  rw [AlgEquiv.one_apply, translationAlgEquiv_apply, overFunctionFieldPullback_apply]
  have hiso : GrpObj.mulRight (1 : 𝟙_ (Over (Spec (.of C))) ⟶ G) = Iso.refl G := by
    rw [← MonObj.one_eq_one]
    exact GrpObj.mulRight_one G
  have hs := congrArg (fun e : G ≅ G => e.hom.left) hiso
  change (GrpObj.mulRight (1 : 𝟙_ (Over (Spec (.of C))) ⟶ G)).hom.left = 𝟙 G.left at hs
  rw [Scheme.Hom.functionFieldPullback_congr _ _ hs, Scheme.Hom.functionFieldPullback_id]
  rfl

/-- **The translation action** `x ↦ σ_x` of the rational points on the function field. -/
def translationHom :
    (𝟙_ (Over (Spec (.of C))) ⟶ G) →* (G.left.functionField ≃ₐ[C] G.left.functionField) where
  toFun := translationAlgEquiv G
  map_one' := translationAlgEquiv_one G
  map_mul' := translationAlgEquiv_mul G

omit [IsIntegral G.left] in
/-- Composing a point with right translation by `x` multiplies it by the constant point `x`. -/
theorem comp_mulRight_hom_eq_mul {S : Over (Spec (.of C))} (p : S ⟶ G)
    (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    p ≫ (GrpObj.mulRight x).hom = p * (toUnit S ≫ x) := by
  rw [GrpObj.mulRight_hom, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    show p ≫ toUnit G = toUnit S from toUnit_unique _ _]
  rfl

/-- **Translating the generic point**: `g · x = g ∘ Spec(σ_x)`. -/
theorem genericPointHom_mul_const (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    genericPointHom G * (toUnit _ ≫ x) =
      pointSourceMap (translationAlgEquiv G x).toAlgHom ≫ genericPointHom G := by
  rw [← comp_mulRight_hom_eq_mul, genericPointHom_comp]
  rfl

end Group

end

end GaloisForLFunctions.HTGeometry
