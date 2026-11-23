import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionField
import Mathlib.AlgebraicGeometry.Stalk

/-! A rational function regular at a rational point has a unique germ, whose
value is obtained by any expression with denominator nonzero at the point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GaloisForLFunctions.HTGeometry GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {Y : Scheme.{0}}
  {t : Y ⟶ Spec (CommRingCat.of K)}

section Generic

variable [IsIntegral Y]

/-- Embed the stalk at a point into the function field by generization. -/
abbrev stalkToFunctionField (y : Y) :
    Y.presheaf.stalk y ⟶ Y.functionField :=
  Y.presheaf.stalkSpecializes (genericPoint_specializes y)

theorem stalkToFunctionField_injective (y : Y) :
    Function.Injective (stalkToFunctionField y).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨V, hy, b, rfl⟩ := Y.presheaf.exists_germ_eq a
  have hη := (genericPoint_specializes y).mem_open V.isOpen hy
  have he := ConcreteCategory.congr_hom
    (Y.presheaf.germ_stalkSpecializes hy (genericPoint_specializes y)) b
  change (stalkToFunctionField y).hom ((Y.presheaf.germ V y hy).hom b) = 0 at ha
  change (stalkToFunctionField y).hom ((Y.presheaf.germ V y hy).hom b) =
    (Y.presheaf.germ V (genericPoint Y) hη).hom b at he
  have hb : b = 0 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    (he.symm.trans (ha.trans (map_zero _).symm))
  rw [hb, map_zero]

/-- The map from the function-field point to a local spectrum is dominant. -/
theorem isDominant_specMap_stalkToFunctionField (y : Y) :
    IsDominant (Spec.map (stalkToFunctionField y)) := by
  apply (isDominant_iff _).mpr
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (stalkToFunctionField_injective y)]
  exact bot_le

end Generic

private theorem closedPoint_eq_specDefault (K : Type) [Field K] :
    (IsLocalRing.closedPoint (CommRingCat.of K) : Spec (CommRingCat.of K)) =
      (default : Spec (CommRingCat.of K)) :=
  Subsingleton.elim _ _

variable (y : Y.BaseFieldPointOver K t)

/-- The homomorphism from the local ring induced by a rational point. -/
abbrev localPointEval :
    Y.presheaf.stalk (y.hom default) ⟶ CommRingCat.of K :=
  eqToHom (congrArg (fun x => Y.presheaf.stalk (y.hom x)) (closedPoint_eq_specDefault K).symm) ≫
    Scheme.stalkClosedPointTo y.hom

theorem localPointEval_germ {V : Y.Opens} (hy : y.hom default ∈ V) (b : Γ(Y, V)) :
    (localPointEval y).hom ((Y.presheaf.germ V (y.hom default) hy).hom b) =
      affinePointEval y hy b := by
  have he (x : Spec (CommRingCat.of K)) (hx : y.hom x ∈ V) (h : x =
      IsLocalRing.closedPoint (CommRingCat.of K)) :
      (Y.presheaf.germ V (y.hom x) hx) ≫ eqToHom
        (congrArg (fun p => Y.presheaf.stalk (y.hom p)) h) ≫ Scheme.stalkClosedPointTo y.hom =
      y.hom.appLE V ⊤ (fun a _ => (Subsingleton.elim x a : x = a) ▸ hx) ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    subst h
    rw [eqToHom_refl, Category.id_comp, Scheme.germ_stalkClosedPointTo y.hom V hx]
    simp only [Scheme.Hom.appLE, Iso.trans_hom, Category.assoc, Functor.mapIso_hom]
    congr 3
  exact ConcreteCategory.congr_hom (he default hy (closedPoint_eq_specDefault K).symm) b

theorem specMap_localPointEval_fromSpecStalk :
    Spec.map (localPointEval y) ≫ Y.fromSpecStalk (y.hom default) = y.hom := by
  have he (x : Spec (CommRingCat.of K))
      (h : IsLocalRing.closedPoint (CommRingCat.of K) = x) :
      Spec.map (eqToHom (congrArg (fun p => Y.presheaf.stalk (y.hom p)) h.symm) ≫
        Scheme.stalkClosedPointTo y.hom) ≫ Y.fromSpecStalk (y.hom x) = y.hom := by
    subst h
    rw [eqToHom_refl, Category.id_comp, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact he default (closedPoint_eq_specDefault K)

theorem localPointEval_isUnit_iff (b : Y.presheaf.stalk (y.hom default)) :
    IsUnit ((localPointEval y).hom b) ↔ IsUnit b := by
  have he (x : Spec (CommRingCat.of K))
      (h : IsLocalRing.closedPoint (CommRingCat.of K) = x) (a : Y.presheaf.stalk (y.hom x)) :
      IsUnit ((eqToHom (congrArg (fun p => Y.presheaf.stalk (y.hom p)) h.symm) ≫
        Scheme.stalkClosedPointTo y.hom).hom a) ↔ IsUnit a := by
    subst h
    rw [eqToHom_refl, Category.id_comp]
    exact ⟨fun ha => isUnit_of_map_unit _ _ ha, fun ha => ha.map _⟩
  exact he default (closedPoint_eq_specDefault K) b

end GlobalTheory.SchemeCohomology
