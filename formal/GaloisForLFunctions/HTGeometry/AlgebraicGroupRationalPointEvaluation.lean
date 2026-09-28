import GaloisForLFunctions.HTGeometry.AlgebraicGroupGenericPoint
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Rational functions on an algebraic group, evaluated at rational points

Let `X` be a scheme over a field `C`.  A section `s` of `O_X` over `U` has a value `s(y) ∈ C` at
every rational point `y` of `U`; it is nonzero exactly when `y` lies in the basic open set of `s`.
On a reduced scheme locally of finite type over an algebraically closed field, a section vanishing
at every rational point is zero (the basic open set would contain a closed point).

For an integral algebraic group `G` over `C` this gives the order-zero geometric inputs of the
isogeny-tail theorem:

* **stabilizers are closed**: for a rational function `f`, the rational points `x` with
  `σ_x f = f` form the rational points of a Zariski-closed subset of `G`, namely
  `⋂_y y⁻¹((G ∖ U) ∪ Z(s − s(y)))` where `f = s` on `U`;
* **translation-invariant rational functions are constant**: `C(G)^(G(C)) = C`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C : Type u} [Field C]

section Evaluation

variable {X : Scheme.{u}}

theorem top_le_preimage_of_mem (y : Spec (.of C) ⟶ X) {U : X.Opens} (hy : y default ∈ U) :
    ⊤ ≤ y ⁻¹ᵁ U := fun z _ => by
  rw [Subsingleton.elim z default]
  exact hy

/-- The value `s(y) ∈ C` of a section at a rational point. -/
def pointEval (y : Spec (.of C) ⟶ X) (U : X.Opens) (hy : y default ∈ U) : Γ(X, U) →+* C :=
  (y.appLE U ⊤ (top_le_preimage_of_mem y hy) ≫ (Scheme.ΓSpecIso (.of C)).hom).hom

/-- Values are compatible with restriction. -/
theorem pointEval_res (y : Spec (.of C) ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (hy : y default ∈ V)
    (s : Γ(X, U)) :
    pointEval y V hy (X.presheaf.map (homOfLE hVU).op s) = pointEval y U (hVU hy) s := by
  simp only [pointEval]
  rw [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.map_appLE]

theorem pointEval_congr {y y' : Spec (.of C) ⟶ X} (h : y = y') (U : X.Opens) (hy : y default ∈ U)
    (hy' : y' default ∈ U) (s : Γ(X, U)) : pointEval y U hy s = pointEval y' U hy' s := by
  subst h
  rfl

/-- Values are compatible with composition. -/
theorem pointEval_comp {Y : Scheme.{u}} (y : Spec (.of C) ⟶ X) (h : X ⟶ Y) (U : Y.Opens)
    (hy : (y ≫ h) default ∈ U) (s : Γ(Y, U)) :
    pointEval (y ≫ h) U hy s = pointEval y (h ⁻¹ᵁ U) hy (h.app U s) := by
  simp only [pointEval]
  rw [← CommRingCat.comp_apply, ← Category.assoc, Scheme.Hom.comp_appLE]

/-- **A section is nonzero at a rational point exactly on its basic open set.** -/
theorem pointEval_ne_zero_iff (y : Spec (.of C) ⟶ X) (U : X.Opens) (hy : y default ∈ U)
    (s : Γ(X, U)) : pointEval y U hy s ≠ 0 ↔ y default ∈ X.basicOpen s := by
  have hpre : y default ∈ X.basicOpen s ↔
      (default : Spec (.of C)) ∈ (Spec (.of C)).basicOpen
        ((Spec (.of C)).presheaf.map (homOfLE (top_le_preimage_of_mem y hy)).op (y.app U s)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [hpre]
  set t := (Spec (.of C)).presheaf.map (homOfLE (top_le_preimage_of_mem y hy)).op (y.app U s)
  have ht : pointEval y U hy s = (Scheme.ΓSpecIso (.of C)).hom t := rfl
  rw [ht]
  constructor
  · intro h0
    have hunit : IsUnit t := by
      have hu : IsUnit ((Scheme.ΓSpecIso (.of C)).hom t) := isUnit_iff_ne_zero.mpr h0
      have := hu.map (Scheme.ΓSpecIso (.of C)).inv.hom
      rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at this
    rw [Scheme.basicOpen_of_isUnit _ hunit]
    trivial
  · intro hmem h0
    have ht0 : t = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of C)).inv.hom h0
      rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this
    rw [ht0, Scheme.basicOpen_zero] at hmem
    exact hmem

variable [IsAlgClosed C] (sX : X ⟶ Spec (.of C)) [LocallyOfFiniteType sX]

include sX in
/-- **On a reduced scheme of finite type over an algebraically closed field, a section vanishing
at every rational point is zero.** -/
theorem eq_zero_of_pointEval_eq_zero [IsReduced X] {U : X.Opens} (s : Γ(X, U))
    (h : ∀ (y : Spec (.of C) ⟶ X) (_ : y ≫ sX = 𝟙 _) (hy : y default ∈ U),
      pointEval y U hy s = 0) : s = 0 := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
    (Set.nonempty_iff_ne_empty.mpr (by
      intro he
      apply hne
      exact TopologicalSpace.Opens.ext he)) (X.basicOpen s).isOpen.isLocallyClosed
  let y := pointOfClosedPoint sX p hpc
  have hyp : y default = p := pointOfClosedPoint_apply sX p hpc _
  have hyU : y default ∈ U := by rw [hyp]; exact X.basicOpen_le s hp
  have h0 := h y (pointOfClosedPoint_comp sX p hpc) hyU
  have hnot : y default ∉ X.basicOpen s := fun hm => (pointEval_ne_zero_iff y U hyU s).mpr hm h0
  rw [hyp] at hnot
  exact hnot hp

end Evaluation

section StructureSection

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of C))

/-- The constants `C → Γ(X, U)` of a scheme over `C`. -/
def structureSection (U : X.Opens) : C →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of C)).inv ≫ sX.appLE ⊤ U le_top).hom

/-- A rational point evaluates constants to themselves. -/
theorem pointEval_structureSection (y : Spec (.of C) ⟶ X) (hys : y ≫ sX = 𝟙 _) (U : X.Opens)
    (hy : y default ∈ U) (c : C) : pointEval y U hy (structureSection sX U c) = c := by
  have key : ∀ (f : Spec (.of C) ⟶ Spec (.of C)) (_ : f = 𝟙 _) (e : ⊤ ≤ f ⁻¹ᵁ ⊤),
      f.appLE ⊤ ⊤ e = 𝟙 _ := by
    rintro f rfl e
    simp [Scheme.Hom.appLE]
  have hcomp : ((Scheme.ΓSpecIso (.of C)).inv ≫ sX.appLE ⊤ U le_top) ≫
      (y.appLE U ⊤ (top_le_preimage_of_mem y hy) ≫ (Scheme.ΓSpecIso (.of C)).hom) = 𝟙 _ := by
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE_assoc, key _ hys, Category.id_comp,
      Iso.inv_hom_id]
  calc pointEval y U hy (structureSection sX U c)
      = (((Scheme.ΓSpecIso (.of C)).inv ≫ sX.appLE ⊤ U le_top) ≫
          (y.appLE U ⊤ (top_le_preimage_of_mem y hy) ≫ (Scheme.ΓSpecIso (.of C)).hom)).hom c :=
        rfl
    _ = c := by rw [hcomp]; rfl

end StructureSection

/-! ### Rational points of an algebraic group -/

section Group

variable [IsAlgClosed C] (G : Over (Spec (.of C))) [GrpObj G] [IsIntegral G.left]
  [LocallyOfFiniteType G.hom]

/-- The underlying morphism `Spec C → G` of a rational point. -/
abbrev rationalPointHom (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) : Spec (.of C) ⟶ G.left := y.left

/-- The rational point of `G` at a closed point. -/
def rationalPointOfClosedPoint (p : G.left) (hp : IsClosed {p}) : 𝟙_ (Over (Spec (.of C))) ⟶ G :=
  Over.homMk (pointOfClosedPoint G.hom p hp) (pointOfClosedPoint_comp G.hom p hp)

omit [GrpObj G] [IsIntegral G.left] in
theorem rationalPointOfClosedPoint_apply (p : G.left) (hp : IsClosed {p}) (z : Spec (.of C)) :
    rationalPointHom G (rationalPointOfClosedPoint G p hp) z = p :=
  pointOfClosedPoint_apply G.hom p hp z

omit [IsAlgClosed C] [GrpObj G] [IsIntegral G.left] [LocallyOfFiniteType G.hom] in
theorem rationalPoint_comp_hom (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    rationalPointHom G y ≫ G.hom = 𝟙 _ :=
  Over.w y

omit [GrpObj G] in
/-- A section on an open of `G` vanishing at every rational point of that open is zero. -/
theorem eq_zero_of_rationalPointEval_eq_zero {U : G.left.Opens} (s : Γ(G.left, U))
    (h : ∀ (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) (hy : rationalPointHom G y default ∈ U),
      pointEval (rationalPointHom G y) U hy s = 0) : s = 0 :=
  eq_zero_of_pointEval_eq_zero G.hom s fun y hys hy => h (Over.homMk y hys) hy

omit [IsAlgClosed C] [GrpObj G] [LocallyOfFiniteType G.hom] in
theorem genericPoint_mem_of_nonempty {U : G.left.Opens} (hU : (U : Set G.left).Nonempty) :
    genericPoint G.left ∈ U :=
  ((genericPoint_spec G.left).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

omit [IsAlgClosed C] [IsIntegral G.left] [LocallyOfFiniteType G.hom] in
/-- Translation by `x` on points: `y ↦ y · x`. -/
theorem comp_mulRight_hom (y x : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    y ≫ (GrpObj.mulRight x).hom = y * x := by
  rw [comp_mulRight_hom_eq_mul, show toUnit (𝟙_ (Over (Spec (.of C)))) = 𝟙 _ from
    toUnit_unique _ _, Category.id_comp]

/-- **The stabilizer of a rational function, in terms of values.**  If `f` is represented by `s`
on `U`, then `σ_x f = f` exactly when `s(y · x) = s(y)` for all rational points `y` with `y` and
`y · x` in `U`. -/
theorem groupTranslationAlgEquiv_germ_eq_iff (x : 𝟙_ (Over (Spec (.of C))) ⟶ G) (U : G.left.Opens)
    (hU : genericPoint G.left ∈ U) (s : Γ(G.left, U)) :
    groupTranslationAlgEquiv G x (G.left.presheaf.germ U _ hU s) = G.left.presheaf.germ U _ hU s ↔
      ∀ (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) (hy : rationalPointHom G y default ∈ U)
        (hyx : rationalPointHom G (y * x) default ∈ U),
        pointEval (rationalPointHom G (y * x)) U hyx s =
          pointEval (rationalPointHom G y) U hy s := by
  set τ := (GrpObj.mulRight x).hom.left with hτ
  have hξ : genericPoint G.left ∈ τ ⁻¹ᵁ U := by
    change τ (genericPoint G.left) ∈ U
    rw [Scheme.Hom.map_genericPoint_of_isDominant]
    exact hU
  set W := U ⊓ τ ⁻¹ᵁ U
  have hξW : genericPoint G.left ∈ W := ⟨hU, hξ⟩
  have hσ : groupTranslationAlgEquiv G x (G.left.presheaf.germ U _ hU s) =
      G.left.presheaf.germ (τ ⁻¹ᵁ U) _ hξ (τ.app U s) := by
    rw [groupTranslationAlgEquiv_apply, overFunctionFieldPullback_apply]
    exact Scheme.Hom.functionFieldPullback_germ τ U hU s
  rw [hσ]
  have hresU := G.left.presheaf.germ_res (homOfLE (inf_le_left : W ≤ U)) _ hξW
  have hresτ := G.left.presheaf.germ_res (homOfLE (inf_le_right : W ≤ τ ⁻¹ᵁ U)) _ hξW
  rw [← hresU, ← hresτ, CommRingCat.comp_apply, CommRingCat.comp_apply,
    (germ_injective_of_isIntegral G.left _ hξW).eq_iff, ← sub_eq_zero]
  have hyx : ∀ y : 𝟙_ (Over (Spec (.of C))) ⟶ G,
      rationalPointHom G (y * x) = rationalPointHom G y ≫ τ := by
    intro y
    rw [← comp_mulRight_hom]
    rfl
  constructor
  · intro h y hy hyxU
    have hyW : rationalPointHom G y default ∈ W := ⟨hy, by
      change τ (rationalPointHom G y default) ∈ U
      rw [← Scheme.Hom.comp_apply, ← hyx]
      exact hyxU⟩
    have h0 := congrArg (pointEval (rationalPointHom G y) W hyW) h
    rw [map_sub, map_zero, sub_eq_zero, pointEval_res, pointEval_res] at h0
    have hc := pointEval_comp (rationalPointHom G y) τ U (by rw [← hyx]; exact hyxU) s
    rw [← h0, ← hc]
    exact pointEval_congr (hyx y) U _ _ s
  · intro h
    refine eq_zero_of_rationalPointEval_eq_zero G _ fun y hyW => ?_
    rw [map_sub, sub_eq_zero, pointEval_res, pointEval_res]
    have hyxU : rationalPointHom G (y * x) default ∈ U := by
      rw [hyx, Scheme.Hom.comp_apply]
      exact hyW.2
    rw [← h y hyW.1 hyxU]
    have hc := pointEval_comp (rationalPointHom G y) τ U (by rw [← hyx]; exact hyxU) s
    rw [← hc]
    exact pointEval_congr (hyx y).symm U _ _ s

omit [IsAlgClosed C] [GrpObj G] [LocallyOfFiniteType G.hom] in
/-- Constants are the germs of the constant sections. -/
theorem germ_structureSection (U : G.left.Opens) (hU : genericPoint G.left ∈ U) (c : C) :
    G.left.presheaf.germ U _ hU (structureSection G.hom U c) =
      algebraMap C G.left.functionField c := by
  have h1 : structureSection G.hom U c = G.left.presheaf.map (homOfLE le_top).op
      (G.hom.appTop ((Scheme.ΓSpecIso (.of C)).inv c)) := rfl
  rw [h1, ← CommRingCat.comp_apply, G.left.presheaf.germ_res,
    ← Scheme.Hom.functionFieldPullback_germ_appTop]
  change _ = G.hom.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv C c)
  rw [specFunctionFieldAlgEquiv_eq_toStalk]
  rfl

variable [IsCommMonObj G]

/-- **Stabilizers of rational functions are Zariski closed.**  For every rational function `f`
there is a closed subset `Z ⊆ G` whose rational points are exactly the `x` with `σ_x f = f`. -/
theorem exists_isClosed_translation_stabilizer (f : G.left.functionField) :
    ∃ Z : Set G.left, IsClosed Z ∧ ∀ x : 𝟙_ (Over (Spec (.of C))) ⟶ G,
      groupTranslationAlgEquiv G x f = f ↔ rationalPointHom G x default ∈ Z := by
  obtain ⟨U, hU, s, rfl⟩ := G.left.presheaf.exists_germ_eq f
  let c : ∀ y : 𝟙_ (Over (Spec (.of C))) ⟶ G, rationalPointHom G y default ∈ U → C :=
    fun y hy => pointEval (rationalPointHom G y) U hy s
  refine ⟨⋂ (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) (hy : rationalPointHom G y default ∈ U),
    ((GrpObj.mulRight y).hom.left.base ⁻¹'
      (G.left.basicOpen (s - structureSection G.hom U (c y hy)) : Set G.left))ᶜ, ?_, ?_⟩
  · refine isClosed_iInter fun y => isClosed_iInter fun hy => ?_
    exact ((G.left.basicOpen _).isOpen.preimage
      (GrpObj.mulRight y).hom.left.base.hom.continuous).isClosed_compl
  · intro x
    rw [groupTranslationAlgEquiv_germ_eq_iff G x U hU s]
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
    refine forall_congr' fun y => forall_congr' fun hy => ?_
    have hpt : (GrpObj.mulRight y).hom.left (rationalPointHom G x default) =
        rationalPointHom G (y * x) default := by
      rw [mul_comm y x, ← comp_mulRight_hom]
      rfl
    rw [hpt]
    have hconst := pointEval_structureSection G.hom (rationalPointHom G (y * x))
      (rationalPoint_comp_hom G _) U
    constructor
    · intro h hmem
      have hyxU := G.left.basicOpen_le _ hmem
      exact (pointEval_ne_zero_iff _ U hyxU _).mpr hmem
        (by rw [map_sub, hconst, h hyxU]; exact sub_self _)
    · intro h hyxU
      by_contra hne
      apply h
      apply (pointEval_ne_zero_iff _ U hyxU _).mp
      rw [map_sub, hconst, sub_ne_zero]
      exact hne

/-- **Translation-invariant rational functions are constant**: `C(G)^(G(C)) = C`. -/
theorem mem_range_algebraMap_of_translation_fixed (f : G.left.functionField)
    (hf : ∀ x : 𝟙_ (Over (Spec (.of C))) ⟶ G, groupTranslationAlgEquiv G x f = f) :
    f ∈ Set.range (algebraMap C G.left.functionField) := by
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨U, hU, s, rfl⟩ := G.left.presheaf.exists_germ_eq f
  obtain ⟨p, hpU, hpc⟩ := nonempty_inter_closedPoints ⟨_, hU⟩ U.isOpen.isLocallyClosed
  let y₀ := rationalPointOfClosedPoint G p hpc
  have hy₀ : rationalPointHom G y₀ default ∈ U := by
    rw [rationalPointOfClosedPoint_apply]
    exact hpU
  set c := pointEval (rationalPointHom G y₀) U hy₀ s
  refine ⟨c, ?_⟩
  have hs : s = structureSection G.hom U c := by
    rw [← sub_eq_zero]
    refine eq_zero_of_rationalPointEval_eq_zero G _ fun z hz => ?_
    rw [map_sub, pointEval_structureSection G.hom _ (rationalPoint_comp_hom G _), sub_eq_zero]
    have hxz : y₀ * (y₀⁻¹ * z) = z := by group
    have h := (groupTranslationAlgEquiv_germ_eq_iff G (y₀⁻¹ * z) U hU s).mp (hf _) y₀ hy₀
      (by rw [hxz]; exact hz)
    exact (pointEval_congr (congrArg (rationalPointHom G) hxz.symm) U hz _ s).trans h
  rw [hs, germ_structureSection]

end Group

end

end GaloisForLFunctions.HTGeometry
