import Mathlib

/-!
# Gauge collapse and stratified observation density

A single-carrier gauge unification presents every doctrine fibre as one and the same category and
every doctrine change as a conjugate of the identity.  Such a change is therefore an equivalence:
it cannot identify nonisomorphic objects, and it cannot invert a noninvertible morphism.  Forcing a
lossy change to be a gauge by localization does not repair it — it erases the very distinction it
was supposed to keep.

The directed replacement keeps the doctrine changes and observes objects through a fixed family of
source probes.  The probe nerve reconstructs objects exactly when the probe functor is dense,
equivalently when its restricted Yoneda embedding is fully faithful; and a complete dense source
nerve cannot descend through a realization that loses morphisms, invertibility, or object
isomorphism.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section GaugeCollapse

variable {C : Type u₁} {Fd : Type u₂} {Fe : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} Fd] [Category.{v₃} Fe]

/-- **Theorem 2.1.**  A doctrine change that is conjugate to the identity through single-carrier
presentations is an equivalence. -/
theorem isEquivalence_of_gauge (φd : C ≌ Fd) (φe : C ≌ Fe) (Fu : Fd ⥤ Fe)
    (η : φd.functor ⋙ Fu ≅ φe.functor) : Fu.IsEquivalence := by
  haveI : (φd.functor ⋙ Fu).IsEquivalence := Functor.isEquivalence_of_iso η.symm
  exact Functor.isEquivalence_of_comp_left φd.functor Fu

/-- **Theorem 2.1 (2).**  A gauge reflects object isomorphism, so a transition identifying two
nonisomorphic objects cannot be a gauge. -/
noncomputable def objIsoOfGauge (Fu : Fd ⥤ Fe) [Fu.IsEquivalence] {X Y : Fd}
    (h : Fu.obj X ≅ Fu.obj Y) : X ≅ Y :=
  (Functor.FullyFaithful.ofFullyFaithful Fu).preimageIso h

/-- **Theorem 2.1 (3).**  A gauge reflects invertibility, so a transition sending a noninvertible
morphism to an isomorphism cannot be a gauge. -/
theorem isIso_of_gauge (Fu : Fd ⥤ Fe) [Fu.IsEquivalence] {X Y : Fd} (f : X ⟶ Y)
    (h : IsIso (Fu.map f)) : IsIso f :=
  Functor.ReflectsIsomorphisms.reflects Fu f

/-- **Theorem 2.1 (1).**  A transition that is not an equivalence rules out single-carrier gauge
unification. -/
theorem no_gauge_of_not_isEquivalence (Fu : Fd ⥤ Fe) (h : ¬ Fu.IsEquivalence) :
    ¬ ∃ (φd : C ≌ Fd) (φe : C ≌ Fe), Nonempty (φd.functor ⋙ Fu ≅ φe.functor) := by
  rintro ⟨φd, φe, ⟨η⟩⟩
  exact h (isEquivalence_of_gauge φd φe Fu η)

end GaugeCollapse

section Localization

variable {E W : Type u₁} [Category.{v₁} E] [Category.{v₂} W]

/-- **Corollary 2.2, `(GOD.7)`.**  In any localization inverting the doctrine-change arrows, two
objects whose changes agree become isomorphic: forcing a lossy change to be a gauge erases the
distinction rather than repairing it. -/
noncomputable def localizationIdentifies (L : E ⥤ W) {a b c d : E} (f : a ⟶ b) (g : d ⟶ c)
    (hf : IsIso (L.map f)) (hg : IsIso (L.map g)) (h : L.obj b ≅ L.obj c) :
    L.obj a ≅ L.obj d :=
  (asIso (L.map f)).trans (h.trans (asIso (L.map g)).symm)

end Localization

section ObservationNerve

variable {P E : Type u₁} [Category.{v₁} P] [Category.{v₁} E]

/-- **Theorem 4.1.**  The probe nerve reconstructs every object exactly when the probe functor is
dense, that is, exactly when the canonical comparison from the colimit over the category of
elements of the nerve is an isomorphism. -/
theorem isDense_iff_nerve_fullyFaithful (J : P ⥤ E) [J.Full] :
    J.IsDense ↔ Nonempty (Presheaf.restrictedULiftYoneda.{v₁} J).FullyFaithful :=
  Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda J

variable {A G : Type u₁} [Category.{v₁} A] [Category.{v₁} G]
variable {Ps : Type u₁} [Category.{v₁} Ps]

/-- **Theorem 4.2.**  A complete source nerve cannot descend through a realization that identifies
two parallel morphisms. -/
theorem faithful_of_nerve_descends {N : E ⥤ Ps} (hN : N.Faithful) {L : E ⥤ A} {B : A ⥤ Ps}
    (hdesc : N ≅ L ⋙ B) : L.Faithful := by
  refine ⟨fun {X Y f g} hfg => ?_⟩
  refine hN.map_injective (?_ : N.map f = N.map g)
  have hf : N.map f = hdesc.hom.app X ≫ (L ⋙ B).map f ≫ hdesc.inv.app Y := by
    have hn := hdesc.hom.naturality f
    rw [← Category.assoc, ← hn, Category.assoc, hdesc.hom_inv_id_app, Category.comp_id]
  have hg : N.map g = hdesc.hom.app X ≫ (L ⋙ B).map g ≫ hdesc.inv.app Y := by
    have hn := hdesc.hom.naturality g
    rw [← Category.assoc, ← hn, Category.assoc, hdesc.hom_inv_id_app, Category.comp_id]
  rw [hf, hg]
  simp only [Functor.comp_map, hfg]

/-- **Theorem 4.2.**  It reflects isomorphisms, so it cannot send a nonisomorphism to an
isomorphism. -/
theorem isIso_of_nerve_descends {N : E ⥤ Ps} [N.ReflectsIsomorphisms] {L : E ⥤ A} {B : A ⥤ Ps}
    (hdesc : N ≅ L ⋙ B) {X Y : E} (f : X ⟶ Y) (hf : IsIso (L.map f)) : IsIso f := by
  haveI : IsIso ((L ⋙ B).map f) := by
    simp only [Functor.comp_map]
    exact (B.mapIso (asIso (L.map f))).isIso_hom
  haveI : IsIso (N.map f) := by
    have hrw : N.map f = hdesc.hom.app X ≫ (L ⋙ B).map f ≫ hdesc.inv.app Y := by
      have hn := hdesc.hom.naturality f
      rw [← Category.assoc, ← hn, Category.assoc, hdesc.hom_inv_id_app, Category.comp_id]
    rw [hrw]
    infer_instance
  exact Functor.ReflectsIsomorphisms.reflects N f

/-- **Theorem 4.2, `(GOD.13c)`.**  It reflects object isomorphism. -/
noncomputable def objIsoOfNerveDescends {N : E ⥤ Ps} (hN : N.FullyFaithful) {L : E ⥤ A}
    {B : A ⥤ Ps} (hdesc : N ≅ L ⋙ B) {X Y : E} (h : L.obj X ≅ L.obj Y) : X ≅ Y :=
  hN.preimageIso ((hdesc.app X).trans ((B.mapIso h).trans (hdesc.app Y).symm))

/-- **Theorem 4.2, `(GOD.13d)`.**  Descent of the nerve through a serial realization implies
descent through its first leg: a later observer cannot repair information already lost. -/
def nerveDescendsSerial {N : E ⥤ Ps} {L : E ⥤ A} {M : A ⥤ G} {B : G ⥤ Ps}
    (hdesc : N ≅ (L ⋙ M) ⋙ B) : N ≅ L ⋙ (M ⋙ B) :=
  hdesc.trans (Functor.associator L M B)

end ObservationNerve

end HTGeometry.ConstraintMotiveRelativity
