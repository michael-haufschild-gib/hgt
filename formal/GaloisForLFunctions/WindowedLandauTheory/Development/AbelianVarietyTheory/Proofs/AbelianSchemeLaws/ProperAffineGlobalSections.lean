import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SmoothFibreEqualizer
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalSectionDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperFieldSections

/-! Global functions on a proper smooth scheme computed through a pointed affine cover. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace GlobalTheory.GlobalFunctions

section Geometry

variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}

theorem exists_eq_of_eq (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) (x : B) (hx : f x = g x) :
    ∃ a : Γ(X, ⊤), (i.appTop ≫ (Scheme.ΓSpecIso B).hom) a = x := by
  obtain ⟨a, ha⟩ := FlatDescent.exists_appTop_eq_of_effectiveEpi i H
    ((Scheme.ΓSpecIso B).inv x) (by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, CommRingCat.comp_apply, hx])
  exact ⟨a, by rw [CommRingCat.comp_apply, ha, Iso.inv_hom_id_apply]⟩

theorem appTop_comp_eq {p : X ⟶ Spec R} {i : Spec B ⟶ X} {φ : R ⟶ B}
    (hφ : i ≫ p = Spec.map φ) :
    p.appTop ≫ i.appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hφ, Scheme.ΓSpecIso_naturality]

theorem eq_zero_of_surjective {p : X ⟶ Spec R} (hp : Function.Surjective p.appTop)
    (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) {φ : R ⟶ B} (hφ : i ≫ p = Spec.map φ)
    {R' : CommRingCat.{0}} (r : B ⟶ R') (hr : Function.Injective (φ ≫ r)) (x : B)
    (hx : f x = g x) (hrx : r x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := exists_eq_of_eq i H x hx
  obtain ⟨c, rfl⟩ := hp a
  rw [← CommRingCat.comp_apply p.appTop, appTop_comp_eq hφ, CommRingCat.comp_apply] at hrx ⊢
  have : (Scheme.ΓSpecIso R).hom c = 0 := hr (hrx.trans (map_zero _).symm)
  rw [this, map_zero]

end Geometry

section Core

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}

noncomputable abbrev prR (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := B)).toRingHom)

noncomputable abbrev prL (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R] B)))

theorem isPullback_pr (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : IsPullback (prR R k B) (prL R k B)
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R k))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R k B)).flip

noncomputable abbrev bc (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    CommRingCat.of (k ⊗[R] B) ⟶ CommRingCat.of (k ⊗[R] C) :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) f).toRingHom

theorem bc_apply (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) (x : k ⊗[R] B) :
    bc k f x = f.toLinearMap.baseChange k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem bc_prR (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    Spec.map (bc k f) ≫ prR R k B = prR R k C ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem bc_prL (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    Spec.map (bc k f) ≫ prL R k B = prL R k C := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem specMap_algHom (f : B →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem eq_zero_fibre (p : X ⟶ Spec (.of R)) [IsProper p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R)
    (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B)
    (hx : f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x)
    (hr : r.toLinearMap.baseChange k x = 0) : x = 0 := by
  let t : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have hX := IsPullback.of_hasPullback p t
  have hB := isPullback_pr R k B
  have hC := isPullback_pr R k C
  let j : Spec (.of (k ⊗[R] B)) ⟶ pullback p t :=
    pullback.lift (prR R k B ≫ i) (prL R k B) (by rw [Category.assoc, hφ]; exact hB.w)
  have hj1 : j ≫ pullback.fst p t = prR R k B ≫ i := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd p t = prL R k B := pullback.lift_snd _ _ _
  have hj : IsPullback (prR R k B) j i (pullback.fst p t) :=
    IsPullback.of_bot (by rw [hj2, hφ]; exact hB) hj1.symm hX
  have hg : IsPullback (prR R k C) (Spec.map (bc k g)) (Spec.map (CommRingCat.ofHom g.toRingHom))
      (prR R k B) :=
    IsPullback.of_bot (by rw [bc_prL, specMap_algHom]; exact hC) (bc_prR k g).symm hB
  have hK : IsPullback (Spec.map (bc k f)) (Spec.map (bc k g)) j j := by
    refine IsPullback.of_right ?_ ?_ hj
    · rw [bc_prR, hj1]
      exact hg.paste_horiz H
    · apply pullback.hom_ext
      · simp only [Category.assoc, hj1]
        rw [← Category.assoc, ← Category.assoc, bc_prR, bc_prR, Category.assoc, Category.assoc, H.w]
      · simp only [Category.assoc, hj2, bc_prL]
  have : Flat j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have : QuasiCompact j := MorphismProperty.of_isPullback hj ‹_›
  have := ProperFunctions.isIso_appTop_of_field (pullback.snd p t)
  refine eq_zero_of_surjective (p := pullback.snd p t) (ConcreteCategory.bijective_of_isIso _).2
    j hK hj2 (bc k r) ?_ x ?_ ?_
  · have : Nontrivial (k ⊗[R] R) := (TensorProduct.rid R k).toEquiv.nontrivial
    exact RingHom.injective _
  · rw [bc_apply, bc_apply, hx]
  · rw [bc_apply, hr]

/-- A smooth affine cover with a chosen base-valued point determines the global scalars. -/
theorem isIso_appTop_of_cover
    [Algebra.Smooth R B] [Algebra.Smooth R C]
    (p : X ⟶ Spec (.of R)) [IsProper p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R) :
    IsIso p.appTop := by
  let u := i.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom
  have h1 : ∀ c, u (p.appTop c) = algebraMap R B ((Scheme.ΓSpecIso (.of R)).hom c) :=
    fun c ↦ congr($(appTop_comp_eq hφ) c)
  have hu : Function.Injective u := by
    have h := FlatDescent.injective_appTop_of_epi i
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1.comp h
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab ↦ ?_, fun a ↦ ?_⟩
  · have h2 := (h1 a).symm.trans ((congrArg u hab).trans (h1 b))
    have h3 := congrArg r h2
    rw [r.commutes, r.commutes] at h3
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1 h3
  · have hfg : u ≫ CommRingCat.ofHom f.toRingHom = u ≫ CommRingCat.ofHom g.toRingHom := by
      simp only [u, Category.assoc]
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, H.w]
    have hfg' : f (u a) = g (u a) := congr($hfg a)
    have h2 := eq_zero_of_fibres f g r (eq_zero_fibre p i f g H hφ r)
      (u a - algebraMap R B (r (u a)))
      (by rw [map_sub, map_sub, hfg', f.commutes, g.commutes])
      (by rw [map_sub, r.commutes]; exact sub_self _)
    refine ⟨(Scheme.ΓSpecIso (.of R)).inv (r (u a)), hu ?_⟩
    rw [h1, Iso.inv_hom_id_apply]
    exact (sub_eq_zero.mp h2).symm

end Core

end GlobalTheory.GlobalFunctions
