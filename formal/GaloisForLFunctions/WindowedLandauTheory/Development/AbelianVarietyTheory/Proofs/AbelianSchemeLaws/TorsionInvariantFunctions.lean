import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalSectionDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.SmoothReducedness
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! A regular function invariant under rational kernel translations descends along
a quasi-compact surjective étale group endomorphism over an algebraically closed field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatDescent

attribute [local instance] Over.cartesianMonoidalCategory

private theorem eq_of_pullback_eq_on_closedPoints {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} [IsReduced X] (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {s t : Γ(X, ⊤)}
    (h : ∀ x (hx : IsClosed {x}), (pointOfClosedPoint p x hx).appTop s =
      (pointOfClosedPoint p x hx).appTop t) : s = t := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  apply sub_eq_zero.mp
  apply eq_zero_of_basicOpen_eq_bot
  by_contra he
  let U := X.basicOpen (s - t)
  have hn : (U : Set X).Nonempty := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp he
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hn U.2.isLocallyClosed
  let a := pointOfClosedPoint p x hxc
  let o := IsLocalRing.closedPoint K
  have ha : a o = x := pointOfClosedPoint_apply p x hxc o
  have hzero : a.appTop (s - t) = 0 := by rw [map_sub, h x hxc, sub_self]
  have hz := Scheme.Γevaluation_naturality_apply a o (s - t)
  rw [hzero, map_zero] at hz
  have hv := (a.residueFieldMap o).hom.injective (hz.trans (map_zero _).symm)
  have hmem := X.evaluation_ne_zero_iff_mem_basicOpen x (U := ⊤) trivial (s - t)
  exact (hmem.mpr hx) (ha ▸ hv)

private theorem resLE_appTop_topIso_inv {X Y : Scheme.{0}} (t : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens} (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop (U.topIso.inv g) = V.topIso.inv (t.appLE U V e g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]

/-- Rational points in the same fibre differ by a rational kernel point. On the
reduced kernel pair, equality at these pairs suffices for descent of functions. -/
theorem existsUnique_descend_of_kernel_translation_invariant {K : Type}
    [Field K] [IsAlgClosed K] {A : Over (Spec (.of K))} [GrpObj A] [IsReduced A.left]
    [LocallyOfFiniteType A.hom] (m : A ⟶ A) [IsMonHom m]
    [Etale m.left] [Surjective m.left] [QuasiCompact m.left]
    (U : A.left.Opens) (f : Γ(A.left, m.left ⁻¹ᵁ U))
    (hf : ∀ (y : 𝟙_ (Over (Spec (.of K))) ⟶ A), y ≫ m = 1 →
      ∀ (e : m.left ⁻¹ᵁ U ≤ ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ (m.left ⁻¹ᵁ U)),
        ((toUnit A ≫ y) * 𝟙 A).left.appLE (m.left ⁻¹ᵁ U) (m.left ⁻¹ᵁ U) e f = f) :
    ∃! g : Γ(A.left, U), m.left.app U g = f := by
  let V := m.left ⁻¹ᵁ U
  let q := m.left ∣_ U
  let s : Γ(V, ⊤) := V.topIso.inv f
  let p : pullback q q ⟶ Spec (.of K) := pullback.fst q q ≫ V.ι ≫ A.hom
  letI : Surjective q := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  letI : IsReduced V := isReduced_of_isOpenImmersion V.ι
  letI : IsReduced (pullback q q) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst q q)
  letI : LocallyOfFiniteType p := by
    change LocallyOfFiniteType (pullback.fst q q ≫ V.ι ≫ A.hom)
    infer_instance
  have hq : q ≫ U.ι = V.ι ≫ m.left := morphismRestrict_ι m.left U
  have e : pullback.fst q q ≫ V.ι ≫ m.left = pullback.snd q q ≫ V.ι ≫ m.left := by
    rw [← hq, ← Category.assoc, ← Category.assoc, pullback.condition]
  have ep : pullback.snd q q ≫ V.ι ≫ A.hom = p := by
    change _ = pullback.fst q q ≫ V.ι ≫ A.hom
    calc
      _ = (pullback.snd q q ≫ V.ι ≫ m.left) ≫ A.hom := by
        simp only [Category.assoc, Over.w]
      _ = (pullback.fst q q ≫ V.ι ≫ m.left) ≫ A.hom := congrArg (· ≫ A.hom) e.symm
      _ = _ := by simp only [Category.assoc, Over.w]
  have hs : (pullback.fst q q).appTop s = (pullback.snd q q).appTop s := by
    refine eq_of_pullback_eq_on_closedPoints p fun x hx => ?_
    let u := pointOfClosedPoint p x hx
    let a : Spec (.of K) ⟶ V := u ≫ pullback.fst q q
    let b : Spec (.of K) ⟶ V := u ≫ pullback.snd q q
    have hau : u ≫ p = 𝟙 _ := pointOfClosedPoint_comp p x hx
    let a' : 𝟙_ (Over (Spec (.of K))) ⟶ A := Over.homMk (a ≫ V.ι) (by
      simp only [a, Category.assoc]; exact hau)
    let b' : 𝟙_ (Over (Spec (.of K))) ⟶ A := Over.homMk (b ≫ V.ι) (by
      exact (Category.assoc b V.ι A.hom).trans
        ((Category.assoc u (pullback.snd q q) (V.ι ≫ A.hom)).trans
          ((congrArg (u ≫ ·) ep).trans hau)))
    have hab : a' ≫ m = b' ≫ m := Over.OverMorphism.ext (by
      change (a ≫ V.ι) ≫ m.left = (b ≫ V.ι) ≫ m.left
      simpa only [a, b, Category.assoc] using congrArg (u ≫ ·) e)
    let y := a' * b'⁻¹
    have hy : y ≫ m = 1 := by
      have hi : b'⁻¹ ≫ m = (b' ≫ m)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
      change (a' * b'⁻¹) ≫ m = 1
      rw [MonObj.mul_comp, hi, hab, mul_inv_cancel]
    let τ : A ⟶ A := (toUnit A ≫ y) * 𝟙 A
    have hτ : τ ≫ m = m := by
      change ((toUnit A ≫ y) * 𝟙 A) ≫ m = m
      rw [MonObj.mul_comp, Category.assoc, hy, MonObj.comp_one, _root_.one_mul, Category.id_comp]
    have hτ' : τ.left ≫ m.left = m.left := congrArg Over.Hom.left hτ
    have hV : V ≤ τ.left ⁻¹ᵁ V := by
      change m.left ⁻¹ᵁ U ≤ τ.left ⁻¹ᵁ (m.left ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, hτ']
    have he : b' ≫ τ = a' := by
      change b' ≫ ((toUnit A ≫ y) * 𝟙 A) = a'
      rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      change y * b' = a'
      exact inv_mul_cancel_right _ _
    have eab : a = b ≫ τ.left.resLE V V hV := by
      apply (cancel_mono V.ι).mp
      exact (congrArg Over.Hom.left he).symm.trans
        ((Category.assoc b V.ι τ.left).trans
          ((congrArg (b ≫ ·) (τ.left.resLE_comp_ι hV).symm).trans (Category.assoc _ _ _).symm))
    have hval : (τ.left.resLE V V hV).appTop s = s :=
      (resLE_appTop_topIso_inv τ.left hV f).trans (congrArg V.topIso.inv (hf y hy hV))
    let ev (f : Spec (.of K) ⟶ V.toScheme) := f.appTop s
    let eval (g : Γ(V.toScheme, ⊤) ⟶ Γ(Spec (.of K), ⊤)) := g s
    calc
      _ = ev a := (congrArg eval (Scheme.Hom.comp_appTop u (pullback.fst q q))).symm
      _ = ev (b ≫ τ.left.resLE V V hV) := congrArg ev eab
      _ = b.appTop ((τ.left.resLE V V hV).appTop s) :=
        congrArg eval (Scheme.Hom.comp_appTop b (τ.left.resLE V V hV))
      _ = ev b := congrArg (fun r => b.appTop r) hval
      _ = _ := congrArg eval (Scheme.Hom.comp_appTop u (pullback.snd q q))
  obtain ⟨g, hg⟩ := exists_appTop_eq_of_effectiveEpi q (IsPullback.of_hasPullback q q) s hs
  let v := U.topIso.hom g
  have hv : U.topIso.inv v = g := Iso.hom_inv_id_apply _ _
  have happ (r : Γ(A.left, U)) : q.appTop (U.topIso.inv r) = V.topIso.inv (m.left.app U r) := by
    have e : m.left.resLE U V le_rfl = q := m.left.resLE_eq_morphismRestrict
    exact (congrArg (fun a : V.toScheme ⟶ U.toScheme => a.appTop (U.topIso.inv r)) e.symm).trans
      ((resLE_appTop_topIso_inv m.left le_rfl r).trans
        (congrArg (fun a : Γ(A.left, U) ⟶ Γ(A.left, V) => V.topIso.inv (a r)) m.left.appLE_eq_app))
  have hinj : Function.Injective V.topIso.inv := ConcreteCategory.injective_of_mono_of_preservesPullback _
  have h' : m.left.app U v = f := hinj ((happ v).symm.trans (by rw [hv]; exact hg))
  refine ⟨v, h', fun w hw => ?_⟩
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback U.topIso.inv)
  apply injective_appTop_of_epi q
  rw [happ, happ, hw, h']

end GlobalTheory.FlatDescent
