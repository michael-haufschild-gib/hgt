import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.SmoothReducedness
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! Equality on geometric points gives effective descent along quasi-compact étale surjections. -/

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/-- Geometric points detect equality on a reduced source with separated target. -/
theorem hom_ext_geometricPoints {X Y B : Scheme.{0}} [IsReduced X] (p : Y ⟶ B)
    [IsSeparated p] {f g : X ⟶ Y} (hfg : f ≫ p = g ≫ p)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (CommRingCat.of Ω) ⟶ X),
      x ≫ f = x ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g p Set.univ dense_univ (fun x _ => ?_) hfg
  let K := X.residueField x
  let Ω := AlgebraicClosure K
  let i : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  haveI : Surjective i := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  refine ext_of_isDominant_of_isSeparated p ?_ i ?_
  · rw [Category.assoc, Category.assoc, hfg]
  · simpa only [Category.assoc] using h Ω (i ≫ X.fromSpecResidueField x)

/-- Fibrewise constancy on geometric points descends a map to a separated scheme. -/
theorem exists_desc_of_etale_of_geometricPoints {X Y Z B : Scheme.{0}} [IsReduced X]
    (c : X ⟶ Y) [QuasiCompact c] [Etale c] [Surjective c] (p : Y ⟶ B) (q : Z ⟶ B)
    [IsSeparated q] (f : X ⟶ Z) (hf : f ≫ q = c ≫ p)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : Spec (CommRingCat.of Ω) ⟶ X),
      x ≫ c = y ≫ c → x ≫ f = y ≫ f) :
    ∃ g : Y ⟶ Z, c ≫ g = f := by
  have hsm : Smooth (pullback.fst c c) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback c c).flip (inferInstance : Smooth c)
  haveI : IsReduced (pullback c c) :=
    @isReduced_of_smooth_of_isReduced _ _ (pullback.fst c c) hsm ‹IsReduced X›
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hom_ext_geometricPoints q ?_ ?_
    · simp only [Category.assoc, hf]
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      have he : (x ≫ pullback.fst c c) ≫ c = (x ≫ pullback.snd c c) ≫ c := by
        rw [Category.assoc, Category.assoc, pullback.condition]
      simpa only [Category.assoc] using h Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) he
  have comp {T : Scheme.{0}} (u v : T ⟶ X) (huv : u ≫ c = v ≫ c) :
      u ≫ f = v ≫ f := by
    let a := pullback.lift u v huv
    calc
      u ≫ f = a ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, pullback.lift_fst]
      _ = a ≫ pullback.snd c c ≫ f := congrArg (a ≫ ·) key
      _ = v ≫ f := by rw [← Category.assoc, pullback.lift_snd]
  exact ⟨EffectiveEpi.desc c f comp, EffectiveEpi.fac c f comp⟩

end GlobalTheory
