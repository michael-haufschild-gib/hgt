import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.HeckeTower
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupMultiplicationEtale

/-! Base change preserves Hecke towers and their fibre actions.
The two pullback projections verify the transitivity and freeness
conditions after change of base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace UpperTheory.Gal.G3

section BaseChange

variable {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'}
  (f : Y ⟶ X) (h : f ≫ p = q)

abbrev bcMap : pullback q g ⟶ pullback p g :=
  ((Over.pullback g).map (Over.homMk f h : Over.mk q ⟶ Over.mk p)).left

@[simp] theorem bcMap_fst : bcMap g f h ≫ pullback.fst p g = pullback.fst q g ≫ f :=
  pullback.lift_fst _ _ _

@[simp] theorem bcMap_snd : bcMap g f h ≫ pullback.snd p g = pullback.snd q g :=
  pullback.lift_snd _ _ _

private theorem isPullback_bcMap :
    IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) :=
  GlobalTheory.GrpTangent.isPullback_baseChange g (Over.homMk f h : Over.mk q ⟶ Over.mk p)

end BaseChange

variable {B B' : Scheme.{0}} {G : Type} [Group G]

def towerBc (X : Tower B' G) (g : B ⟶ B') : Tower B G where
  ι := X.ι
  K := X.K
  Δ := X.Δ
  K_le := X.K_le
  deep := X.deep
  idx := X.idx
  Z i := pullback (X.q i) g
  q i := pullback.snd (X.q i) g
  tr i j h a b := bcMap g (X.tr i j h a b) (X.tr_q i j h a b)
  tr_q i j h a b := bcMap_snd _ _ _
  tr_self i k a b hk := by
    apply pullback.hom_ext
    · rw [bcMap_fst, X.tr_self i k a b hk, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  tr_mul i j m h h' a b a' b' a'' b'' := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc,
        X.tr_mul i j m h h' a b a' b' a'' b'', bcMap_fst]
    · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  fin i j a b := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_bcMap g _ _) (X.fin i j a b)
  etale i j a b := MorphismProperty.of_isPullback (P := @Etale) (isPullback_bcMap g _ _) (X.etale i j a b)
  onto i j a b := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_bcMap g _ _) (X.onto i j a b)
  trans i j a b hn Ω _ _ x y he := by
    have ef := congrArg (· ≫ pullback.fst (X.q j) g) he
    have es := congrArg (· ≫ pullback.snd (X.q j) g) he
    simp only [Category.assoc, bcMap_fst] at ef
    simp only [Category.assoc, bcMap_snd] at es
    obtain ⟨k, hk, a', b', eq⟩ := X.trans i j a b hn Ω (x ≫ pullback.fst _ _) (y ≫ pullback.fst _ _)
      (by simpa only [Category.assoc] using ef)
    refine ⟨k, hk, a', b', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, eq, Category.assoc]
    · rw [Category.assoc, bcMap_snd, es]
  free i j hij k hk a b Ω _ _ x e := by
    have ef := congrArg (· ≫ pullback.fst (X.q i) g) e
    simp only [Category.assoc, bcMap_fst] at ef
    exact X.free i j hij k hk a b Ω (x ≫ pullback.fst _ _) (by simpa only [Category.assoc] using ef)

end UpperTheory.Gal.G3

#print axioms UpperTheory.Gal.G3.towerBc
