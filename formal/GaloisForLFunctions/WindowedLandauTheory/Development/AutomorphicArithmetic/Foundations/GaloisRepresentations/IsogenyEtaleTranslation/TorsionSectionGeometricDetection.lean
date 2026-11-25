import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupMultiplicationEtale
import Mathlib.FieldTheory.AlgebraicClosure

/-! Equality of torsion sections is detected on geometric points, including over nonreduced bases. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory

/-- The equalizer of two lifts along an étale map is open. Geometric points detect whether it is all of the source. -/
theorem hom_ext_geometricPoints_of_etale {X Y S : Scheme.{0}} (p : Y ⟶ S) [Etale p]
    {a b : X ⟶ Y} (w : a ≫ p = b ≫ p)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ X),
      x ≫ a = x ≫ b) : a = b := by
  let i : X ⟶ pullback p p := pullback.lift a b w
  have ha : i ≫ pullback.fst p p = a := pullback.lift_fst _ _ _
  have hb : i ≫ pullback.snd p p = b := pullback.lift_snd _ _ _
  let e := pullback.snd (pullback.diagonal p) i
  have he : Function.Surjective e := by
    intro z
    let K := AlgebraicClosure (X.residueField z)
    let x : Spec (CommRingCat.of K) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField z) K)) ≫ X.fromSpecResidueField z
    have hx : (x ≫ a) ≫ pullback.diagonal p = x ≫ i := by
      apply pullback.hom_ext
      · rw [Category.assoc (x ≫ a), pullback.diagonal_fst, Category.comp_id, Category.assoc x i, ha]
      · rw [Category.assoc (x ≫ a), pullback.diagonal_snd, Category.comp_id, Category.assoc x i, hb]
        exact h K x
    let g := pullback.lift _ _ hx
    have hg : g ≫ e = x := pullback.lift_snd _ _ _
    let z₀ : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    refine ⟨g z₀, ?_⟩
    exact (congrArg (fun f => f z₀) hg).trans
      ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _))
  haveI : Epi e.base := (TopCat.epi_iff_surjective _).mpr he
  haveI : IsOpenImmersion e := inferInstanceAs (IsOpenImmersion (pullback.snd (pullback.diagonal p) i))
  haveI : IsIso e := IsOpenImmersion.isIso e
  have hv : i = inv e ≫ pullback.fst (pullback.diagonal p) i ≫ pullback.diagonal p := by
    rw [pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← ha, ← hb, hv]
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id]

end GlobalTheory

namespace GlobalTheory.TorsGeomPow

open GlobalTheory.GrpTangent

/-- A geometric bound on the order of a torsion section descends over the entire base. -/
theorem pow_eq_one_of_geometric_points {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    {T : Over S} {x : T ⟶ A} (hx : x ^ n = 1) (d : ℕ)
    (hpt : ∀ (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) : x ^ d = 1 := by
  letI : Etale (mulN A n).left := etale_mulN A hn
  have he : (x ^ d) ≫ mulN A n = (1 : T ⟶ A) ≫ mulN A n := by
    rw [comp_mulN, comp_mulN, ← pow_mul, Nat.mul_comm d n, pow_mul, hx]
    simp only [one_pow]
  apply Over.OverMorphism.ext
  refine hom_ext_geometricPoints_of_etale (mulN A n).left (congrArg Over.Hom.left he) ?_
  intro K _ _ ξ
  let u : Over.mk (ξ ≫ T.hom) ⟶ T := Over.homMk ξ rfl
  have hu : u ≫ x ^ d = u ≫ (1 : T ⟶ A) := by
    rw [MonObj.comp_pow, hpt K ξ, MonObj.comp_one]
  exact congrArg Over.Hom.left hu

end GlobalTheory.TorsGeomPow
