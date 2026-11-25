import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeProductGeometry

/-! The alternating cube bundle has a canonical generator on each identity face. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

/-- The partial product for one subset of the three coordinates. -/
def cubeMorphism (I : Finset (Fin 3)) : (A ⊗ (A ⊗ A)).left ⟶ A.left :=
  (∏ j ∈ I, cubeProjection A j).left

/-- The sign of a subset in the alternating cube. -/
def cubeExponent (I : Finset (Fin 3)) : ℤ := (-1) ^ (3 - I.card)

/-- The alternating tensor product of pullbacks along all partial products. -/
def cubeBundle (L : LB A.left) : LB (A ⊗ (A ⊗ A)).left :=
  LB.LinComb L (cubeMorphism A) cubeExponent

/-- Toggling an identity coordinate pairs equal morphisms with opposite exponents. -/
theorem cube_face_cancels {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ A)).left)
    (i : Fin 3) (b : Z ⟶ S) (h : r ≫ (cubeProjection A i).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ A.left) → U) :
    ∏ I, k (r ≫ cubeMorphism A I) ^ cubeExponent I = 1 := by
  let T := Over.mk (r ≫ (A ⊗ (A ⊗ A)).hom)
  let x : T ⟶ A ⊗ (A ⊗ A) := Over.homMk r rfl
  have hb : b = T.hom := by
    have e := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at e
    exact (e.trans (Category.comp_id _)).symm
  have hx : x ≫ cubeProjection A i = 1 := by
    apply Over.OverMorphism.ext
    rw [Hom.one_def]
    exact h.trans (by rw [hb]; rfl)
  let E : (A ⊗ (A ⊗ A) ⟶ A) →* (T ⟶ A) :=
    { toFun := fun f => x ≫ f
      map_one' := MonObj.comp_one x
      map_mul' := MonObj.comp_mul x }
  let flip (I : Finset (Fin 3)) := if i ∈ I then I.erase i else insert i I
  let F (I : Finset (Fin 3)) := k (r ≫ cubeMorphism A I) ^ cubeExponent I
  have cancel (I : Finset (Fin 3)) (hi : i ∉ I) : F I * F (insert i I) = 1 := by
    have hm : r ≫ cubeMorphism A (insert i I) = r ≫ cubeMorphism A I := by
      change (E (∏ j ∈ insert i I, cubeProjection A j)).left =
        (E (∏ j ∈ I, cubeProjection A j)).left
      rw [Finset.prod_insert hi, map_mul, show E (cubeProjection A i) = 1 from hx, one_mul]
    have hcard : I.card + 1 ≤ 3 := by
      simpa only [Finset.card_insert_of_notMem hi, Fintype.card_fin] using
        (Finset.card_le_univ (insert i I))
    have hp : 3 - I.card = 3 - (I.card + 1) + 1 := by omega
    have he : cubeExponent I = -cubeExponent (insert i I) := by
      simp only [cubeExponent, Finset.card_insert_of_notMem hi]
      rw [hp, pow_succ, mul_neg_one]
    change k (r ≫ cubeMorphism A I) ^ cubeExponent I *
      k (r ≫ cubeMorphism A (insert i I)) ^ cubeExponent (insert i I) = 1
    rw [hm, he, zpow_neg, inv_mul_cancel]
  change ∏ I, F I = 1
  refine Finset.prod_ninvolution flip ?_ ?_ (fun _ => Finset.mem_univ _) ?_
  · intro I
    by_cases hi : i ∈ I
    · have e := cancel (I.erase i) (Finset.notMem_erase _ _)
      rw [Finset.insert_erase hi] at e
      simpa only [flip, if_pos hi, mul_comm] using e
    · simpa only [flip, if_neg hi] using cancel I hi
  · intro I _ e
    have hmem := congrArg (i ∈ ·) e
    by_cases hi : i ∈ I <;> simp [flip, hi] at hmem
  · intro I
    by_cases hi : i ∈ I
    · simp only [flip, if_pos hi, Finset.notMem_erase, if_false, Finset.insert_erase hi]
    · simp only [flip, if_neg hi, Finset.mem_insert_self, if_true, Finset.erase_insert hi]

/-- The ordinary pullback of the cube bundle to an identity face is trivial. -/
theorem trivial_cube_face {L : LB A.left} (hL : L.IsLB)
    {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ A)).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (cubeProjection A i).left = b ≫ η[A].left) :
    ∃ t : ((cubeBundle A L).pull r).Gen, t.IsGen := by
  apply (trivial_pull_linComb L hL (cubeMorphism A) cubeExponent r).2
  obtain ⟨t, ht, -⟩ := exists_gen_of_cancellation L hL _ _ (cube_face_cancels A r i b h)
  exact ⟨t, ht⟩

end GlobalTheory.AbLaw.Cube
