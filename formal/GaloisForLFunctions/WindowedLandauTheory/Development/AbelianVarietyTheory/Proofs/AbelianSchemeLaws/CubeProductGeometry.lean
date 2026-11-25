import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks

/-! Projection of the abelian cube onto its third factor is a family of abelian squares. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} (A : Over S)

/-- The three projections of the right-associated triple product over the base. -/
def cubeProjection : Fin 3 → (A ⊗ (A ⊗ A) ⟶ A) :=
  ![fst A (A ⊗ A), snd A (A ⊗ A) ≫ fst A A, snd A (A ⊗ A) ≫ snd A A]

/-- On pulling back the third projection, the first two factors base change to the new base. -/
theorem exists_cube_chart {T : Scheme.{0}} (j : T ⟶ A.left) :
    let B := (Over.pullback (j ≫ A.hom)).obj A
    ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ A)).left,
      IsPullback q (B ⊗ B).hom (cubeProjection A 2).left j ∧
      q ≫ (cubeProjection A 0).left =
        (fst B B).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (cubeProjection A 1).left =
        (snd B B).left ≫ pullback.fst A.hom (j ≫ A.hom) := by
  let B := (Over.pullback (j ≫ A.hom)).obj A
  let b : B.left ⟶ A.left := pullback.fst A.hom (j ≫ A.hom)
  have hB : IsPullback b B.hom A.hom (j ≫ A.hom) := IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback _ _
  have h₃ : IsPullback (fst A (A ⊗ A)).left (snd A (A ⊗ A)).left A.hom (A ⊗ A).hom :=
    IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom :=
    IsPullback.of_hasPullback _ _
  have hm₀ : b ≫ A.hom = (B.hom ≫ j) ≫ A.hom :=
    hB.w.trans (Category.assoc _ _ _).symm
  let m : B.left ⟶ (A ⊗ A).left := h₂.lift b (B.hom ≫ j) hm₀
  have m₁ : m ≫ (fst A A).left = b := h₂.lift_fst _ _ _
  have m₂ : m ≫ (snd A A).left = B.hom ≫ j := h₂.lift_snd _ _ _
  have hm : IsPullback m B.hom (snd A A).left j :=
    IsPullback.of_right (by rw [m₁]; exact hB) m₂ h₂
  have mw : m ≫ (A ⊗ A).hom = B.hom ≫ j ≫ A.hom := by
    calc
      m ≫ (A ⊗ A).hom = m ≫ (snd A A).left ≫ A.hom :=
        (congrArg (m ≫ ·) (Over.w (snd A A))).symm
      _ = (m ≫ (snd A A).left) ≫ A.hom := (Category.assoc _ _ _).symm
      _ = (B.hom ≫ j) ≫ A.hom := congrArg (· ≫ A.hom) m₂
      _ = B.hom ≫ j ≫ A.hom := Category.assoc _ _ _
  have ho : IsPullback ((fst B B).left ≫ b) (snd B B).left A.hom (m ≫ (A ⊗ A).hom) := by
    rw [mw]
    exact hBB.paste_horiz hB
  have hq₀ : ((fst B B).left ≫ b) ≫ A.hom = ((snd B B).left ≫ m) ≫ (A ⊗ A).hom :=
    ho.w.trans (Category.assoc _ _ _).symm
  let q := h₃.lift ((fst B B).left ≫ b) ((snd B B).left ≫ m) hq₀
  have q₁ : q ≫ (fst A (A ⊗ A)).left = (fst B B).left ≫ b := h₃.lift_fst _ _ _
  have q₂ : q ≫ (snd A (A ⊗ A)).left = (snd B B).left ≫ m := h₃.lift_snd _ _ _
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ A)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h₃
  refine ⟨q, ?_, q₁, ?_⟩
  · change IsPullback q (B ⊗ B).hom ((snd A (A ⊗ A)).left ≫ (snd A A).left) j
    rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · change q ≫ (snd A (A ⊗ A)).left ≫ (fst A A).left = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (fst A A).left) q₂).trans
        ((Category.assoc _ _ _).trans (congrArg ((snd B B).left ≫ ·) m₁)))

end GlobalTheory.AbLaw.Cube
