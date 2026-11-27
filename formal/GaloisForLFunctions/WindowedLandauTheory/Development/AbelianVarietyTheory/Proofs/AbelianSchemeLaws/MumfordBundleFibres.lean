import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TranslationDifferenceAdditivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters

/-! Restricting the universal translation difference to a fibre gives the
translation difference at the point of that fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.TwistTranslate GlobalTheory.TranslateAdditive
open scoped CategoryTheory.Obj

namespace GlobalTheory.MumfordFibre

attribute [local instance] Over.cartesianMonoidalCategory

/-- The composite pullback and the iterated pullback present the same bundle. -/
theorem exists_iso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    ∃ w : LB.Iso ((L.pull f).pull g) (L.pull (g ≫ f)), w.IsGen :=
  (pullFormalChart L (fun _ : PUnit => f) (fun _ => 1) g).iso_of_common
    (ChartPull.id (L.pull (g ≫ f))) (hL.pull (g ≫ f))

/-- Restriction to a fixed translating point is compatible with pullback. -/
theorem exists_iso_pull_translDiff {K : Type} [Field K] {A : Over (Spec (.of K))}
    [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over (Spec (.of K))}
    (p : T ⟶ A ⊗ A) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A)
    (hp : p ≫ fst A A = toUnit T ≫ x) :
    let M := LB.LinComb L (K := Fin 2) ![(translate A x).left, 𝟙 A.left] ![1, -1]
    ∃ w : LB.Iso (M.pull (p ≫ snd A A).left) ((translDiff A L (𝟙 A)).pull p.left), w.IsGen := by
  let d : Fin 2 → ℤ := ![1, -1]
  let g : Fin 2 → (A.left ⟶ A.left) := ![(translate A x).left, 𝟙 A.left]
  let f : Fin 2 → ((A ⊗ A).left ⟶ A.left) := ![(translPt A (𝟙 A)).left, (snd A A).left]
  let q := p ≫ snd A A
  have ht : translPt A (𝟙 A) = fst A A * snd A A := by
    rw [translPt, Category.comp_id, Hom.mul_def]
  have h : (fun k => p.left ≫ f k) = (fun k => q.left ≫ g k) := by
    funext k
    fin_cases k
    · change (p ≫ translPt A (𝟙 A)).left = (q ≫ translate A x).left
      apply congrArg Over.Hom.left
      simp only [ht, q, TwistTranslate.translate, MonObj.comp_mul, hp, comp_toUnit_assoc, Category.comp_id]
    · exact (Category.comp_id q.left).symm
  let P := pullFormalChart L g d q.left
  let Q : ChartPull ((translDiff A L (𝟙 A)).pull p.left)
      (LB.LinComb L (fun k => q.left ≫ g k) d) (𝟙 T.left) :=
    h ▸ pullFormalChart L f d p.left
  exact P.iso_of_common Q (hL.linComb _ _)

end GlobalTheory.MumfordFibre
