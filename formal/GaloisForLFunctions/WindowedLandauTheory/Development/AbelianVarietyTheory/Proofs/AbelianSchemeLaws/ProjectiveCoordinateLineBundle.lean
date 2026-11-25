import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveEmbeddingCoordinates

/-! Projective coordinate ratios glue the tautological degree-one line bundle and its sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ProjectiveSections.Coordinates

variable {X : Scheme.{0}} {n : ℕ} (C : Coordinates X n)

private theorem ratio_mul_on (i j k : Fin (n + 1)) {W : X.Opens} (hi : W ≤ C.U i) (hj : W ≤ C.U j) :
    resG X hi (C.ratio i j) * resG X hj (C.ratio j k) = resG X hi (C.ratio i k) := by
  have e := congrArg (resG X (le_inf hi hj)) (C.ratio_mul i j k)
  simpa only [map_mul, resG_resG] using e

private theorem isUnit_res_ratio (i j : Fin (n + 1)) :
    IsUnit (resG X (inf_le_left : C.U i ⊓ C.U j ≤ C.U i) (C.ratio i j)) := by
  let h := (C.basicOpen_ratio i j).ge
  have e := (X.toRingedSpace.isUnit_res_basicOpen (C.ratio i j)).map (resG X h)
  change IsUnit (resG X h (resG X (X.basicOpen_le (C.ratio i j)) (C.ratio i j))) at e
  rwa [resG_resG] at e

/-- Local generators are the coordinate sections on their respective nonvanishing opens. -/
def coordinateBundle : LB X where
  ι := Fin (n + 1)
  U := C.U
  g i j := (isUnit_res_ratio C i j).unit

private theorem coordinateBundle_g (i j : Fin (n + 1)) :
    ((C.coordinateBundle).g i j).val =
      resG X (inf_le_left : C.U i ⊓ C.U j ≤ C.U i) (C.ratio i j) :=
  (isUnit_res_ratio C i j).unit_spec

theorem coordinateBundle_isLB : (C.coordinateBundle).IsLB where
  cover := C.cover
  g_self i := by
    apply Units.ext
    change resG X (le_inf le_rfl le_rfl : C.U i ≤ C.U i ⊓ C.U i)
      ((C.coordinateBundle).g i i).val = 1
    rw [coordinateBundle_g, resG_resG, C.ratio_self, map_one]
  cocycle i j k := by
    apply Units.ext
    let W := C.U i ⊓ C.U j ⊓ C.U k
    let hi : W ≤ C.U i := inf_le_left.trans inf_le_left
    let hj : W ≤ C.U j := inf_le_left.trans inf_le_right
    let hk : W ≤ C.U k := inf_le_right
    change resG X (le_inf hi hj) ((C.coordinateBundle).g i j).val *
      resG X (le_inf hj hk) ((C.coordinateBundle).g j k).val =
        resG X (le_inf hi hk) ((C.coordinateBundle).g i k).val
    simp only [coordinateBundle_g, resG_resG]
    exact C.ratio_mul_on i j k hi hj

/-- In chart `i`, the `j`-th coordinate section is represented by the ratio `Xⱼ/Xᵢ`. -/
def coordinateSection (j : Fin (n + 1)) : (C.coordinateBundle).Sec where
  f i := C.ratio i j
  compat i k := by
    change resG X (inf_le_left : C.U i ⊓ C.U k ≤ C.U i) (C.ratio i j) =
      ((C.coordinateBundle).g i k).val * resG X inf_le_right (C.ratio k j)
    rw [coordinateBundle_g]
    exact (C.ratio_mul i k j).symm

theorem nonzeroLocus_coordinateSection (i : Fin (n + 1)) : nonzeroLocus (C.coordinateSection i) = C.U i := by
  change (⨆ j, X.basicOpen (C.ratio j i)) = C.U i
  simp only [C.basicOpen_ratio, ← iSup_inf_eq, C.cover, top_inf_eq]

def coordinateSectionRatio (i j : Fin (n + 1)) : Γ(X, nonzeroLocus (C.coordinateSection i)) :=
  resG X (C.nonzeroLocus_coordinateSection i).le (C.ratio i j)

theorem coordinateSectionRatio_rel (i j k : Fin (n + 1)) :
    resG X (inf_le_right : nonzeroLocus (C.coordinateSection i) ⊓ C.U k ≤ C.U k)
      ((C.coordinateSection j).f k) =
      resG X inf_le_left (C.coordinateSectionRatio i j) * resG X inf_le_right ((C.coordinateSection i).f k) := by
  change resG X inf_le_right (C.ratio k j) =
    resG X inf_le_left (resG X (C.nonzeroLocus_coordinateSection i).le (C.ratio i j)) *
      resG X inf_le_right (C.ratio k i)
  rw [resG_resG, mul_comm]
  exact (C.ratio_mul_on k i j inf_le_right (inf_le_left.trans (C.nonzeroLocus_coordinateSection i).le)).symm

theorem coordinateSectionRatio_aeval_surjective {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (i : Fin (n + 1))
    (h : letI := sectionAlgebra f (C.U i)
      Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, C.U i)) (C.ratio i))) :
    letI := sectionAlgebra f (nonzeroLocus (C.coordinateSection i))
    Function.Surjective (MvPolynomial.aeval (R := R) (C.coordinateSectionRatio i)) := by
  let V := nonzeroLocus (C.coordinateSection i)
  let e := C.nonzeroLocus_coordinateSection i
  let ρ := sectionRes f (homOfLE e.le)
  letI := sectionAlgebra f V
  letI := sectionAlgebra f (C.U i)
  have hρ : Function.Surjective ρ := by
    intro x
    refine ⟨resG X e.ge x, ?_⟩
    change resG X e.le (resG X e.ge x) = x
    rw [resG_resG, resG_self]
  have he : ρ.comp (MvPolynomial.aeval (R := R) (C.ratio i)) =
      MvPolynomial.aeval (C.coordinateSectionRatio i) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  rw [← he]
  exact hρ.comp h

end GlobalTheory.ProjectiveSections.Coordinates
