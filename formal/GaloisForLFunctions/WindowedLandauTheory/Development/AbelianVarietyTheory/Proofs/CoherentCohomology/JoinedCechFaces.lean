import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechDatum
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! If coefficients outside one face vanish, the joined Čech complex is the
Čech complex of that face. -/

noncomputable section

open CategoryTheory GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

variable {R ι κ : Type} [CommRing R] [LinearOrder ι] [LinearOrder κ]
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ)) [∀ s, Module R (D.obj s)]
  (hD : ∀ {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) (r : R) (x : D.obj s),
    D.res h (r • x) = r • D.res h x)

include hD in
theorem leftSlice_linear (J : Finset κ) {s t : Finset ι} (h : s ⊆ t) (r : R)
    (x : (D.leftSlice J).obj s) :
    (D.leftSlice J).res h (r • x) = r • (D.leftSlice J).res h x :=
  hD (uni_mono h (Finset.Subset.refl _)) r x

include hD in
theorem rightSlice_linear (I : Finset ι) {s t : Finset κ} (h : s ⊆ t) (r : R)
    (x : (D.rightSlice I).obj s) :
    (D.rightSlice I).res h (r • x) = r • (D.rightSlice I).res h x :=
  hD (uni_mono (Finset.Subset.refl _) h) r x

private def leftFaceTerm (n : ℕ) :
    D.degreeSubmodule (R := R) n →ₗ[R] (D.leftSlice ∅).degreeSubmodule (R := R) n where
  toFun x := ⟨fun I => x.1 (uni I ∅), fun I hI => x.2 _ (by simpa only [card_uni, Finset.card_empty, add_zero] using hI)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem leftFaceTerm_bijective
    (hzero : ∀ s : Finset (ι ⊕ₗ κ), rgt s ≠ ∅ → Subsingleton (D.obj s)) (n : ℕ) :
    Function.Bijective (D.leftFaceTerm (R := R) n) := by
  classical
  refine ⟨fun x y he => Subtype.ext (funext fun s => ?_), fun x => ?_⟩
  · obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    by_cases hJ : J = ∅
    · subst J
      exact congrArg (fun z : (D.leftSlice ∅).degreeSubmodule (R := R) n => z.1 I) he
    · exact (hzero (uni I J) (by simpa only [rgt_uni] using hJ)).elim _ _
  · let a (I : Finset ι) (J : Finset κ) : D.obj (uni I J) :=
      if h : J = ∅ then h.symm ▸ x.1 I else 0
    let y := (D.cochainSlices R).symm a
    have hy (I : Finset ι) (J : Finset κ) : y (uni I J) = a I J :=
      congrFun (congrFun ((D.cochainSlices R).apply_symm_apply a) I) J
    have hd : D.IsDeg y n := by
      intro s
      obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
      intro hs
      rw [hy]
      by_cases hJ : J = ∅
      · subst J
        exact (dif_pos rfl).trans
          (x.2 I (by simpa only [card_uni, Finset.card_empty, add_zero] using hs))
      · exact dif_neg hJ
    exact ⟨⟨y, hd⟩, Subtype.ext (funext fun I => (hy I ∅).trans (dif_pos rfl))⟩

/-- Restrict to the left face when all coefficients with a right index vanish. -/
def linearComplexIsoLeftFace
    (hzero : ∀ s : Finset (ι ⊕ₗ κ), rgt s ≠ ∅ → Subsingleton (D.obj s)) :
    D.linearComplex hD ≅ (D.leftSlice ∅).linearComplex (D.leftSlice_linear hD ∅) := by
  let φ : D.linearComplex hD ⟶ (D.leftSlice ∅).linearComplex (D.leftSlice_linear hD ∅) :=
    CochainComplex.ofHom (fun n => ModuleCat.ofHom (D.leftFaceTerm n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [linearComplex, CochainComplex.of_d]
      refine Subtype.ext (funext fun I => ?_)
      change (D.leftSlice ∅).d (fun A => x.1 (uni A ∅)) I = D.d x.1 (uni I ∅)
      rw [D.d_uni, show (D.rightSlice I).d (fun B => x.1 (uni I B)) ∅ = 0 by simp [FinsetCechDatum.d],
        smul_zero, add_zero])
  haveI (n : ℕ) : IsIso (φ.f n) := by
    let e := LinearEquiv.ofBijective (D.leftFaceTerm (R := R) n) (D.leftFaceTerm_bijective hzero n)
    change IsIso e.toModuleIso.hom
    infer_instance
  letI := HomologicalComplex.Hom.isIso_of_components φ
  exact asIso φ

private def rightFaceTerm (n : ℕ) :
    D.degreeSubmodule (R := R) n →ₗ[R] (D.rightSlice ∅).degreeSubmodule (R := R) n where
  toFun x := ⟨fun J => x.1 (uni ∅ J), fun J hJ => x.2 _ (by simpa only [card_uni, Finset.card_empty, zero_add] using hJ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rightFaceTerm_bijective
    (hzero : ∀ s : Finset (ι ⊕ₗ κ), lft s ≠ ∅ → Subsingleton (D.obj s)) (n : ℕ) :
    Function.Bijective (D.rightFaceTerm (R := R) n) := by
  classical
  refine ⟨fun x y he => Subtype.ext (funext fun s => ?_), fun x => ?_⟩
  · obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    by_cases hI : I = ∅
    · subst I
      exact congrArg (fun z : (D.rightSlice ∅).degreeSubmodule (R := R) n => z.1 J) he
    · exact (hzero (uni I J) (by simpa only [lft_uni] using hI)).elim _ _
  · let a (I : Finset ι) (J : Finset κ) : D.obj (uni I J) :=
      if h : I = ∅ then h.symm ▸ x.1 J else 0
    let y := (D.cochainSlices R).symm a
    have hy (I : Finset ι) (J : Finset κ) : y (uni I J) = a I J :=
      congrFun (congrFun ((D.cochainSlices R).apply_symm_apply a) I) J
    have hd : D.IsDeg y n := by
      intro s
      obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
      intro hs
      rw [hy]
      by_cases hI : I = ∅
      · subst I
        exact (dif_pos rfl).trans
          (x.2 J (by simpa only [card_uni, Finset.card_empty, zero_add] using hs))
      · exact dif_neg hI
    exact ⟨⟨y, hd⟩, Subtype.ext (funext fun J => (hy ∅ J).trans (dif_pos rfl))⟩

/-- Restrict to the right face when all coefficients with a left index vanish. -/
def linearComplexIsoRightFace
    (hzero : ∀ s : Finset (ι ⊕ₗ κ), lft s ≠ ∅ → Subsingleton (D.obj s)) :
    D.linearComplex hD ≅ (D.rightSlice ∅).linearComplex (D.rightSlice_linear hD ∅) := by
  let φ : D.linearComplex hD ⟶ (D.rightSlice ∅).linearComplex (D.rightSlice_linear hD ∅) :=
    CochainComplex.ofHom (fun n => ModuleCat.ofHom (D.rightFaceTerm n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [linearComplex, CochainComplex.of_d]
      refine Subtype.ext (funext fun J => ?_)
      change (D.rightSlice ∅).d (fun B => x.1 (uni ∅ B)) J = D.d x.1 (uni ∅ J)
      rw [D.d_uni, show (D.leftSlice J).d (fun A => x.1 (uni A J)) ∅ = 0 by simp [FinsetCechDatum.d],
        zero_add, Finset.card_empty, pow_zero, one_smul])
  haveI (n : ℕ) : IsIso (φ.f n) := by
    let e := LinearEquiv.ofBijective (D.rightFaceTerm (R := R) n) (D.rightFaceTerm_bijective hzero n)
    change IsIso e.toModuleIso.hom
    infer_instance
  letI := HomologicalComplex.Hom.isIso_of_components φ
  exact asIso φ

end HTGeometry.FinsetCechDatum
