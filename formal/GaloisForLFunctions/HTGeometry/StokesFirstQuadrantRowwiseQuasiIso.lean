import GaloisForLFunctions.HTGeometry.StokesFirstQuadrantTotalSingle
import GaloisForLFunctions.HTGeometry.StokesNonnegativePrefixFiltration
import GaloisForLFunctions.HTGeometry.StokesShortExactQuasiIso

/-!
# Rowwise quasi-isomorphisms and first-quadrant totalization

A morphism of nonnegative bicomplexes of module presheaves that is a quasi-isomorphism in every
row induces a quasi-isomorphism on total complexes. The proof uses finite stupid prefixes, adjacent
short exact sequences, exact totalization, and degreewise stabilization at prefix `n + 1`.
-/

open CategoryTheory Limits

universe u

namespace GaloisForLFunctions.IrregularStokes.FirstQuadrantRowwiseQuasiIso

open FirstQuadrantTotalExact
open FirstQuadrantTotalSingle
open NonnegativePrefixFiltration

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

abbrev M := ModulePresheaf A
abbrev B := ModulePresheafBicomplex A

noncomputable def prefixZeroIso (K : B A) :
    prefixTrunc K 0 ≅ outerSingle A (K.X 0) 0 :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if hi : i = 0 then
      prefixXIso K 0 i (by omega) ≪≫ K.XIsoOfEq hi ≪≫
        (HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.down ℕ) 0 (K.X 0) i hi).symm
    else
      (prefix_isZero_X K 0 i (by omega)).iso
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 (K.X 0) i hi))
    (fun i j hij => by
      have hi : 0 < i := by
        change j + 1 = i at hij
        omega
      exact (prefix_isZero_X K 0 i hi).eq_of_src _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma prefixZeroIso_naturality {K L : B A} (φ : K ⟶ L) :
    prefixTruncMap φ 0 ≫ (prefixZeroIso A L).hom =
      (prefixZeroIso A K).hom ≫ outerSingleMap A (φ.f 0) 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f]
    dsimp [prefixZeroIso]
    change (prefixTruncMap φ 0).f 0 ≫
        (prefixXIso L 0 0 le_rfl).hom ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X 0)).inv =
      (prefixXIso K 0 0 le_rfl).hom ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 0 (K.X 0)).inv ≫
            (outerSingleMap A (φ.f 0) 0).f 0
    calc
      _ = (prefixXIso K 0 0 le_rfl).hom ≫ φ.f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X 0)).inv := by
        rw [← Category.assoc,
          prefixTruncMap_prefixXIso_hom φ 0 0 le_rfl]
        rw [Category.assoc]
      _ = _ := by
        rw [HomologicalComplex.single_map_f_self]
        simp only [Iso.inv_hom_id_assoc]
  · exact (prefix_isZero_X K 0 i (by omega)).eq_of_src _ _

theorem totalPrefixZeroMap_quasiIso {K L : B A} (φ : K ⟶ L)
    [QuasiIso (φ.f 0)] :
    QuasiIso (HomologicalComplex₂.total.map (prefixTruncMap φ 0)
      (ComplexShape.down ℕ)) := by
  letI : QuasiIso
      (HomologicalComplex₂.total.map (outerSingleMap A (φ.f 0) 0)
        (ComplexShape.down ℕ)) := totalSingleMap_quasiIso A (φ.f 0) 0
  letI : IsIso (HomologicalComplex₂.total.map (prefixZeroIso A K).hom
      (ComplexShape.down ℕ)) := by
    change IsIso ((HomologicalComplex₂.totalFunctor (M A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)).map (prefixZeroIso A K).hom)
    infer_instance
  letI : IsIso (HomologicalComplex₂.total.map (prefixZeroIso A L).hom
      (ComplexShape.down ℕ)) := by
    change IsIso ((HomologicalComplex₂.totalFunctor (M A)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)).map (prefixZeroIso A L).hom)
    infer_instance
  have hnat := congrArg
    (fun ψ => HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ))
    (prefixZeroIso_naturality A φ)
  simp only [HomologicalComplex₂.total.map_comp] at hnat
  haveI : QuasiIso
      (HomologicalComplex₂.total.map (prefixTruncMap φ 0)
          (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map (prefixZeroIso A L).hom
          (ComplexShape.down ℕ)) := by
    rw [hnat]
    infer_instance
  exact quasiIso_of_comp_right _
    (HomologicalComplex₂.total.map (prefixZeroIso A L).hom
      (ComplexShape.down ℕ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem totalPrefixMap_quasiIso {K L : B A} (φ : K ⟶ L)
    (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) (r : ℕ) :
    QuasiIso (HomologicalComplex₂.total.map (prefixTruncMap φ r)
      (ComplexShape.down ℕ)) := by
  induction r with
  | zero =>
      letI : QuasiIso (φ.f 0) := hφ 0
      exact totalPrefixZeroMap_quasiIso A φ
  | succ r ih =>
      let F := HomologicalComplex₂.totalFunctor (M A)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)
      have hK := totalFunctor_map_shortExact A
        (prefixShortComplex K r) (prefixShortExact K r)
      have hL := totalFunctor_map_shortExact A
        (prefixShortComplex L r) (prefixShortExact L r)
      apply ShortExactQuasiIso.quasiIso_middle
        (F.mapShortComplex.map (prefixShortComplexMap φ r)) hK hL
      · change QuasiIso (HomologicalComplex₂.total.map
          (prefixTruncMap φ r) (ComplexShape.down ℕ))
        exact ih
      · letI : QuasiIso (φ.f (r + 1)) := hφ (r + 1)
        change QuasiIso (HomologicalComplex₂.total.map
          (outerSingleMap A (φ.f (r + 1)) (r + 1))
            (ComplexShape.down ℕ))
        exact totalSingleMap_quasiIso A (φ.f (r + 1)) (r + 1)

theorem totalPrefixInclusion_f_isIso (K : B A) (r n : ℕ) (hn : n ≤ r) :
    IsIso ((HomologicalComplex₂.total.map (prefixInclusion K r)
      (ComplexShape.down ℕ)).f n) := by
  change IsIso (GradedObject.mapMap
    (HomologicalComplex₂.toGradedObjectMap (prefixInclusion K r))
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) n)
  change IsIso (Limits.Sigma.map (fun x : Antidiagonal n =>
    HomologicalComplex₂.toGradedObjectMap (prefixInclusion K r) x))
  letI (x : Antidiagonal n) : IsIso
      (HomologicalComplex₂.toGradedObjectMap (prefixInclusion K r) x) := by
    rcases x with ⟨⟨i, j⟩, hij⟩
    have hi : i ≤ r := by
      change i + j = n at hij
      omega
    change IsIso (((prefixInclusion K r).f i).f j)
    rw [prefixInclusion_f_of_le K r i hi]
    infer_instance
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem totalPrefixInclusion_quasiIsoAt (K : B A) (n : ℕ) :
    QuasiIsoAt (HomologicalComplex₂.total.map (prefixInclusion K (n + 1))
      (ComplexShape.down ℕ)) n := by
  rw [quasiIsoAt_iff]
  let ψ := (HomologicalComplex.shortComplexFunctor (M A)
    (ComplexShape.down ℕ) n).map
      (HomologicalComplex₂.total.map (prefixInclusion K (n + 1))
        (ComplexShape.down ℕ))
  letI : IsIso ψ.τ₁ := by
    change IsIso ((HomologicalComplex₂.total.map
      (prefixInclusion K (n + 1)) (ComplexShape.down ℕ)).f
        ((ComplexShape.down ℕ).prev n))
    apply totalPrefixInclusion_f_isIso A K
    simp
  letI : IsIso ψ.τ₂ := by
    change IsIso ((HomologicalComplex₂.total.map
      (prefixInclusion K (n + 1)) (ComplexShape.down ℕ)).f n)
    apply totalPrefixInclusion_f_isIso A K
    omega
  letI : IsIso ψ.τ₃ := by
    change IsIso ((HomologicalComplex₂.total.map
      (prefixInclusion K (n + 1)) (ComplexShape.down ℕ)).f
        ((ComplexShape.down ℕ).next n))
    apply totalPrefixInclusion_f_isIso A K
    cases n with
    | zero => simp
    | succ n =>
        simp
        omega
  letI : IsIso ψ := ShortComplex.isIso_of_isIso ψ
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A rowwise quasi-isomorphism of nonnegative bicomplexes induces a quasi-isomorphism on
first-quadrant total complexes. -/
theorem totalMap_quasiIso_of_rowwise {K L : B A} (φ : K ⟶ L)
    (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) :
    QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro n
  letI : QuasiIso (HomologicalComplex₂.total.map
      (prefixTruncMap φ (n + 1)) (ComplexShape.down ℕ)) :=
    totalPrefixMap_quasiIso A φ hφ (n + 1)
  letI : QuasiIsoAt (HomologicalComplex₂.total.map
      (prefixInclusion K (n + 1)) (ComplexShape.down ℕ)) n :=
    totalPrefixInclusion_quasiIsoAt A K n
  letI : QuasiIsoAt (HomologicalComplex₂.total.map
      (prefixInclusion L (n + 1)) (ComplexShape.down ℕ)) n :=
    totalPrefixInclusion_quasiIsoAt A L n
  have hnat := congrArg
    (fun ψ => HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ))
    (prefixInclusion_naturality φ (n + 1))
  simp only [HomologicalComplex₂.total.map_comp] at hnat
  letI : QuasiIsoAt
      (HomologicalComplex₂.total.map (prefixTruncMap φ (n + 1))
          (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map (prefixInclusion L (n + 1))
          (ComplexShape.down ℕ)) n := inferInstance
  letI : QuasiIsoAt
      (HomologicalComplex₂.total.map (prefixInclusion K (n + 1))
          (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n := by
    rw [← hnat]
    infer_instance
  exact quasiIsoAt_of_comp_left
    (HomologicalComplex₂.total.map (prefixInclusion K (n + 1))
      (ComplexShape.down ℕ))
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n

end GaloisForLFunctions.IrregularStokes.FirstQuadrantRowwiseQuasiIso
