import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionMorphisms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback

/-! Relative ampleness presents the inverse image of an affine open as a projective scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
open CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology UpperTheory.Cb

namespace GlobalTheory.ProjectiveSections

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

private theorem isProjOver_of_section_system {L : LB X} (hL : L.IsLB)
    (f : X ⟶ Spec (CommRingCat.of R)) {n : ℕ}
    (s : Fin (n + 1) → L.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (h : ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
      ∃ r : Fin (n + 1) → Γ(X, nonzeroLocus (s i)),
        (∀ j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k)) ∧
        (letI := sectionAlgebra f (nonzeroLocus (s i))
         Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, nonzeroLocus (s i))) r))) :
    IsProjOver f := by
  cases subsingleton_or_nontrivial R
  · haveI : IsEmpty (Spec (CommRingCat.of R)) := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    haveI : IsEmpty X := Function.isEmpty f
    have a : IsInitial X := (Scheme.isInitial_iff_isEmpty.mpr inferInstance).some
    let i := a.to (PSpace R 0)
    haveI : IsClosedImmersion i := by
      refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
        (PSpace.coordinateOpen R 0) (PSpace.iSup_coordinateOpen R 0)).2 fun j => ?_
      haveI : IsAffine (PSpace.coordinateOpen R 0 j).toScheme := pspaceChart_isAffine j
      haveI : IsEmpty (i ⁻¹ᵁ PSpace.coordinateOpen R 0 j).toScheme := inferInstanceAs
        (IsEmpty ((i ⁻¹ᵁ PSpace.coordinateOpen R 0 j) : Set X))
      refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
      intro u
      exact ⟨0, Subsingleton.elim _ _⟩
    exact ⟨0, i, inferInstance, a.hom_ext _ _⟩
  · choose r hr using fun i => (h i).2
    exact ⟨n, sectionMorphism s f r (fun i => (hr i).1) hL hc,
      sectionMorphism_isClosedImmersion s f r (fun i => (hr i).1) hL hc
        (fun i => (h i).1) (fun i => (hr i).2),
      sectionMorphism_base s f r (fun i => (hr i).1) hL hc⟩

private theorem sectionAlgebra_comp_iso (q : X ⟶ Y) (e : Y ⟶ Spec (CommRingCat.of R))
    [IsIso e] (W : X.Opens) {ι : Type} (r : ι → Γ(X, W))
    (hr : Function.Surjective (MvPolynomial.eval₂Hom (q.appLE ⊤ W le_top).hom r)) :
    letI := sectionAlgebra (q ≫ e) W
    Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, W)) r) := by
  letI := sectionAlgebra (q ≫ e) W
  let b : CommRingCat.of R ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso _).inv ≫ e.appLE ⊤ ⊤ le_top
  haveI : IsIso b := by
    have he : e.appLE ⊤ ⊤ (by simp) = e.appTop := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
        using (rfl : e.appTop = e.appTop)
    haveI : IsIso e.appTop := inferInstanceAs (IsIso (e.app ⊤))
    dsimp only [b]
    rw [he]
    infer_instance
  have hc : b ≫ q.appLE ⊤ W le_top =
      (Scheme.ΓSpecIso _).inv ≫ (q ≫ e).appLE ⊤ W le_top :=
    (Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE q e ⊤ ⊤ W le_top le_top))
  have hp : MvPolynomial.eval₂Hom (algebraMap R Γ(X, W)) r =
      (MvPolynomial.eval₂Hom (q.appLE ⊤ W le_top).hom r).comp (MvPolynomial.map b.hom) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.map_C]
      exact (ConcreteCategory.congr_hom hc x).symm
    · intro j
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.map_X]
  rw [hp]
  exact hr.comp (MvPolynomial.map_surjective _ (ConcreteCategory.bijective_of_isIso b).2)

attribute [local instance] Over.cartesianMonoidalCategory

/-- The section systems in the definition of relative ampleness give projective embeddings
over affine base charts. -/
theorem isProjOver_of_relAmple_on_affine {S : Scheme.{0}} {A : Over S} [GrpObj A]
    {L : LB A.left} (hL : L.IsLB) (h : RelAmple A L) {W : S.Opens} (hW : IsAffineOpen W) :
    IsProjOver (A.hom ∣_ W ≫ hW.isoSpec.hom) := by
  obtain ⟨m, _, n, s, hc, hs⟩ := h W hW
  have hb : (powOver A L W m).IsLB := hL.linComb _ _
  exact isProjOver_of_section_system hb _ s hc fun i => by
    obtain ⟨haff, r, hratio, hsurj⟩ := hs i
    exact ⟨haff, r, hratio, sectionAlgebra_comp_iso _ hW.isoSpec.hom _ r hsurj⟩

end GlobalTheory.ProjectiveSections
