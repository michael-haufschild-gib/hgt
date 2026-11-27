import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineSectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback

/-! Relative ampleness presents the inverse image of an affine open as a projective scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
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
    exact isProjOver_of_isEmpty f
  · choose r hr using fun i => (h i).2
    exact (Coordinates.ofSections hL s r (fun i => (hr i).1) hc).isProjOver f
      (fun i => (h i).1) (fun i => (hr i).2)

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

/-- Over an affine base the relatively ample bundle gives a projective embedding. -/
theorem isProjOver_of_relAmple {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
    {L : LB A.left} (hL : L.IsLB) (h : RelAmple A L) : IsProjOver A.hom := by
  obtain ⟨m, _, n, s, hc, hs⟩ := h ⊤ (isAffineOpen_top _)
  let W : (Spec (CommRingCat.of R)).Opens := ⊤
  let q := A.hom ∣_ W
  haveI : IsIso W.ι := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have hproj : IsProjOver (q ≫ W.ι) :=
    isProjOver_of_section_system (hL.linComb _ _) _ s hc fun i => by
      obtain ⟨haff, r, hratio, hsurj⟩ := hs i
      exact ⟨haff, r, hratio, sectionAlgebra_comp_iso _ W.ι _ r hsurj⟩
  change IsProjOver (A.hom ∣_ W ≫ W.ι) at hproj
  rw [morphismRestrict_ι] at hproj
  let i := (A.hom ⁻¹ᵁ W).ι
  haveI : IsIso i := inferInstanceAs (IsIso A.left.topIso.hom)
  obtain ⟨N, a, _, hbase⟩ := hproj
  exact ⟨N, inv i ≫ a, inferInstance, by
    rw [Category.assoc, hbase, IsIso.inv_hom_id_assoc]⟩

end GlobalTheory.ProjectiveSections
