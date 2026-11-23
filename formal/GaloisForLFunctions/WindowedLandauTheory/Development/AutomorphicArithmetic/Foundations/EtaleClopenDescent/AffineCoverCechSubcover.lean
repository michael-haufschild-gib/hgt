import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverGenericGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverHodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechSubcoverLift

/-! Ordered restriction on regular rational cochains realizes the
identity on Hodge cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField] [Smooth s]
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {U : ι → X.Opens}
  {A : Finset ι → Subalgebra K X.functionField} {B : Finset κ → Subalgebra K X.functionField}

local instance : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X.carrier) :=
  hasExt_of_enoughInjectives _

private abbrev coeffSheaf (p : ℕ) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s p)

theorem IsAffCover.formCochainsEquiv_subcover (j : κ ↪o ι)
    (h : IsAffCover s U A) (g : IsAffCover s (U ∘ j) B) (p q : ℕ)
    (x : (h.formCechDatum p).cochainComplex.X q) :
    (g.formCochainsEquiv p q ((subcoverCechMap ⊤ U j (coeffSheaf (s := s) p)).f q x)).val =
      restrictIndex (k := K) j (h.formCochainsEquiv p q x).val := by
  funext I
  rw [restrictIndex_apply]
  by_cases hi : I.Nonempty
  · have hj : (I.map j.toEmbedding).Nonempty := Finset.map_nonempty.mpr hi
    rw [g.formCochainsEquiv_apply p q _ hi, h.formCochainsEquiv_apply p q x hj,
      subcoverCechMap_apply]
    exact h.sectionRationalForms_restriction g hj hi p
      (eqToHom (coverInter_orderEmbedding ⊤ U j I).symm) (x.val (I.map j.toEmbedding))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hi
    subst I
    rw [Finset.map_empty, g.formCochainsEquiv_apply_empty, h.formCochainsEquiv_apply_empty]

/-- The class of a regular rational cocycle restricts to the same
Hodge class on the subcover. -/
theorem IsAffCover.hodgeCechEquiv_subcover (j : κ ↪o ι)
    (h : IsAffCover s U A) (g : IsAffCover s (U ∘ j) B)
    (hB : ∀ I, I.Nonempty → A (I.map j.toEmbedding) = B I)
    (p q : ℕ) (x : HodgeCohomology s p q) :
    let L := cech (fun I => omB K X.functionField (A I) p)
    let R := cech (fun I => omB K X.functionField (B I) p)
    let f := restrictIndex (k := K) (M := DR K X.functionField) j
    let hf : IsMap L R f := isMap_restrictIndex _ _ j
      (fun I hi => le_of_eq (congrArg (fun B => omB K X.functionField B p) (hB I hi)))
    L.hmap R f hf q (h.hodgeCechEquiv p q x) = g.hodgeCechEquiv p q x := by
  intro L R f hf
  have ha (I : Finset ι) (hi : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) := by
    simpa only [coverInter, top_inf_eq] using h.affine I hi
  have hb (I : Finset κ) (hi : I.Nonempty) : IsAffineOpen (coverInter ⊤ (U ∘ j) I) := by
    simpa only [coverInter, top_inf_eq] using g.affine I hi
  let H := affineFormsLeray s p q h.cover.ge ha
  let G := affineFormsLeray s p q g.cover.ge hb
  let φ := subcoverCechMap ⊤ U j (coeffSheaf (s := s) p)
  obtain ⟨z, rfl⟩ := H.surjective x
  let z' := HomologicalComplex.homologyMap φ q z
  have hR : G z' = H z :=
    moduleLerayLinearEquivAt_subcover j (relativeForms s p) q h.cover.ge g.cover.ge
      (fun I hi => relativeForms_acyclicOn s p (ha I hi))
      (fun I hi => relativeForms_acyclicOn s p (hb I hi)) z
  calc
    _ = L.hmap R f hf q (h.formCechLinearEquiv p q z) :=
      congrArg (L.hmap R f hf q) (h.hodgeCechEquiv_affineFormsLeray p q ha z)
    _ = g.formCechLinearEquiv p q z' :=
      (h.formCechLinearEquiv_natural p q g φ f hf (h.formCochainsEquiv_subcover j g p q) z).symm
    _ = g.hodgeCechEquiv p q (G z') := (g.hodgeCechEquiv_affineFormsLeray p q hb z').symm
    _ = _ := congrArg (g.hodgeCechEquiv p q) hR

end GlobalTheory.PD
