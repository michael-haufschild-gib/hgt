import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IntegralClosureFiniteImage
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCoordinateIntersections
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveProjectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothNormalCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveSpaceDimension

/-! The sections on the inverse images of projective chart intersections
are precisely the normalizations of the corresponding ratio algebras. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} {d : ℕ} {f : X ⟶ PSpace K d}

private abbrev baseInter (I : Finset (Fin (d + 1))) := I.inf (PSpace.coordinateOpen K d)

private abbrev sourceChart (i : Fin (d + 1)) := f ⁻¹ᵁ PSpace.coordinateOpen K d i

omit [IsIntegral X] in
private theorem preimage_baseInter (I : Finset (Fin (d + 1))) :
    f ⁻¹ᵁ baseInter (K := K) I = I.inf (sourceChart (f := f)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [baseInter, Finset.inf_empty, Scheme.Hom.preimage_top]
  | insert j J hj ih =>
    change f ⁻¹ᵁ ((insert j J).inf (PSpace.coordinateOpen K d)) =
      (insert j J).inf (sourceChart (f := f))
    rw [Finset.inf_insert, f.preimage_inf, Finset.inf_insert]
    exact congrArg ((sourceChart (f := f) j) ⊓ ·) ih

private theorem generic_mem_baseInter_preimage (hgen : ∀ i, genericPoint X ∈ sourceChart (f := f) i)
    (I : Finset (Fin (d + 1))) : genericPoint X ∈ f ⁻¹ᵁ baseInter (K := K) I := by
  classical
  rw [preimage_baseInter]
  induction I using Finset.induction_on with
  | empty => simp
  | insert i J hi ih => rw [Finset.inf_insert]; exact ⟨hgen i, ih⟩

private theorem isAffineOpen_baseInter {I : Finset (Fin (d + 1))} (hI : I.Nonempty) :
    IsAffineOpen (baseInter (K := K) I) := by
  simpa only [HTGeometry.coverInter, top_inf_eq] using
    PSpace.isAffineOpen_coordinateInter K d hI

/-- The normalization of the target ratio algebra is the generic image of
the sections on the corresponding inverse image. -/
theorem projectionNormalization_eq_range [IsFinite f] [SmoothOfRelativeDimension d s]
    (hf : f ≫ PSpace.str K d = s) (hgen : ∀ i, genericPoint X ∈ sourceChart (f := f) i)
    (I : Finset (Fin (d + 1))) (hI : I.Nonempty) (y : X.functionField) :
    letI := sectionFunctionFieldAlgebra s
    let x := projectionCoordinates hf (hgen 0)
    y ∈ rB K X.functionField x I ↔ ∃ b : Γ(X, f ⁻¹ᵁ baseInter (K := K) I),
      (X.presheaf.germ _ (genericPoint X) (generic_mem_baseInter_preimage hgen I)).hom b = y := by
  letI := sectionFunctionFieldAlgebra s
  let F := projectionField hf (hgen 0)
  let x := projectionCoordinates hf (hgen 0)
  let V := baseInter (K := K) I
  let U := f ⁻¹ᵁ V
  let B := SectionRing s U
  have hV : IsAffineOpen V := isAffineOpen_baseInter hI
  have hU : IsAffineOpen U := hV.preimage f
  let hη := generic_mem_baseInter_preimage hgen I
  letI : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  letI : Algebra B X.functionField := (X.germToFunctionField U).hom.toAlgebra
  letI : IsFractionRing B X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsIntegrallyClosed B := integrallyClosed_smooth_affineOpen s d hU
  let g := sectionToFunctionField s U
  let q := sectionPullback hf V
  let R := rA K x I
  have hcoord (i : I) (j : Fin (d + 1)) :
      (g.comp q) (coordinateInterRatio K I i j) = F.val (x j / x i) := by
    change (g.comp q) (coordinateInterRatio K I i j) = ((x j / x i : F) : X.functionField)
    exact (congrArg g (sectionPullback_coordinateInterRatio K hf I i j)).trans
      ((germ_pspacePullRatio f U hη i.1 j _).trans
        (projectionCoordinates_ratio hf (hgen 0) i.1 j (hgen i.1)).symm)
  have hR : R.map F.val = (g.comp q).range := by
    rw [← Algebra.map_top, ← adjoin_coordinateInterRatio_eq_top K I hI]
    change (Algebra.adjoin K _).map F.val = (Algebra.adjoin K _).map (g.comp q)
    rw [AlgHom.map_adjoin, AlgHom.map_adjoin]
    congr 1
    ext z
    constructor
    · rintro ⟨a, ⟨i, hi, j, rfl⟩, rfl⟩
      exact ⟨coordinateInterRatio K I ⟨i, hi⟩ j, ⟨(⟨i, hi⟩, j), rfl⟩, hcoord _ _⟩
    · rintro ⟨b, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      exact ⟨x j / x i, ⟨i, i.2, j, rfl⟩, (hcoord _ _).symm⟩
  let e := R.equivMapOfInjective F.val Subtype.val_injective
  have halg : (algebraMap (R.map F.val) X.functionField).comp e.toRingEquiv.toRingHom =
      algebraMap R X.functionField := rfl
  have he := e.toRingEquiv.isIntegral_iff halg y
  have hr : (R.map F.val).toSubring = ((algebraMap B X.functionField).comp q.toRingHom).range :=
    congrArg Subalgebra.toSubring hR
  have hfin : q.toRingHom.Finite := f.finite_app V hV
  change IsIntegral R y ↔ ∃ b : B, algebraMap B X.functionField b = y
  rw [he]
  change IsIntegral (R.map F.val).toSubring y ↔ _
  rw [hr]
  exact isIntegral_range_iff_of_finite q.toRingHom hfin y

/-- A finite projection with generic point in every coordinate chart gives
the normalized affine cover of the source. -/
theorem isAffCover_projection [IsFinite f] [SmoothOfRelativeDimension d s]
    (hf : f ≫ PSpace.str K d = s) (hgen : ∀ i, genericPoint X ∈ sourceChart (f := f) i) :
    letI := sectionFunctionFieldAlgebra s
    IsAffCover s (sourceChart (f := f)) (rB K X.functionField (projectionCoordinates hf (hgen 0))) := by
  letI := sectionFunctionFieldAlgebra s
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro I hI
    rw [← preimage_baseInter]
    exact (isAffineOpen_baseInter hI).preimage f
  · change (⨆ i, f ⁻¹ᵁ PSpace.coordinateOpen K d i) = ⊤
    rw [← f.preimage_iSup, PSpace.iSup_coordinateOpen, f.preimage_top]
  · intro I
    rw [← preimage_baseInter]
    exact generic_mem_baseInter_preimage hgen I
  · intro I hI y
    have key (V : X.Opens) (_ : V = f ⁻¹ᵁ baseInter (K := K) I) (hV : genericPoint X ∈ V) :
        y ∈ rB K X.functionField (projectionCoordinates hf (hgen 0)) I ↔
          ∃ a : Γ(X, V), (X.presheaf.germ V (genericPoint X) hV).hom a = y := by
      subst V
      exact projectionNormalization_eq_range hf hgen I hI y
    exact key _ (preimage_baseInter I).symm _

/-- The function field of a finite projection is a finite separable extension
of the rational field, with smooth normalized coordinate algebras. -/
theorem isFinCover_projection [IsAlgClosed K] [CharZero K] [IsFinite f] [SmoothOfRelativeDimension d s]
    (hf : f ≫ PSpace.str K d = s) (hgen : ∀ i, genericPoint X ∈ sourceChart (f := f) i) :
    letI := sectionFunctionFieldAlgebra s
    IsFinCover K X.functionField (projectionCoordinates hf (hgen 0)) := by
  letI := sectionFunctionFieldAlgebra s
  let F := projectionField hf (hgen 0)
  letI : FiniteDimensional F X.functionField := finiteDimensional_projectionField hf (hgen 0)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hcov := isAffCover_projection hf hgen
  refine {
    pd := isPd_projectionCoordinates hf hgen
    fin := inferInstance
    smooth := ?_
    sep := inferInstance }
  intro i
  let U := ({i} : Finset (Fin (d + 1))).inf (sourceChart (f := f))
  have hU : IsAffineOpen U := hcov.affine {i} (Finset.singleton_nonempty i)
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have ht : U ≤ s ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := le_top
  have hs : (algebraMap K (SectionRing s U)).Smooth :=
    RingHom.Smooth.respectsIso.right _ e (s.smooth_appLE (isAffineOpen_top _) hU ht)
  letI : Algebra.Smooth K (SectionRing s U) := RingHom.smooth_algebraMap.mp hs
  exact Algebra.Smooth.of_equiv (hcov.sectionEquiv {i} (Finset.singleton_nonempty i))

end GlobalTheory.SchemeCohomology
