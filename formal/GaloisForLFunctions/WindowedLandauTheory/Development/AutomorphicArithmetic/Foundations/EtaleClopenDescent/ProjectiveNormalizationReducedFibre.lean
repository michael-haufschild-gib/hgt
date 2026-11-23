import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveNormalizationCharts
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedTransversalProjection

/-! Normalized projective charts with a reduced origin fibre through
a prescribed finite set of rational points. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} (d : ℕ) [SmoothOfRelativeDimension d s]

private theorem isReduced_quotient_of_coordinateEquiv {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (r : Fin d → A) (t : Fin d → B) (he : ∀ j, e (r j) = t j)
    (h : IsReduced (A ⧸ Ideal.span (Set.range r))) : IsReduced (B ⧸ Ideal.span (Set.range t)) := by
  have himage : (e : A → B) '' Set.range r = Set.range t := by
    rw [← Set.range_comp e r]
    exact congrArg Set.range (funext he)
  have hmap : Ideal.span (Set.range t) = (Ideal.span (Set.range r)).map e.toRingHom := by
    rw [Ideal.map_span, show ⇑e.toRingHom = ⇑e from rfl, himage]
  let q := Ideal.quotientEquiv _ _ e hmap
  letI := h
  exact isReduced_of_injective q.symm q.symm.injective

private def chartEquivAt {ι : Type} {U : ι → X.Opens}
    [Algebra K X.functionField] {B : Finset ι → Subalgebra K X.functionField} (h : IsAffCover s U B) (i : ι) (V : X.Opens) (hV : U i = V) :
    SectionRing s V ≃ₐ[K] B {i} :=
  have E : ({i} : Finset ι).inf U = V := (Finset.inf_singleton).trans hV
  E ▸ h.sectionEquiv {i} (Finset.singleton_nonempty i)

omit [IsAlgClosed K] [CharZero K] in
private theorem chartEquivAt_val {ι : Type} {U : ι → X.Opens}
    [Algebra K X.functionField] {B : Finset ι → Subalgebra K X.functionField}
    (h : IsAffCover s U B) (i : ι) (V : X.Opens) (hV : U i = V)
    (hη : genericPoint X ∈ V) (a : SectionRing s V) :
    (chartEquivAt h i V hV a : X.functionField) = (X.presheaf.germ V _ hη).hom a := by
  have key (W : X.Opens) (hW : ({i} : Finset ι).inf U = W)
      (hη' : genericPoint X ∈ W) (a' : SectionRing s W) :
      ((hW ▸ h.sectionEquiv {i} (Finset.singleton_nonempty i) :
          SectionRing s W ≃ₐ[K] B {i}) a' : X.functionField) =
        (X.presheaf.germ W _ hη').hom a' := by
    subst W
    rfl
  exact key V ((Finset.inf_singleton).trans hV) hη a

/-- A smooth integral projective scheme over an algebraically closed field
of characteristic zero has a normalized projective cover with reduced origin
fibre through every point of a prescribed finite set. -/
theorem exists_finiteCover_projSpace_reduced_fibre_origin (hp : IsProjOver s)
    (S : Finset (X.BaseFieldPointOver K s)) :
    letI := sectionFunctionFieldAlgebra s
    ∃ (F : IntermediateField K X.functionField) (x : Fin (d + 1) → F)
      (U : Fin (d + 1) → X.Opens),
      IsFinCover K X.functionField x ∧ IsAffCover s U (rB K X.functionField x) ∧
      IsReduced ((rB K X.functionField x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem K X.functionField x j⟩ : rB K X.functionField x {0}))) ∧
      ∀ y ∈ S, ∃ hy : y.hom default ∈ U 0,
        ∀ (j : Fin d) (hη : genericPoint X ∈ U 0) (a : SectionRing s (U 0)),
          (X.presheaf.germ (U 0) _ hη).hom a = algebraMap F X.functionField (x j.succ / x 0) →
            affinePointEval y hy a = 0 := by
  letI := sectionFunctionFieldAlgebra s
  obtain ⟨N, i, hi, hstr⟩ := hp
  letI := hi
  obtain ⟨T, hred⟩ := exists_transversalProjectionForms_reduced i hstr d S
  let G (j : Fin (d + 1)) := (T.forms j).1
  let hG (j : Fin (d + 1)) := (T.forms j).2
  let f := formProjection i G hG s T.cover
  letI : IsFinite f := formProjection_isFinite i G hG s T.cover hstr T.positive
  have hf := formProjection_base i G hG s T.cover
  let U (j : Fin (d + 1)) := f ⁻¹ᵁ PSpace.coordinateOpen K d j
  let V (j : Fin (d + 1)) := formBasicOpen i (G j)
  have hu (j : Fin (d + 1)) : U j = V j := formProjection_preimage i G hG s T.cover j
  have hgen (j : Fin (d + 1)) : genericPoint X ∈ U j := (hu j).ge (T.generic j)
  let F := projectionField hf (hgen 0)
  let x := projectionCoordinates hf (hgen 0)
  have hcov := isAffCover_projection hf hgen
  let e := chartEquivAt hcov 0 (V 0) (hu 0)
  let r (j : Fin d) : SectionRing s (V 0) := projectiveRatio i (hG 0) (hG j.succ)
  letI : Nonempty (V 0) := ⟨⟨genericPoint X, T.generic 0⟩⟩
  have hg (j : Fin d) :
      (X.presheaf.germ (V 0) _ (T.generic 0)).hom (r j) =
        algebraMap F X.functionField (x j.succ / x 0) := by
    change (X.presheaf.germ (V 0) _ (T.generic 0)).hom (projectiveRatio i (hG 0) (hG j.succ)) = _
    rw [← formProjection_ratio i G hG s T.cover 0 j.succ]
    exact (germ_pspacePullRatio f (V 0) (T.generic 0) 0 j.succ (hu 0).ge).trans
      (projectionCoordinates_ratio hf (hgen 0) 0 j.succ (hgen 0)).symm
  have he (j : Fin d) : e (r j) = (⟨_, tco_mem K X.functionField x j⟩ : rB K X.functionField x {0}) :=
    Subtype.ext ((chartEquivAt_val hcov 0 (V 0) (hu 0) (T.generic 0) (r j)).trans (hg j))
  have hcov' : IsAffCover s V (rB K X.functionField x) := (funext hu) ▸ hcov
  refine ⟨F, x, V, isFinCover_projection hf hgen, hcov',
    isReduced_quotient_of_coordinateEquiv d e.toRingEquiv r _ he hred, ?_⟩
  intro y hy
  obtain ⟨hy₀, hz⟩ := T.pinned y hy
  refine ⟨hy₀, fun j hη a ha => ?_⟩
  have h : a = r j := germ_injective_of_isIntegral X (genericPoint X) hη (ha.trans (hg j).symm)
  rw [h]
  exact (affinePointEval_projectiveRatio_eq_zero_iff i (hG 0) (hG j.succ) y hy₀).mpr (hz j)

end GlobalTheory.SchemeCohomology
