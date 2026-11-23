import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteProjectiveProjection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedProjectionFibre
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TransversalProjectionForms

/-! The coordinate equations of a transverse projective projection cut out a reduced fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  {f : X ⟶ PSpace K d}

private def chartPolynomialPullback_cast (hf : f ≫ PSpace.str K d = s)
    (i : Fin (d + 1)) {W : X.Opens} (hW : f ⁻¹ᵁ PSpace.coordinateOpen K d i = W) :
    MvPolynomial {j : Fin (d + 1) // j ≠ i} K →ₐ[K] SectionRing s W :=
  hW ▸ chartPolynomialPullback hf i

private theorem chartPolynomialPullback_cast_X (hf : f ≫ PSpace.str K d = s)
    (i : Fin (d + 1)) {W : X.Opens} (hW : f ⁻¹ᵁ PSpace.coordinateOpen K d i = W)
    (j : {j : Fin (d + 1) // j ≠ i}) :
    chartPolynomialPullback_cast hf i hW (MvPolynomial.X j) = pspacePullRatio f W i hW.ge j.1 := by
  subst W
  exact chartPolynomialPullback_X hf i j

private theorem isReduced_originFibre_cast [IsAlgClosed K] [IsFinite f] [LocallyOfFiniteType s]
    (hf : f ≫ PSpace.str K d = s) (i : Fin (d + 1)) {W : X.Opens}
    (hW : f ⁻¹ᵁ PSpace.coordinateOpen K d i = W) :
    let A := SectionRing s W
    let φ := chartPolynomialPullback_cast hf i hW
    let I := Ideal.span (Set.range fun j => φ (MvPolynomial.X j))
    (∀ y : {y : X.BaseFieldPointOver K s // y.hom default ∈ W},
      (∀ j, affinePointEval y.1 y.2 (φ (MvPolynomial.X j)) = 0) →
      SpansCotangentAt y.1 y.2 (fun j => φ (MvPolynomial.X j))) →
    IsReduced (A ⧸ I) := by
  subst W
  exact isReduced_projectiveChart_originFibre hf i

/-- The section ring of the origin chart modulo its coordinate ratios is
reduced for the projection given by transverse forms. -/
theorem isReduced_originFibre_of_transversalProjectionForms [IsAlgClosed K] [IsIntegral X]
    [LocallyOfFiniteType s] {N : ℕ} (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hi : i ≫ PSpace.str K N = s) {S : Finset (X.BaseFieldPointOver K s)}
    (T : TransversalProjectionForms i d S) :
    let W := formBasicOpen i (T.forms 0).1
    let A := SectionRing s W
    let r (j : Fin d) : A := projectiveRatio i (T.forms 0).2 (T.forms j.succ).2
    IsReduced (A ⧸ Ideal.span (Set.range r)) := by
  intro W A r
  let F (j : Fin (d + 1)) := (T.forms j).1
  let hF (j : Fin (d + 1)) := (T.forms j).2
  let f := formProjection i F hF s T.cover
  have hf : f ≫ PSpace.str K d = s := formProjection_base i F hF s T.cover
  letI : IsFinite f := formProjection_isFinite i F hF s T.cover hi T.positive
  let e : f ⁻¹ᵁ PSpace.coordinateOpen K d 0 = W := formProjection_preimage i F hF s T.cover 0
  let J := {j : Fin (d + 1) // j ≠ 0}
  let φ := chartPolynomialPullback_cast hf 0 e
  have hφ (j : J) : φ (MvPolynomial.X j) = projectiveRatio i (hF 0) (hF j.1) :=
    (chartPolynomialPullback_cast_X hf 0 e j).trans (formProjection_ratio i F hF s T.cover 0 j.1)
  have hr : Set.range (fun j : J => φ (MvPolynomial.X j)) = Set.range r := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j.1.pred j.2, ?_⟩
      change r (j.1.pred j.2) = φ (MvPolynomial.X j)
      rw [hφ]
      simp only [r, Fin.succ_pred]
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.succ, Fin.succ_ne_zero j⟩, hφ _⟩
  have ht (y : {y : X.BaseFieldPointOver K s // y.hom default ∈ W})
      (hy : ∀ j : J, affinePointEval y.1 y.2 (φ (MvPolynomial.X j)) = 0) :
      SpansCotangentAt y.1 y.2 (fun j : J => φ (MvPolynomial.X j)) := by
    have hzero (j : Fin d) : y.1.hom default ∉ formBasicOpen i (F j.succ) := by
      apply (affinePointEval_projectiveRatio_eq_zero_iff i (hF 0) (hF j.succ) y.1 y.2).mp
      exact (congrArg (affinePointEval y.1 y.2) (hφ ⟨j.succ, Fin.succ_ne_zero j⟩)).symm.trans
        (hy ⟨j.succ, Fin.succ_ne_zero j⟩)
    unfold SpansCotangentAt
    rw [hr]
    exact T.tangent y.1 y.2 hzero
  have hred := isReduced_originFibre_cast hf 0 e ht
  exact (congrArg (fun P : Set A => IsReduced (A ⧸ Ideal.span P)) hr).mp hred

/-- A smooth integral projective scheme admits a finite projection whose
origin fibre is reduced and contains the prescribed rational points. -/
theorem exists_transversalProjectionForms_reduced [IsAlgClosed K] [CharZero K] [IsIntegral X]
    {N : ℕ} (i : X ⟶ PSpace K N) [IsClosedImmersion i] (hi : i ≫ PSpace.str K N = s)
    (d : ℕ) [SmoothOfRelativeDimension d s] (S : Finset (X.BaseFieldPointOver K s)) :
    ∃ T : TransversalProjectionForms i d S,
      let W := formBasicOpen i (T.forms 0).1
      let A := SectionRing s W
      let r (j : Fin d) : A := projectiveRatio i (T.forms 0).2 (T.forms j.succ).2
      IsReduced (A ⧸ Ideal.span (Set.range r)) := by
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨T⟩ := exists_transversalProjectionForms i hi d S
  exact ⟨T, isReduced_originFibre_of_transversalProjectionForms i hi T⟩

end GlobalTheory.SchemeCohomology
