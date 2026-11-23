import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartMorphisms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedArtinianFibre

/-! The origin fibre of a finite map to a projective coordinate chart is
reduced when the coordinate functions generate its cotangent spaces. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} {n : ℕ}
  {s : X ⟶ Spec (CommRingCat.of K)} {f : X ⟶ PSpace K n}

/-- The finite map on a standard affine chart, with polynomial coordinates. -/
def chartPolynomialPullback (hf : f ≫ PSpace.str K n = s) (i : Fin (n + 1)) :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} K →ₐ[K]
      SectionRing s (f ⁻¹ᵁ PSpace.coordinateOpen K n i) :=
  (sectionPullback hf (PSpace.coordinateOpen K n i)).comp (pspaceChartAlgEquiv K i).toAlgHom

theorem chartPolynomialPullback_X (hf : f ≫ PSpace.str K n = s) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    chartPolynomialPullback hf i (MvPolynomial.X j) =
      pspacePullRatio f (f ⁻¹ᵁ PSpace.coordinateOpen K n i) i le_rfl j.1 := by
  let V := PSpace.coordinateOpen K n i
  have h := congrArg (sectionPullback hf V) (pspaceChartAlgEquiv_X K i j)
  exact h.trans (congrArg (fun a : Γ(PSpace K n, V) ⟶ Γ(X, f ⁻¹ᵁ V) =>
    a.hom (pspaceChartRatio K i j.1)) (f.app_eq_appLE (U := V)))

theorem chartPolynomialPullback_finite [IsFinite f] (hf : f ≫ PSpace.str K n = s)
    (i : Fin (n + 1)) : (chartPolynomialPullback hf i).Finite :=
  RingHom.Finite.comp (f.finite_app _ (pspaceChart_isAffine i))
    (pspaceChartAlgEquiv K i).toRingEquiv.finite

variable [IsAlgClosed K] [IsFinite f] [LocallyOfFiniteType s]

/-- The origin fibre is reduced if, at every rational point of the fibre,
the coordinate functions span the maximal ideal modulo its square. -/
theorem isReduced_projectiveChart_originFibre (hf : f ≫ PSpace.str K n = s) (i : Fin (n + 1)) :
    let U := f ⁻¹ᵁ PSpace.coordinateOpen K n i
    let A := SectionRing s U
    let φ := chartPolynomialPullback hf i
    let I := Ideal.span (Set.range fun j => φ (MvPolynomial.X j))
    (∀ y : {y : X.BaseFieldPointOver K s // y.hom default ∈ U},
      (∀ j, affinePointEval y.1 y.2 (φ (MvPolynomial.X j)) = 0) →
      let m := RingHom.ker (affinePointEval y.1 y.2).toRingHom
      m ≤ I ⊔ m ^ 2) →
    IsReduced (A ⧸ I) := by
  intro U A φ I htr
  have hU : IsAffineOpen U := (pspaceChart_isAffine i).preimage f
  letI : Module.Finite K (A ⧸ I) :=
    finite_quotient_of_polynomial_coordinates φ (chartPolynomialPullback_finite hf i)
  letI : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite K (A ⧸ I)
  apply isReduced_of_artinian_quotient
  intro m hm hIm
  letI := hm
  obtain ⟨y, hy⟩ := exists_affinePoint_ker hU m
  have hz (j : {j : Fin (n + 1) // j ≠ i}) : affinePointEval y.1 y.2 (φ (MvPolynomial.X j)) = 0 := by
    have hmem : φ (MvPolynomial.X j) ∈ m := hIm (Ideal.subset_span (Set.mem_range_self j))
    exact RingHom.mem_ker.mp (hy.symm ▸ hmem)
  simpa only [hy] using htr y hz

end GlobalTheory.SchemeCohomology
