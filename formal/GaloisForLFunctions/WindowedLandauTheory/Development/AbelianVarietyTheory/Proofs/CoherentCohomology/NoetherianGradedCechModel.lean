import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatHomogeneousLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGradedCechCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedChartDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedMatrixBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps

/-! A graded Čech complex on smooth charts descends to a flat complex over a Noetherian ring. -/

open CategoryTheory DirectSum HTGeometry MvPolynomial

namespace GlobalTheory.SmoothDescent

private theorem nonempty_gradedCechIso_of_saturating {ι R G M : Type} [DecidableEq ι] [LinearOrder ι]
    [CommRing R] [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G]
    {D : ℤ → Submodule R M} [PolyGradedSMul ι D] [Decomposition D]
    {E : ℤ → Submodule R G} [PolyGradedSMul ι E] [Decomposition E]
    {f : M →ₗ[MvPolynomial ι R] G} (hf : IsGradedMap D E f)
    (hsat : ∀ i : ι, (∀ y, f y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧
      (∀ z, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range f))
    (n : ℤ) : Nonempty (gradedCech (ι := ι) D n ≅ gradedCech (ι := ι) E n) := by
  let φ := homLocDatumMap hf n
  have hφ (s : Finset ι) (r : R) (x : (homLocDatum (ι := ι) D n).obj s) :
      φ.app s (r • x) = r • φ.app s x := (homLocMap hf s n).map_smul r x
  let g := FinsetCechDatum.linearCochainMap
    (fun h => homLocDatum_res_smul D h n) (fun h => homLocDatum_res_smul E h n) φ hφ
  haveI : IsIso g := FinsetCechDatum.isIso_linearCochainMap _ _ _ _ (fun _ ⟨i, hi⟩ =>
    homLocMap_bijective_of_X hf hi (hsat i).1 (hsat i).2 n)
  exact ⟨asIso g⟩

/-- Smooth coefficient charts with finite projective dehomogenizations give a flat,
bounded Čech model with finite cohomology over a Noetherian coefficient ring. -/
theorem exists_noetherian_gradedCech_model {ι R G : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G]
    (D : ℤ → Submodule R G) [PolyGradedSMul ι D] [Decomposition D]
    (hChart : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P),
      Algebra.Smooth R B ∧ Module.Finite B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (X i) = 1 ∧
        (letI := Module.compHom P π.toRingHom
         Nonempty (QuotSMulTop (X i - 1 : MvPolynomial ι R) G ≃ₗ[MvPolynomial ι R] P)))
    (n : ℤ) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : IsNoetherianRing R₀) (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)),
      (∀ l j, Φ₀ l j ∈ polyGrading ι R₀ (e j - d l)) ∧
      let C := gradedCech (ι := ι) (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) n
      (∀ q, Module.Flat R₀ (C.X q)) ∧ (∀ q, Fintype.card ι ≤ q → Limits.IsZero (C.X q)) ∧
        (∀ q, Module.Finite R₀ (C.homology q)) ∧
        Nonempty (((ModuleCat.extendScalars R₀.val.toRingHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj C
          ≅ gradedCech (ι := ι) D n) := by
  obtain ⟨R₀, hnoeth, a, b, d, e, Φ₀, ψ, hΦ₀, hψ, h⟩ := exists_descended_graded_presentation D hChart
  let Φ := Φ₀.map (MvPolynomial.map R₀.val.toRingHom)
  let D₀ := grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)
  let D₁ := grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)
  have hΦ (l : Fin a) (j : Fin b) : Φ l j ∈ polyGrading ι R (e j - d l) :=
    map_mem_polyGrading R₀.val.toRingHom (hΦ₀ l j)
  letI : Decomposition D₀ := grQuotDecomposition (isGradedMap_mulVecLin hΦ₀).isHomogeneous_range
  letI : Decomposition D₁ := grQuotDecomposition (isGradedMap_mulVecLin hΦ).isHomogeneous_range
  obtain ⟨f, hf, hX, hdeg⟩ := exists_graded_matrix_baseChange (R := R) d Φ₀
  obtain ⟨iso₀⟩ := nonempty_gradedCech_baseChangeIso D₀ D₁ f hf hX hdeg n
  obtain ⟨iso₁⟩ := nonempty_gradedCechIso_of_saturating hψ (fun i => (h i).2) n
  letI := hnoeth
  refine ⟨R₀, hnoeth, a, b, d, e, Φ₀, hΦ₀,
    flat_gradedCech_of_flat_specializations D₀ (fun i => (h i).1) n, ?_,
    finite_gradedCech_homology D₀ n, ⟨iso₀ ≪≫ iso₁⟩⟩
  exact (homLocDatum (ι := ι) D₀ n).linearComplex_X_isZero (fun h => homLocDatum_res_smul D₀ h n)

end GlobalTheory.SmoothDescent
